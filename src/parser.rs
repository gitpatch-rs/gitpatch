use std::borrow::Cow;
use std::error::Error;

use chrono::DateTime;
use nom::combinator::verify;
use nom::*;
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_until},
    character::complete::{char, digit1, line_ending, none_of, not_line_ending, one_of},
    combinator::{map, map_opt, not, opt},
    error::context,
    multi::{many0, many1},
    sequence::{delimited, preceded, terminated, tuple},
};

use crate::ast::*;

type Input<'a> = nom_locate::LocatedSpan<&'a str>;

/// Type returned when an error occurs while parsing a patch
#[derive(Debug, Clone)]
pub struct ParseError<'a> {
    /// The line where the parsing error occurred
    pub line: u32,
    /// The offset within the input where the parsing error occurred
    pub offset: usize,
    /// The failed input
    pub fragment: &'a str,
    /// The actual parsing error
    pub kind: nom::error::ErrorKind,
}

#[doc(hidden)]
impl<'a> From<nom::Err<nom::error::Error<Input<'a>>>> for ParseError<'a> {
    fn from(err: nom::Err<nom::error::Error<Input<'a>>>) -> Self {
        match err {
            nom::Err::Incomplete(_) => unreachable!("bug: parser should not return incomplete"),
            // Unify both error types because at this point the error is not recoverable
            nom::Err::Error(error) | nom::Err::Failure(error) => Self {
                line: error.input.location_line(),
                offset: error.input.location_offset(),
                fragment: error.input.fragment(),
                kind: error.code,
            },
        }
    }
}

impl std::fmt::Display for ParseError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "Line {}: Error while parsing: {}",
            self.line, self.fragment
        )
    }
}

impl Error for ParseError<'_> {
    fn description(&self) -> &str {
        self.kind.description()
    }
}

fn consume_content_line(input: Input<'_>) -> IResult<Input<'_>, (&str, bool)> {
    let (input, raw) = terminated(not_line_ending, line_ending)(input)?;

    let (input, missing_newline) = opt(terminated(
        tag("\\ No newline at end of file"),
        opt(line_ending),
    ))(input)?;

    Ok((input, (raw.fragment(), missing_newline.is_some())))
}

pub(crate) fn parse_single_patch(s: &str) -> Result<Patch<'_>, ParseError<'_>> {
    let (remaining_input, patch) = patch(Input::new(s))?;
    // Parser should return an error instead of producing remaining input
    assert!(
        remaining_input.fragment().is_empty(),
        "bug: failed to parse entire input. \
        Remaining: '{}'",
        remaining_input.fragment()
    );
    Ok(patch)
}

pub(crate) fn parse_multiple_patches(s: &str) -> Result<Vec<Patch<'_>>, ParseError<'_>> {
    let (remaining_input, patches) = multiple_patches(Input::new(s))?;
    // Parser should return an error instead of producing remaining input
    if !remaining_input.fragment().is_empty() {
        return Err(ParseError {
            line: remaining_input.location_line(),
            offset: remaining_input.location_offset(),
            fragment: remaining_input.fragment(),
            kind: nom::error::ErrorKind::Eof,
        });
    }
    Ok(patches)
}

fn multiple_patches(input: Input) -> IResult<Input, Vec<Patch>> {
    many1(patch)(input)
}

fn patch(input: Input) -> IResult<Input, Patch> {
    if let Ok(patch) = binary_files_differ(input) {
        return Ok(patch);
    }
    if let Ok(patch) = file_rename_only(input) {
        return Ok(patch);
    }
    let (input, files) = headers(input)?;
    let (input, hunks) = chunks(input)?;
    // Ignore trailing empty lines produced by some diff programs
    let (input, _) = many0(line_ending)(input)?;

    let (old_missing_newline, new_missing_newline) = hunks
        .last()
        .map(|hunk| (hunk.old_missing_newline, hunk.new_missing_newline))
        .unwrap_or((false, false));

    let (old, new) = files;
    Ok((
        input,
        Patch {
            old,
            new,
            hunks,
            old_missing_newline,
            new_missing_newline,
        },
    ))
}

/// Recognize a "binary files XX and YY differ" line as an empty patch.
fn binary_files_differ(input: Input) -> IResult<Input, Patch> {
    // The names aren't quoted so this seems to require lookahead and then
    // parsing the identified string.
    let (input, (old, new)) = context(
        "Binary file line",
        delimited(
            tag("Binary files "),
            map_opt(take_until("\n"), |names: Input<'_>| {
                names
                    .trim_end()
                    .strip_suffix(" differ")
                    .and_then(|s| s.split_once(" and "))
            }),
            line_ending,
        ),
    )(input)?;
    Ok((
        input,
        Patch {
            old: File {
                path: Cow::Borrowed(old),
                meta: None,
            },
            new: File {
                path: Cow::Borrowed(new),
                meta: None,
            },
            hunks: Vec::new(),
            old_missing_newline: false,
            new_missing_newline: false,
        },
    ))
}

/// Parse patches with "similarity index 100%", i.e., patches where a file is renamed without any
/// other change in its diff.
///
/// The `parse` function should handle rename diffs with similary index less than 100%, at least as per the test
/// `parses_file_renames_with_some_diff`.
fn file_rename_only(input: Input<'_>) -> IResult<Input<'_>, Patch<'_>> {
    let (rest, _parsed) = take_until("\nsimilarity index 100%\n")(input)?;
    let (rest, _parsed) = tag("\nsimilarity index 100%\n")(rest)?;

    let (rest, old_name) = delimited(tag("rename from "), take_until("\n"), line_ending)(rest)?;

    let (rest, new_name) = delimited(tag("rename to "), take_until("\n"), line_ending)(rest)?;

    Ok((
        rest,
        Patch {
            old: File {
                path: Cow::Borrowed(&old_name),
                meta: None,
            },
            new: File {
                path: Cow::Borrowed(&new_name),
                meta: None,
            },
            hunks: Vec::new(),
            old_missing_newline: false,
            new_missing_newline: false,
        },
    ))
}

// Header lines
fn headers(input: Input) -> IResult<Input, (File, File)> {
    // Ignore any preamble lines in produced diffs
    let (input, _) = take_until("--- ")(input)?;
    let (input, _) = tag("--- ")(input)?;
    let (input, oldfile) = header_line_content(input)?;
    let (input, _) = line_ending(input)?;
    let (input, _) = tag("+++ ")(input)?;
    let (input, newfile) = header_line_content(input)?;
    let (input, _) = line_ending(input)?;
    Ok((input, (oldfile, newfile)))
}

fn header_line_content(input: Input) -> IResult<Input, File> {
    let (input, filename) = filename(input)?;
    let (input, after) = opt(preceded(char('\t'), file_metadata))(input)?;

    Ok((
        input,
        File {
            path: filename,
            meta: after.and_then(|after| match after {
                Cow::Borrowed("") => None,
                Cow::Borrowed("\t") => None,
                _ => Some(
                    DateTime::parse_from_str(after.as_ref(), "%F %T%.f %z")
                        .or_else(|_| DateTime::parse_from_str(after.as_ref(), "%F %T %z"))
                        .ok()
                        .map_or_else(|| FileMetadata::Other(after), FileMetadata::DateTime),
                ),
            }),
        },
    ))
}

// Hunks of the file differences
fn chunks(input: Input) -> IResult<Input, Vec<Hunk>> {
    many1(chunk)(input)
}

fn is_next_header(input: Input<'_>) -> bool {
    // Check for diff file header or chunk header
    input.starts_with("diff ")
        || input.starts_with("--- ")
        || input.starts_with("+++ ")
        || input.starts_with("@@ ")
}

/// Looks for lines starting with + or - or space, but not +++ or ---. Not a foolproof check.
///
/// For example, if someone deletes a line that was using the pre-decrement (--) operator or adds a
/// line that was using the pre-increment (++) operator, this will fail.
///
/// Example where this doesn't work:
///
/// --- main.c
/// +++ main.c
/// @@ -1,4 +1,7 @@
/// +#include<stdio.h>
/// +
///  int main() {
///  double a;
/// --- a;
/// +++ a;
/// +printf("%d\n", a);
///  }
///
/// We will fail to parse this entire diff.
///
/// By checking for `+++ ` instead of just `+++`, we add at least a little more robustness because
/// we know that people typically write `++a`, not `++ a`. That being said, this is still not enough
/// to guarantee correctness in all cases.
///
///FIXME: Use the ranges in the chunk header to figure out how many chunk lines to parse. Will need
/// to figure out how to count in nom more robustly than many1!(). Maybe using switch!()?
///FIXME: The test_parse_triple_plus_minus_hack test will no longer panic when this is fixed.
fn chunk(input: Input) -> IResult<Input, Hunk> {
    let (input, ranges) = chunk_header(input)?;

    // Parse chunk lines, using the range information to guide parsing
    let (input, lines) = many0(verify(
        alt((
            // Detect added lines
            map(
                preceded(tuple((char('+'), not(tag("++ ")))), consume_content_line),
                |(line, missing_newline)| LineKind::Add.to_line_full(line, missing_newline),
            ),
            // Detect removed lines
            map(
                preceded(tuple((char('-'), not(tag("-- ")))), consume_content_line),
                |(line, missing_newline)| LineKind::Remove.to_line_full(line, missing_newline),
            ),
            // Detect context lines
            map(
                preceded(char(' '), consume_content_line),
                |(line, missing_newline)| LineKind::Context.to_line_full(line, missing_newline),
            ),
            // Handle empty lines within the chunk
            map(tag("\n"), |_| LineKind::Context.to_line_full("", false)),
        )),
        // Stop parsing when we detect the next header or have parsed the expected number of lines
        |_| !is_next_header(input),
    ))(input)?;

    // Track whether the last line for each side of the hunk is missing a final newline
    let mut new_missing_newline = false;
    let mut old_missing_newline = false;
    for line in &lines {
        let is_new = matches!(line.kind, LineKind::Add | LineKind::Context);
        let is_old = matches!(line.kind, LineKind::Remove | LineKind::Context);

        if is_new {
            new_missing_newline = line.missing_newline;
        }

        if is_old {
            old_missing_newline = line.missing_newline;
        }
    }

    let (old_range, new_range, range_hint) = ranges;
    Ok((
        input,
        Hunk {
            old_range,
            new_range,
            range_hint,
            lines,
            old_missing_newline,
            new_missing_newline,
        },
    ))
}

fn chunk_header(input: Input<'_>) -> IResult<Input<'_>, (Range, Range, &'_ str)> {
    let (input, _) = tag("@@ -")(input)?;
    let (input, old_range) = range(input)?;
    let (input, _) = tag(" +")(input)?;
    let (input, new_range) = range(input)?;
    let (input, _) = tag(" @@")(input)?;

    // Save hint provided after @@ (git sometimes adds this)
    let (input, range_hint) = not_line_ending(input)?;
    let (input, _) = line_ending(input)?;
    Ok((input, (old_range, new_range, &range_hint)))
}

fn range(input: Input<'_>) -> IResult<Input<'_>, Range> {
    let (input, start) = u64_digit(input)?;
    let (input, count) = opt(preceded(char(','), u64_digit))(input)?;
    let count = count.unwrap_or(1);
    Ok((input, Range { start, count }))
}

fn u64_digit(input: Input<'_>) -> IResult<Input<'_>, u64> {
    let (input, digits) = digit1(input)?;
    let num = digits.fragment().parse::<u64>().unwrap();
    Ok((input, num))
}

fn filename(input: Input<'_>) -> IResult<Input<'_>, Cow<'_, str>> {
    alt((quoted, bare))(input)
}

fn file_metadata(input: Input) -> IResult<Input, Cow<str>> {
    alt((
        quoted,
        map(not_line_ending, |data: Input<'_>| {
            Cow::Borrowed(*data.fragment())
        }),
    ))(input)
}

fn quoted(input: Input) -> IResult<Input, Cow<str>> {
    delimited(char('\"'), unescaped_str, char('\"'))(input)
}

fn bare(input: Input) -> IResult<Input, Cow<str>> {
    map(is_not("\t\r\n"), |data: Input<'_>| {
        Cow::Borrowed(*data.fragment())
    })(input)
}

fn unescaped_str(input: Input) -> IResult<Input, Cow<str>> {
    let (input, raw) = many1(alt((unescaped_char, escaped_char)))(input)?;
    Ok((input, raw.into_iter().collect::<Cow<str>>()))
}

// Parses an unescaped character
fn unescaped_char(input: Input) -> IResult<Input, char> {
    none_of("\0\n\r\t\\\"")(input)
}

// Parses an escaped character and returns its unescaped equivalent
fn escaped_char(input: Input) -> IResult<Input, char> {
    map(preceded(char('\\'), one_of(r#"0nrt"\"#)), |ch| match ch {
        '0' => '\0',
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        '"' => '"',
        '\\' => '\\',
        _ => unreachable!(),
    })(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    use pretty_assertions::assert_eq;

    type ParseResult<'a, T> = Result<T, nom::Err<nom::error::Error<Input<'a>>>>;

    // Using a macro instead of a function so that error messages cite the most helpful line number
    macro_rules! test_parser {
        ($parser:ident($input:expr) -> @($expected_remaining_input:expr, $expected:expr $(,)*)) => {
            let (remaining_input, result) = $parser(Input::new($input))?;
            assert_eq!(*remaining_input.fragment(), $expected_remaining_input,
                "unexpected remaining input after parse");
            assert_eq!(result, $expected);
        };
        ($parser:ident($input:expr) -> $expected:expr) => {
            test_parser!($parser($input) -> @("", $expected));
        };
    }

    #[test]
    fn test_unescape() -> ParseResult<'static, ()> {
        test_parser!(unescaped_str("file \\\"name\\\"") -> "file \"name\"".to_string());
        Ok(())
    }

    #[test]
    fn test_quoted() -> ParseResult<'static, ()> {
        test_parser!(quoted("\"file name\"") -> "file name".to_string());
        Ok(())
    }

    #[test]
    fn test_bare() -> ParseResult<'static, ()> {
        test_parser!(bare("file-name ") -> @("", "file-name ".to_string()));
        test_parser!(bare("file-name\t") -> @("\t", "file-name".to_string()));
        test_parser!(bare("file-name\n") -> @("\n", "file-name".to_string()));
        Ok(())
    }

    #[test]
    fn test_filename() -> ParseResult<'static, ()> {
        // bare
        test_parser!(filename("asdf\t") -> @("\t", "asdf".to_string()));

        // quoted
        test_parser!(filename(r#""a/My Project/src/foo.rs" "#) -> @(" ", "a/My Project/src/foo.rs".to_string()));
        test_parser!(filename(r#""\"asdf\" fdsh \\\t\r" "#) -> @(" ", "\"asdf\" fdsh \\\t\r".to_string()));
        test_parser!(filename(r#""a s\"\nd\0f" "#) -> @(" ", "a s\"\nd\0f".to_string()));
        Ok(())
    }

    #[test]
    fn test_header_line_contents() -> ParseResult<'static, ()> {
        test_parser!(header_line_content("lao\n") -> @("\n", File {
            path: "lao".into(),
            meta: None,
        }));

        test_parser!(header_line_content("lao\t2002-02-21 23:30:39.942229878 -0800\n") -> @(
            "\n",
            File {
                path: "lao".into(),
                meta: Some(FileMetadata::DateTime(
                    DateTime::parse_from_rfc3339("2002-02-21T23:30:39.942229878-08:00").unwrap()
                )),
            },
        ));

        test_parser!(header_line_content("lao\t2002-02-21 23:30:39 -0800\n") -> @(
            "\n",
            File {
                path: "lao".into(),
                meta: Some(FileMetadata::DateTime(
                    DateTime::parse_from_rfc3339("2002-02-21T23:30:39-08:00").unwrap()
                )),
            },
        ));

        test_parser!(header_line_content("lao\t08f78e0addd5bf7b7aa8887e406493e75e8d2b55\n") -> @(
            "\n",
            File {
                path: "lao".into(),
                meta: Some(FileMetadata::Other("08f78e0addd5bf7b7aa8887e406493e75e8d2b55".into()))
            },
        ));
        Ok(())
    }

    #[test]
    fn test_headers() -> ParseResult<'static, ()> {
        let sample = "\
--- lao	2002-02-21 23:30:39.942229878 -0800
+++ tzu	2002-02-21 23:30:50.442260588 -0800\n";
        test_parser!(headers(sample) -> (
            File {
                path: "lao".into(),
                meta: Some(FileMetadata::DateTime(
                    DateTime::parse_from_rfc3339("2002-02-21T23:30:39.942229878-08:00").unwrap()
                )),
            },
            File {
                path: "tzu".into(),
                meta: Some(FileMetadata::DateTime(
                    DateTime::parse_from_rfc3339("2002-02-21T23:30:50.442260588-08:00").unwrap()
                )),
            },
        ));

        let sample2 = "\
--- lao
+++ tzu\n";
        test_parser!(headers(sample2) -> (
            File {path: "lao".into(), meta: None},
            File {path: "tzu".into(), meta: None},
        ));

        let sample2b = "\
--- lao
+++ tzu	\n";
        test_parser!(headers(sample2b) -> (
            File {path: "lao".into(), meta: None},
            File {path: "tzu".into(), meta: None},
        ));

        let sample3 = "\
--- lao	08f78e0addd5bf7b7aa8887e406493e75e8d2b55
+++ tzu	e044048282ce75186ecc7a214fd3d9ba478a2816\n";
        test_parser!(headers(sample3) -> (
            File {
                path: "lao".into(),
                meta: Some(FileMetadata::Other("08f78e0addd5bf7b7aa8887e406493e75e8d2b55".into())),
            },
            File {
                path: "tzu".into(),
                meta: Some(FileMetadata::Other("e044048282ce75186ecc7a214fd3d9ba478a2816".into())),
            },
        ));
        Ok(())
    }

    #[test]
    fn test_headers_crlf() -> ParseResult<'static, ()> {
        let sample = "\
--- lao	2002-02-21 23:30:39.942229878 -0800\r
+++ tzu	2002-02-21 23:30:50.442260588 -0800\r\n";
        test_parser!(headers(sample) -> (
            File {
                path: "lao".into(),
                meta: Some(FileMetadata::DateTime(
                    DateTime::parse_from_rfc3339("2002-02-21T23:30:39.942229878-08:00").unwrap()
                )),
            },
            File {
                path: "tzu".into(),
                meta: Some(FileMetadata::DateTime(
                    DateTime::parse_from_rfc3339("2002-02-21T23:30:50.442260588-08:00").unwrap()
                )),
            },
        ));
        Ok(())
    }

    #[test]
    fn test_range() -> ParseResult<'static, ()> {
        test_parser!(range("1,7") -> Range { start: 1, count: 7 });

        test_parser!(range("2") -> Range { start: 2, count: 1 });
        Ok(())
    }

    #[test]
    fn test_chunk_header() -> ParseResult<'static, ()> {
        test_parser!(chunk_header("@@ -1,7 +1,6 @@ foo bar\n") -> (
            Range { start: 1, count: 7 },
            Range { start: 1, count: 6 },
            " foo bar",
        ));
        Ok(())
    }

    #[test]
    fn test_chunk() -> ParseResult<'static, ()> {
        let sample = "\
@@ -1,7 +1,6 @@
-The Way that can be told of is not the eternal Way;
-The name that can be named is not the eternal name.
 The Nameless is the origin of Heaven and Earth;
-The Named is the mother of all things.
+The named is the mother of all things.
+
 Therefore let there always be non-being,
   so we may see their subtlety,
 And let there always be being,\n";
        let expected = Hunk {
            old_range: Range { start: 1, count: 7 },
            new_range: Range { start: 1, count: 6 },
            range_hint: "",
            old_missing_newline: false,
            new_missing_newline: false,
            lines: vec![
                LineKind::Remove.to_line("The Way that can be told of is not the eternal Way;"),
                LineKind::Remove.to_line("The name that can be named is not the eternal name."),
                LineKind::Context.to_line("The Nameless is the origin of Heaven and Earth;"),
                LineKind::Remove.to_line("The Named is the mother of all things."),
                LineKind::Add.to_line("The named is the mother of all things."),
                LineKind::Add.to_line(""),
                LineKind::Context.to_line("Therefore let there always be non-being,"),
                LineKind::Context.to_line("  so we may see their subtlety,"),
                LineKind::Context.to_line("And let there always be being,"),
            ],
        };
        test_parser!(chunk(sample) -> expected);
        Ok(())
    }

    #[test]
    fn test_patch() -> ParseResult<'static, ()> {
        // https://www.gnu.org/software/diffutils/manual/html_node/Example-Unified.html
        let sample = "\
--- lao	2002-02-21 23:30:39.942229878 -0800
+++ tzu	2002-02-21 23:30:50.442260588 -0800
@@ -1,7 +1,6 @@
-The Way that can be told of is not the eternal Way;
-The name that can be named is not the eternal name.
 The Nameless is the origin of Heaven and Earth;
-The Named is the mother of all things.
+The named is the mother of all things.
+
 Therefore let there always be non-being,
   so we may see their subtlety,
 And let there always be being,
@@ -9,3 +8,6 @@
 The two are the same,
 But after they are produced,
   they have different names.
+They both may be called deep and profound.
+Deeper and more profound,
+The door of all subtleties!\n";

        let expected = Patch {
            old: File {
                path: "lao".into(),
                meta: Some(FileMetadata::DateTime(
                    DateTime::parse_from_rfc3339("2002-02-21T23:30:39.942229878-08:00").unwrap(),
                )),
            },
            new: File {
                path: "tzu".into(),
                meta: Some(FileMetadata::DateTime(
                    DateTime::parse_from_rfc3339("2002-02-21T23:30:50.442260588-08:00").unwrap(),
                )),
            },
            old_missing_newline: false,
            new_missing_newline: false,
            hunks: vec![
                Hunk {
                    old_range: Range { start: 1, count: 7 },
                    new_range: Range { start: 1, count: 6 },
                    range_hint: "",
                    old_missing_newline: false,
                    new_missing_newline: false,
                    lines: vec![
                        LineKind::Remove
                            .to_line("The Way that can be told of is not the eternal Way;"),
                        LineKind::Remove
                            .to_line("The name that can be named is not the eternal name."),
                        LineKind::Context
                            .to_line("The Nameless is the origin of Heaven and Earth;"),
                        LineKind::Remove.to_line("The Named is the mother of all things."),
                        LineKind::Add.to_line("The named is the mother of all things."),
                        LineKind::Add.to_line(""),
                        LineKind::Context.to_line("Therefore let there always be non-being,"),
                        LineKind::Context.to_line("  so we may see their subtlety,"),
                        LineKind::Context.to_line("And let there always be being,"),
                    ],
                },
                Hunk {
                    old_range: Range { start: 9, count: 3 },
                    new_range: Range { start: 8, count: 6 },
                    range_hint: "",
                    old_missing_newline: false,
                    new_missing_newline: false,
                    lines: vec![
                        LineKind::Context.to_line("The two are the same,"),
                        LineKind::Context.to_line("But after they are produced,"),
                        LineKind::Context.to_line("  they have different names."),
                        LineKind::Add.to_line("They both may be called deep and profound."),
                        LineKind::Add.to_line("Deeper and more profound,"),
                        LineKind::Add.to_line("The door of all subtleties!"),
                    ],
                },
            ],
        };

        test_parser!(patch(sample) -> expected);

        assert_eq!(format!("{}\n", expected), sample);

        Ok(())
    }
}
