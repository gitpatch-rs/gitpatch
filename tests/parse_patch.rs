use chrono::DateTime;
use gitpatch::{File, FileMetadata, Line, ParseError, Patch};

use pretty_assertions::assert_eq;

#[test]
fn test_parse() -> Result<(), ParseError<'static>> {
    let sample = "\
--- before.py
+++ after.py
@@ -1,4 +1,4 @@
-bacon
-eggs
-ham
+python
+eggy
+hamster
 guido\n";
    let patch = Patch::from_single(sample)?;
    assert_eq!(
        patch.old,
        File {
            path: "before.py".into(),
            meta: None
        }
    );
    assert_eq!(
        patch.new,
        File {
            path: "after.py".into(),
            meta: None
        }
    );
    assert!(patch.end_newline_after() && patch.end_newline_after());

    assert_eq!(format!("{}\n", patch), sample);

    Ok(())
}

#[test]
fn test_parse_no_newline_indicator() -> Result<(), ParseError<'static>> {
    let sample = "\
--- before.py
+++ after.py
@@ -1,4 +1,4 @@
-bacon
-eggs
-ham
+python
+eggy
+hamster
 guido
\\ No newline at end of file\n";
    let patch = Patch::from_single(sample)?;
    assert_eq!(
        patch.old,
        File {
            path: "before.py".into(),
            meta: None
        }
    );
    assert_eq!(
        patch.new,
        File {
            path: "after.py".into(),
            meta: None
        }
    );
    assert!(!patch.end_newline_before() && !patch.end_newline_after());

    assert_eq!(format!("{}\n", patch), sample);

    Ok(())
}

#[test]
fn test_parse_no_newline_indicator_inside() -> Result<(), ParseError<'static>> {
    let sample = "\
--- test.txt
+++ test.txt
@@ -1,4 +1,5 @@
 python
 eggy
 hamster
-guido
\\ No newline at end of file
+
+hello
\\ No newline at end of file\n";
    let patch = Patch::from_single(sample)?;
    assert_eq!(
        patch.old,
        File {
            path: "test.txt".into(),
            meta: None
        }
    );
    assert_eq!(
        patch.new,
        File {
            path: "test.txt".into(),
            meta: None
        }
    );
    assert!(!patch.end_newline_before() && !patch.end_newline_after());

    assert_eq!(format!("{}\n", patch), sample);

    Ok(())
}

#[test]
fn test_parse_timestamps() -> Result<(), ParseError<'static>> {
    let sample = "\
--- before.py\t2002-02-21 23:30:39.942229878 -0800
+++ after.py\t2002-02-21 23:30:50 -0800
@@ -1,4 +1,4 @@
-bacon
-eggs
-ham
+python
+eggy
+hamster
 guido
\\ No newline at end of file";
    let patch = Patch::from_single(sample)?;
    assert_eq!(
        patch.old,
        File {
            path: "before.py".into(),
            meta: Some(FileMetadata::DateTime(
                DateTime::parse_from_rfc3339("2002-02-21T23:30:39.942229878-08:00").unwrap()
            )),
        }
    );
    assert_eq!(
        patch.new,
        File {
            path: "after.py".into(),
            meta: Some(FileMetadata::DateTime(
                DateTime::parse_from_rfc3339("2002-02-21T23:30:50-08:00").unwrap()
            )),
        }
    );
    assert!(!patch.end_newline_after() && !patch.end_newline_before());

    // to_string() uses Display but adds no trailing newline
    assert_eq!(patch.to_string(), sample);

    Ok(())
}

#[test]
fn test_parse_other() -> Result<(), ParseError<'static>> {
    let sample = "\
--- before.py\t08f78e0addd5bf7b7aa8887e406493e75e8d2b55
+++ after.py\te044048282ce75186ecc7a214fd3d9ba478a2816
@@ -1,4 +1,4 @@
-bacon
-eggs
-ham
+python
+eggy
+hamster
 guido\n";
    let patch = Patch::from_single(sample)?;
    assert_eq!(
        patch.old,
        File {
            path: "before.py".into(),
            meta: Some(FileMetadata::Other(
                "08f78e0addd5bf7b7aa8887e406493e75e8d2b55".into()
            )),
        }
    );
    assert_eq!(
        patch.new,
        File {
            path: "after.py".into(),
            meta: Some(FileMetadata::Other(
                "e044048282ce75186ecc7a214fd3d9ba478a2816".into()
            )),
        }
    );
    assert!(patch.end_newline_before() && patch.end_newline_after());

    assert_eq!(format!("{}\n", patch), sample);

    Ok(())
}

#[test]
fn test_parse_escaped() -> Result<(), ParseError<'static>> {
    let sample = "\
--- before.py\t\"asdf \\\\ \\n \\t \\0 \\r \\\" \"
+++ \"My Work/after.py\"\t\"My project is cool! Wow!!; SELECT * FROM USERS;\"
@@ -1,4 +1,4 @@
-bacon
-eggs
-ham
+python
+eggy
+hamster
 guido\n";
    let patch = Patch::from_single(sample)?;
    assert_eq!(
        patch.old,
        File {
            path: "before.py".into(),
            meta: Some(FileMetadata::Other("asdf \\ \n \t \0 \r \" ".into())),
        }
    );
    assert_eq!(
        patch.new,
        File {
            path: "My Work/after.py".into(),
            meta: Some(FileMetadata::Other(
                "My project is cool! Wow!!; SELECT * FROM USERS;".into()
            )),
        }
    );
    assert!(patch.end_newline_before() && patch.end_newline_after());

    assert_eq!(format!("{}\n", patch), sample);

    Ok(())
}

#[test]
fn test_parse_triple_plus_minus() -> Result<(), ParseError<'static>> {
    // Our parser has some hacky rules to make sure that lines starting with +++ or --- aren't
    // interpreted as regular addition/removal lines that could be part of a hunk. This test checks
    // to make sure that code is working.
    let sample = r#"--- main.c
+++ main.c
@@ -1,4 +1,7 @@
+#include<stdio.h>
+
 int main() {
 double a;
---a;
+++a;
+printf("%d\n", a);
 }
"#;
    let patches = Patch::from_multiple(sample).unwrap();
    assert_eq!(patches.len(), 1);

    let patch = &patches[0];
    assert_eq!(
        patch.old,
        File {
            path: "main.c".into(),
            meta: None
        }
    );
    assert_eq!(
        patch.new,
        File {
            path: "main.c".into(),
            meta: None
        }
    );
    assert!(patch.end_newline_before() && patch.end_newline_after());

    assert_eq!(patch.hunks.len(), 1);
    assert_eq!(patch.hunks[0].lines.len(), 8);

    assert_eq!(format!("{}\n", patch), sample);

    Ok(())
}

//FIXME: This test should NOT panic. When we have more sophisticated chunk line parsing that
// actually takes the hunk ranges into account, the #[should_panic] annotation should be removed.
// See the FIXME comment on top of the chunk_line parser.
#[test]
#[should_panic]
fn test_parse_triple_plus_minus_hack() {
    // Our parser has some hacky rules to make sure that lines starting with +++ or --- aren't
    // interpreted as regular addition/removal lines that could be part of a hunk. This test
    // demonstrates that these rules are not foolproof. The only differences between this test and
    // test_parse_triple_plus_minus are `--- a` and `+++ a` vs `---a` and `+++a`. In either case,
    // we should be able to determine that those lines do not start a new patch based on the ranges
    // provided for the hunk.
    let sample = r#"--- main.c
+++ main.c
@@ -1,4 +1,7 @@
+#include<stdio.h>
+
 int main() {
 double a;
--- a;
+++ a;
+printf("%d\n", a);
 }
"#;
    let patches = Patch::from_multiple(sample).unwrap();
    assert_eq!(patches.len(), 1);

    let patch = &patches[0];
    assert_eq!(
        patch.old,
        File {
            path: "main.c".into(),
            meta: None
        }
    );
    assert_eq!(
        patch.new,
        File {
            path: "main.c".into(),
            meta: None
        }
    );
    assert!(patch.end_newline_before() && patch.end_newline_after());

    assert_eq!(patch.hunks.len(), 1);
    assert_eq!(patch.hunks[0].lines.len(), 8);

    assert_eq!(format!("{}\n", patch), sample);
}

#[test]
fn binary_diff_with_crlf() {
    let sample = "Binary files old.bin and new.bin differ\r\n";

    let patch = Patch::from_single(sample).unwrap();
    assert_eq!(patch.old.path, "old.bin");
    assert_eq!(patch.old.meta, None);
    assert_eq!(patch.new.path, "new.bin");
    assert_eq!(patch.new.meta, None);
    assert_eq!(patch.hunks, []);
}

#[test]
fn binary_diff_with_ambiguous_names() {
    // The main goal here is that this doesn't crash or error:
    // the format with quotes means for some names there is no
    // unambiguous meaning.
    let sample = "Binary files a differ program and a patcher binary and a wiggler differ\r\n";

    let patch = Patch::from_single(sample).unwrap();
    assert_eq!(patch.old.path, "a differ program");
    assert_eq!(patch.old.meta, None);
    assert_eq!(patch.new.path, "a patcher binary and a wiggler");
    assert_eq!(patch.new.meta, None);
    assert_eq!(patch.hunks, []);
}

#[test]
fn binary_diff_with_spaces_in_name() {
    let sample = "Binary files an old binary and a new binary differ\n";

    let patch = Patch::from_single(sample).unwrap();
    assert_eq!(patch.old.path, "an old binary");
    assert_eq!(patch.old.meta, None);
    assert_eq!(patch.new.path, "a new binary");
    assert_eq!(patch.new.meta, None);
    assert_eq!(patch.hunks, []);
}

#[test]
fn single_binary_diff() {
    let sample = "Binary files old.bin and new.bin differ\n";

    let patch = Patch::from_single(sample).unwrap();
    assert_eq!(patch.old.path, "old.bin");
    assert_eq!(patch.old.meta, None);
    assert_eq!(patch.new.path, "new.bin");
    assert_eq!(patch.new.meta, None);
    assert_eq!(patch.hunks, []);
}

#[test]
fn multiple_binary_diffs() {
    let sample = "Binary files old.bin and new.bin differ
Binary files old1.bin and new1.bin differ
";
    let patches = Patch::from_multiple(sample).unwrap();
    assert_eq!(patches.len(), 2);
    assert_eq!(patches[0].old.path, "old.bin");
    assert_eq!(patches[1].old.path, "old1.bin");
}

#[test]
fn binary_diff_with_text_diff() {
    let sample = "\
--- before.py
+++ after.py
@@ -1,4 +1,4 @@
-bacon
-eggs
-ham
+python
+eggy
+hamster
 guido
Binary files old.bin and new.bin differ
";
    let patches = Patch::from_multiple(sample).unwrap();
    assert_eq!(patches.len(), 2);
    assert_eq!(patches[0].old.path, "before.py");
    assert_eq!(patches[1].old.path, "old.bin");
}

#[test]
fn parses_file_renames_with_some_diff() {
    let sample = "\
diff --git a/src/ast.rs b/src/ast-2.rs
similarity index 99%
rename from src/ast.rs
rename to src/ast-2.rs
index d923f10..b47f160 100644
--- a/src/ast.rs
+++ b/src/ast-2.rs
@@ -4,6 +4,7 @@ use std::fmt;
 use chrono::{DateTime, FixedOffset};
 
 use crate::parser::{parse_multiple_patches, parse_single_patch, ParseError};
+use new_crate;
 
 /// A complete patch summarizing the differences between two files
 #[derive(Debug, Clone, Eq, PartialEq)]
";

    let patches = Patch::from_multiple(sample).unwrap();
    assert_eq!(patches.len(), 1);
    assert_eq!(patches[0].old.path, "a/src/ast.rs");
    assert_eq!(patches[0].new.path, "b/src/ast-2.rs");

    assert!(patches[0].hunks[0]
        .lines
        .iter()
        .any(|line| matches!(line, Line::Add("use new_crate;", true))));
}

#[test]
fn parses_file_rename_with_100_pct_similarity() {
    let sample = "\
diff --git a/original-path.rs b/new-path.rs
similarity index 100%
rename from original-path.rs
rename to new-path.rs
";

    let patches = Patch::from_multiple(sample).unwrap();

    assert_eq!(patches.len(), 1);
    assert_eq!(patches[0].old.path, "original-path.rs");
    assert_eq!(patches[0].new.path, "new-path.rs");
    assert!(patches[0].hunks.is_empty());
}
