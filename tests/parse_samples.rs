use std::fs;
use std::path::PathBuf;

use pretty_assertions::assert_eq;

use gitpatch::Patch;

fn visit_patches<F>(test_dir: &str, extension: &str, f: F)
where
    F: Fn(&str, &PathBuf),
{
    let samples_path = PathBuf::from(file!()).parent().unwrap().join(test_dir);
    for file in fs::read_dir(samples_path).unwrap() {
        let path = file.unwrap().path();
        if path.extension().unwrap_or_default() != extension {
            continue;
        }

        f(fs::read_to_string(dbg!(&path)).unwrap().as_str(), &path);
    }
}

// Make sure that the patch file we produce parses to the same information as the original
// patch file.
fn verify_patch_roundtrip(data: &str, path: &PathBuf) {
    let patches = Patch::from_multiple(data)
        .unwrap_or_else(|err| panic!("failed to parse {:?}, error: {}", path, err));

    #[allow(clippy::format_collect)] // Display::fmt is the only way to resolve Patch->str
    let patch_file: String = patches.iter().map(|patch| format!("{}\n", patch)).collect();
    println!("{}", patch_file);
    let patches2 = Patch::from_multiple(&patch_file).unwrap_or_else(|err| {
        panic!(
            "failed to re-parse {:?} after formatting, error: {}",
            path, err
        )
    });
    assert_eq!(patches, patches2);
}

#[test]
fn parse_samples() {
    visit_patches("samples", "diff", verify_patch_roundtrip);
}

#[test]
fn parse_wild_samples() {
    visit_patches("wild-samples", "patch", verify_patch_roundtrip);
}
