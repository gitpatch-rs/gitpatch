//! Parse a patch from a file or stdin, then print it out as a patch.

use std::{
    env::args,
    fs::read_to_string,
    io::{stdin, Read},
};

use gitpatch::Patch;

fn main() {
    let mut patch_text = String::new();
    if let Some(filename) = args().nth(1) {
        patch_text = read_to_string(filename).unwrap();
    } else {
        stdin().read_to_string(&mut patch_text).unwrap();
    };
    let patches = Patch::from_multiple(&patch_text).unwrap();
    for patch in patches {
        println!("{}", patch);
    }
}
