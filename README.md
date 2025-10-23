# Patch

[![Checks](https://github.com/gitpatch-rs/gitpatch/actions/workflows/checks.yml/badge.svg)](https://github.com/gitpatch-rs/gitpatch/actions/workflows/checks.yml)
[![Crates.io Badge](https://img.shields.io/crates/v/gitpatch.svg)](https://crates.io/crates/gitpatch)
[![docs.rs](https://docs.rs/patch/badge.svg)](https://docs.rs/patch)
[![Lines of Code](https://tokei.rs/b1/github/gitpatch-rs/gitpatch)](https://github.com/gitpatch-rs/gitpatch)

Rust crate for parsing and producing patch files in the [Unified Format].

The parser attempts to be forgiving enough to be compatible with diffs produced
by programs like git. It accomplishes this by ignoring the additional code
context and information provided in the diff by those programs.

See the **[Documentation]** for more information and for examples.

[Unified Format]: https://www.gnu.org/software/diffutils/manual/html_node/Unified-Format.html
[Documentation]: https://docs.rs/gitpatch
