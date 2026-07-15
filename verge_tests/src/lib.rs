//! Integration tests for Verge public APIs.
//!
//! These modules intentionally live outside `verge_lib` so they exercise the same
//! visibility, imports, and broadcast defaults available to downstream users.

#![allow(incomplete_features)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(unused_doc_comments)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(rustdoc::invalid_rust_codeblocks)]
#![feature(allocator_api)]
#![feature(sized_hierarchy)]
#![feature(pattern)]
#![feature(specialization)]
#![feature(slice_index_methods)]

use vstd::prelude::*;
use std::io::Write;

mod io;
mod cmp;
mod str;

verus! {

/// Executably assert a condition, to check for proof soundness.
#[verifier::external_body]
fn exec_assert(cond: bool)
    requires cond,
{
    assert!(cond);
}

} // verus!

/// Entry point for running all executable tests.
pub fn run() {
    println!("{}", style::bold("Verge executable tests"));
    let mut count = 0;
    count += run_suite("cmp", cmp::run);
    count += run_suite("str", str::run);
    println!(
        "\n{} {} passed; 0 failed",
        style::green("test result: ok."),
        count,
    );
}

pub(crate) fn run_suite(name: &str, run: impl FnOnce() -> usize) -> usize {
    println!("\n{} {name}", style::cyan("running"));
    let count = run();
    println!(
        "{} {}: {} passed",
        style::green("ok"),
        name,
        count,
    );
    count
}

pub(crate) fn run_test(name: &str, test: impl FnOnce()) -> usize {
    print!("    {} {name} ... ", style::dim("test"));
    std::io::stdout().flush().expect("flush test progress");
    test();
    println!("{}", style::green("ok"));
    1
}

mod style {
    const RESET: &str = "\x1b[0m";
    const BOLD: &str = "\x1b[1m";
    const CYAN: &str = "\x1b[36m";
    const DIM: &str = "\x1b[2m";
    const GREEN: &str = "\x1b[32m";

    fn enabled() -> bool {
        std::env::var_os("NO_COLOR").is_none()
    }

    fn paint(code: &str, text: &str) -> String {
        if enabled() {
            format!("{code}{text}{RESET}")
        } else {
            text.to_string()
        }
    }

    pub(super) fn bold(text: &str) -> String {
        paint(BOLD, text)
    }

    pub(super) fn cyan(text: &str) -> String {
        paint(CYAN, text)
    }

    pub(super) fn dim(text: &str) -> String {
        paint(DIM, text)
    }

    pub(super) fn green(text: &str) -> String {
        paint(GREEN, text)
    }
}
