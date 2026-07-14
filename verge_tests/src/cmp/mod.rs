//! Tests for comparison APIs.

mod array;
mod pointer;
mod result;
mod slice;
mod string;
mod tuple;
mod vec;
mod vec_deque;

use vstd::prelude::*;

verus! {

proof fn cmp_module_marker() {}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_suite("cmp::array", array::run);
    count += crate::run_suite("cmp::pointer", pointer::run);
    count += crate::run_suite("cmp::result", result::run);
    count += crate::run_suite("cmp::slice", slice::run);
    count += crate::run_suite("cmp::string", string::run);
    count += crate::run_suite("cmp::tuple", tuple::run);
    count += crate::run_suite("cmp::vec", vec::run);
    count += crate::run_suite("cmp::vec_deque", vec_deque::run);
    count
}
