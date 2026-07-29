//! Tests for slice comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_slice_first_difference_methods_are_callable() {
    proof {
        broadcast use vstd::array::group_array_axioms;
        broadcast use verge::cmp::slice::group_slice_ordering;
        reveal_with_fuel(lexico_eq, 3);
        reveal_with_fuel(lexico_cmp, 3);
    }

    let a = [1u32, 2u32].as_slice();
    let b = [1u32, 3u32].as_slice();

    test!(a == a);
    test!(a != b);
    test!(a.partial_cmp(b) == Some(Ordering::Less));
    test!(a < b);
    test!(a <= b);
    test!(b > a);
    test!(b >= a);
    test!(a.cmp(b) == Ordering::Less);
}

fn test_slice_prefix_methods_are_callable() {
    proof {
        broadcast use vstd::array::group_array_axioms;
        broadcast use verge::cmp::slice::group_slice_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    let short = [1u32].as_slice();
    let long = [1u32, 2u32].as_slice();
    test!(short.partial_cmp(long) == Some(Ordering::Less));
    test!(short < long);
    test!(short <= long);
    test!(long > short);
    test!(long >= short);
    test!(short.cmp(long) == Ordering::Less);
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "cmp::slice::first_difference_methods_are_callable",
        test_slice_first_difference_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::slice::prefix_methods_are_callable",
        test_slice_prefix_methods_are_callable,
    );
    count
}
