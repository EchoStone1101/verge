//! Tests for array comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_array_first_difference_methods_are_callable() {
    proof {
        broadcast use verge::cmp::array::group_array_ordering;
        reveal_with_fuel(lexico_eq, 3);
        reveal_with_fuel(lexico_cmp, 3);
    }

    let a = [1u32, 2u32];
    let b = [1u32, 3u32];

    test!(a == [1u32, 2u32]);
    test!(a != b);
    test!(a.partial_cmp(&b) == Some(Ordering::Less));
    test!(a < b);
    test!(a <= b);
    test!(b > a);
    test!(b >= a);
    test!(a.cmp(&b) == Ordering::Less);
}

fn test_array_provided_ord_methods_are_callable() {
    proof {
        broadcast use verge::cmp::array::group_array_ordering;
        reveal_with_fuel(lexico_eq, 3);
        reveal_with_fuel(lexico_cmp, 3);
    }

    test!([1u32, 2u32].max([1u32, 3u32]) == [1u32, 3u32]);
    test!([1u32, 2u32].min([1u32, 3u32]) == [1u32, 2u32]);
    test!([1u32, 2u32].clamp([1u32, 1u32], [1u32, 3u32]) == [1u32, 2u32]);
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "cmp::array::first_difference_methods_are_callable",
        test_array_first_difference_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::array::provided_ord_methods_are_callable",
        test_array_provided_ord_methods_are_callable,
    );
    count
}
