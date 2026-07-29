//! Tests for tuple comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_tuple_comparison_methods_are_callable() {
    let a = (1u32, 9u32);
    let b = (2u32, 0u32);

    test!(a == (1u32, 9u32));
    test!(a != b);
    test!(a < b);
    test!(b > a);
    test!(a <= b);
    test!(b >= a);
    test!(a.partial_cmp(&b) == Some(Ordering::Less));
    test!(a.cmp(&b) == Ordering::Less);

    test!(a.max(b) == b);
    test!(a.min(b) == a);
    test!(a.clamp(a, b) == a);
}

fn test_unit_tuple_comparison_methods_are_callable() {
    proof {
        broadcast use verge::cmp::tuple::group_unit_ordering;
    }

    test!(() == ());
    test!(!(() != ()));
    test!(().partial_cmp(&()) == Some(Ordering::Equal));
    test!(!(() < ()));
    test!(() <= ());
    test!(!(() > ()));
    test!(() >= ());
    test!(().cmp(&()) == Ordering::Equal);

    test!(().max(()) == ());
    test!(().min(()) == ());
    test!(().clamp((), ()) == ());
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "cmp::tuple::comparison_methods_are_callable",
        test_tuple_comparison_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::tuple::unit_tuple_comparison_methods_are_callable",
        test_unit_tuple_comparison_methods_are_callable,
    );
    count
}
