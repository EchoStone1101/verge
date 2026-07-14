//! Tests for tuple comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_tuple_comparison_methods_are_callable() {
    let a = (1u32, 9u32);
    let b = (2u32, 0u32);
    let c = (1u32, 9u32);

    let eq = a == c;
    let ne = a != b;
    let lt = a < b;
    let gt = b > a;
    assert(eq);
    crate::exec_assert(eq);
    assert(ne);
    crate::exec_assert(ne);
    assert(lt);
    crate::exec_assert(lt);
    assert(gt);
    crate::exec_assert(gt);
    let cmp = a.cmp(&b);
    assert(cmp == Ordering::Less);
    crate::exec_assert(cmp == Ordering::Less);

    let max = a.max(b);
    let min = a.min(b);
    let clamp = a.clamp(a, b);
    assert(max == b);
    crate::exec_assert(max == b);
    assert(min == a);
    crate::exec_assert(min == a);
    assert(clamp == a);
    crate::exec_assert(clamp == a);
}

fn test_unit_tuple_comparison_methods_are_callable() {
    proof {
        broadcast use verge::cmp::tuple::group_unit_ordering;
    }

    let a = ();
    let b = ();

    let eq = a == b;
    let ne = a != b;
    let partial = a.partial_cmp(&b);
    let lt = a < b;
    let le = a <= b;
    let gt = a > b;
    let ge = a >= b;
    let cmp = a.cmp(&b);
    assert(eq);
    crate::exec_assert(eq);
    assert(!ne);
    crate::exec_assert(!ne);
    assert(partial == Some(Ordering::Equal));
    crate::exec_assert(partial == Some(Ordering::Equal));
    assert(!lt);
    crate::exec_assert(!lt);
    assert(le);
    crate::exec_assert(le);
    assert(!gt);
    crate::exec_assert(!gt);
    assert(ge);
    crate::exec_assert(ge);
    assert(cmp == Ordering::Equal);
    crate::exec_assert(cmp == Ordering::Equal);

    let max = a.max(b);
    let min = a.min(b);
    let clamp = a.clamp((), ());
    assert(max == ());
    crate::exec_assert(max == ());
    assert(min == ());
    crate::exec_assert(min == ());
    assert(clamp == ());
    crate::exec_assert(clamp == ());
}

// XXX(Verus): Tuple `PartialOrd::partial_cmp`, `le`, and `ge` are not supported yet
// due to a Verus self-reference issue.
// fn test_tuple_cyclic_partial_ord_methods_are_callable() {
//     let a = (1u32, 9u32);
//     let b = (2u32, 0u32);
//
//     let partial = a.partial_cmp(&b);
//     let le = a <= b;
//     let ge = b >= a;
//     assert(partial == Some(Ordering::Less));
//     assert(le);
//     assert(ge);
// }

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
