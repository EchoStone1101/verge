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
    let c = [1u32, 2u32];

    let eq = a == c;
    let ne = a != b;
    let partial = a.partial_cmp(&b);
    let lt = a < b;
    let le = a <= b;
    let gt = b > a;
    let ge = b >= a;
    let cmp = a.cmp(&b);

    assert(eq);
    crate::exec_assert(eq);
    assert(ne);
    crate::exec_assert(ne);
    assert(partial == Some(Ordering::Less));
    crate::exec_assert(partial == Some(Ordering::Less));
    assert(lt);
    crate::exec_assert(lt);
    assert(le);
    crate::exec_assert(le);
    assert(gt);
    crate::exec_assert(gt);
    assert(ge);
    crate::exec_assert(ge);
    assert(cmp == Ordering::Less);
    crate::exec_assert(cmp == Ordering::Less);
}

fn test_array_provided_ord_methods_are_callable() {
    proof {
        broadcast use verge::cmp::array::group_array_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    let a = [1u32, 2u32];
    let b = [1u32, 3u32];
    let max = a.max(b);
    let min = a.min(b);
    let clamp = [1u32, 2u32].clamp([1u32, 1u32], [1u32, 3u32]);
    let _ = max;
    let _ = min;
    let _ = clamp;

    // XXX(Verus): `Ord::{max,min,clamp}` exists for arrays, but current
    // downstream proof support does not establish the selected result from the
    // array `cmp` spec due to limitations in Verus.
    // let max_is_b = max == b;
    // let min_is_a = min == a;
    // let clamp_is_a = clamp == a;
    // assert(max_is_b);
    // assert(min_is_a);
    // assert(clamp_is_a);
    // crate::exec_assert(max_is_b);
    // crate::exec_assert(min_is_a);
    // crate::exec_assert(clamp_is_a);
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
