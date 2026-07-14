//! Tests for slice comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
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

    let arr_a = [1u32, 2u32];
    let arr_b = [1u32, 3u32];
    let arr_c = [1u32, 2u32];
    let a = arr_a.as_slice();
    let b = arr_b.as_slice();
    let c = arr_c.as_slice();

    let eq = a == c;
    // XXX(Verus): `PartialEq::ne` impl is default provided for `[T]`,
    // which Verus doesn't support yet.
    let partial = a.partial_cmp(b);
    let lt = a < b;
    let le = a <= b;
    let gt = b > a;
    let ge = b >= a;
    let cmp = a.cmp(b);
    assert(eq) by {
        assert(a@ =~= c@);
        lemma_lexico_eq_reflexive::<u32>(a@);
    };
    crate::exec_assert(eq);
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

    proof {
        verge::cmp::slice::lemma_slice_lexico_partial_cmp_spec(a, b);
        verge::cmp::slice::lemma_slice_lexico_cmp_spec(a, b);
    }
    assert(<[u32] as PartialOrdSpec>::partial_cmp_spec(a, b) == Some(Ordering::Less));
    crate::exec_assert(a < b);
    assert(<[u32] as OrdSpec>::cmp_spec(a, b) == Ordering::Less);
    crate::exec_assert(cmp == Ordering::Less);
}

fn test_slice_prefix_methods_are_callable() {
    proof {
        broadcast use vstd::array::group_array_axioms;
        broadcast use verge::cmp::slice::group_slice_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    let arr_short = [1u32];
    let arr_long = [1u32, 2u32];
    let short = arr_short.as_slice();
    let long = arr_long.as_slice();
    let partial = short.partial_cmp(long);
    let lt = short < long;
    let le = short <= long;
    let gt = long > short;
    let ge = long >= short;
    let cmp = short.cmp(long);
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
