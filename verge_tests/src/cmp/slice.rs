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
    let partial = a.partial_cmp(b);
    let cmp = a.cmp(b);
    assert(eq) by {
        assert(a@ =~= c@);
        lemma_lexico_eq_reflexive::<u32>(a@);
    };
    assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);

    proof {
        verge::cmp::slice::lemma_slice_lexico_partial_cmp_spec(a, b);
        verge::cmp::slice::lemma_slice_lexico_cmp_spec(a, b);
    }
    assert(<[u32] as PartialOrdSpec>::partial_cmp_spec(a, b) == Some(Ordering::Less));
    assert(<[u32] as OrdSpec>::cmp_spec(a, b) == Ordering::Less);
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
    let cmp = short.cmp(long);
    assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);
}

fn test_verified_bridge_lemmas_for_slice(arr_a: &[u32], arr_b: &[u32]) {
    proof {
        broadcast use verge::cmp::slice::group_slice_ordering;
        <[u32] as PartialEqVerified>::lemma_obeys_eq_spec();
        <[u32] as PartialOrdVerified>::lemma_obeys_partial_cmp_spec();
        <[u32] as OrdVerified>::lemma_obeys_cmp_spec();
        lemma_slice_lexico_partial_cmp_spec(arr_a, arr_b);
        lemma_slice_lexico_cmp_spec(arr_a, arr_b);
    }
    assert(<[u32] as PartialOrdSpec>::partial_cmp_spec(arr_a, arr_b) == lexico_cmp(arr_a@, arr_b@));
    assert(Some(<[u32] as OrdSpec>::cmp_spec(arr_a, arr_b)) == lexico_cmp(arr_a@, arr_b@));
}

// TODO(issue): `PartialEq::ne` and `PartialOrd::{lt,le,gt,ge}` are provided
// trait methods for slices; Verus currently rejects `assume_specification` for
// provided trait methods, so direct `!=`, `<`, `<=`, `>`, `>=`, `.ne`, `.lt`,
// `.le`, `.gt`, and `.ge` calls are intentionally not enabled here.
// TODO(issue): `Ord::{max,min,clamp}` take `Self` by value and are not callable
// for unsized `[T]` slices. Use arrays, `Vec<T>`, or `VecDeque<T>` for owned
// provided-method coverage.
// TODO(issue): The generic bridge lemmas currently require implicit `Sized`, so
// `lemma_partial_eq_verified::<[T]>()`, `lemma_partial_ord_verified::<[T]>()`,
// and `lemma_ord_verified::<[T]>()` are not callable for unsized slices.

} // verus!
