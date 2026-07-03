//! Tests for array comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
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
    let partial = a.partial_cmp(&b);
    let cmp = a.cmp(&b);
    assert(eq) by {
        assert(a@ =~= c@);
        lemma_lexico_eq_reflexive::<u32>(a@);
    };
    assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);

    proof {
        verge::cmp::array::lemma_array_lexico_partial_cmp_spec(&a, &b);
        verge::cmp::array::lemma_array_lexico_cmp_spec(&a, &b);
    }
    assert(<[u32; 2] as PartialOrdSpec>::partial_cmp_spec(&a, &b) == Some(Ordering::Less));
    assert(<[u32; 2] as OrdSpec>::cmp_spec(&a, &b) == Ordering::Less);
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
    assert(max == b);
    assert(min == a);
    assert(clamp == a);
}

fn test_verified_bridge_lemmas_for_array() {
    proof {
        lemma_partial_eq_verified::<[u32; 2]>();
        lemma_partial_ord_verified::<[u32; 2]>();
        lemma_ord_verified::<[u32; 2]>();
        broadcast use verge::cmp::array::group_array_ordering;
    }

    let a = [1u32, 2u32];
    let b = [1u32, 3u32];
    proof {
        reveal_with_fuel(lexico_cmp, 3);
        verge::cmp::array::lemma_array_lexico_partial_cmp_spec(&a, &b);
        verge::cmp::array::lemma_array_lexico_cmp_spec(&a, &b);
    }
    assert(<[u32; 2] as PartialOrdSpec>::partial_cmp_spec(&a, &b) == Some(Ordering::Less));
    assert(<[u32; 2] as OrdSpec>::cmp_spec(&a, &b) == Ordering::Less);
}

// TODO(issue): `PartialEq::ne` and `PartialOrd::{lt,le,gt,ge}` are provided
// trait methods for arrays; Verus currently rejects `assume_specification` for
// provided trait methods, so direct `!=`, `<`, `<=`, `>`, `>=`, `.ne`, `.lt`,
// `.le`, `.gt`, and `.ge` calls are intentionally not enabled here.
// TODO(issue): Rust arrays implement comparison only for equal lengths, so the
// executable prefix case `[1] < [1, 2]` is not type-correct for arrays. The
// same prefix shape is covered by the slice, `Vec<T>`, and `VecDeque<T>` tests.

} // verus!
