//! Tests for `Vec<T>` comparison APIs.

use core::cmp::Ordering;
use std::vec::Vec;

use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_vec_first_difference_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use verge::cmp::vec::group_vec_ordering;
        reveal_with_fuel(lexico_eq, 3);
        reveal_with_fuel(lexico_cmp, 3);
    }

    let mut a = Vec::<u32>::new();
    a.push(1u32);
    a.push(2u32);
    let mut b = Vec::<u32>::new();
    b.push(1u32);
    b.push(3u32);
    let mut c = Vec::<u32>::new();
    c.push(1u32);
    c.push(2u32);

    let eq = a == c;
    let ne = a.ne(&b);
    let partial = a.partial_cmp(&b);
    let cmp = a.cmp(&b);
    assert(eq) by {
        assert(a@ =~= c@);
        lemma_lexico_eq_reflexive::<u32>(a@);
    };
    assert(ne) by {
        lemma_lexico_cmp_eq_consistent::<u32>(a@, b@);
    };
    assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);

    proof {
        verge::cmp::vec::lemma_vec_lexico_partial_cmp_spec(&a, &b);
        verge::cmp::vec::lemma_vec_lexico_cmp_spec(&a, &b);
    }
    assert(<Vec<u32> as PartialOrdSpec>::partial_cmp_spec(&a, &b) == Some(Ordering::Less));
    assert(<Vec<u32> as OrdSpec>::cmp_spec(&a, &b) == Ordering::Less);
}

fn test_vec_prefix_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use verge::cmp::vec::group_vec_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    let mut short = Vec::<u32>::new();
    short.push(1u32);
    let mut long = Vec::<u32>::new();
    long.push(1u32);
    long.push(2u32);
    let partial = short.partial_cmp(&long);
    let cmp = short.cmp(&long);
    assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);
}

fn test_vec_provided_ord_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use verge::cmp::vec::group_vec_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    let mut a = Vec::<u32>::new();
    a.push(1u32);
    a.push(2u32);
    let mut b = Vec::<u32>::new();
    b.push(1u32);
    b.push(3u32);
    let max = a.max(b);
    assert(max@ =~= seq![1u32, 3u32]);

    let mut a = Vec::<u32>::new();
    a.push(1u32);
    a.push(2u32);
    let mut b = Vec::<u32>::new();
    b.push(1u32);
    b.push(3u32);
    let min = a.min(b);
    assert(min@ =~= seq![1u32, 2u32]);

    let mut low = Vec::<u32>::new();
    low.push(1u32);
    low.push(1u32);
    let mut high = Vec::<u32>::new();
    high.push(1u32);
    high.push(3u32);
    let mut value = Vec::<u32>::new();
    value.push(1u32);
    value.push(2u32);
    let clamp = value.clamp(low, high);
    assert(clamp@ =~= seq![1u32, 2u32]);
}

fn test_verified_bridge_lemmas_for_vec() {
    proof {
        lemma_partial_eq_verified::<Vec<u32>>();
        lemma_partial_ord_verified::<Vec<u32>>();
        lemma_ord_verified::<Vec<u32>>();
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use verge::cmp::vec::group_vec_ordering;
    }

    let mut a = Vec::<u32>::new();
    a.push(1u32);
    a.push(2u32);
    let mut b = Vec::<u32>::new();
    b.push(1u32);
    b.push(3u32);
    proof {
        reveal_with_fuel(lexico_cmp, 3);
        verge::cmp::vec::lemma_vec_lexico_partial_cmp_spec(&a, &b);
        verge::cmp::vec::lemma_vec_lexico_cmp_spec(&a, &b);
    }
    assert(<Vec<u32> as PartialOrdSpec>::partial_cmp_spec(&a, &b) == Some(Ordering::Less));
    assert(<Vec<u32> as OrdSpec>::cmp_spec(&a, &b) == Ordering::Less);
}

// XXX(Verus): `PartialOrd::{lt,le,gt,ge}` are provided trait methods for
// `Vec<T>`; Verus currently rejects `assume_specification` for provided trait
// methods, so direct `<`, `<=`, `>`, `>=`, `.lt`, `.le`, `.gt`, and `.ge` calls
// are intentionally not enabled here.

} // verus!
