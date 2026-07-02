//! Tests for tuple comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
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
    assert(ne);
    assert(lt);
    assert(gt);
    let cmp = a.cmp(&b);
    assert(cmp == Ordering::Less);

    let method_eq = a.eq(&c);
    let method_ne = a.ne(&b);
    let method_lt = a.lt(&b);
    let method_gt = b.gt(&a);
    assert(method_eq);
    assert(method_ne);
    assert(method_lt);
    assert(method_gt);

    let max = a.max(b);
    let min = a.min(b);
    let clamp = a.clamp(a, b);
    assert(max == b);
    assert(min == a);
    assert(clamp == a);
}

// XXX(issue): Tuple `PartialOrd::partial_cmp`, `le`, and `ge` are currently not
// directly callable from Verus. Adding the suggested `assume_specification` items
// creates a cyclic self-reference through `vstd::laws_cmp` tuple broadcasts.
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

fn test_verified_bridge_lemmas_for_tuple() {
    proof {
        lemma_partial_eq_verified::<(u32, u32)>();
        lemma_partial_ord_verified::<(u32, u32)>();
        lemma_ord_verified::<(u32, u32)>();
    }

    let tuple_a = (1u32, 9u32);
    let tuple_b = (2u32, 0u32);
    assert(<(u32, u32) as PartialOrdSpec>::partial_cmp_spec(&tuple_a, &tuple_b) == Some(Ordering::Less));
    assert(<(u32, u32) as OrdSpec>::cmp_spec(&tuple_a, &tuple_b) == Ordering::Less);
}

} // verus!
