//! Tests for `Option<T>` comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_option_comparison_methods_are_callable() {
    let none: Option<u32> = None;
    let some3 = Some(3u32);
    let some5 = Some(5u32);

    let none_lt_some = none < some3;
    let none_le_some = none <= some3;
    let some_lt_some = some3 < some5;
    let some_gt_none = some3 > none;
    let some_ge_some = some5 >= some3;
    assert(none_lt_some);
    assert(none_le_some);
    assert(some_lt_some);
    assert(some_gt_none);
    assert(some_ge_some);
    let partial = some3.partial_cmp(&some5);
    let cmp = some3.cmp(&some5);
    assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);

    let method_eq = some3.eq(&some3);
    let method_ne = none.ne(&some3);
    let method_lt = some3.lt(&some5);
    let method_le = none.le(&some3);
    let method_gt = some3.gt(&none);
    let method_ge = some5.ge(&some3);
    assert(method_eq);
    assert(method_ne);
    assert(method_lt);
    assert(method_le);
    assert(method_gt);
    assert(method_ge);

    let max = some3.max(some5);
    let min = some3.min(some5);
    let clamp = some3.clamp(none, some5);
    assert(max == some5);
    assert(min == some3);
    assert(clamp == some3);
}

fn test_verified_bridge_lemmas_for_option() {
    proof {
        lemma_partial_eq_verified::<Option<u32>>();
        lemma_partial_ord_verified::<Option<u32>>();
        lemma_ord_verified::<Option<u32>>();
    }

    let some3 = Some(3u32);
    let some5 = Some(5u32);
    assert(<Option<u32> as PartialOrdSpec>::partial_cmp_spec(&some3, &some5) == Some(Ordering::Less));
    assert(<Option<u32> as OrdSpec>::cmp_spec(&some3, &some5) == Ordering::Less);
}

} // verus!
