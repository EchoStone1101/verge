//! Tests for shared-reference comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_reference_comparison_methods_are_callable() {
    let a: u32 = 3;
    let b: u32 = 5;
    let ar = &a;
    let br = &b;

    let neq = ar != br;
    let lt = ar < br;
    let le = ar <= br;
    let gt = br > ar;
    let ge = br >= ar;
    assert(neq);
    assert(lt);
    assert(le);
    assert(gt);
    assert(ge);
    let partial = ar.partial_cmp(&br);
    let cmp = ar.cmp(&br);
    assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);

    let method_eq = ar.eq(ar);
    let method_ne = ar.ne(br);
    let method_lt = ar.lt(br);
    let method_le = ar.le(br);
    let method_gt = br.gt(ar);
    let method_ge = br.ge(ar);
    assert(method_eq);
    assert(method_ne);
    assert(method_lt);
    assert(method_le);
    assert(method_gt);
    assert(method_ge);

    let max = ar.max(br);
    let min = ar.min(br);
    let clamp = ar.clamp(ar, br);
    assert(*max == b);
    assert(*min == a);
    assert(*clamp == a);
}

} // verus!
