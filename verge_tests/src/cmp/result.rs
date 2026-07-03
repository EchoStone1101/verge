//! Tests for `Result<T, E>` comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_result_comparison_methods_are_callable() {
    proof {
        lemma_partial_eq_verified::<Result<u32, u32>>();
        lemma_partial_ord_verified::<Result<u32, u32>>();
        lemma_ord_verified::<Result<u32, u32>>();
        broadcast use group_result_ordering;
    }

    let err2: Result<u32, u32> = Err(2u32);
    let err4: Result<u32, u32> = Err(4u32);
    let ok3: Result<u32, u32> = Ok(3u32);
    let ok5: Result<u32, u32> = Ok(5u32);

    let err_lt_ok = err4 < ok3;
    let err_le_ok = err4 <= ok3;
    let ok_gt_err = ok3 > err4;
    let ok_ge_err = ok3 >= err4;
    let err_lt_err = err2 < err4;
    let ok_lt_ok = ok3 < ok5;
    assert(err_lt_ok);
    assert(err_le_ok);
    assert(ok_gt_err);
    assert(ok_ge_err);
    assert(err_lt_err);
    assert(ok_lt_ok);

    let partial_err_ok = err4.partial_cmp(&ok3);
    let partial_err_err = err2.partial_cmp(&err4);
    let partial_ok_ok = ok3.partial_cmp(&ok5);
    assert(partial_err_ok == Some(Ordering::Less));
    assert(partial_err_err == Some(Ordering::Less));
    assert(partial_ok_ok == Some(Ordering::Less));

    let cmp_err_ok = err4.cmp(&ok3);
    let cmp_err_err = err2.cmp(&err4);
    let cmp_ok_ok = ok3.cmp(&ok5);
    assert(cmp_err_ok == Ordering::Less);
    assert(cmp_err_err == Ordering::Less);
    assert(cmp_ok_ok == Ordering::Less);

    let method_eq = ok3.eq(&ok3);
    let method_ne = err4.ne(&ok3);
    let method_lt = err4.lt(&ok3);
    let method_le = err2.le(&err4);
    let method_gt = ok3.gt(&err4);
    let method_ge = ok5.ge(&ok3);
    assert(method_eq);
    assert(method_ne);
    assert(method_lt);
    assert(method_le);
    assert(method_gt);
    assert(method_ge);

    let max_err_ok = err4.max(ok3);
    let min_err_ok = err4.min(ok3);
    let clamp_err = err4.clamp(err2, ok5);
    let clamp_low = err2.clamp(err4, ok5);
    let clamp_high = ok5.clamp(err2, ok3);
    assert(max_err_ok == ok3);
    assert(min_err_ok == err4);
    assert(clamp_err == err4);
    assert(clamp_low == err4);
    assert(clamp_high == ok3);
}

fn test_verified_bridge_lemmas_for_result() {
    proof {
        lemma_partial_eq_verified::<Result<u32, u32>>();
        lemma_partial_ord_verified::<Result<u32, u32>>();
        lemma_ord_verified::<Result<u32, u32>>();
        broadcast use group_result_ordering;
    }

    let err4: Result<u32, u32> = Err(4u32);
    let ok3: Result<u32, u32> = Ok(3u32);
    let ok5: Result<u32, u32> = Ok(5u32);
    assert(<Result<u32, u32> as PartialOrdSpec>::partial_cmp_spec(&err4, &ok3) == Some(Ordering::Less));
    assert(<Result<u32, u32> as PartialOrdSpec>::partial_cmp_spec(&ok3, &ok5) == Some(Ordering::Less));
    assert(<Result<u32, u32> as OrdSpec>::cmp_spec(&err4, &ok3) == Ordering::Less);
    assert(<Result<u32, u32> as OrdSpec>::cmp_spec(&ok3, &ok5) == Ordering::Less);
}

} // verus!
