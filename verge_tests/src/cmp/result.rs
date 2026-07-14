//! Tests for `Result<T, E>` comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_result_comparison_methods_are_callable() {
    proof {
        broadcast use group_result_ordering;
    }

    let err2: Result<u32, u32> = Err(2u32);
    let err4: Result<u32, u32> = Err(4u32);
    let err5: Result<u32, u32> = Err(5u32);
    let ok3: Result<u32, u32> = Ok(3u32);
    let ok4: Result<u32, u32> = Ok(4u32);
    let ok5: Result<u32, u32> = Ok(5u32);

    let ok_eq = ok3 == ok3;
    assert(ok_eq);
    crate::exec_assert(ok_eq);

    let err_lt_err = err2 < err4;
    let ok_lt_ok = ok3 < ok5;
    assert(err_lt_err);
    crate::exec_assert(err_lt_err);
    assert(ok_lt_ok);
    crate::exec_assert(ok_lt_ok);

    let partial_err_err = err2.partial_cmp(&err4);
    let partial_ok_ok = ok3.partial_cmp(&ok5);
    assert(partial_err_err == Some(Ordering::Less));
    crate::exec_assert(partial_err_err == Some(Ordering::Less));
    assert(partial_ok_ok == Some(Ordering::Less));
    crate::exec_assert(partial_ok_ok == Some(Ordering::Less));

    let cmp_err_err = err2.cmp(&err4);
    let cmp_ok_ok = ok3.cmp(&ok5);
    assert(cmp_err_err == Ordering::Less);
    crate::exec_assert(cmp_err_err == Ordering::Less);
    assert(cmp_ok_ok == Ordering::Less);
    crate::exec_assert(cmp_ok_ok == Ordering::Less);

    let max_err = err2.max(err4);
    let min_err = err2.min(err4);
    let clamp_err = err4.clamp(err2, err5);
    let max_ok = ok3.max(ok5);
    let min_ok = ok3.min(ok5);
    let clamp_ok = ok4.clamp(ok3, ok5);
    let max_err_is_err4 = max_err == err4;
    let min_err_is_err2 = min_err == err2;
    let clamp_err_is_err4 = clamp_err == err4;
    let max_ok_is_ok5 = max_ok == ok5;
    let min_ok_is_ok3 = min_ok == ok3;
    let clamp_ok_is_ok4 = clamp_ok == ok4;
    assert(max_err_is_err4);
    crate::exec_assert(max_err_is_err4);
    assert(min_err_is_err2);
    crate::exec_assert(min_err_is_err2);
    assert(clamp_err_is_err4);
    crate::exec_assert(clamp_err_is_err4);
    assert(max_ok_is_ok5);
    crate::exec_assert(max_ok_is_ok5);
    assert(min_ok_is_ok3);
    crate::exec_assert(min_ok_is_ok3);
    assert(clamp_ok_is_ok4);
    crate::exec_assert(clamp_ok_is_ok4);

    let ok_lt_err = ok3 < err4;
    let ok_le_err = ok3 <= err4;
    let err_gt_ok = err4 > ok3;
    let err_ge_ok = err4 >= ok3;
    let err_lt_ok = err4 < ok3;
    let ok_gt_err = ok3 > err4;
    let partial_ok_err = ok3.partial_cmp(&err4);
    let partial_err_ok = err4.partial_cmp(&ok3);
    let cmp_ok_err = ok3.cmp(&err4);
    let cmp_err_ok = err4.cmp(&ok3);
    assert(ok_lt_err);
    crate::exec_assert(ok_lt_err);
    assert(ok_le_err);
    crate::exec_assert(ok_le_err);
    assert(err_gt_ok);
    crate::exec_assert(err_gt_ok);
    assert(err_ge_ok);
    crate::exec_assert(err_ge_ok);
    assert(!err_lt_ok);
    crate::exec_assert(!err_lt_ok);
    assert(!ok_gt_err);
    crate::exec_assert(!ok_gt_err);
    assert(partial_ok_err == Some(Ordering::Less));
    crate::exec_assert(partial_ok_err == Some(Ordering::Less));
    assert(partial_err_ok == Some(Ordering::Greater));
    crate::exec_assert(partial_err_ok == Some(Ordering::Greater));
    assert(cmp_ok_err == Ordering::Less);
    crate::exec_assert(cmp_ok_err == Ordering::Less);
    assert(cmp_err_ok == Ordering::Greater);
    crate::exec_assert(cmp_err_ok == Ordering::Greater);
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "cmp::result::comparison_methods_are_callable",
        test_result_comparison_methods_are_callable,
    );
    count
}
