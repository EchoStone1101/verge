//! Tests for owning-pointer comparison APIs.

use core::cmp::Ordering;
use std::rc::Rc;

use vstd::prelude::*;
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_box_comparison_methods_are_callable() {
    proof {
        broadcast use verge::cmp::pointer::group_pointer_ordering;
    }

    let a = Box::new(3u32);
    let b = Box::new(5u32);
    let c = Box::new(3u32);

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

    let max = Box::new(3u32).max(Box::new(5u32));
    assert(*max == 5u32);
    crate::exec_assert(*max == 5u32);

    let min = Box::new(3u32).min(Box::new(5u32));
    assert(*min == 3u32);
    crate::exec_assert(*min == 3u32);

    let clamp = Box::new(4u32).clamp(Box::new(3u32), Box::new(5u32));
    assert(*clamp == 4u32);
    crate::exec_assert(*clamp == 4u32);
}

fn test_rc_comparison_methods_are_callable() {
    proof {
        broadcast use verge::cmp::pointer::group_pointer_ordering;
    }

    let a = Rc::new(3u32);
    let b = Rc::new(5u32);
    let c = Rc::new(3u32);

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

    let max = a.clone().max(b.clone());
    assert(*max == *b);
    crate::exec_assert(*max == *b);

    let min = a.clone().min(b.clone());
    assert(*min == *a);
    crate::exec_assert(*min == *a);

    let clamp = Rc::new(4u32).clamp(a.clone(), b.clone());
    assert(*clamp == 4u32);
    crate::exec_assert(*clamp == 4u32);
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "cmp::pointer::box_comparison_methods_are_callable",
        test_box_comparison_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::pointer::rc_comparison_methods_are_callable",
        test_rc_comparison_methods_are_callable,
    );
    count
}
