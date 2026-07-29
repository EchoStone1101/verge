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

    test!(a == Box::new(3u32));
    test!(a != b);
    test!(a.partial_cmp(&b) == Some(Ordering::Less));
    test!(a < b);
    test!(a <= b);
    test!(b > a);
    test!(b >= a);
    test!(a.cmp(&b) == Ordering::Less);

    test!(*Box::new(3u32).max(Box::new(5u32)) == 5u32);

    test!(*Box::new(3u32).min(Box::new(5u32)) == 3u32);

    test!(*Box::new(4u32).clamp(Box::new(3u32), Box::new(5u32)) == 4u32);
}

fn test_rc_comparison_methods_are_callable() {
    proof {
        broadcast use verge::cmp::pointer::group_pointer_ordering;
    }

    let a = Rc::new(3u32);
    let b = Rc::new(5u32);

    test!(a == Rc::new(3u32));
    test!(a != b);
    test!(a.partial_cmp(&b) == Some(Ordering::Less));
    test!(a < b);
    test!(a <= b);
    test!(b > a);
    test!(b >= a);
    test!(a.cmp(&b) == Ordering::Less);

    test!(*a.clone().max(b.clone()) == *b);

    test!(*a.clone().min(b.clone()) == *a);

    test!(*Rc::new(4u32).clamp(a.clone(), b.clone()) == 4u32);
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
