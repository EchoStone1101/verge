//! Tests for owning-pointer comparison APIs.

use core::cmp::Ordering;
use std::rc::Rc;

use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
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
    assert(ne);
    assert(partial == Some(Ordering::Less));
    assert(lt);
    assert(le);
    assert(gt);
    assert(ge);
    assert(cmp == Ordering::Less);

    let method_eq = a.eq(&c);
    let method_ne = a.ne(&b);
    let method_lt = a.lt(&b);
    let method_le = a.le(&b);
    let method_gt = b.gt(&a);
    let method_ge = b.ge(&a);
    assert(method_eq);
    assert(method_ne);
    assert(method_lt);
    assert(method_le);
    assert(method_gt);
    assert(method_ge);

    let max = Box::new(3u32).max(Box::new(5u32));
    assert(*max == 5u32);

    let min = Box::new(3u32).min(Box::new(5u32));
    assert(*min == 3u32);

    let clamp = Box::new(4u32).clamp(Box::new(3u32), Box::new(5u32));
    assert(*clamp == 4u32);
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
    assert(ne);
    assert(partial == Some(Ordering::Less));
    assert(lt);
    assert(le);
    assert(gt);
    assert(ge);
    assert(cmp == Ordering::Less);

    let method_eq = a.eq(&c);
    let method_ne = a.ne(&b);
    let method_lt = a.lt(&b);
    let method_le = a.le(&b);
    let method_gt = b.gt(&a);
    let method_ge = b.ge(&a);
    assert(method_eq);
    assert(method_ne);
    assert(method_lt);
    assert(method_le);
    assert(method_gt);
    assert(method_ge);

    let max = Rc::new(3u32).max(Rc::new(5u32));
    assert(*max == 5u32);

    let min = Rc::new(3u32).min(Rc::new(5u32));
    assert(*min == 3u32);

    let clamp = Rc::new(4u32).clamp(Rc::new(3u32), Rc::new(5u32));
    assert(*clamp == 4u32);
}

fn test_verified_bridge_lemmas_for_pointers() {
    proof {
        lemma_partial_eq_verified::<Box<u32>>();
        lemma_partial_ord_verified::<Box<u32>>();
        lemma_ord_verified::<Box<u32>>();
        lemma_partial_eq_verified::<Rc<u32>>();
        lemma_partial_ord_verified::<Rc<u32>>();
        lemma_ord_verified::<Rc<u32>>();
        broadcast use verge::cmp::pointer::group_pointer_ordering;
    }

    let box_a = Box::new(3u32);
    let box_b = Box::new(5u32);
    assert(<Box<u32> as PartialOrdSpec>::partial_cmp_spec(&box_a, &box_b) == Some(Ordering::Less));
    assert(<Box<u32> as OrdSpec>::cmp_spec(&box_a, &box_b) == Ordering::Less);

    let rc_a = Rc::new(3u32);
    let rc_b = Rc::new(5u32);
    assert(<Rc<u32> as PartialOrdSpec>::partial_cmp_spec(&rc_a, &rc_b) == Some(Ordering::Less));
    assert(<Rc<u32> as OrdSpec>::cmp_spec(&rc_a, &rc_b) == Ordering::Less);
}

} // verus!
