//! Tests for `VecDeque<T>` comparison APIs.

use core::cmp::Ordering;
use std::collections::VecDeque;

use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn deque_two(first: u32, second: u32) -> (ret: VecDeque<u32>)
    ensures
        ret@ == seq![first, second],
{
    let mut ret = VecDeque::new();
    ret.push_back(first);
    ret.push_back(second);
    ret
}

fn deque_one(first: u32) -> (ret: VecDeque<u32>)
    ensures
        ret@ == seq![first],
{
    let mut ret = VecDeque::new();
    ret.push_back(first);
    ret
}

fn test_vec_deque_first_difference_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vecdeque::group_vec_dequeue_axioms;
        broadcast use verge::cmp::vec_deque::group_vec_deque_ordering;
        reveal_with_fuel(lexico_eq, 3);
        reveal_with_fuel(lexico_cmp, 3);
    }

    let a = deque_two(1u32, 2u32);
    let b = deque_two(1u32, 3u32);
    let c = deque_two(1u32, 2u32);

    let eq = a == c;
    let partial = a.partial_cmp(&b);
    let cmp = a.cmp(&b);
    assert(eq) by {
        assert(a@ =~= c@);
        lemma_lexico_eq_reflexive::<u32>(a@);
    };
    crate::exec_assert(eq);
    assert(partial == Some(Ordering::Less));
    crate::exec_assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);
    crate::exec_assert(cmp == Ordering::Less);
    proof {
        verge::cmp::vec_deque::lemma_vec_deque_lexico_partial_cmp_spec(&a, &b);
        verge::cmp::vec_deque::lemma_vec_deque_lexico_cmp_spec(&a, &b);
    }
    assert(<VecDeque<u32> as PartialOrdSpec>::partial_cmp_spec(&a, &b) == Some(Ordering::Less));
    crate::exec_assert(partial == Some(Ordering::Less));
    assert(<VecDeque<u32> as OrdSpec>::cmp_spec(&a, &b) == Ordering::Less);
    crate::exec_assert(cmp == Ordering::Less);
}

fn test_vec_deque_prefix_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vecdeque::group_vec_dequeue_axioms;
        broadcast use verge::cmp::vec_deque::group_vec_deque_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    let short = deque_one(1u32);
    let long = deque_two(1u32, 2u32);
    let partial = short.partial_cmp(&long);
    let cmp = short.cmp(&long);
    assert(partial == Some(Ordering::Less));
    crate::exec_assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);
    crate::exec_assert(cmp == Ordering::Less);
}

fn test_vec_deque_provided_ord_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vecdeque::group_vec_dequeue_axioms;
        broadcast use verge::cmp::vec_deque::group_vec_deque_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    let max = deque_two(1u32, 2u32).max(deque_two(1u32, 3u32));
    assert(max@ =~= seq![1u32, 3u32]);
    crate::exec_assert(max.len() == 2 && max[0] == 1u32 && max[1] == 3u32);

    let min = deque_two(1u32, 2u32).min(deque_two(1u32, 3u32));
    assert(min@ =~= seq![1u32, 2u32]);
    crate::exec_assert(min.len() == 2 && min[0] == 1u32 && min[1] == 2u32);

    let clamp = deque_two(1u32, 2u32).clamp(deque_two(1u32, 1u32), deque_two(1u32, 3u32));
    assert(clamp@ =~= seq![1u32, 2u32]);
    crate::exec_assert(clamp.len() == 2 && clamp[0] == 1u32 && clamp[1] == 2u32);
}


// XXX(Verus): the `VecDeque<T>` impls only override `PartialEq::eq` and
// `PartialOrd::partial_cmp`; they inherit `ne`, `lt`, `le`, `gt`, and `ge` from
// the trait defaults, so Verus cannot assume-specify those impl-default methods.
// Direct `!=`, `<`, `<=`, `>`, `>=`, `.ne`, `.lt`, `.le`, `.gt`, and `.ge`
// calls are currently not supported.

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "cmp::vec_deque::first_difference_methods_are_callable",
        test_vec_deque_first_difference_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::vec_deque::prefix_methods_are_callable",
        test_vec_deque_prefix_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::vec_deque::provided_ord_methods_are_callable",
        test_vec_deque_provided_ord_methods_are_callable,
    );
    count
}
