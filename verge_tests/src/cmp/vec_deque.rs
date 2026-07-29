//! Tests for `VecDeque<T>` comparison APIs.

use core::cmp::Ordering;
use std::collections::VecDeque;

use vstd::prelude::*;
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

    test!(a == a);
    test!(a.partial_cmp(&b) == Some(Ordering::Less));
    test!(a.cmp(&b) == Ordering::Less);
}

fn test_vec_deque_prefix_comparison_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vecdeque::group_vec_dequeue_axioms;
        broadcast use verge::cmp::vec_deque::group_vec_deque_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    let short = deque_one(1u32);
    let long = deque_two(1u32, 2u32);
    test!(short.partial_cmp(&long) == Some(Ordering::Less));
    test!(short.cmp(&long) == Ordering::Less);
}

fn test_vec_deque_default_partial_ord_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vecdeque::group_vec_dequeue_axioms;
        broadcast use verge::cmp::vec_deque::group_vec_deque_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    let short = deque_one(1u32);
    let long = deque_two(1u32, 2u32);

    test!(short < long);
    test!(short <= long);
    test!(long > short);
    test!(long >= short);

    test!(short.lt(&long));
    test!(short.le(&long));
    test!(long.gt(&short));
    test!(long.ge(&short));
}

fn test_vec_deque_provided_ord_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vecdeque::group_vec_dequeue_axioms;
        broadcast use verge::cmp::vec_deque::group_vec_deque_ordering;
        reveal_with_fuel(lexico_eq, 3);
        reveal_with_fuel(lexico_cmp, 3);
    }

    test!(deque_two(1u32, 2u32).max(deque_two(1u32, 3u32)) == deque_two(1u32, 3u32));
    test!(deque_two(1u32, 2u32).min(deque_two(1u32, 3u32)) == deque_two(1u32, 2u32));
    test!(deque_two(1u32, 2u32).clamp(deque_two(1u32, 1u32), deque_two(1u32, 3u32)) == deque_two(1u32, 2u32));
}


} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "cmp::vec_deque::first_difference_methods_are_callable",
        test_vec_deque_first_difference_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::vec_deque::prefix_comparison_methods_are_callable",
        test_vec_deque_prefix_comparison_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::vec_deque::default_partial_ord_methods_are_callable",
        test_vec_deque_default_partial_ord_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::vec_deque::provided_ord_methods_are_callable",
        test_vec_deque_provided_ord_methods_are_callable,
    );
    count
}
