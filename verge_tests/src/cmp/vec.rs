//! Tests for `Vec<T>` comparison APIs.

use core::cmp::Ordering;
use std::vec::Vec;

use vstd::prelude::*;
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_vec_first_difference_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use verge::cmp::vec::group_vec_ordering;
        reveal_with_fuel(lexico_eq, 3);
        reveal_with_fuel(lexico_cmp, 3);
    }

    let a = vec![1u32, 2u32];
    let b = vec![1u32, 3u32];
    let c = vec![1u32, 2u32];

    test!(a == c);
    test!(a.ne(&b));
    test!(a.partial_cmp(&b) == Some(Ordering::Less));
    test!(a.cmp(&b) == Ordering::Less);
}

fn test_vec_prefix_comparison_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use verge::cmp::vec::group_vec_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    let short = vec![1u32];
    let long = vec![1u32, 2u32];
    test!(short.partial_cmp(&long) == Some(Ordering::Less));
    test!(short.cmp(&long) == Ordering::Less);
}

fn test_vec_default_partial_ord_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use verge::cmp::vec::group_vec_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    let short = vec![1u32];
    let long = vec![1u32, 2u32];

    test!(short < long);
    test!(short <= long);
    test!(long > short);
    test!(long >= short);

    test!(short.lt(&long));
    test!(short.le(&long));
    test!(long.gt(&short));
    test!(long.ge(&short));
}

fn test_vec_provided_ord_methods_are_callable() {
    proof {
        broadcast use vstd::std_specs::vec::group_vec_axioms;
        broadcast use verge::cmp::vec::group_vec_ordering;
        reveal_with_fuel(lexico_cmp, 3);
    }

    test!(vec![1u32, 2u32].max(vec![1u32, 3u32]) == vec![1u32, 3u32]);
    test!(vec![1u32, 2u32].min(vec![1u32, 3u32]) == vec![1u32, 2u32]);
    test!(vec![1u32, 2u32].clamp(vec![1u32, 1u32], vec![1u32, 3u32]) == vec![1u32, 2u32]);
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "cmp::vec::first_difference_methods_are_callable",
        test_vec_first_difference_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::vec::prefix_comparison_methods_are_callable",
        test_vec_prefix_comparison_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::vec::default_partial_ord_methods_are_callable",
        test_vec_default_partial_ord_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::vec::provided_ord_methods_are_callable",
        test_vec_provided_ord_methods_are_callable,
    );
    count
}
