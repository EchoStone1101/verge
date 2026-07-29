//! Tests for string comparison APIs.

use core::cmp::Ordering;
use vstd::prelude::*;
use verge::cmp::{lexico_eq, lexico_cmp};
use verge::prelude::*;
use verge::str::*;

verus! {

fn test_str_comparison_methods_are_callable() {
    proof {
        broadcast use group_str_axioms;
        broadcast use verge::cmp::string::group_str_ordering;
        reveal_strlit("ab");
        reveal_strlit("ac");
        reveal_with_fuel(lexico_eq, 3);
        reveal_with_fuel(lexico_cmp, 3);
    }

    let a: &str = "ab";
    let b: &str = "ac";
    test!(a == a);
    test!(a != b);
    test!(a < b);
    test!(a <= b);
    test!(b > a);
    test!(b >= a);

    test!(a.partial_cmp(b) == Some(Ordering::Less));
    test!(a.cmp(b) == Ordering::Less);
    test!(a.max(b) == b);
    test!(a.min(b) == a);
    test!(a.clamp(a, b) == a);
}

fn test_string_comparison_methods_are_callable() {
    proof {
        broadcast use group_str_axioms;
        broadcast use verge::cmp::string::group_str_ordering;
        reveal_strlit("ab");
        reveal_strlit("ac");
        reveal_with_fuel(lexico_eq, 3);
        reveal_with_fuel(lexico_cmp, 3);
    }

    let a = String::from_str("ab");
    let b = String::from_str("ac");
    test!(a == a);
    test!(a != b);
    test!(a < b);
    test!(a <= b);
    test!(b > a);
    test!(b >= a);
    test!(a.partial_cmp(&b) == Some(Ordering::Less));
    test!(a.cmp(&b) == Ordering::Less);
    test!(a.clone().max(b.clone()) == b);
    test!(a.clone().min(b.clone()) == a);
    test!(a.clone().clamp(a.clone(), b.clone()) == a);
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "cmp::string::str_comparison_methods_are_callable",
        test_str_comparison_methods_are_callable,
    );
    count += crate::run_test(
        "cmp::string::comparison_methods_are_callable",
        test_string_comparison_methods_are_callable,
    );
    count
}
