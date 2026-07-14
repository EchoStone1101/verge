//! Tests for string comparison APIs.

use core::cmp::Ordering;
use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
use verge::cmp::{lexico_cmp, lemma_lexico_cmp_eq_consistent, lemma_lexico_eq_reflexive};
use verge::prelude::*;
use verge::str::*;

verus! {

fn test_str_comparison_methods_are_callable() {
    proof {
        broadcast use group_str_axioms;
        broadcast use verge::cmp::string::group_str_ordering;
        reveal_strlit("ab");
        reveal_strlit("ac");
        reveal_with_fuel(lexico_cmp, 3);
    }

    let a: &str = "ab";
    let b: &str = "ac";
    let eq = <str as PartialEq>::eq(a, a);
    let ne = <str as PartialEq>::ne(a, b);
    let lt = a < b;
    let le = a <= b;
    let gt = b > a;
    let ge = b >= a;
    assert(eq) by {
        lemma_lexico_eq_reflexive::<u8>(a@.as_bytes());
    };
    crate::exec_assert(eq);
    assert(ne) by {
        lemma_lexico_cmp_eq_consistent::<u8>(a@.as_bytes(), b@.as_bytes());
    };
    crate::exec_assert(ne);
    assert(lt);
    crate::exec_assert(lt);
    assert(le);
    crate::exec_assert(le);
    assert(gt);
    crate::exec_assert(gt);
    assert(ge);
    crate::exec_assert(ge);

    let partial = a.partial_cmp(b);
    let cmp = a.cmp(b);
    assert(partial == Some(Ordering::Less));
    crate::exec_assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);
    crate::exec_assert(cmp == Ordering::Less);

    let max = a.max(b);
    let min = a.min(b);
    let clamp = a.clamp(a, b);

    let max_eq_b = max == b;
    assert(max_eq_b) by {
        assert(max@ =~= b@);
        verge::cmp::string::lemma_str_eq_spec(max, b);
        lemma_lexico_eq_reflexive::<u8>(b@.as_bytes());
    };
    crate::exec_assert(max_eq_b);
    let min_eq_a = min == a;
    assert(min_eq_a) by {
        assert(min@ =~= a@);
        verge::cmp::string::lemma_str_eq_spec(min, a);
        lemma_lexico_eq_reflexive::<u8>(a@.as_bytes());
    };
    crate::exec_assert(min_eq_a);
    let clamp_eq_a = clamp == a;
    assert(clamp_eq_a) by {
        assert(clamp@ =~= a@);
        verge::cmp::string::lemma_str_eq_spec(clamp, a);
        lemma_lexico_eq_reflexive::<u8>(a@.as_bytes());
    };
    crate::exec_assert(clamp_eq_a);
}

fn test_string_comparison_methods_are_callable() {
    proof {
        broadcast use group_str_axioms;
        broadcast use verge::cmp::string::group_str_ordering;
        reveal_strlit("ab");
        reveal_strlit("ac");
        reveal_with_fuel(lexico_cmp, 3);
    }

    let a = String::from_str("ab");
    let b = String::from_str("ac");
    let eq = a == a;
    let ne = a != b;
    let lt = a < b;
    let le = a <= b;
    let gt = b > a;
    let ge = b >= a;
    assert(eq) by {
        lemma_lexico_eq_reflexive::<u8>(a@.as_bytes());
    };
    crate::exec_assert(eq);
    assert(ne) by {
        lemma_lexico_cmp_eq_consistent::<u8>(a@.as_bytes(), b@.as_bytes());
    };
    crate::exec_assert(ne);
    assert(lt);
    crate::exec_assert(lt);
    assert(le);
    crate::exec_assert(le);
    assert(gt);
    crate::exec_assert(gt);
    assert(ge);
    crate::exec_assert(ge);

    let a = String::from_str("ab");
    let b = String::from_str("ac");
    proof {
        verge::cmp::string::lemma_string_lexico_partial_cmp_spec(&a, &b);
        verge::cmp::string::lemma_string_lexico_cmp_spec(&a, &b);
    }

    let eq = a == a;
    assert(eq) by {
        lemma_lexico_eq_reflexive::<u8>(a@.as_bytes());
    };
    crate::exec_assert(eq);

    let partial = a.partial_cmp(&b);
    let cmp = a.cmp(&b);
    assert(<String as PartialOrdSpec>::partial_cmp_spec(&a, &b) == Some(Ordering::Less));
    crate::exec_assert(partial == Some(Ordering::Less));
    assert(<String as OrdSpec>::cmp_spec(&a, &b) == Ordering::Less);
    crate::exec_assert(cmp == Ordering::Less);

    assert(partial == Some(Ordering::Less));
    crate::exec_assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);
    crate::exec_assert(cmp == Ordering::Less);

    let max = a.max(b);
    assert(max@ =~= "ac"@);
    crate::exec_assert(max == String::from_str("ac"));

    let a = String::from_str("ab");
    let b = String::from_str("ac");
    let min = a.min(b);
    assert(min@ =~= "ab"@);
    crate::exec_assert(min == String::from_str("ab"));

    let a = String::from_str("ab");
    let b = String::from_str("ac");
    let value = String::from_str("ab");
    let clamp = value.clamp(a, b);
    assert(clamp@ =~= "ab"@);
    crate::exec_assert(clamp == String::from_str("ab"));
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
