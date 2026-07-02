//! Tests for string comparison APIs.

use core::cmp::Ordering;
use std::collections::BTreeMap;
use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
use verge::cmp::{
    lexico_cmp, lemma_lexico_cmp_eq_consistent, lemma_lexico_eq_reflexive, lemma_ord_verified,
    lemma_partial_eq_verified, lemma_partial_ord_verified, OrdVerified, PartialEqVerified,
    PartialOrdVerified,
};
use verge::prelude::*;
use verge::str::*;

verus! {

fn test_str_comparison_methods_are_callable() {
    proof {
        broadcast use group_str_axioms;
        broadcast use group_str_ordering;
        reveal_strlit("ab");
        reveal_strlit("ac");
        reveal_with_fuel(lexico_cmp, 3);
    }

    let a: &str = "ab";
    let b: &str = "ac";
    assert(a@ < b@);
    let eq = <str as PartialEq>::eq(a, a);
    let ne = <str as PartialEq>::ne(a, b);
    let lt = a < b;
    let le = a <= b;
    let gt = b > a;
    let ge = b >= a;
    assert(eq) by {
        lemma_lexico_eq_reflexive::<u8>(a@.as_bytes());
    };
    assert(lt);
    assert(le);
    assert(gt);
    assert(ge);

    let partial = a.partial_cmp(b);
    let cmp = a.cmp(b);
    assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);
    let method_lt = a.lt(b);
    let method_le = a.le(b);
    let method_gt = b.gt(a);
    let method_ge = b.ge(a);
    assert(method_lt);
    assert(method_le);
    assert(method_gt);
    assert(method_ge);
    assert(ne) by {
        lemma_lexico_cmp_eq_consistent::<u8>(a@.as_bytes(), b@.as_bytes());
    };

    let max = a.max(b);
    let min = a.min(b);
    let clamp = a.clamp(a, b);
    assert(max@ =~= b@);
    assert(min@ =~= a@);
    assert(clamp@ =~= a@);
}

fn test_string_comparison_methods_are_callable() {
    proof {
        broadcast use group_str_axioms;
        broadcast use group_str_ordering;
        reveal_strlit("ab");
        reveal_strlit("ac");
        reveal_with_fuel(lexico_cmp, 3);
    }

    let a = String::from_str("ab");
    let b = String::from_str("ac");
    assert(a@ < b@);
    let eq = a == a;
    let ne = a != b;
    let lt = a < b;
    let le = a <= b;
    let gt = b > a;
    let ge = b >= a;
    assert(eq) by {
        lemma_lexico_eq_reflexive::<u8>(a@.as_bytes());
    };
    assert(lt);
    assert(le);
    assert(gt);
    assert(ge);

    let a = String::from_str("ab");
    let b = String::from_str("ac");
    proof {
        lemma_string_lexico_partial_cmp_spec(&a, &b);
        lemma_string_lexico_cmp_spec(&a, &b);
    }
    assert(<String as PartialOrdSpec>::partial_cmp_spec(&a, &b) == Some(Ordering::Less));
    assert(<String as OrdSpec>::cmp_spec(&a, &b) == Ordering::Less);

    let partial = a.partial_cmp(&b);
    let cmp = a.cmp(&b);
    assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);
    let method_eq = a.eq(&a);
    let method_ne = a.ne(&b);
    let method_lt = a.lt(&b);
    let method_le = a.le(&b);
    let method_gt = b.gt(&a);
    let method_ge = b.ge(&a);
    assert(method_eq) by {
        lemma_lexico_eq_reflexive::<u8>(a@.as_bytes());
    };
    assert(method_ne) by {
        lemma_lexico_cmp_eq_consistent::<u8>(a@.as_bytes(), b@.as_bytes());
    };
    assert(method_lt);
    assert(method_le);
    assert(method_gt);
    assert(method_ge);
    assert(ne) by {
        lemma_lexico_cmp_eq_consistent::<u8>(a@.as_bytes(), b@.as_bytes());
    };

    let max = a.max(b);
    assert(max@ =~= "ac"@);

    let a = String::from_str("ab");
    let b = String::from_str("ac");
    let min = a.min(b);
    assert(min@ =~= "ab"@);

    let a = String::from_str("ab");
    let b = String::from_str("ac");
    let value = String::from_str("ab");
    let clamp = value.clamp(a, b);
    assert(clamp@ =~= "ab"@);
}

fn test_verified_bridge_lemmas_for_strings() {
    proof {
        lemma_partial_eq_verified::<String>();
        lemma_partial_ord_verified::<String>();
        lemma_ord_verified::<String>();
        <str as PartialEqVerified>::lemma_obeys_eq_spec();
        <str as PartialOrdVerified>::lemma_obeys_partial_cmp_spec();
        <str as OrdVerified>::lemma_obeys_cmp_spec();
    }
}

fn test_btree_map_string_key() {
    proof {
        broadcast use group_str_axioms;
        broadcast use group_str_ordering;
        broadcast use vstd::std_specs::btree::group_btree_axioms;
        verge::cmp::lemma_ord_verified::<String>();
        reveal_strlit("key");
    }

    let mut map = BTreeMap::<String, u32>::new();
    let lookup = String::from_str("key");
    map.insert(lookup.clone(), 7);

    let contains = map.contains_key(&lookup);
    assert(contains);
}

} // verus!
