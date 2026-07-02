//! Specifications and lemmas for string comparison.
//!
//! ## Specification Methodology
//! `vstd` provides the `PartialEqSpec`, `PartialOrdSpec`, and `OrdSpec` traits as
//! the standard way to build comparison specs. However, the orphan rule blocks
//! Verge from implementing the traits directly on `str` and `String`. As a
//! workaround, we introduce broadcast lemmas that link the `vstd` spec methods
//! with actual spec clauses.

use super::*;
use vstd::std_specs::cmp::*;

use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use std::string::String;

verus! {

/// Allows for `spec`-mode comparisons on strings.
pub trait StringSpecOrd {
    spec fn spec_lt(self, rhs: Self) -> bool;
    spec fn spec_le(self, rhs: Self) -> bool;
    spec fn spec_gt(self, rhs: Self) -> bool;
    spec fn spec_ge(self, rhs: Self) -> bool;
}

impl StringSpecOrd for Seq<char> {

    open spec fn spec_lt(self, rhs: Self) -> bool
        { crate::cmp::lexico_cmp(self.as_bytes(), rhs.as_bytes()) == Some(Ordering::Less) }

    open spec fn spec_le(self, rhs: Self) -> bool
        { crate::cmp::lexico_cmp(self.as_bytes(), rhs.as_bytes()) != Some(Ordering::Greater) }

    open spec fn spec_gt(self, rhs: Self) -> bool
        { crate::cmp::lexico_cmp(self.as_bytes(), rhs.as_bytes()) == Some(Ordering::Greater) }

    open spec fn spec_ge(self, rhs: Self) -> bool
        { crate::cmp::lexico_cmp(self.as_bytes(), rhs.as_bytes()) != Some(Ordering::Less) }
}

/// Linking lemmas for string comparison.
pub broadcast group group_str_ordering {
    lemma_str_obeys_eq_spec,
    lemma_string_obeys_eq_spec,
    lemma_str_eq_spec,
    lemma_string_eq_spec,
    lemma_str_obeys_partial_cmp_spec,
    lemma_string_obeys_partial_cmp_spec,
    lemma_str_lexico_partial_cmp_spec,
    lemma_string_lexico_partial_cmp_spec,
    lemma_str_obeys_cmp_spec,
    lemma_string_obeys_cmp_spec,
    lemma_str_lexico_cmp_spec,
    lemma_string_lexico_cmp_spec,
}

// `PartialEq`

/// Enable `str` equality.
pub assume_specification[ <str as PartialEq>::eq ](s: &str, other: &str) -> bool;

/// Proof that asserts `str` obeys `PartialEq`.
pub broadcast axiom fn lemma_str_obeys_eq_spec()
    ensures
        #[trigger] <str as PartialEqSpec>::obeys_eq_spec();

/// Proof that asserts `String` obeys `PartialEq`.
pub broadcast axiom fn lemma_string_obeys_eq_spec()
    ensures
        #[trigger] <String as PartialEqSpec>::obeys_eq_spec();

/// Proof that links `PartialEqSpec::eq_spec` for `str` with byte-wise string equality.
pub broadcast axiom fn lemma_str_eq_spec(a: &str, b: &str)
    ensures
        #![trigger <str as PartialEqSpec>::eq_spec(a, b)]
        <str as PartialEqSpec>::eq_spec(a, b) ==
            crate::cmp::lexico_eq(a@.as_bytes(), b@.as_bytes());

/// Proof that links `PartialEqSpec::eq_spec` for `String` with byte-wise string equality.
pub broadcast axiom fn lemma_string_eq_spec(a: &String, b: &String)
    ensures
        #![trigger <String as PartialEqSpec>::eq_spec(a, b)]
        <String as PartialEqSpec>::eq_spec(a, b) ==
            crate::cmp::lexico_eq(a@.as_bytes(), b@.as_bytes());

// `PartialOrd`

/// Enable `String::partial_cmp`.
pub assume_specification[ <String as PartialOrd>::partial_cmp ](a: &String, b: &String) -> Option<Ordering>;

/// Enable `str::partial_cmp`.
pub assume_specification[ <str as PartialOrd>::partial_cmp ](a: &str, b: &str) -> Option<Ordering>;

/// Proof that asserts `str` obeys `PartialOrd`.
pub broadcast axiom fn lemma_str_obeys_partial_cmp_spec()
    ensures
        #[trigger] <str as PartialOrdSpec>::obeys_partial_cmp_spec();

/// Proof that asserts `String` obeys `PartialOrd`.
pub broadcast axiom fn lemma_string_obeys_partial_cmp_spec()
    ensures
        #[trigger] <String as PartialOrdSpec>::obeys_partial_cmp_spec();

/// Proof that links `PartialOrdSpec::partial_cmp_spec` for `str` with actual specs.
pub broadcast axiom fn lemma_str_lexico_partial_cmp_spec(a: &str, b: &str)
    ensures
        #![trigger <str as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <str as PartialOrdSpec>::partial_cmp_spec(a, b) ==
            crate::cmp::lexico_cmp(a@.as_bytes(), b@.as_bytes());

/// Proof that links `PartialOrdSpec::partial_cmp_spec` for `String` with actual specs.
pub broadcast axiom fn lemma_string_lexico_partial_cmp_spec(a: &String, b: &String)
    ensures
        #![trigger <String as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <String as PartialOrdSpec>::partial_cmp_spec(a, b) ==
            crate::cmp::lexico_cmp(a@.as_bytes(), b@.as_bytes());

// `Ord`

/// Enable `String::cmp`.
pub assume_specification[ <String as Ord>::cmp ](a: &String, b: &String) -> Ordering;

/// Enable `str::cmp`.
pub assume_specification[ <str as Ord>::cmp ](a: &str, b: &str) -> Ordering;

/// Proof that asserts `str` obeys `Ord`.
pub broadcast axiom fn lemma_str_obeys_cmp_spec()
    ensures
        #[trigger] <str as OrdSpec>::obeys_cmp_spec();

/// Proof that asserts `String` obeys `Ord`.
pub broadcast axiom fn lemma_string_obeys_cmp_spec()
    ensures
        #[trigger] <String as OrdSpec>::obeys_cmp_spec();

/// Proof that links `OrdSpec::cmp_spec` for `str` with actual specs.
pub broadcast axiom fn lemma_str_lexico_cmp_spec(a: &str, b: &str)
    ensures
        #![trigger <str as OrdSpec>::cmp_spec(a, b)]
        <str as OrdSpec>::cmp_spec(a, b) ==
            crate::cmp::lexico_cmp(a@.as_bytes(), b@.as_bytes())->0;

/// Proof that links `OrdSpec::cmp_spec` for `String` with actual specs.
pub broadcast axiom fn lemma_string_lexico_cmp_spec(a: &String, b: &String)
    ensures
        #![trigger <String as OrdSpec>::cmp_spec(a, b)]
        <String as OrdSpec>::cmp_spec(a, b) ==
            crate::cmp::lexico_cmp(a@.as_bytes(), b@.as_bytes())->0;

impl crate::cmp::PartialEqVerified for str {
    proof fn lemma_obeys_eq_spec() {
        broadcast use group_str_ordering;
    }

    proof fn lemma_eq_symmetric(a: &Self, b: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_eq_symmetric::<u8>(a@.as_bytes(), b@.as_bytes());
    }

    proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_eq_transitive::<u8>(a@.as_bytes(), b@.as_bytes(), c@.as_bytes());
    }
}

impl crate::cmp::EqVerified for str {
    proof fn lemma_eq_reflexive(a: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_eq_reflexive::<u8>(a@.as_bytes());
    }
}

impl crate::cmp::PartialOrdVerified for str {
    proof fn lemma_obeys_partial_cmp_spec() {
        broadcast use group_str_ordering;
    }

    proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_cmp_eq_consistent::<u8>(a@.as_bytes(), b@.as_bytes());
        if a.partial_cmp_spec(b) == Some(Ordering::Equal) {
            assert forall|c: &Self| a.partial_cmp_spec(c) == b.partial_cmp_spec(c) by {
                crate::cmp::lemma_lexico_cmp_eq_consistent::<u8>(a@.as_bytes(), b@.as_bytes());
                assert(crate::cmp::lexico_cmp(a@.as_bytes(), c@.as_bytes())
                    == crate::cmp::lexico_cmp(b@.as_bytes(), c@.as_bytes()));
            }
        }
    }

    proof fn lemma_cmp_dual(a: &Self, b: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_cmp_dual::<u8>(a@.as_bytes(), b@.as_bytes());
    }

    proof fn lemma_cmp_transitive(a: &Self, b: &Self, c: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_cmp_transitive::<u8>(a@.as_bytes(), b@.as_bytes(), c@.as_bytes());
    }
}

impl crate::cmp::OrdVerified for str {
    proof fn lemma_obeys_cmp_spec() {
        broadcast use group_str_ordering;
    }

    proof fn lemma_cmp_consistent(a: &Self, b: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_cmp_total::<u8>(a@.as_bytes(), b@.as_bytes());
    }
}

impl crate::cmp::PartialEqVerified for String {
    proof fn lemma_obeys_eq_spec() {
        broadcast use group_str_ordering;
    }

    proof fn lemma_eq_symmetric(a: &Self, b: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_eq_symmetric::<u8>(a@.as_bytes(), b@.as_bytes());
    }

    proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_eq_transitive::<u8>(a@.as_bytes(), b@.as_bytes(), c@.as_bytes());
    }
}

impl crate::cmp::EqVerified for String {
    proof fn lemma_eq_reflexive(a: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_eq_reflexive::<u8>(a@.as_bytes());
    }
}

impl crate::cmp::PartialOrdVerified for String {
    proof fn lemma_obeys_partial_cmp_spec() {
        broadcast use group_str_ordering;
    }

    proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_cmp_eq_consistent::<u8>(a@.as_bytes(), b@.as_bytes());
        if a.partial_cmp_spec(b) == Some(Ordering::Equal) {
            assert forall|c: &Self| a.partial_cmp_spec(c) == b.partial_cmp_spec(c) by {
                crate::cmp::lemma_lexico_cmp_eq_consistent::<u8>(a@.as_bytes(), b@.as_bytes());
                assert(crate::cmp::lexico_cmp(a@.as_bytes(), c@.as_bytes())
                    == crate::cmp::lexico_cmp(b@.as_bytes(), c@.as_bytes()));
            }
        }
    }

    proof fn lemma_cmp_dual(a: &Self, b: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_cmp_dual::<u8>(a@.as_bytes(), b@.as_bytes());
    }

    proof fn lemma_cmp_transitive(a: &Self, b: &Self, c: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_cmp_transitive::<u8>(a@.as_bytes(), b@.as_bytes(), c@.as_bytes());
    }
}

impl crate::cmp::OrdVerified for String {
    proof fn lemma_obeys_cmp_spec() {
        broadcast use group_str_ordering;
    }

    proof fn lemma_cmp_consistent(a: &Self, b: &Self) {
        broadcast use group_str_ordering;
        crate::cmp::lemma_lexico_cmp_total::<u8>(a@.as_bytes(), b@.as_bytes());
    }
}

} // verus!
