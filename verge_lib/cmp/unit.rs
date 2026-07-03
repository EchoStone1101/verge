//! Verified comparison impls for unit.

use super::*;

verus! {

/// Linking lemmas for unit comparison.
pub broadcast group group_unit_ordering {
    lemma_unit_obeys_eq_spec,
    lemma_unit_eq_spec,
    lemma_unit_obeys_partial_cmp_spec,
    lemma_unit_partial_cmp_spec,
    lemma_unit_obeys_cmp_spec,
    lemma_unit_cmp_spec,
}

/// Enable unit equality.
pub assume_specification[ <() as PartialEq>::eq ](a: &(), b: &()) -> bool;

/// Enable unit inequality.
pub assume_specification[ <() as PartialEq>::ne ](a: &(), b: &()) -> bool;

/// Enable unit partial comparison.
pub assume_specification[ <() as PartialOrd>::partial_cmp ](a: &(), b: &()) -> Option<Ordering>;

/// Enable unit total comparison.
pub assume_specification[ <() as Ord>::cmp ](a: &(), b: &()) -> Ordering;

/// Proof that asserts unit obeys `PartialEq`.
pub broadcast axiom fn lemma_unit_obeys_eq_spec()
    ensures
        #[trigger] <() as PartialEqSpec>::obeys_eq_spec();

/// Proof that unit equality is always true.
pub broadcast axiom fn lemma_unit_eq_spec(a: &(), b: &())
    ensures
        #![trigger <() as PartialEqSpec>::eq_spec(a, b)]
        <() as PartialEqSpec>::eq_spec(a, b);

/// Proof that asserts unit obeys `PartialOrd`.
pub broadcast axiom fn lemma_unit_obeys_partial_cmp_spec()
    ensures
        #[trigger] <() as PartialOrdSpec>::obeys_partial_cmp_spec();

/// Proof that unit partial comparison is always equal.
pub broadcast axiom fn lemma_unit_partial_cmp_spec(a: &(), b: &())
    ensures
        #![trigger <() as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <() as PartialOrdSpec>::partial_cmp_spec(a, b) == Some(Ordering::Equal);

/// Proof that asserts unit obeys `Ord`.
pub broadcast axiom fn lemma_unit_obeys_cmp_spec()
    ensures
        #[trigger] <() as OrdSpec>::obeys_cmp_spec();

/// Proof that unit total comparison is always equal.
pub broadcast axiom fn lemma_unit_cmp_spec(a: &(), b: &())
    ensures
        #![trigger <() as OrdSpec>::cmp_spec(a, b)]
        <() as OrdSpec>::cmp_spec(a, b) == Ordering::Equal;

impl PartialEqVerified for () {
    proof fn lemma_obeys_eq_spec() {
        broadcast use group_unit_ordering;
    }

    proof fn lemma_eq_symmetric(a: &Self, b: &Self) {
        broadcast use group_unit_ordering;
    }

    proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {
        broadcast use group_unit_ordering;
    }
}

impl EqVerified for () {
    proof fn lemma_eq_reflexive(a: &Self) {
        broadcast use group_unit_ordering;
    }
}

impl PartialOrdVerified for () {
    proof fn lemma_obeys_partial_cmp_spec() {
        broadcast use group_unit_ordering;
    }

    proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self) {
        broadcast use group_unit_ordering;
        assert forall|c: &Self| a.partial_cmp_spec(c) == b.partial_cmp_spec(c) by {
            broadcast use group_unit_ordering;
        }
    }

    proof fn lemma_cmp_dual(a: &Self, b: &Self) {
        broadcast use group_unit_ordering;
    }

    proof fn lemma_cmp_transitive(a: &Self, b: &Self, c: &Self) {
        broadcast use group_unit_ordering;
    }
}

impl OrdVerified for () {
    proof fn lemma_obeys_cmp_spec() {
        broadcast use group_unit_ordering;
    }

    proof fn lemma_cmp_consistent(a: &Self, b: &Self) {
        broadcast use group_unit_ordering;
    }
}

} // verus!
