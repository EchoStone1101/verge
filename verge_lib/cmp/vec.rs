//! Specifications and verified comparison impls for `Vec<T>`.

use super::*;
use core::alloc::Allocator;
use core::cmp::{Ord, Ordering, PartialEq, PartialOrd};
use std::vec::Vec;
use vstd::std_specs::cmp::*;

verus! {

/// Linking lemmas for vector comparison.
pub broadcast group group_vec_ordering {
    lemma_vec_eq_spec,
    lemma_vec_obeys_partial_cmp_spec,
    lemma_vec_lexico_partial_cmp_spec,
    lemma_vec_obeys_cmp_spec,
    lemma_vec_lexico_cmp_spec,
}

/// Enable `Vec::ne`.
pub assume_specification<T: PartialEq<U>, U, A1: Allocator, A2: Allocator>[ <Vec<T, A1> as PartialEq<Vec<U, A2>>>::ne ](
    a: &Vec<T, A1>,
    b: &Vec<U, A2>,
) -> bool;

/// Enable `Vec::partial_cmp`.
pub assume_specification<T: PartialOrd, A1: Allocator, A2: Allocator>[ <Vec<T, A1> as PartialOrd<Vec<T, A2>>>::partial_cmp ](
    a: &Vec<T, A1>,
    b: &Vec<T, A2>,
) -> Option<Ordering>;

/// Enable `Vec::cmp`.
pub assume_specification<T: Ord, A: Allocator>[ <Vec<T, A> as Ord>::cmp ](
    a: &Vec<T, A>,
    b: &Vec<T, A>,
) -> Ordering;

/// Proof that links vstd's vector `eq_spec` with lexicographic equality.
pub broadcast axiom fn lemma_vec_eq_spec<T: PartialEq>(a: &Vec<T>, b: &Vec<T>)
    ensures
        #![trigger <Vec<T> as PartialEqSpec>::eq_spec(a, b)]
        <Vec<T> as PartialEqSpec>::eq_spec(a, b) == crate::cmp::lexico_eq(a@, b@);

/// Proof that asserts vector partial comparison obeys the element partial comparison spec.
pub broadcast axiom fn lemma_vec_obeys_partial_cmp_spec<T: PartialOrd>()
    ensures
        #[trigger] <Vec<T> as PartialOrdSpec>::obeys_partial_cmp_spec()
            == T::obeys_partial_cmp_spec();

/// Proof that links vector `partial_cmp_spec` with lexicographic comparison.
pub broadcast axiom fn lemma_vec_lexico_partial_cmp_spec<T: PartialOrd>(a: &Vec<T>, b: &Vec<T>)
    ensures
        #![trigger <Vec<T> as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <Vec<T> as PartialOrdSpec>::partial_cmp_spec(a, b) == crate::cmp::lexico_cmp(a@, b@);

/// Proof that asserts vector total comparison obeys the element total comparison spec.
pub broadcast axiom fn lemma_vec_obeys_cmp_spec<T: Ord>()
    ensures
        #[trigger] <Vec<T> as OrdSpec>::obeys_cmp_spec() == T::obeys_cmp_spec();

/// Proof that links vector `cmp_spec` with lexicographic comparison.
pub broadcast axiom fn lemma_vec_lexico_cmp_spec<T: Ord>(a: &Vec<T>, b: &Vec<T>)
    ensures
        #![trigger <Vec<T> as OrdSpec>::cmp_spec(a, b)]
        Some(<Vec<T> as OrdSpec>::cmp_spec(a, b)) == crate::cmp::lexico_cmp(a@, b@);

impl<T: PartialEqVerified> PartialEqVerified for Vec<T> {
    proof fn lemma_obeys_eq_spec() {
        T::lemma_obeys_eq_spec();
    }

    proof fn lemma_eq_symmetric(a: &Vec<T>, b: &Vec<T>) {
        lemma_vec_eq_spec(a, b);
        lemma_vec_eq_spec(b, a);
        lemma_lexico_eq_symmetric(a@, b@);
    }

    proof fn lemma_eq_transitive(a: &Vec<T>, b: &Vec<T>, c: &Vec<T>) {
        lemma_vec_eq_spec(a, b);
        lemma_vec_eq_spec(b, c);
        lemma_vec_eq_spec(a, c);
        lemma_lexico_eq_transitive(a@, b@, c@);
    }
}

impl<T: EqVerified> EqVerified for Vec<T> {
    proof fn lemma_eq_reflexive(a: &Vec<T>) {
        lemma_vec_eq_spec(a, a);
        lemma_lexico_eq_reflexive(a@);
    }
}

impl<T: PartialOrdVerified> PartialOrdVerified for Vec<T> {
    proof fn lemma_obeys_partial_cmp_spec() {
        broadcast use group_vec_ordering;
        T::lemma_obeys_partial_cmp_spec();
        assert(<Vec<T> as PartialOrdSpec>::obeys_partial_cmp_spec());
    }

    proof fn lemma_cmp_eq_consistent(a: &Vec<T>, b: &Vec<T>) {
        lemma_vec_eq_spec(a, b);
        lemma_vec_lexico_partial_cmp_spec(a, b);
        lemma_lexico_cmp_eq_consistent(a@, b@);
        if <Vec<T> as PartialOrdSpec>::partial_cmp_spec(a, b) == Some(Ordering::Equal) {
            assert forall|c: &Vec<T>| #[trigger] <Vec<T> as PartialOrdSpec>::partial_cmp_spec(a, c)
                == <Vec<T> as PartialOrdSpec>::partial_cmp_spec(b, c) by {
                lemma_vec_lexico_partial_cmp_spec(a, c);
                lemma_vec_lexico_partial_cmp_spec(b, c);
            };
        }
    }

    proof fn lemma_cmp_dual(a: &Vec<T>, b: &Vec<T>) {
        lemma_vec_lexico_partial_cmp_spec(a, b);
        lemma_vec_lexico_partial_cmp_spec(b, a);
        lemma_lexico_cmp_dual(a@, b@);
    }

    proof fn lemma_cmp_transitive(a: &Vec<T>, b: &Vec<T>, c: &Vec<T>) {
        lemma_vec_lexico_partial_cmp_spec(a, b);
        lemma_vec_lexico_partial_cmp_spec(b, c);
        lemma_vec_lexico_partial_cmp_spec(a, c);
        lemma_lexico_cmp_transitive(a@, b@, c@);
    }
}

impl<T: OrdVerified> OrdVerified for Vec<T> {
    proof fn lemma_obeys_cmp_spec() {
        broadcast use group_vec_ordering;
        T::lemma_obeys_cmp_spec();
        assert(<Vec<T> as OrdSpec>::obeys_cmp_spec());
    }

    proof fn lemma_cmp_consistent(a: &Vec<T>, b: &Vec<T>) {
        lemma_vec_lexico_partial_cmp_spec(a, b);
        lemma_vec_lexico_cmp_spec(a, b);
    }
}

} // verus!
