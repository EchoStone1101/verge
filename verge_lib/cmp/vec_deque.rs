//! Specifications and verified comparison impls for `VecDeque<T>`.

use super::*;
use core::alloc::Allocator;
use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use std::collections::VecDeque;
use vstd::std_specs::cmp::*;

verus! {

/// Linking lemmas for vector deque comparison.
pub broadcast group group_vec_deque_ordering {
    lemma_vec_deque_obeys_eq_spec,
    lemma_vec_deque_eq_spec,
    lemma_vec_deque_obeys_partial_cmp_spec,
    lemma_vec_deque_lexico_partial_cmp_spec,
    lemma_vec_deque_obeys_cmp_spec,
    lemma_vec_deque_lexico_cmp_spec,
}

/// Enable `VecDeque::eq`.
pub assume_specification<T: PartialEq, A: Allocator>[ <VecDeque<T, A> as PartialEq>::eq ](
    a: &VecDeque<T, A>,
    b: &VecDeque<T, A>,
) -> bool;

/// Enable `VecDeque::partial_cmp`.
pub assume_specification<T: PartialOrd, A: Allocator>[ <VecDeque<T, A> as PartialOrd>::partial_cmp ](
    a: &VecDeque<T, A>,
    b: &VecDeque<T, A>,
) -> Option<Ordering>;

/// Enable `VecDeque::cmp`.
pub assume_specification<T: Ord, A: Allocator>[ <VecDeque<T, A> as Ord>::cmp ](
    a: &VecDeque<T, A>,
    b: &VecDeque<T, A>,
) -> Ordering;

/// Proof that asserts vector deque equality obeys the element equality spec.
pub broadcast axiom fn lemma_vec_deque_obeys_eq_spec<T: PartialEq>()
    ensures
        #[trigger] <VecDeque<T> as PartialEqSpec>::obeys_eq_spec() == T::obeys_eq_spec();

/// Proof that links vector deque `eq_spec` with lexicographic equality.
pub broadcast axiom fn lemma_vec_deque_eq_spec<T: PartialEq>(a: &VecDeque<T>, b: &VecDeque<T>)
    ensures
        #![trigger <VecDeque<T> as PartialEqSpec>::eq_spec(a, b)]
        <VecDeque<T> as PartialEqSpec>::eq_spec(a, b) == crate::cmp::lexico_eq(a@, b@);

/// Proof that asserts vector deque partial comparison obeys the element partial comparison spec.
pub broadcast axiom fn lemma_vec_deque_obeys_partial_cmp_spec<T: PartialOrd>()
    ensures
        #[trigger] <VecDeque<T> as PartialOrdSpec>::obeys_partial_cmp_spec()
            == T::obeys_partial_cmp_spec();

/// Proof that links vector deque `partial_cmp_spec` with lexicographic comparison.
pub broadcast axiom fn lemma_vec_deque_lexico_partial_cmp_spec<T: PartialOrd>(
    a: &VecDeque<T>,
    b: &VecDeque<T>,
)
    ensures
        #![trigger <VecDeque<T> as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <VecDeque<T> as PartialOrdSpec>::partial_cmp_spec(a, b) == crate::cmp::lexico_cmp(a@, b@);

/// Proof that asserts vector deque total comparison obeys the element total comparison spec.
pub broadcast axiom fn lemma_vec_deque_obeys_cmp_spec<T: Ord>()
    ensures
        #[trigger] <VecDeque<T> as OrdSpec>::obeys_cmp_spec() == T::obeys_cmp_spec();

/// Proof that links vector deque `cmp_spec` with lexicographic comparison.
pub broadcast axiom fn lemma_vec_deque_lexico_cmp_spec<T: Ord>(a: &VecDeque<T>, b: &VecDeque<T>)
    ensures
        #![trigger <VecDeque<T> as OrdSpec>::cmp_spec(a, b)]
        Some(<VecDeque<T> as OrdSpec>::cmp_spec(a, b)) == crate::cmp::lexico_cmp(a@, b@);

impl<T: PartialEqVerified> PartialEqVerified for VecDeque<T> {
    proof fn lemma_obeys_eq_spec() {
        broadcast use group_vec_deque_ordering;
        T::lemma_obeys_eq_spec();
        assert(<VecDeque<T> as PartialEqSpec>::obeys_eq_spec());
    }

    proof fn lemma_eq_symmetric(a: &VecDeque<T>, b: &VecDeque<T>) {
        lemma_vec_deque_eq_spec(a, b);
        lemma_vec_deque_eq_spec(b, a);
        lemma_lexico_eq_symmetric(a@, b@);
    }

    proof fn lemma_eq_transitive(a: &VecDeque<T>, b: &VecDeque<T>, c: &VecDeque<T>) {
        lemma_vec_deque_eq_spec(a, b);
        lemma_vec_deque_eq_spec(b, c);
        lemma_vec_deque_eq_spec(a, c);
        lemma_lexico_eq_transitive(a@, b@, c@);
    }
}

impl<T: EqVerified> EqVerified for VecDeque<T> {
    proof fn lemma_eq_reflexive(a: &VecDeque<T>) {
        lemma_vec_deque_eq_spec(a, a);
        lemma_lexico_eq_reflexive(a@);
    }
}

impl<T: PartialOrdVerified> PartialOrdVerified for VecDeque<T> {
    proof fn lemma_obeys_partial_cmp_spec() {
        broadcast use group_vec_deque_ordering;
        T::lemma_obeys_partial_cmp_spec();
        assert(<VecDeque<T> as PartialOrdSpec>::obeys_partial_cmp_spec());
    }

    proof fn lemma_cmp_eq_consistent(a: &VecDeque<T>, b: &VecDeque<T>) {
        lemma_vec_deque_eq_spec(a, b);
        lemma_vec_deque_lexico_partial_cmp_spec(a, b);
        lemma_lexico_cmp_eq_consistent(a@, b@);
        if <VecDeque<T> as PartialOrdSpec>::partial_cmp_spec(a, b) == Some(Ordering::Equal) {
            assert forall|c: &VecDeque<T>| #[trigger] <VecDeque<T> as PartialOrdSpec>::partial_cmp_spec(a, c)
                == <VecDeque<T> as PartialOrdSpec>::partial_cmp_spec(b, c) by {
                lemma_vec_deque_lexico_partial_cmp_spec(a, c);
                lemma_vec_deque_lexico_partial_cmp_spec(b, c);
            };
        }
    }

    proof fn lemma_cmp_dual(a: &VecDeque<T>, b: &VecDeque<T>) {
        lemma_vec_deque_lexico_partial_cmp_spec(a, b);
        lemma_vec_deque_lexico_partial_cmp_spec(b, a);
        lemma_lexico_cmp_dual(a@, b@);
    }

    proof fn lemma_cmp_transitive(a: &VecDeque<T>, b: &VecDeque<T>, c: &VecDeque<T>) {
        lemma_vec_deque_lexico_partial_cmp_spec(a, b);
        lemma_vec_deque_lexico_partial_cmp_spec(b, c);
        lemma_vec_deque_lexico_partial_cmp_spec(a, c);
        lemma_lexico_cmp_transitive(a@, b@, c@);
    }
}

impl<T: OrdVerified> OrdVerified for VecDeque<T> {
    proof fn lemma_obeys_cmp_spec() {
        broadcast use group_vec_deque_ordering;
        T::lemma_obeys_cmp_spec();
        assert(<VecDeque<T> as OrdSpec>::obeys_cmp_spec());
    }

    proof fn lemma_cmp_consistent(a: &VecDeque<T>, b: &VecDeque<T>) {
        lemma_vec_deque_lexico_partial_cmp_spec(a, b);
        lemma_vec_deque_lexico_cmp_spec(a, b);
    }
}

} // verus!
