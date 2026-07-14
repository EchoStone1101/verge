//! Specifications and verified comparison impls for slices.
//!
//! The Rust slice comparison traits are external to Verge, so this module links
//! their vstd spec methods to Verge's lexicographic sequence specs by broadcast
//! axioms and then proves the local `*Verified` traits from those links.

use super::*;
use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use vstd::std_specs::cmp::*;

verus! {

/// Linking lemmas for slice comparison.
pub broadcast group group_slice_ordering {
    lemma_slice_obeys_eq_spec,
    lemma_slice_eq_spec,
    lemma_slice_obeys_partial_cmp_spec,
    lemma_slice_lexico_partial_cmp_spec,
    lemma_slice_obeys_cmp_spec,
    lemma_slice_lexico_cmp_spec,
}

/// Enable slice equality.
pub assume_specification<T: PartialEq<U>, U>[ <[T] as PartialEq<[U]>>::eq ](
    a: &[T],
    b: &[U],
) -> bool;

/// Enable slice partial comparison.
pub assume_specification<T: PartialOrd>[ <[T] as PartialOrd>::partial_cmp ](
    a: &[T],
    b: &[T],
) -> Option<Ordering>;

/// Enable `<` for slices.
pub assume_specification<T: PartialOrd>[ <[T] as PartialOrd>::lt ](
    a: &[T],
    b: &[T],
) -> bool;

/// Enable `<=` for slices.
pub assume_specification<T: PartialOrd>[ <[T] as PartialOrd>::le ](
    a: &[T],
    b: &[T],
) -> bool;

/// Enable `>` for slices.
pub assume_specification<T: PartialOrd>[ <[T] as PartialOrd>::gt ](
    a: &[T],
    b: &[T],
) -> bool;

/// Enable `>=` for slices.
pub assume_specification<T: PartialOrd>[ <[T] as PartialOrd>::ge ](
    a: &[T],
    b: &[T],
) -> bool;

/// Enable slice total comparison.
pub assume_specification<T: Ord>[ <[T] as Ord>::cmp ](a: &[T], b: &[T]) -> Ordering;

/// Proof that asserts slice equality obeys the element equality spec.
pub broadcast axiom fn lemma_slice_obeys_eq_spec<T: PartialEq>()
    ensures
        #[trigger] <[T] as PartialEqSpec>::obeys_eq_spec() == T::obeys_eq_spec();

/// Proof that links slice `eq_spec` with lexicographic equality.
pub broadcast axiom fn lemma_slice_eq_spec<T: PartialEq>(a: &[T], b: &[T])
    ensures
        #![trigger <[T] as PartialEqSpec>::eq_spec(a, b)]
        <[T] as PartialEqSpec>::eq_spec(a, b) == crate::cmp::lexico_eq(a@, b@);

/// Proof that asserts slice partial comparison obeys the element partial comparison spec.
pub broadcast axiom fn lemma_slice_obeys_partial_cmp_spec<T: PartialOrd>()
    ensures
        #[trigger] <[T] as PartialOrdSpec>::obeys_partial_cmp_spec()
            == T::obeys_partial_cmp_spec();

/// Proof that links slice `partial_cmp_spec` with lexicographic comparison.
pub broadcast axiom fn lemma_slice_lexico_partial_cmp_spec<T: PartialOrd>(a: &[T], b: &[T])
    ensures
        #![trigger <[T] as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <[T] as PartialOrdSpec>::partial_cmp_spec(a, b) == crate::cmp::lexico_cmp(a@, b@);

/// Proof that asserts slice total comparison obeys the element total comparison spec.
pub broadcast axiom fn lemma_slice_obeys_cmp_spec<T: Ord>()
    ensures
        #[trigger] <[T] as OrdSpec>::obeys_cmp_spec() == T::obeys_cmp_spec();

/// Proof that links slice `cmp_spec` with lexicographic comparison.
pub broadcast axiom fn lemma_slice_lexico_cmp_spec<T: Ord>(a: &[T], b: &[T])
    ensures
        #![trigger <[T] as OrdSpec>::cmp_spec(a, b)]
        Some(<[T] as OrdSpec>::cmp_spec(a, b)) == crate::cmp::lexico_cmp(a@, b@);

impl<T: PartialEqVerified> PartialEqVerified for [T] {
    proof fn lemma_obeys_eq_spec() {
        broadcast use group_slice_ordering;
        T::lemma_obeys_eq_spec();
        assert(<[T] as PartialEqSpec>::obeys_eq_spec());
    }

    proof fn lemma_eq_symmetric(a: &[T], b: &[T]) {
        lemma_slice_eq_spec(a, b);
        lemma_slice_eq_spec(b, a);
        lemma_lexico_eq_symmetric(a@, b@);
    }

    proof fn lemma_eq_transitive(a: &[T], b: &[T], c: &[T]) {
        lemma_slice_eq_spec(a, b);
        lemma_slice_eq_spec(b, c);
        lemma_slice_eq_spec(a, c);
        lemma_lexico_eq_transitive(a@, b@, c@);
    }
}

impl<T: EqVerified> EqVerified for [T] {
    proof fn lemma_eq_reflexive(a: &[T]) {
        lemma_slice_eq_spec(a, a);
        lemma_lexico_eq_reflexive(a@);
    }
}

impl<T: PartialOrdVerified> PartialOrdVerified for [T] {
    proof fn lemma_obeys_partial_cmp_spec() {
        broadcast use group_slice_ordering;
        T::lemma_obeys_partial_cmp_spec();
        assert(<[T] as PartialOrdSpec>::obeys_partial_cmp_spec());
    }

    proof fn lemma_cmp_eq_consistent(a: &[T], b: &[T]) {
        lemma_slice_eq_spec(a, b);
        lemma_slice_lexico_partial_cmp_spec(a, b);
        lemma_lexico_cmp_eq_consistent(a@, b@);
        if <[T] as PartialOrdSpec>::partial_cmp_spec(a, b) == Some(Ordering::Equal) {
            assert forall|c: &[T]| #[trigger] <[T] as PartialOrdSpec>::partial_cmp_spec(a, c)
                == <[T] as PartialOrdSpec>::partial_cmp_spec(b, c) by {
                lemma_slice_lexico_partial_cmp_spec(a, c);
                lemma_slice_lexico_partial_cmp_spec(b, c);
            };
        }
    }

    proof fn lemma_cmp_dual(a: &[T], b: &[T]) {
        lemma_slice_lexico_partial_cmp_spec(a, b);
        lemma_slice_lexico_partial_cmp_spec(b, a);
        lemma_lexico_cmp_dual(a@, b@);
    }

    proof fn lemma_cmp_transitive(a: &[T], b: &[T], c: &[T]) {
        lemma_slice_lexico_partial_cmp_spec(a, b);
        lemma_slice_lexico_partial_cmp_spec(b, c);
        lemma_slice_lexico_partial_cmp_spec(a, c);
        lemma_lexico_cmp_transitive(a@, b@, c@);
    }
}

impl<T: OrdVerified> OrdVerified for [T] {
    proof fn lemma_obeys_cmp_spec() {
        broadcast use group_slice_ordering;
        T::lemma_obeys_cmp_spec();
        assert(<[T] as OrdSpec>::obeys_cmp_spec());
    }

    proof fn lemma_cmp_consistent(a: &[T], b: &[T]) {
        lemma_slice_lexico_partial_cmp_spec(a, b);
        lemma_slice_lexico_cmp_spec(a, b);
    }
}

} // verus!
