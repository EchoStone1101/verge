//! Specifications and verified comparison impls for arrays.

use super::*;
use core::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use vstd::std_specs::cmp::*;

verus! {

/// Linking lemmas for array comparison.
pub broadcast group group_array_ordering {
    lemma_array_obeys_eq_spec,
    lemma_array_eq_spec,
    lemma_array_obeys_partial_cmp_spec,
    lemma_array_lexico_partial_cmp_spec,
    lemma_array_obeys_cmp_spec,
    lemma_array_lexico_cmp_spec,
}

/// Enable array inequality.
pub assume_specification<T: PartialEq<U>, U, const N: usize>[ <[T; N] as PartialEq<[U; N]>>::ne ](
    a: &[T; N],
    b: &[U; N],
) -> bool;

/// Enable array partial comparison.
pub assume_specification<T: PartialOrd, const N: usize>[ <[T; N] as PartialOrd>::partial_cmp ](
    a: &[T; N],
    b: &[T; N],
) -> Option<Ordering>;

/// Enable array less-than comparison.
pub assume_specification<T: PartialOrd, const N: usize>[ <[T; N] as PartialOrd>::lt ](
    a: &[T; N],
    b: &[T; N],
) -> bool;

/// Enable arrays less-than-or-equal comparison.
pub assume_specification<T: PartialOrd, const N: usize>[ <[T; N] as PartialOrd>::le ](
    a: &[T; N],
    b: &[T; N],
) -> bool;

/// Enable arrays greater-than comparison.
pub assume_specification<T: PartialOrd, const N: usize>[ <[T; N] as PartialOrd>::gt ](
    a: &[T; N],
    b: &[T; N],
) -> bool;

/// Enable arrays greater-than-or-equal comparison.
pub assume_specification<T: PartialOrd, const N: usize>[ <[T; N] as PartialOrd>::ge ](
    a: &[T; N],
    b: &[T; N],
) -> bool;

/// Enable array total comparison.
pub assume_specification<T: Ord, const N: usize>[ <[T; N] as Ord>::cmp ](
    a: &[T; N],
    b: &[T; N],
) -> Ordering;

// XXX(Verus): the array `Ord` impl does not explicitly override `clamp`, `min`,
// or `max`, so Verus cannot assume-specify those impl-default methods.

/// Proof that asserts array equality obeys the element equality spec.
pub broadcast axiom fn lemma_array_obeys_eq_spec<T: PartialEq, const N: usize>()
    ensures
        #[trigger] <[T; N] as PartialEqSpec>::obeys_eq_spec() == T::obeys_eq_spec();

/// Proof that links array `eq_spec` with lexicographic equality.
pub broadcast axiom fn lemma_array_eq_spec<T: PartialEq, const N: usize>(a: &[T; N], b: &[T; N])
    ensures
        #![trigger <[T; N] as PartialEqSpec>::eq_spec(a, b)]
        <[T; N] as PartialEqSpec>::eq_spec(a, b) == crate::cmp::lexico_eq(a@, b@);

/// Proof that asserts array partial comparison obeys the element partial comparison spec.
pub broadcast axiom fn lemma_array_obeys_partial_cmp_spec<T: PartialOrd, const N: usize>()
    ensures
        #[trigger] <[T; N] as PartialOrdSpec>::obeys_partial_cmp_spec()
            == T::obeys_partial_cmp_spec();

/// Proof that links array `partial_cmp_spec` with lexicographic comparison.
pub broadcast axiom fn lemma_array_lexico_partial_cmp_spec<T: PartialOrd, const N: usize>(
    a: &[T; N],
    b: &[T; N],
)
    ensures
        #![trigger <[T; N] as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <[T; N] as PartialOrdSpec>::partial_cmp_spec(a, b) == crate::cmp::lexico_cmp(a@, b@);

/// Proof that asserts array total comparison obeys the element total comparison spec.
pub broadcast axiom fn lemma_array_obeys_cmp_spec<T: Ord, const N: usize>()
    ensures
        #[trigger] <[T; N] as OrdSpec>::obeys_cmp_spec() == T::obeys_cmp_spec();

/// Proof that links array `cmp_spec` with lexicographic comparison.
pub broadcast axiom fn lemma_array_lexico_cmp_spec<T: Ord, const N: usize>(a: &[T; N], b: &[T; N])
    ensures
        #![trigger <[T; N] as OrdSpec>::cmp_spec(a, b)]
        Some(<[T; N] as OrdSpec>::cmp_spec(a, b)) == crate::cmp::lexico_cmp(a@, b@);

impl<T: PartialEqVerified, const N: usize> PartialEqVerified for [T; N] {
    proof fn lemma_obeys_eq_spec() {
        broadcast use group_array_ordering;
        T::lemma_obeys_eq_spec();
        assert(<[T; N] as PartialEqSpec>::obeys_eq_spec());
    }

    proof fn lemma_eq_symmetric(a: &[T; N], b: &[T; N]) {
        lemma_array_eq_spec(a, b);
        lemma_array_eq_spec(b, a);
        lemma_lexico_eq_symmetric(a@, b@);
    }

    proof fn lemma_eq_transitive(a: &[T; N], b: &[T; N], c: &[T; N]) {
        lemma_array_eq_spec(a, b);
        lemma_array_eq_spec(b, c);
        lemma_array_eq_spec(a, c);
        lemma_lexico_eq_transitive(a@, b@, c@);
    }
}

impl<T: EqVerified, const N: usize> EqVerified for [T; N] {
    proof fn lemma_eq_reflexive(a: &[T; N]) {
        lemma_array_eq_spec(a, a);
        lemma_lexico_eq_reflexive(a@);
    }
}

impl<T: PartialOrdVerified, const N: usize> PartialOrdVerified for [T; N] {
    proof fn lemma_obeys_partial_cmp_spec() {
        broadcast use group_array_ordering;
        T::lemma_obeys_partial_cmp_spec();
        assert(<[T; N] as PartialOrdSpec>::obeys_partial_cmp_spec());
    }

    proof fn lemma_cmp_eq_consistent(a: &[T; N], b: &[T; N]) {
        lemma_array_eq_spec(a, b);
        lemma_array_lexico_partial_cmp_spec(a, b);
        lemma_lexico_cmp_eq_consistent(a@, b@);
        if <[T; N] as PartialOrdSpec>::partial_cmp_spec(a, b) == Some(Ordering::Equal) {
            assert forall|c: &[T; N]| #[trigger] <[T; N] as PartialOrdSpec>::partial_cmp_spec(a, c)
                == <[T; N] as PartialOrdSpec>::partial_cmp_spec(b, c) by {
                lemma_array_lexico_partial_cmp_spec(a, c);
                lemma_array_lexico_partial_cmp_spec(b, c);
            };
        }
    }

    proof fn lemma_cmp_dual(a: &[T; N], b: &[T; N]) {
        lemma_array_lexico_partial_cmp_spec(a, b);
        lemma_array_lexico_partial_cmp_spec(b, a);
        lemma_lexico_cmp_dual(a@, b@);
    }

    proof fn lemma_cmp_transitive(a: &[T; N], b: &[T; N], c: &[T; N]) {
        lemma_array_lexico_partial_cmp_spec(a, b);
        lemma_array_lexico_partial_cmp_spec(b, c);
        lemma_array_lexico_partial_cmp_spec(a, c);
        lemma_lexico_cmp_transitive(a@, b@, c@);
    }
}

impl<T: OrdVerified, const N: usize> OrdVerified for [T; N] {
    proof fn lemma_obeys_cmp_spec() {
        broadcast use group_array_ordering;
        T::lemma_obeys_cmp_spec();
        assert(<[T; N] as OrdSpec>::obeys_cmp_spec());
    }

    proof fn lemma_cmp_consistent(a: &[T; N], b: &[T; N]) {
        lemma_array_lexico_partial_cmp_spec(a, b);
        lemma_array_lexico_cmp_spec(a, b);
    }
}

} // verus!
