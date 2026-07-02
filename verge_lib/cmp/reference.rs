//! Verified comparison impls for shared references.

use super::*;

verus! {

impl<T: PartialEqVerified> PartialEqVerified for &T {
    proof fn lemma_obeys_eq_spec() {
        T::lemma_obeys_eq_spec();
    }
    proof fn lemma_eq_symmetric(a: &&T, b: &&T) {
        T::lemma_eq_symmetric(*a, *b);
    }
    proof fn lemma_eq_transitive(a: &&T, b: &&T, c: &&T) {
        T::lemma_eq_transitive(*a, *b, *c);
    }
}

impl<T: EqVerified> EqVerified for &T {
    proof fn lemma_eq_reflexive(a: &&T) {
        T::lemma_eq_reflexive(*a);
    }
}

impl<T: PartialOrdVerified> PartialOrdVerified for &T {
    proof fn lemma_obeys_partial_cmp_spec() {
        T::lemma_obeys_partial_cmp_spec();
    }
    proof fn lemma_cmp_eq_consistent(a: &&T, b: &&T) {
        T::lemma_cmp_eq_consistent(*a, *b);
    }
    proof fn lemma_cmp_dual(a: &&T, b: &&T) {
        T::lemma_cmp_dual(*a, *b);
    }
    proof fn lemma_cmp_transitive(a: &&T, b: &&T, c: &&T) {
        T::lemma_cmp_transitive(*a, *b, *c);
    }
}

impl<T: OrdVerified> OrdVerified for &T {
    proof fn lemma_obeys_cmp_spec() {
        T::lemma_obeys_cmp_spec();
    }
    proof fn lemma_cmp_consistent(a: &&T, b: &&T) {
        T::lemma_cmp_consistent(*a, *b);
    }
}

} // verus!
