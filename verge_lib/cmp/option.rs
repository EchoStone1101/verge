//! Verified comparison impls for `Option<T>`.

use super::*;

verus! {

impl<T: PartialEqVerified> PartialEqVerified for Option<T> {
    proof fn lemma_obeys_eq_spec() {
        T::lemma_obeys_eq_spec();
    }
    proof fn lemma_eq_symmetric(a: &Option<T>, b: &Option<T>) {
        match (a, b) {
            (Some(x), Some(y)) => T::lemma_eq_symmetric(x, y),
            _ => {},
        }
    }
    proof fn lemma_eq_transitive(a: &Option<T>, b: &Option<T>, c: &Option<T>) {
        match (a, b, c) {
            (Some(x), Some(y), Some(z)) => T::lemma_eq_transitive(x, y, z),
            _ => {},
        }
    }
}

impl<T: EqVerified> EqVerified for Option<T> {
    proof fn lemma_eq_reflexive(a: &Option<T>) {
        match a {
            Some(x) => T::lemma_eq_reflexive(x),
            None => {},
        }
    }
}

impl<T: PartialOrdVerified + PartialEqVerified> PartialOrdVerified for Option<T> {
    proof fn lemma_obeys_partial_cmp_spec() {
        T::lemma_obeys_partial_cmp_spec();
    }
    proof fn lemma_cmp_eq_consistent(a: &Option<T>, b: &Option<T>) {
        match (a, b) {
            (Some(x), Some(y)) => {
                T::lemma_cmp_eq_consistent(x, y);
            },
            _ => {},
        }
    }
    proof fn lemma_cmp_dual(a: &Option<T>, b: &Option<T>) {
        match (a, b) {
            (Some(x), Some(y)) => T::lemma_cmp_dual(x, y),
            _ => {},
        }
    }
    proof fn lemma_cmp_transitive(a: &Option<T>, b: &Option<T>, c: &Option<T>) {
        match (a, b, c) {
            (Some(x), Some(y), Some(z)) => T::lemma_cmp_transitive(x, y, z),
            _ => {},
        }
    }
}

impl<T: OrdVerified> OrdVerified for Option<T> {
    proof fn lemma_obeys_cmp_spec() {
        T::lemma_obeys_cmp_spec();
    }
    proof fn lemma_cmp_consistent(a: &Option<T>, b: &Option<T>) {
        match (a, b) {
            (Some(x), Some(y)) => T::lemma_cmp_consistent(x, y),
            _ => {},
        }
    }
}

} // verus!
