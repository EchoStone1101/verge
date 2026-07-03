//! Verified comparison impls for `Result<T, E>`.

use super::*;
use core::cmp::{Ord, Ordering, PartialEq, PartialOrd};
use vstd::std_specs::cmp::{OrdSpec, PartialEqSpec, PartialOrdSpec};

verus! {

/// Linking lemmas for `Result<T, E>` comparison.
pub broadcast group group_result_ordering {
    lemma_result_obeys_eq_spec,
    lemma_result_eq_spec,
    lemma_result_obeys_partial_cmp_spec,
    lemma_result_partial_cmp_spec,
    lemma_result_obeys_cmp_spec,
    lemma_result_cmp_spec,
}

/// Proof that asserts `Result<T, E>` obeys `PartialEq` when its contents do.
pub broadcast axiom fn lemma_result_obeys_eq_spec<T: PartialEqSpec, E: PartialEqSpec>()
    ensures
        T::obeys_eq_spec() && E::obeys_eq_spec() ==>
            #[trigger] <Result<T, E> as PartialEqSpec>::obeys_eq_spec();

/// Proof that links `PartialEqSpec::eq_spec` for `Result<T, E>` with Rust's variant-wise equality.
pub broadcast axiom fn lemma_result_eq_spec<T: PartialEqSpec, E: PartialEqSpec>(a: &Result<T, E>, b: &Result<T, E>)
    ensures
        #![trigger <Result<T, E> as PartialEqSpec>::eq_spec(a, b)]
        <Result<T, E> as PartialEqSpec>::eq_spec(a, b) == match (a, b) {
            (Ok(x), Ok(y)) => x.eq_spec(y),
            (Err(x), Err(y)) => x.eq_spec(y),
            _ => false,
        };

/// Enable `Result::eq`.
pub assume_specification<T: PartialEq, E: PartialEq>[ <Result<T, E> as PartialEq>::eq ](
    x: &Result<T, E>,
    y: &Result<T, E>,
) -> bool;

/// Proof that asserts `Result<T, E>` obeys `PartialOrd` when its contents do.
pub broadcast axiom fn lemma_result_obeys_partial_cmp_spec<T: PartialOrdSpec, E: PartialOrdSpec>()
    ensures
        T::obeys_partial_cmp_spec() && E::obeys_partial_cmp_spec() ==>
            #[trigger] <Result<T, E> as PartialOrdSpec>::obeys_partial_cmp_spec();

/// Proof that links `PartialOrdSpec::partial_cmp_spec` for `Result<T, E>` with Rust's ordering.
pub broadcast axiom fn lemma_result_partial_cmp_spec<T: PartialOrdSpec, E: PartialOrdSpec>(a: &Result<T, E>, b: &Result<T, E>)
    ensures
        #![trigger <Result<T, E> as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <Result<T, E> as PartialOrdSpec>::partial_cmp_spec(a, b) == match (a, b) {
            (Ok(x), Ok(y)) => x.partial_cmp_spec(y),
            (Ok(_), Err(_)) => Some(Ordering::Greater),
            (Err(_), Ok(_)) => Some(Ordering::Less),
            (Err(x), Err(y)) => x.partial_cmp_spec(y),
        };

/// Enable `Result::partial_cmp`.
pub assume_specification<T: PartialOrd, E: PartialOrd>[ <Result<T, E> as PartialOrd>::partial_cmp ](
    x: &Result<T, E>,
    y: &Result<T, E>,
) -> Option<Ordering>;

/// Proof that asserts `Result<T, E>` obeys `Ord` when its contents do.
pub broadcast axiom fn lemma_result_obeys_cmp_spec<T: OrdSpec, E: OrdSpec>()
    ensures
        T::obeys_cmp_spec() && E::obeys_cmp_spec() ==>
            #[trigger] <Result<T, E> as OrdSpec>::obeys_cmp_spec();

/// Proof that links `OrdSpec::cmp_spec` for `Result<T, E>` with Rust's ordering.
pub broadcast axiom fn lemma_result_cmp_spec<T: OrdSpec, E: OrdSpec>(a: &Result<T, E>, b: &Result<T, E>)
    ensures
        #![trigger <Result<T, E> as OrdSpec>::cmp_spec(a, b)]
        <Result<T, E> as OrdSpec>::cmp_spec(a, b) == match (a, b) {
            (Ok(x), Ok(y)) => x.cmp_spec(y),
            (Ok(_), Err(_)) => Ordering::Greater,
            (Err(_), Ok(_)) => Ordering::Less,
            (Err(x), Err(y)) => x.cmp_spec(y),
        };

/// Enable `Result::cmp`.
pub assume_specification<T: Ord, E: Ord>[ <Result<T, E> as Ord>::cmp ](
    x: &Result<T, E>,
    y: &Result<T, E>,
) -> Ordering;

impl<T: PartialEqVerified, E: PartialEqVerified> PartialEqVerified for Result<T, E> {
    proof fn lemma_obeys_eq_spec() {
        T::lemma_obeys_eq_spec();
        E::lemma_obeys_eq_spec();
        broadcast use group_result_ordering;
    }

    proof fn lemma_eq_symmetric(a: &Result<T, E>, b: &Result<T, E>) {
        broadcast use group_result_ordering;
        match (a, b) {
            (Ok(x), Ok(y)) => T::lemma_eq_symmetric(x, y),
            (Err(x), Err(y)) => E::lemma_eq_symmetric(x, y),
            _ => {},
        }
    }

    proof fn lemma_eq_transitive(a: &Result<T, E>, b: &Result<T, E>, c: &Result<T, E>) {
        broadcast use group_result_ordering;
        match (a, b, c) {
            (Ok(x), Ok(y), Ok(z)) => T::lemma_eq_transitive(x, y, z),
            (Err(x), Err(y), Err(z)) => E::lemma_eq_transitive(x, y, z),
            _ => {},
        }
    }
}

impl<T: EqVerified, E: EqVerified> EqVerified for Result<T, E> {
    proof fn lemma_eq_reflexive(a: &Result<T, E>) {
        broadcast use group_result_ordering;
        match a {
            Ok(x) => T::lemma_eq_reflexive(x),
            Err(x) => E::lemma_eq_reflexive(x),
        }
    }
}

impl<T: PartialOrdVerified, E: PartialOrdVerified> PartialOrdVerified for Result<T, E> {
    proof fn lemma_obeys_partial_cmp_spec() {
        T::lemma_obeys_partial_cmp_spec();
        E::lemma_obeys_partial_cmp_spec();
        broadcast use group_result_ordering;
    }

    proof fn lemma_cmp_eq_consistent(a: &Result<T, E>, b: &Result<T, E>) {
        broadcast use group_result_ordering;
        match (a, b) {
            (Ok(x), Ok(y)) => {
                T::lemma_cmp_eq_consistent(x, y);
                if a.partial_cmp_spec(b) == Some(Ordering::Equal) {
                    assert forall|c: &Result<T, E>| a.partial_cmp_spec(c) == b.partial_cmp_spec(c) by {
                        broadcast use group_result_ordering;
                        match c {
                            Ok(z) => assert(x.partial_cmp_spec(z) == y.partial_cmp_spec(z)),
                            Err(_) => {},
                        }
                    }
                }
            },
            (Err(x), Err(y)) => {
                E::lemma_cmp_eq_consistent(x, y);
                if a.partial_cmp_spec(b) == Some(Ordering::Equal) {
                    assert forall|c: &Result<T, E>| a.partial_cmp_spec(c) == b.partial_cmp_spec(c) by {
                        broadcast use group_result_ordering;
                        match c {
                            Ok(_) => {},
                            Err(z) => assert(x.partial_cmp_spec(z) == y.partial_cmp_spec(z)),
                        }
                    }
                }
            },
            _ => {},
        }
    }

    proof fn lemma_cmp_dual(a: &Result<T, E>, b: &Result<T, E>) {
        broadcast use group_result_ordering;
        match (a, b) {
            (Ok(x), Ok(y)) => T::lemma_cmp_dual(x, y),
            (Err(x), Err(y)) => E::lemma_cmp_dual(x, y),
            _ => {},
        }
    }

    proof fn lemma_cmp_transitive(a: &Result<T, E>, b: &Result<T, E>, c: &Result<T, E>) {
        broadcast use group_result_ordering;
        match (a, b, c) {
            (Ok(x), Ok(y), Ok(z)) => T::lemma_cmp_transitive(x, y, z),
            (Err(x), Err(y), Err(z)) => E::lemma_cmp_transitive(x, y, z),
            _ => {},
        }
    }
}

impl<T: OrdVerified, E: OrdVerified> OrdVerified for Result<T, E> {
    proof fn lemma_obeys_cmp_spec() {
        T::lemma_obeys_cmp_spec();
        E::lemma_obeys_cmp_spec();
        broadcast use group_result_ordering;
    }

    proof fn lemma_cmp_consistent(a: &Result<T, E>, b: &Result<T, E>) {
        broadcast use group_result_ordering;
        match (a, b) {
            (Ok(x), Ok(y)) => T::lemma_cmp_consistent(x, y),
            (Err(x), Err(y)) => E::lemma_cmp_consistent(x, y),
            _ => {},
        }
    }
}

} // verus!
