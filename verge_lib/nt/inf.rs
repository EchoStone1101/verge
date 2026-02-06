//! Proofs and specifications for (positive) "infinity".
//!
//! An "infinity" value is an "sufficiently large" `int` plus a finite offset `n`, or `inf(n)`.
//! It holds two constracts: (1) any `inf(n)` is always greater than any given finite integer 
//! (2) `inf(a) + b == inf(a + b)` for any finite `a` and `b`. It does not actually represent 
//! infinity, which would otherwise derive `false` under spec-equality: `forall|n: int| inf + n == inf` 
//! would imply `forall|n: int| n == 0`.
//! 
//! # Finiteness
//! Finiteness may go beyond native integer types - `pow2((usize::MAX * usize::MAX) as nat)`, 
//! while astronomically large and does not fit in any `exec` type, is still a finite number.
//! Essentially, the result of any number of arithmetical operations over native integer 
//! types (e.g., `i32` and `usize`), in a program that terminates, can be proven to be finite. 
//!
//! # Why "infinity"?
//! Given the arguments about finiteness above, a terminating `exec` program will only ever
//! refine a condition like `exists|i: int| i > N` for any constant `N` for a finite number of times, 
//! so an ultimate (suffciently large) `i` that satisfies all such conditions must exist.
//! However, actually `choose`-ing the `i` value is not directly possible as it would involve a
//! quantifier over "future program states". The `inf` value solves exactly this issue.
//!
//! In practice, `inf` values can be used as the cardinality of `Seq`s or `Set`s. 
//! For example, a tap that endlessly produces some `T` value can be specified as a `Seq<T>` 
//! with an `inf` length.

//TODO(xyx): this seems to introduce non-termination. Maybe use a feature guard? 

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

use std::marker::Copy;

verus! {

/// This function creates a "sufficiently large" `int` value plus an `ofs` offset.
pub uninterp spec fn inf(ofs: int) -> int
    recommends is_finite(ofs),
;

/// This predicate represents finiteness.
pub uninterp spec fn is_finite(n: int) -> bool;

pub broadcast group group_inf_axioms {
    axiom_is_finite_base_literal,
    axiom_is_finite_base_set,
}

/// The main infinity property.
#[verifier::external_body]
pub axiom fn axiom_inf_is_sufficiently_large(ofs: int, n: int)
    requires
        is_finite(ofs) && is_finite(n),
    ensures
        inf(ofs) > n,
;

/// Axiom for `inf(a) + b == inf(a + b)`.
#[verifier::external_body]
pub axiom fn axiom_inf_is_linear(ofs: int, n: int)
    requires
        is_finite(ofs) && is_finite(n),
    ensures 
        inf(ofs + n) == inf(ofs) + n,
        is_finite(ofs + n),
;

/// Base axiom for finiteness, by literal value.
#[verifier::external_body]
pub broadcast axiom fn axiom_is_finite_base_literal(n: int)
    requires
        -(u128::MAX as int) <= n <= u128::MAX as int,
    ensures 
        #[trigger] is_finite(n as int),
;

/// Base axiom for finiteness, by set finiteness.
#[verifier::external_body]
pub broadcast axiom fn axiom_is_finite_base_set<T>(s: Set<T>)
    requires 
        s.finite(),
    ensures 
        #[trigger] is_finite(s.len() as int),
;

/// Inductive axiom for finiteness (basic).
#[verifier::external_body]
pub axiom fn axiom_is_finite_induct_basic(n1: int, n2: int)
    requires 
        is_finite(n1) && is_finite(n2),
    ensures 
        is_finite(n1 + n2),
        is_finite(n1 - n2),
        is_finite(n1 * n2),
;

/// Inductive axiom for finiteness (div/mod).
#[verifier::external_body]
pub axiom fn axiom_is_finite_induct_divmod(n1: int, n2: int)
    requires 
        is_finite(n1) && is_finite(n2),
        n2 != 0,
    ensures 
        is_finite(n1 / n2),
        is_finite(n1 % n2),
;

/// Inductive axiom for finiteness (pow).
#[verifier::external_body]
pub axiom fn axiom_is_finite_induct_pow(n1: int, n2: int)
    requires 
        is_finite(n1) && is_finite(n2),
        n2 >= 0,
    ensures 
        is_finite(pow(n1, n2 as nat)),
;

mod tests {
    use super::*;
    use crate::nt::{prime_factors, lemma_prime_factors_bound, lemma_prime_factor_exists};

    broadcast use group_inf_axioms;

    proof fn test_is_finite() {
        assert(is_finite(42usize as int));
        assert(is_finite(set!{1int, 2, 3}.len() as int));
        assert(is_finite(
            pow(i128::MIN as int - 1, prime_factors(u128::MAX as nat).len() + 1) * (200int / 3 % 4)
        )) by {
            lemma_prime_factors_bound(u128::MAX as nat);
            lemma_prime_factor_exists(u128::MAX as nat);

            axiom_is_finite_induct_basic(i128::MIN as int, 1);
            axiom_is_finite_induct_basic(prime_factors(u128::MAX as nat).len() as int, 1);
            axiom_is_finite_induct_pow(i128::MIN as int - 1, (prime_factors(u128::MAX as nat).len() + 1) as int);
            axiom_is_finite_induct_basic(
                pow(i128::MIN as int - 1, prime_factors(u128::MAX as nat).len() + 1) as int,
                200int / 3 % 4,
            );
        }
    }

    proof fn test_inf() {
        let inf = inf(0int);
        assert(inf > u128::MAX as int) by { 
            axiom_inf_is_sufficiently_large(0, u128::MAX as int);
        }
        assert(inf - usize::MAX as int > u128::MAX as int) by {
            axiom_inf_is_linear(0int, -(usize::MAX as int));
            axiom_inf_is_sufficiently_large(-(usize::MAX as int), u128::MAX as int);
        }
    }

}



} // verus!

