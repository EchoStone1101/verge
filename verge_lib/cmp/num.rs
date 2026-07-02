//! Verified comparison impls for primitive number and boolean types.

use super::*;

// Macro for EqVerified primitives
macro_rules! impl_eq_verified_primitive {
    ($($t:ty),*) => {
        $(
        verus! {
            impl PartialEqVerified for $t {
                proof fn lemma_obeys_eq_spec() {}
                proof fn lemma_eq_symmetric(a: &$t, b: &$t) {}
                proof fn lemma_eq_transitive(a: &$t, b: &$t, c: &$t) {}
            }
            impl EqVerified for $t {
                proof fn lemma_eq_reflexive(a: &$t) {}
            }
        }
        )*
    }
}

impl_eq_verified_primitive!(bool, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

// Macro for PartialOrdVerified + OrdVerified numeric primitives
macro_rules! impl_partial_ord_verified_numeric {
    ($($t:ty),*) => {
        $(
        verus! {
            impl PartialOrdVerified for $t {
                proof fn lemma_obeys_partial_cmp_spec() {}
                proof fn lemma_cmp_eq_consistent(a: &$t, b: &$t) {}
                proof fn lemma_cmp_dual(a: &$t, b: &$t) {}
                proof fn lemma_cmp_transitive(a: &$t, b: &$t, c: &$t) {}
            }
            impl OrdVerified for $t {
                proof fn lemma_obeys_cmp_spec() {}
                proof fn lemma_cmp_consistent(a: &$t, b: &$t) {}
            }
        }
        )*
    }
}

impl_partial_ord_verified_numeric!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
