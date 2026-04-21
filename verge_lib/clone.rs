//! Verified trait invariants for `Clone`.
//!
//! ## Inter-Trait Invariants 
//! `Clone` alone carries no invariant. However, when combined with other traits, 
//! Rust language design does have further specifications:
//! - `PartialEq`: `x == x ==> x.clone() == x`. 
//! - `Copy`: `x.clone()` is a *bit-wise* copy.
//! Traits in this module each carries a proof of these cross-trait invariants.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::pervasive::strictly_cloned;
use vstd::std_specs::cmp::*;
use crate::cmp::PartialEqVerified;

verus! {

/// A verified `Clone + PartialEq` that requires a proof that cloning preserves
/// equality: if `a.eq_spec(a)`, then `clone(a).eq_spec(a)`.
///
/// For `EqVerified` types (where reflexivity holds), this simplifies to:
/// cloning always produces an `eq_spec`-equal value.
pub trait ClonePartialEq: Clone + PartialEqVerified {
    /// Proof that cloning preserves `eq_spec`.
    proof fn lemma_clone_preserves_eq(a: &Self)
        requires
            Self::obeys_eq_spec(),
            a.eq_spec(a),
        ensures
            forall|ret: Self| 
                #[trigger] strictly_cloned(*a, ret) ==> a.eq_spec(&ret);
}

/// A verified `Copy` that requires a proof that cloning produces a spec-equal value.
///
/// For `Copy` types, Rust requires that `clone()` is equivalent to a bit-wise copy.
/// This trait approximates that requirement using Verus's ghost-mode `==`.
///
/// **Gap:** Ghost-mode `==` is not strictly bit-wise equality. For immutable references
/// (`&T`), spec `==` compares the pointed-to values rather than the pointer addresses.
/// In practice this distinction rarely matters for correctness of collections or
/// algorithms, but it means `CopyVerified` is slightly weaker than true bit-wise
/// identity for reference types.
pub trait CopyVerified: Copy {
    /// Proof that cloning a `Copy` type produces a spec-equal (ghost `==`) value.
    proof fn lemma_clone_identical(a: &Self)
        ensures
            forall|ret: Self| 
                #[trigger] strictly_cloned(*a, ret) ==> ret == *a;
}

} // verus!

// Macro for primitive implementations
macro_rules! impl_clone_verified_primitive {
    ($($t:ty),*) => {
        $(
        verus! {
            impl ClonePartialEq for $t {
                proof fn lemma_clone_preserves_eq(a: &$t) {}
            }
            impl CopyVerified for $t {
                proof fn lemma_clone_identical(a: &$t) {}
            }
        }
        )*
    }
}

impl_clone_verified_primitive!(bool, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

verus! {

// --- References ---

impl<T: ClonePartialEq> ClonePartialEq for &T {
    proof fn lemma_clone_preserves_eq(a: &&T) {}
}

impl<T: CopyVerified> CopyVerified for &T {
    proof fn lemma_clone_identical(a: &&T) {}
}

// --- Option ---

impl<T: ClonePartialEq> ClonePartialEq for Option<T> {
    proof fn lemma_clone_preserves_eq(a: &Option<T>) {
        match a {
            Some(x) => T::lemma_clone_preserves_eq(x),
            None => {},
        }
    }
}

} // verus!
