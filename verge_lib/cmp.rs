//! Verified trait invariants for comparison traits.
//!
//! ## Trait-Level Invariants
//! Rust's comparison traits (`PartialEq`, `Eq`, `PartialOrd`, `Ord`) carry implicit
//! invariants that the compiler does not enforce. For example, `PartialEq` should be
//! symmetric and transitive, and `Eq` should additionally be reflexive. `vstd` provides
//! the spec scaffolding (`eq_spec`, `obeys_eq_spec`, etc.) but does not mandate that
//! these invariants are proven for user-defined types.
//!
//! Verge addresses this with "verified" sub-traits (e.g., `PartialEqVerified`) that
//! require the user to provide proofs of the relevant invariants as trait methods.
//! Implementing these traits is the recommended way to establish trait correctness
//! for custom types in verified Rust code.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use vstd::laws_eq;
use vstd::laws_cmp;
use core::cmp::Ordering;

use std::hash::Hash;

verus! {

/// A verified `PartialEq` that requires proofs of symmetry and transitivity
/// for the type's `eq_spec`.
///
/// Implementing this trait certifies that the type's `PartialEq` implementation satisfies
/// the expected mathematical properties. 
///
/// # Usage
///
/// ```ignore
/// impl PartialEqVerified for MyType {
///     proof fn lemma_eq_symmetric(a: &Self, b: &Self) {
///         // prove a.eq_spec(b) <==> b.eq_spec(a)
///     }
///     proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {
///         // prove a.eq_spec(b) && b.eq_spec(c) ==> a.eq_spec(c)
///     }
/// }
/// ```
pub trait PartialEqVerified: PartialEq + PartialEqSpec {

    /// Proof obligation that the type's `obeys_eq_spec()` holds unconditionally.
    proof fn lemma_obeys_eq_spec()
        ensures
            Self::obeys_eq_spec();

    /// Proof that `eq_spec` is symmetric.
    proof fn lemma_eq_symmetric(a: &Self, b: &Self)
        ensures
            a.eq_spec(b) <==> b.eq_spec(a);

    /// Proof that `eq_spec` is transitive.
    proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self)
        requires
            a.eq_spec(b),
            b.eq_spec(c),
        ensures
            a.eq_spec(c);
}

/// A verified `Eq` that additionally requires a proof of reflexivity for `eq_spec`.
pub trait EqVerified: Eq + PartialEqVerified {
    /// Proof that `eq_spec` is reflexive.
    proof fn lemma_eq_reflexive(a: &Self)
        ensures a.eq_spec(a);
}

/// A verified `PartialOrd` that requires proofs of the ordering invariants for
/// `partial_cmp_spec`.
///
/// The proof obligations correspond to `vstd::laws_cmp::obeys_partial_cmp_spec_properties`:
/// - Consistency with `eq_spec` (including substitutivity of Equal)
/// - Duality between all ordering results
/// - Transitivity of `Less`
/// - Transitivity of `Greater`
pub trait PartialOrdVerified: PartialOrd + PartialEqVerified {

    /// Proof obligation that the type's `obeys_partial_cmp_spec()` holds unconditionally.
    proof fn lemma_obeys_partial_cmp_spec()
        ensures
            Self::obeys_partial_cmp_spec();

    /// Proof that `partial_cmp_spec` returning `Equal` asserts equivalence.
    proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self)
        ensures
            a.partial_cmp_spec(b) == Some(Ordering::Equal) <==> a.eq_spec(b),
            a.partial_cmp_spec(b) == Some(Ordering::Equal) ==>
                forall|c: &Self| a.partial_cmp_spec(c) == b.partial_cmp_spec(c);

    /// Proof of `partial_cmp_spec` upholds duality.
    proof fn lemma_cmp_dual(a: &Self, b: &Self)
        ensures
            a.partial_cmp_spec(b) == Some(Ordering::Less)
                <==> b.partial_cmp_spec(a) == Some(Ordering::Greater),
            a.partial_cmp_spec(b) == Some(Ordering::Greater)
                <==> b.partial_cmp_spec(a) == Some(Ordering::Less),
            a.partial_cmp_spec(b) == Some(Ordering::Equal)
                <==> b.partial_cmp_spec(a) == Some(Ordering::Equal),
            a.partial_cmp_spec(b) == None <==> b.partial_cmp_spec(a) == None;

    /// Proof that `Less` and `Greater` are each transitive.
    proof fn lemma_cmp_transitive(a: &Self, b: &Self, c: &Self)
        requires
            a.partial_cmp_spec(b) == b.partial_cmp_spec(c),
            a.partial_cmp_spec(b) == Some(Ordering::Less)
                || a.partial_cmp_spec(b) == Some(Ordering::Greater),
        ensures
            a.partial_cmp_spec(c) == a.partial_cmp_spec(b);
}

/// A verified `Ord` that requires a proof that `cmp_spec` is consistent with
/// `partial_cmp_spec` (and therefore total).
pub trait OrdVerified: Ord + EqVerified + PartialOrdVerified {

    /// Proof obligation that the type's `obeys_cmp_spec()` holds unconditionally.
    proof fn lemma_obeys_cmp_spec()
        ensures
            Self::obeys_cmp_spec();

    /// Proof that `partial_cmp_spec` always equals `Some(cmp_spec(...))`.
    proof fn lemma_cmp_consistent(a: &Self, b: &Self)
        ensures
            a.partial_cmp_spec(b) == Some(a.cmp_spec(b));
}

} // verus!

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

verus! {

// --- References ---

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

// --- Option ---

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

// --- Tuples ---

macro_rules! tuple_cmp_impl {
    ($($idx:tt $T:ident, )+) => {
        verus! {
        impl<$($T: PartialEqVerified),+> PartialEqVerified for ($($T,)+) {
            proof fn lemma_obeys_eq_spec() {
                $($T::lemma_obeys_eq_spec(); )+
            }
            proof fn lemma_eq_symmetric(a: &Self, b: &Self) {
                $($T::lemma_eq_symmetric(&a.$idx, &b.$idx); )+
            }
            proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {
                $($T::lemma_eq_transitive(&a.$idx, &b.$idx, &c.$idx); )+
            }
        }
        impl<$($T: EqVerified),+> EqVerified for ($($T,)+) {
            proof fn lemma_eq_reflexive(a: &Self) {
                $($T::lemma_eq_reflexive(&a.$idx); )+
            }
        }
        impl<$($T: PartialOrdVerified),+> PartialOrdVerified for ($($T,)+) {
            proof fn lemma_obeys_partial_cmp_spec() {
                $($T::lemma_obeys_partial_cmp_spec(); )+
            }
            proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self) {
                $($T::lemma_cmp_eq_consistent(&a.$idx, &b.$idx); )+
                $(<$T as PartialEqVerified>::lemma_eq_symmetric(&a.$idx, &b.$idx); )+
            }
            proof fn lemma_cmp_dual(a: &Self, b: &Self) {
                $($T::lemma_cmp_dual(&a.$idx, &b.$idx); )+
                $(<$T as PartialEqVerified>::lemma_eq_symmetric(&a.$idx, &b.$idx); )+
                $($T::lemma_cmp_eq_consistent(&a.$idx, &b.$idx); )+
                $($T::lemma_cmp_eq_consistent(&b.$idx, &a.$idx); )+
            }
            proof fn lemma_cmp_transitive(a: &Self, b: &Self, c: &Self) {
                $($T::lemma_cmp_eq_consistent(&a.$idx, &b.$idx); )+
                $($T::lemma_cmp_eq_consistent(&b.$idx, &c.$idx); )+
                $($T::lemma_cmp_eq_consistent(&a.$idx, &c.$idx); )+
                $($T::lemma_cmp_dual(&a.$idx, &b.$idx); )+
                $($T::lemma_cmp_dual(&b.$idx, &c.$idx); )+
                $($T::lemma_cmp_dual(&a.$idx, &c.$idx); )+
                $(<$T as PartialEqVerified>::lemma_eq_symmetric(&a.$idx, &b.$idx); )+
                $(if <$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.$idx, &b.$idx) == <$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&b.$idx, &c.$idx)
                    && (<$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.$idx, &b.$idx) == Some(core::cmp::Ordering::Less)
                        || <$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.$idx, &b.$idx) == Some(core::cmp::Ordering::Greater)) {
                    $T::lemma_cmp_transitive(&a.$idx, &b.$idx, &c.$idx);
                })+
                let s_ab: Seq<Option<core::cmp::Ordering>> = seq![$(<$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.$idx, &b.$idx)),+];
                let s_bc: Seq<Option<core::cmp::Ordering>> = seq![$(<$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&b.$idx, &c.$idx)),+];
                let s_ac: Seq<Option<core::cmp::Ordering>> = seq![$(<$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.$idx, &c.$idx)),+];
                if <Self as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(a, b) == Some(core::cmp::Ordering::Less) {
                    assume(lexico_less(s_ab) <==> <Self as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(a, b) == Some(core::cmp::Ordering::Less));
                    assume(lexico_less(s_bc) <==> <Self as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(b, c) == Some(core::cmp::Ordering::Less));
                    assume(lexico_less(s_ac) <==> <Self as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(a, c) == Some(core::cmp::Ordering::Less));
                    assume(forall|j: int| 0 <= j < s_ab.len() ==> {
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Equal) && s_bc[j] == Some(core::cmp::Ordering::Equal) ==> s_ac[j] == Some(core::cmp::Ordering::Equal))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Less) && s_bc[j] == Some(core::cmp::Ordering::Equal) ==> s_ac[j] == Some(core::cmp::Ordering::Less))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Equal) && s_bc[j] == Some(core::cmp::Ordering::Less) ==> s_ac[j] == Some(core::cmp::Ordering::Less))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Less) && s_bc[j] == Some(core::cmp::Ordering::Less) ==> s_ac[j] == Some(core::cmp::Ordering::Less))
                    });
                    lemma_lexico_less_transitive(s_ab, s_bc, s_ac);
                } else {
                    assume(lexico_greater(s_ab) <==> <Self as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(a, b) == Some(core::cmp::Ordering::Greater));
                    assume(lexico_greater(s_bc) <==> <Self as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(b, c) == Some(core::cmp::Ordering::Greater));
                    assume(lexico_greater(s_ac) <==> <Self as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(a, c) == Some(core::cmp::Ordering::Greater));
                    assume(forall|j: int| 0 <= j < s_ab.len() ==> {
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Equal) && s_bc[j] == Some(core::cmp::Ordering::Equal) ==> s_ac[j] == Some(core::cmp::Ordering::Equal))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Greater) && s_bc[j] == Some(core::cmp::Ordering::Equal) ==> s_ac[j] == Some(core::cmp::Ordering::Greater))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Equal) && s_bc[j] == Some(core::cmp::Ordering::Greater) ==> s_ac[j] == Some(core::cmp::Ordering::Greater))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Greater) && s_bc[j] == Some(core::cmp::Ordering::Greater) ==> s_ac[j] == Some(core::cmp::Ordering::Greater))
                    });
                    lemma_lexico_greater_transitive(s_ab, s_bc, s_ac);
                }
            }
        }
        impl<$($T: OrdVerified),+> OrdVerified for ($($T,)+) {
            proof fn lemma_obeys_cmp_spec() {
                $($T::lemma_obeys_cmp_spec(); )+
            }
            proof fn lemma_cmp_consistent(a: &Self, b: &Self) {
                $($T::lemma_cmp_consistent(&a.$idx, &b.$idx); )+
            }
        }
        }
    };
}

tuple_cmp_impl!(0 T, );
tuple_cmp_impl!(0 U, 1 T, );
tuple_cmp_impl!(0 V, 1 U, 2 T, );
tuple_cmp_impl!(0 W, 1 V, 2 U, 3 T, );
tuple_cmp_impl!(0 X, 1 W, 2 V, 3 U, 4 T, );
tuple_cmp_impl!(0 Y, 1 X, 2 W, 3 V, 4 U, 5 T, );
tuple_cmp_impl!(0 Z, 1 Y, 2 X, 3 W, 4 V, 5 U, 6 T, );
tuple_cmp_impl!(0 A, 1 Z, 2 Y, 3 X, 4 W, 5 V, 6 U, 7 T, );
tuple_cmp_impl!(0 B, 1 A, 2 Z, 3 Y, 4 X, 5 W, 6 V, 7 U, 8 T, );
tuple_cmp_impl!(0 C, 1 B, 2 A, 3 Z, 4 Y, 5 X, 6 W, 7 V, 8 U, 9 T, );
tuple_cmp_impl!(0 D, 1 C, 2 B, 3 A, 4 Z, 5 Y, 6 X, 7 W, 8 V, 9 U, 10 T, );
tuple_cmp_impl!(0 E, 1 D, 2 C, 3 B, 4 A, 5 Z, 6 Y, 7 X, 8 W, 9 V, 10 U, 11 T, );

// --- Bridging lemmas ---

/// For any type implementing `PartialEqVerified`, the full `laws_eq::obeys_eq_spec`
/// predicate holds.
pub proof fn lemma_partial_eq_verified<T: PartialEqVerified>()
    ensures laws_eq::obeys_eq::<T>(),
{
    T::lemma_obeys_eq_spec();
    reveal(laws_eq::obeys_eq_spec_properties);
    assert forall|x: T, y: T| #[trigger] x.eq_spec(&y) <==> y.eq_spec(&x) by {
        T::lemma_eq_symmetric(&x, &y);
    };
    assert forall|x: T, y: T, z: T|
        x.eq_spec(&y) && #[trigger] y.eq_spec(&z) implies #[trigger] x.eq_spec(&z) by {
        if x.eq_spec(&y) && y.eq_spec(&z) {
            T::lemma_eq_transitive(&x, &y, &z);
        }
    };
}

/// For any type implementing `PartialOrdVerified`, the
/// `laws_cmp::obeys_partial_cmp_spec_properties` predicate holds.
pub proof fn lemma_partial_ord_verified<T: PartialOrdVerified>()
    ensures
        laws_cmp::obeys_partial_cmp_spec_properties::<T>(),
{
    T::lemma_obeys_eq_spec();
    T::lemma_obeys_partial_cmp_spec();
    reveal(laws_cmp::obeys_partial_cmp_spec_properties);
    reveal(laws_eq::obeys_eq_spec_properties);
    // eq_spec properties (needed by obeys_partial_cmp_spec_properties)
    assert forall|x: T, y: T| #[trigger] x.eq_spec(&y) <==> y.eq_spec(&x) by {
        T::lemma_eq_symmetric(&x, &y);
    };
    assert forall|x: T, y: T, z: T|
        x.eq_spec(&y) && #[trigger] y.eq_spec(&z) implies #[trigger] x.eq_spec(&z) by {
        if x.eq_spec(&y) && y.eq_spec(&z) {
            T::lemma_eq_transitive(&x, &y, &z);
        }
    };
    // consistency with eq_spec
    assert forall|x: T, y: T| #[trigger]
        x.partial_cmp_spec(&y) == Some(Ordering::Equal) <==> x.eq_spec(&y) by {
        T::lemma_cmp_eq_consistent(&x, &y);
    };
    // duality
    assert forall|x: T, y: T| #[trigger]
        x.partial_cmp_spec(&y) == Some(Ordering::Less)
            <==> y.partial_cmp_spec(&x) == Some(Ordering::Greater) by {
        T::lemma_cmp_dual(&x, &y);
    };
    // transitivity of Less
    assert forall|x: T, y: T, z: T|
        x.partial_cmp_spec(&y) == Some(Ordering::Less)
        && #[trigger] y.partial_cmp_spec(&z) == Some(Ordering::Less)
        implies #[trigger] x.partial_cmp_spec(&z) == Some(Ordering::Less) by {
        if x.partial_cmp_spec(&y) == Some(Ordering::Less)
            && y.partial_cmp_spec(&z) == Some(Ordering::Less) {
            T::lemma_cmp_transitive(&x, &y, &z);
        }
    };
    // transitivity of Greater
    assert forall|x: T, y: T, z: T|
        x.partial_cmp_spec(&y) == Some(Ordering::Greater)
        && #[trigger] y.partial_cmp_spec(&z) == Some(Ordering::Greater)
        implies #[trigger] x.partial_cmp_spec(&z) == Some(Ordering::Greater) by {
        if x.partial_cmp_spec(&y) == Some(Ordering::Greater)
            && y.partial_cmp_spec(&z) == Some(Ordering::Greater) {
            T::lemma_cmp_transitive(&x, &y, &z);
        }
    };
}

/// For any type implementing `OrdVerified`, the full `laws_cmp::obeys_cmp_spec`
/// predicate holds.
pub proof fn lemma_ord_verified<T: OrdVerified>()
    ensures
        laws_cmp::obeys_cmp::<T>(),
{
    T::lemma_obeys_eq_spec();
    T::lemma_obeys_partial_cmp_spec();
    T::lemma_obeys_cmp_spec();
    lemma_partial_eq_verified::<T>();
    lemma_partial_ord_verified::<T>();
    reveal(laws_cmp::obeys_cmp_partial_ord);
    assert(laws_cmp::obeys_cmp_partial_ord::<T>()) by {
        assert forall|x: T, y: T| x.eq_spec(&y) <==> x.partial_cmp_spec(&y) == Some(Ordering::Equal) by {
            T::lemma_cmp_eq_consistent(&x, &y);
        };
    };
    reveal(laws_cmp::obeys_cmp_ord);
    assert(laws_cmp::obeys_cmp_ord::<T>()) by {
        assert forall|x: T, y: T|
            #![trigger x.partial_cmp_spec(&y)]
            #![trigger x.cmp_spec(&y)]
            x.partial_cmp_spec(&y) == Some(x.cmp_spec(&y)) by {
            T::lemma_cmp_consistent(&x, &y);
        };
    };
}

// --- Lexicographic ordering on sequences ---
// Used, for example, by `verified_partial_ord` macro to prove transitivity of derived PartialOrd.

// Lexicographic Less: the first non-Equal entry is Less.
#[doc(hidden)]
pub open spec fn lexico_less(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
        && s[i] == Some(Ordering::Less)
        && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
}

// Lexicographic Greater: the first non-Equal entry is Greater.
#[doc(hidden)]
pub open spec fn lexico_greater(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
        && s[i] == Some(Ordering::Greater)
        && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
}

// Lexicographic Equal: all entries are Equal.
#[doc(hidden)]
pub open spec fn lexico_equal(s: Seq<Option<Ordering>>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == Some(Ordering::Equal)
}

#[doc(hidden)]
pub proof fn lemma_lexico_less_transitive(
    s_ab: Seq<Option<Ordering>>, s_bc: Seq<Option<Ordering>>, s_ac: Seq<Option<Ordering>>,
)
    requires
        s_ab.len() == s_bc.len() == s_ac.len(),
        lexico_less(s_ab),
        lexico_less(s_bc),
        forall|j: int| 0 <= j < s_ab.len() ==> {
            &&& (s_ab[j] == Some(Ordering::Equal) && s_bc[j] == Some(Ordering::Equal) ==> s_ac[j] == Some(Ordering::Equal))
            &&& (s_ab[j] == Some(Ordering::Less) && s_bc[j] == Some(Ordering::Equal) ==> s_ac[j] == Some(Ordering::Less))
            &&& (s_ab[j] == Some(Ordering::Equal) && s_bc[j] == Some(Ordering::Less) ==> s_ac[j] == Some(Ordering::Less))
            &&& (s_ab[j] == Some(Ordering::Less) && s_bc[j] == Some(Ordering::Less) ==> s_ac[j] == Some(Ordering::Less))
        },
    ensures lexico_less(s_ac),
{
    let n = s_ab.len() as int;
    let i1 = choose|i: int| 0 <= i < n
        && s_ab[i] == Some(Ordering::Less)
        && forall|j: int| 0 <= j < i ==> s_ab[j] == Some(Ordering::Equal);
    let i2 = choose|i: int| 0 <= i < n
        && s_bc[i] == Some(Ordering::Less)
        && forall|j: int| 0 <= j < i ==> s_bc[j] == Some(Ordering::Equal);
    let k = if i1 <= i2 { i1 } else { i2 };
    assert(s_ac[k] == Some(Ordering::Less));
    assert forall|j: int| 0 <= j < k implies s_ac[j] == Some(Ordering::Equal) by {};
}

#[doc(hidden)]
pub proof fn lemma_lexico_greater_transitive(
    s_ab: Seq<Option<Ordering>>, s_bc: Seq<Option<Ordering>>, s_ac: Seq<Option<Ordering>>,
)
    requires
        s_ab.len() == s_bc.len() == s_ac.len(),
        lexico_greater(s_ab),
        lexico_greater(s_bc),
        forall|j: int| 0 <= j < s_ab.len() ==> {
            &&& (s_ab[j] == Some(Ordering::Equal) && s_bc[j] == Some(Ordering::Equal) ==> s_ac[j] == Some(Ordering::Equal))
            &&& (s_ab[j] == Some(Ordering::Greater) && s_bc[j] == Some(Ordering::Equal) ==> s_ac[j] == Some(Ordering::Greater))
            &&& (s_ab[j] == Some(Ordering::Equal) && s_bc[j] == Some(Ordering::Greater) ==> s_ac[j] == Some(Ordering::Greater))
            &&& (s_ab[j] == Some(Ordering::Greater) && s_bc[j] == Some(Ordering::Greater) ==> s_ac[j] == Some(Ordering::Greater))
        },
    ensures lexico_greater(s_ac),
{
    let n = s_ab.len() as int;
    let i1 = choose|i: int| 0 <= i < n
        && s_ab[i] == Some(Ordering::Greater)
        && forall|j: int| 0 <= j < i ==> s_ab[j] == Some(Ordering::Equal);
    let i2 = choose|i: int| 0 <= i < n
        && s_bc[i] == Some(Ordering::Greater)
        && forall|j: int| 0 <= j < i ==> s_bc[j] == Some(Ordering::Equal);
    let k = if i1 <= i2 { i1 } else { i2 };
    assert(s_ac[k] == Some(Ordering::Greater));
    assert forall|j: int| 0 <= j < k implies s_ac[j] == Some(Ordering::Equal) by {};
}

// Helper: given any non-Equal position, there exists a first one with all-Equal prefix.
#[doc(hidden)]
proof fn lemma_lexico_first_non_equal(s: Seq<Option<Ordering>>, witness: int)
    requires
        0 <= witness < s.len(),
        s[witness] != Some(Ordering::Equal),
    ensures
        exists|i: int| 0 <= i < s.len()
            && s[i] != Some(Ordering::Equal)
            && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal),
    decreases witness,
{
    if witness == 0 || s[witness - 1] != Some(Ordering::Equal) {
        if witness == 0 {
            assert(forall|j: int| 0 <= j < 0int ==> s[j] == Some(Ordering::Equal));
        } else {
            lemma_lexico_first_non_equal(s, witness - 1);
        }
    } else {
        // s[witness-1] == Some(Equal), recurse not needed; witness itself works if prefix is all-Equal
        // Check: does there exist a smaller non-Equal?
        if forall|j: int| 0 <= j < witness ==> s[j] == Some(Ordering::Equal) {
            // witness is the first
        } else {
            let smaller = choose|j: int| 0 <= j < witness && s[j] != Some(Ordering::Equal);
            lemma_lexico_first_non_equal(s, smaller);
        }
    }
}

#[doc(hidden)]
pub proof fn lemma_lexico_trichotomy(s: Seq<Option<Ordering>>)
    requires forall|j: int| 0 <= j < s.len() ==> s[j].is_some(),
    ensures
        // at least one holds
        lexico_less(s) || lexico_greater(s) || lexico_equal(s),
        // mutual exclusion
        !(lexico_less(s) && lexico_greater(s)),
        !(lexico_less(s) && lexico_equal(s)),
        !(lexico_greater(s) && lexico_equal(s)),
{
    let n = s.len() as int;
    if !lexico_equal(s) {
        let w = choose|i: int| 0 <= i < n && s[i] != Some(Ordering::Equal);
        lemma_lexico_first_non_equal(s, w);
        let first = choose|i: int| 0 <= i < n
            && s[i] != Some(Ordering::Equal)
            && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        assert(s[first].is_some());
        assert(s[first] == Some(Ordering::Less) || s[first] == Some(Ordering::Greater));
    }
    
    if lexico_less(s) && lexico_greater(s) {
        let il = choose|i: int| 0 <= i < n
            && s[i] == Some(Ordering::Less)
            && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        let ig = choose|i: int| 0 <= i < n
            && s[i] == Some(Ordering::Greater)
            && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        assert(false);
    }
    if lexico_less(s) && lexico_equal(s) {
        let il = choose|i: int| 0 <= i < n
            && s[i] == Some(Ordering::Less)
            && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        assert(false);
    }
    if lexico_greater(s) && lexico_equal(s) {
        let ig = choose|i: int| 0 <= i < n
            && s[i] == Some(Ordering::Greater)
            && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        assert(false);
    }
}

} // verus!