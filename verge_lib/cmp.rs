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
//!
//! ## Known Limitations
//! Tuples implement `PartialEq`, `Eq`, `PartialOrd`, and `Ord` in `std`; however their 
//! specs are not in `vstd` yet, and Verge cannot provide that implementaton (since the spec
//! extension traits are defined in `vstd`). 
//! The current recommended workaround is to explictly define the tuple as a *tuple struct*, 
//! then use the `derive_*` macros provided by Verge to get the derived trait implementation
//! as well as proof of invariants. 
//!
//! For example:
//! 
//! ```ignore
//! #[verge_macros::derive_eq]
//! struct Pair(u8, i32); 
//! 
//! fn compare_pairs(p1: &Pair, p2: &Pair) -> (ret: bool)
//!     returns
//!         PartialEqSpec::eq_spec(p1, p2),
//! {
//!     proof { PartialEqVerified::lemma_eq_symmetric(p1, p2); }
//!     p2 == p1
//! }
//! ```

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
pub trait PartialEqVerified: PartialEq {
    /// Proof that `eq_spec` is symmetric.
    proof fn lemma_eq_symmetric(a: &Self, b: &Self)
        requires
            Self::obeys_eq_spec(),
        ensures 
            a.eq_spec(b) <==> b.eq_spec(a);

    /// Proof that `eq_spec` is transitive.
    proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self)
        requires
            Self::obeys_eq_spec(),
            a.eq_spec(b),
            b.eq_spec(c),
        ensures
            a.eq_spec(c);
}

/// A verified `Eq` that additionally requires a proof of reflexivity for `eq_spec`.
pub trait EqVerified: Eq + PartialEqVerified {
    /// Proof that `eq_spec` is reflexive.
    proof fn lemma_eq_reflexive(a: &Self)
        requires Self::obeys_eq_spec(),
        ensures a.eq_spec(a);
}

/// A verified `PartialOrd` that requires proofs of the ordering invariants for
/// `partial_cmp_spec`.
///
/// The proof obligations correspond to `vstd::laws_cmp::obeys_partial_cmp_spec_properties`:
/// - Consistency with `eq_spec`
/// - Duality between `Less` and `Greater`
/// - Transitivity of `Less`
/// - Transitivity of `Greater`
pub trait PartialOrdVerified: PartialOrd + PartialEqVerified {
    /// Proof that `partial_cmp_spec` returning `Equal` is equivalent to `eq_spec`.
    proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self)
        requires
            Self::obeys_eq_spec(),
            Self::obeys_partial_cmp_spec(),
        ensures
            a.partial_cmp_spec(b) == Some(Ordering::Equal) <==> a.eq_spec(b);

    /// Proof that `Less` in one direction means `Greater` in the other.
    proof fn lemma_cmp_dual(a: &Self, b: &Self)
        requires
            Self::obeys_partial_cmp_spec(),
        ensures
            a.partial_cmp_spec(b) == Some(Ordering::Less)
                <==> b.partial_cmp_spec(a) == Some(Ordering::Greater);

    /// Proof that `Less` is transitive.
    proof fn lemma_cmp_less_transitive(a: &Self, b: &Self, c: &Self)
        requires
            Self::obeys_partial_cmp_spec(),
            a.partial_cmp_spec(b) == Some(Ordering::Less),
            b.partial_cmp_spec(c) == Some(Ordering::Less),
        ensures
            a.partial_cmp_spec(c) == Some(Ordering::Less);

    /// Proof that `Greater` is transitive.
    proof fn lemma_cmp_greater_transitive(a: &Self, b: &Self, c: &Self)
        requires
            Self::obeys_partial_cmp_spec(),
            a.partial_cmp_spec(b) == Some(Ordering::Greater),
            b.partial_cmp_spec(c) == Some(Ordering::Greater),
        ensures
            a.partial_cmp_spec(c) == Some(Ordering::Greater);

    /// Proof that comparability is transitive: if `a` is comparable to `b` and
    /// `b` is comparable to `c`, then `a` is comparable to `c`.
    proof fn lemma_cmp_comparable(a: &Self, b: &Self, c: &Self)
        requires
            Self::obeys_partial_cmp_spec(),
            a.partial_cmp_spec(b).is_some(),
            b.partial_cmp_spec(c).is_some(),
        ensures
            a.partial_cmp_spec(c).is_some();

    /// `Less` is substitutive on the right with respect to `eq_spec`.
    /// Default proof: by ruling out `Equal` and `Greater` using eq-consistency,
    /// eq-transitivity, duality, less-transitivity, and comparability.
    proof fn lemma_less_eq_subst(a: &Self, b: &Self, c: &Self)
        requires
            Self::obeys_eq_spec(),
            Self::obeys_partial_cmp_spec(),
            a.partial_cmp_spec(b) == Some(Ordering::Less),
            b.eq_spec(c),
        ensures
            a.partial_cmp_spec(c) == Some(Ordering::Less),
    {
        Self::lemma_cmp_eq_consistent(b, c);
        Self::lemma_cmp_comparable(a, b, c);
        Self::lemma_cmp_eq_consistent(a, c);
        Self::lemma_cmp_eq_consistent(a, b);
        Self::lemma_cmp_dual(c, a);
        Self::lemma_cmp_dual(a, c);
        // Rule out Equal
        if a.partial_cmp_spec(c) == Some(Ordering::Equal) {
            Self::lemma_eq_symmetric(b, c);
            Self::lemma_eq_transitive(a, c, b);
            // a == c && c == b ==> a == b ==> partial_cmp(a,b) == Equal. Contradiction.
        }
        // Rule out Greater
        if a.partial_cmp_spec(c) == Some(Ordering::Greater) {
            // c < a (duality). c < a && a < b ==> c < b (less_transitive).
            Self::lemma_cmp_less_transitive(c, a, b);
            // But b == c ==> c == b ==> partial_cmp(c,b) == Equal. Contradiction.
            Self::lemma_eq_symmetric(b, c);
            Self::lemma_cmp_eq_consistent(c, b);
        }
    }

    /// `Less` is substitutive on the left with respect to `eq_spec`.
    proof fn lemma_eq_less_subst(a: &Self, b: &Self, c: &Self)
        requires
            Self::obeys_eq_spec(),
            Self::obeys_partial_cmp_spec(),
            a.eq_spec(b),
            b.partial_cmp_spec(c) == Some(Ordering::Less),
        ensures
            a.partial_cmp_spec(c) == Some(Ordering::Less),
    {
        Self::lemma_cmp_eq_consistent(a, b);
        Self::lemma_cmp_comparable(a, b, c);
        Self::lemma_cmp_eq_consistent(a, c);
        Self::lemma_cmp_eq_consistent(b, c);
        Self::lemma_cmp_dual(a, c);
        Self::lemma_cmp_dual(c, a);
        // Rule out Equal
        if a.partial_cmp_spec(c) == Some(Ordering::Equal) {
            // a == c && a == b (symmetry) ==> b == c. contradicts b < c.
            Self::lemma_eq_symmetric(a, b);
            Self::lemma_eq_transitive(b, a, c);
        }
        // Rule out Greater
        if a.partial_cmp_spec(c) == Some(Ordering::Greater) {
            // c < a (duality). b < c (given). b < c && c < a ==> b < a (less_transitive).
            // But a == b ==> b == a ==> partial_cmp(b,a) == Equal. Contradiction.
            Self::lemma_cmp_less_transitive(b, c, a);
            Self::lemma_eq_symmetric(a, b);
            Self::lemma_cmp_eq_consistent(b, a);
        }
    }

    /// `Greater` is substitutive on the right with respect to `eq_spec`.
    proof fn lemma_greater_eq_subst(a: &Self, b: &Self, c: &Self)
        requires
            Self::obeys_eq_spec(),
            Self::obeys_partial_cmp_spec(),
            a.partial_cmp_spec(b) == Some(Ordering::Greater),
            b.eq_spec(c),
        ensures
            a.partial_cmp_spec(c) == Some(Ordering::Greater),
    {
        // a > b ==> b < a (duality(b,a)). b == c ==> c == b (symmetry).
        // c == b && b < a ==> c < a (eq_less_subst(c,b,a)). c < a ==> a > c (duality(c,a)).
        Self::lemma_cmp_dual(b, a);
        Self::lemma_eq_symmetric(b, c);
        Self::lemma_eq_less_subst(c, b, a);
        Self::lemma_cmp_dual(c, a);
    }

    /// `Greater` is substitutive on the left with respect to `eq_spec`.
    proof fn lemma_eq_greater_subst(a: &Self, b: &Self, c: &Self)
        requires
            Self::obeys_eq_spec(),
            Self::obeys_partial_cmp_spec(),
            a.eq_spec(b),
            b.partial_cmp_spec(c) == Some(Ordering::Greater),
        ensures
            a.partial_cmp_spec(c) == Some(Ordering::Greater),
    {
        // b > c ==> c < b (duality(c,b)). a == b ==> b == a (symmetry).
        // c < b && b == a ==> c < a (less_eq_subst(c,b,a)). c < a ==> a > c (duality(c,a)).
        Self::lemma_cmp_dual(c, b);
        Self::lemma_eq_symmetric(a, b);
        Self::lemma_less_eq_subst(c, b, a);
        Self::lemma_cmp_dual(c, a);
    }
}

/// A verified `Ord` that requires a proof that `cmp_spec` is consistent with
/// `partial_cmp_spec` (and therefore total).
pub trait OrdVerified: Ord + EqVerified + PartialOrdVerified {
    /// Proof that `partial_cmp_spec` always equals `Some(cmp_spec(...))`.
    proof fn lemma_cmp_consistent(a: &Self, b: &Self)
        requires
            Self::obeys_cmp_spec(),
            Self::obeys_partial_cmp_spec(),
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
                proof fn lemma_cmp_eq_consistent(a: &$t, b: &$t) {}
                proof fn lemma_cmp_dual(a: &$t, b: &$t) {}
                proof fn lemma_cmp_less_transitive(a: &$t, b: &$t, c: &$t) {}
                proof fn lemma_cmp_greater_transitive(a: &$t, b: &$t, c: &$t) {}
                proof fn lemma_cmp_comparable(a: &$t, b: &$t, c: &$t) {}
            }
            impl OrdVerified for $t {
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
    proof fn lemma_cmp_eq_consistent(a: &&T, b: &&T) {
        T::lemma_cmp_eq_consistent(*a, *b);
    }
    proof fn lemma_cmp_dual(a: &&T, b: &&T) {
        T::lemma_cmp_dual(*a, *b);
    }
    proof fn lemma_cmp_less_transitive(a: &&T, b: &&T, c: &&T) {
        T::lemma_cmp_less_transitive(*a, *b, *c);
    }
    proof fn lemma_cmp_greater_transitive(a: &&T, b: &&T, c: &&T) {
        T::lemma_cmp_greater_transitive(*a, *b, *c);
    }
    proof fn lemma_cmp_comparable(a: &&T, b: &&T, c: &&T) {
        T::lemma_cmp_comparable(*a, *b, *c);
    }
}

impl<T: OrdVerified> OrdVerified for &T {
    proof fn lemma_cmp_consistent(a: &&T, b: &&T) {
        T::lemma_cmp_consistent(*a, *b);
    }
}

// --- Option ---

impl<T: PartialEqVerified> PartialEqVerified for Option<T> {
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
    proof fn lemma_cmp_less_transitive(a: &Option<T>, b: &Option<T>, c: &Option<T>) {
        match (a, b, c) {
            (Some(x), Some(y), Some(z)) => T::lemma_cmp_less_transitive(x, y, z),
            _ => {},
        }
    }
    proof fn lemma_cmp_greater_transitive(a: &Option<T>, b: &Option<T>, c: &Option<T>) {
        match (a, b, c) {
            (Some(x), Some(y), Some(z)) => T::lemma_cmp_greater_transitive(x, y, z),
            _ => {},
        }
    }
    proof fn lemma_cmp_comparable(a: &Option<T>, b: &Option<T>, c: &Option<T>) {
        // Option comparison is total (always returns Some), so comparable is trivially true.
        match (a, b, c) {
            (Some(x), Some(y), Some(z)) => T::lemma_cmp_comparable(x, y, z),
            _ => { admit(); },
        }
    }
}

impl<T: OrdVerified> OrdVerified for Option<T> {
    proof fn lemma_cmp_consistent(a: &Option<T>, b: &Option<T>) {
        match (a, b) {
            (Some(x), Some(y)) => T::lemma_cmp_consistent(x, y),
            _ => {},
        }
    }
}

// --- Bridging lemmas ---

/// For any type implementing `PartialEqVerified`, the full `laws_eq::obeys_eq_spec`
/// predicate holds.
pub proof fn lemma_partial_eq_verified<T: PartialEqVerified>()
    requires T::obeys_eq_spec(),
    ensures laws_eq::obeys_eq_spec::<T>(),
{
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
    requires
        T::obeys_eq_spec(),
        T::obeys_partial_cmp_spec(),
    ensures
        laws_cmp::obeys_partial_cmp_spec_properties::<T>(),
{
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
            T::lemma_cmp_less_transitive(&x, &y, &z);
        }
    };
    // transitivity of Greater
    assert forall|x: T, y: T, z: T|
        x.partial_cmp_spec(&y) == Some(Ordering::Greater)
        && #[trigger] y.partial_cmp_spec(&z) == Some(Ordering::Greater)
        implies #[trigger] x.partial_cmp_spec(&z) == Some(Ordering::Greater) by {
        if x.partial_cmp_spec(&y) == Some(Ordering::Greater)
            && y.partial_cmp_spec(&z) == Some(Ordering::Greater) {
            T::lemma_cmp_greater_transitive(&x, &y, &z);
        }
    };
}

/// For any type implementing `OrdVerified`, the full `laws_cmp::obeys_cmp_spec`
/// predicate holds.
pub proof fn lemma_ord_verified<T: OrdVerified>()
    requires
        T::obeys_eq_spec(),
        T::obeys_partial_cmp_spec(),
        T::obeys_cmp_spec(),
    ensures
        laws_cmp::obeys_cmp_spec::<T>(),
{
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
// Used by `verified_partial_ord` macro to prove transitivity of derived PartialOrd.

/// Lexicographic Less: the first non-Equal entry is Less.
pub open spec fn lexico_less(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
        && s[i] == Some(Ordering::Less)
        && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
}

/// Lexicographic Greater: the first non-Equal entry is Greater.
pub open spec fn lexico_greater(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
        && s[i] == Some(Ordering::Greater)
        && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
}

/// Lexicographic Equal: all entries are Equal.
pub open spec fn lexico_equal(s: Seq<Option<Ordering>>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == Some(Ordering::Equal)
}

} // verus!

// --- Tuple PartialEq support ---
// Std implements PartialEq for tuples up to 12 elements.
// vstd has no support for this.
//
// Limitation: Rust's orphan rules prevent Verge from implementing vstd's
// PartialEqSpecImpl for tuples (both the trait and the type are foreign).
// Only vstd itself can add PartialEqSpecImpl for tuples.
//
// What Verge CAN provide: assume_specification for tuple eq,
// making exec == callable. Without PartialEqSpecImpl, there's no eq_spec.

macro_rules! impl_tuple_eq_spec {
    ([$(($T:ident, $n:tt)),*]) => {
        verus! {
            pub assume_specification<$($T: PartialEq),*>
                [<($($T,)*) as PartialEq>::eq](a: &($($T,)*), b: &($($T,)*)) -> bool;
        }
    }
}

impl_tuple_eq_spec!([(T0, 0)]);
impl_tuple_eq_spec!([(T0, 0), (T1, 1)]);
impl_tuple_eq_spec!([(T0, 0), (T1, 1), (T2, 2)]);
impl_tuple_eq_spec!([(T0, 0), (T1, 1), (T2, 2), (T3, 3)]);
impl_tuple_eq_spec!([(T0, 0), (T1, 1), (T2, 2), (T3, 3), (T4, 4)]);
impl_tuple_eq_spec!([(T0, 0), (T1, 1), (T2, 2), (T3, 3), (T4, 4), (T5, 5)]);
impl_tuple_eq_spec!([(T0, 0), (T1, 1), (T2, 2), (T3, 3), (T4, 4), (T5, 5), (T6, 6)]);
impl_tuple_eq_spec!([(T0, 0), (T1, 1), (T2, 2), (T3, 3), (T4, 4), (T5, 5), (T6, 6), (T7, 7)]);
impl_tuple_eq_spec!([(T0, 0), (T1, 1), (T2, 2), (T3, 3), (T4, 4), (T5, 5), (T6, 6), (T7, 7), (T8, 8)]);
impl_tuple_eq_spec!([(T0, 0), (T1, 1), (T2, 2), (T3, 3), (T4, 4), (T5, 5), (T6, 6), (T7, 7), (T8, 8), (T9, 9)]);
impl_tuple_eq_spec!([(T0, 0), (T1, 1), (T2, 2), (T3, 3), (T4, 4), (T5, 5), (T6, 6), (T7, 7), (T8, 8), (T9, 9), (T10, 10)]);
impl_tuple_eq_spec!([(T0, 0), (T1, 1), (T2, 2), (T3, 3), (T4, 4), (T5, 5), (T6, 6), (T7, 7), (T8, 8), (T9, 9), (T10, 10), (T11, 11)]);
