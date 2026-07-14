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

verus! {

pub mod lexico;
mod internal;
pub mod array;
pub mod num;
pub mod option;
pub mod pointer;
pub mod reference;
pub mod result;
pub mod slice;
pub mod string;
pub mod tuple;
pub mod vec;
pub mod vec_deque;

pub use lexico::*;
pub use array::*;
pub use num::*;
pub use option::*;
pub use pointer::*;
pub use reference::*;
pub use result::*;
pub use slice::*;
pub use string::*;
pub use tuple::*;
pub use vec::*;
pub use vec_deque::*;

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

    /// Proof that `partial_cmp_spec` returning `Equal` asserts equivalence, which means two things:
    /// - (1) `Some(Equal)` is equivalent to `PartialEq::eq`
    /// - (2) two equal values are equivalent when compared with another value
    proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self)
        ensures
            a.partial_cmp_spec(b) == Some(Ordering::Equal) <==> a.eq_spec(b),
            a.partial_cmp_spec(b) == Some(Ordering::Equal) ==>
                forall|c: &Self| a.partial_cmp_spec(c) == b.partial_cmp_spec(c);

    /// Proof that `partial_cmp_spec` upholds duality.
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

/// Broadcast lemmas that link `core::cmp::Ordering` equality specs to Rust's
/// concrete `Ordering` equality.
pub broadcast group group_ordering_eq {
    lemma_ordering_obeys_eq_spec,
    lemma_ordering_eq_spec,
}

/// Proof that `Ordering` obeys its `PartialEqSpec` contract.
pub broadcast axiom fn lemma_ordering_obeys_eq_spec()
    ensures
        #[trigger] <Ordering as PartialEqSpec>::obeys_eq_spec();

/// Link `Ordering::eq_spec` to concrete equality between `Ordering` variants.
pub broadcast axiom fn lemma_ordering_eq_spec(a: &Ordering, b: &Ordering)
    ensures
        #![trigger <Ordering as PartialEqSpec>::eq_spec(a, b)]
        <Ordering as PartialEqSpec>::eq_spec(a, b) == (*a == *b);

/// Enable direct `Ordering` equality calls in verified code.
pub assume_specification[ <Ordering as PartialEq<Ordering>>::eq ](
    a: &Ordering,
    b: &Ordering,
) -> bool;

impl PartialEqVerified for Ordering {
    proof fn lemma_obeys_eq_spec() {
        broadcast use group_ordering_eq;
    }

    proof fn lemma_eq_symmetric(a: &Ordering, b: &Ordering) {
        broadcast use group_ordering_eq;
    }

    proof fn lemma_eq_transitive(a: &Ordering, b: &Ordering, c: &Ordering) {
        broadcast use group_ordering_eq;
    }
}

impl EqVerified for Ordering {
    proof fn lemma_eq_reflexive(a: &Ordering) {
        broadcast use group_ordering_eq;
    }
}

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

} // verus!
