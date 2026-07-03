//! Verified comparison impls for owning pointer types.

use super::*;
use core::alloc::Allocator;
use core::marker::MetaSized;
use std::rc::Rc;

verus! {

/// Linking lemmas for owning pointer comparisons.
pub broadcast group group_pointer_ordering {
    lemma_box_obeys_eq_spec,
    lemma_box_eq_spec,
    lemma_box_obeys_partial_cmp_spec,
    lemma_box_partial_cmp_spec,
    lemma_box_obeys_cmp_spec,
    lemma_box_cmp_spec,
    lemma_rc_obeys_eq_spec,
    lemma_rc_eq_spec,
    lemma_rc_obeys_partial_cmp_spec,
    lemma_rc_partial_cmp_spec,
    lemma_rc_obeys_cmp_spec,
    lemma_rc_cmp_spec,
}

/// Enable `Box<T>` equality.
pub assume_specification<T: MetaSized + PartialEq, A: Allocator>[ <Box<T, A> as PartialEq>::eq ](a: &Box<T, A>, b: &Box<T, A>) -> bool;

/// Enable `Box<T>` inequality.
pub assume_specification<T: MetaSized + PartialEq, A: Allocator>[ <Box<T, A> as PartialEq>::ne ](a: &Box<T, A>, b: &Box<T, A>) -> bool;

/// Enable `Box<T>` partial comparison.
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Box<T, A> as PartialOrd>::partial_cmp ](a: &Box<T, A>, b: &Box<T, A>) -> Option<Ordering>;

/// Enable `Box<T>` less-than comparison.
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Box<T, A> as PartialOrd>::lt ](a: &Box<T, A>, b: &Box<T, A>) -> bool;

/// Enable `Box<T>` less-than-or-equal comparison.
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Box<T, A> as PartialOrd>::le ](a: &Box<T, A>, b: &Box<T, A>) -> bool;

/// Enable `Box<T>` greater-than comparison.
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Box<T, A> as PartialOrd>::gt ](a: &Box<T, A>, b: &Box<T, A>) -> bool;

/// Enable `Box<T>` greater-than-or-equal comparison.
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Box<T, A> as PartialOrd>::ge ](a: &Box<T, A>, b: &Box<T, A>) -> bool;

/// Enable `Box<T>` total comparison.
pub assume_specification<T: MetaSized + Ord, A: Allocator>[ <Box<T, A> as Ord>::cmp ](a: &Box<T, A>, b: &Box<T, A>) -> Ordering;

/// Enable `Rc<T>` equality.
pub assume_specification<T: MetaSized + PartialEq, A: Allocator>[ <Rc<T, A> as PartialEq>::eq ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;

/// Enable `Rc<T>` inequality.
pub assume_specification<T: MetaSized + PartialEq, A: Allocator>[ <Rc<T, A> as PartialEq>::ne ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;

/// Enable `Rc<T>` partial comparison.
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Rc<T, A> as PartialOrd>::partial_cmp ](a: &Rc<T, A>, b: &Rc<T, A>) -> Option<Ordering>;

/// Enable `Rc<T>` less-than comparison.
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Rc<T, A> as PartialOrd>::lt ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;

/// Enable `Rc<T>` less-than-or-equal comparison.
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Rc<T, A> as PartialOrd>::le ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;

/// Enable `Rc<T>` greater-than comparison.
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Rc<T, A> as PartialOrd>::gt ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;

/// Enable `Rc<T>` greater-than-or-equal comparison.
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Rc<T, A> as PartialOrd>::ge ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;

/// Enable `Rc<T>` total comparison.
pub assume_specification<T: MetaSized + Ord, A: Allocator>[ <Rc<T, A> as Ord>::cmp ](a: &Rc<T, A>, b: &Rc<T, A>) -> Ordering;

/// Proof that links `Box<T>` `PartialEq` obedience to `T`.
pub broadcast axiom fn lemma_box_obeys_eq_spec<T: PartialEq>()
    ensures
        #[trigger] <Box<T> as PartialEqSpec>::obeys_eq_spec() == <T as PartialEqSpec>::obeys_eq_spec();

/// Proof that links `Box<T>` equality with the pointee equality.
pub broadcast axiom fn lemma_box_eq_spec<T: PartialEq>(a: &Box<T>, b: &Box<T>)
    ensures
        #![trigger <Box<T> as PartialEqSpec>::eq_spec(a, b)]
        <Box<T> as PartialEqSpec>::eq_spec(a, b) == <T as PartialEqSpec>::eq_spec(&**a, &**b);

/// Proof that links `Box<T>` `PartialOrd` obedience to `T`.
pub broadcast axiom fn lemma_box_obeys_partial_cmp_spec<T: PartialOrd>()
    ensures
        #[trigger] <Box<T> as PartialOrdSpec>::obeys_partial_cmp_spec() == <T as PartialOrdSpec>::obeys_partial_cmp_spec();

/// Proof that links `Box<T>` partial comparison with the pointee comparison.
pub broadcast axiom fn lemma_box_partial_cmp_spec<T: PartialOrd>(a: &Box<T>, b: &Box<T>)
    ensures
        #![trigger <Box<T> as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <Box<T> as PartialOrdSpec>::partial_cmp_spec(a, b) == <T as PartialOrdSpec>::partial_cmp_spec(&**a, &**b);

/// Proof that links `Box<T>` `Ord` obedience to `T`.
pub broadcast axiom fn lemma_box_obeys_cmp_spec<T: Ord>()
    ensures
        #[trigger] <Box<T> as OrdSpec>::obeys_cmp_spec() == <T as OrdSpec>::obeys_cmp_spec();

/// Proof that links `Box<T>` total comparison with the pointee comparison.
pub broadcast axiom fn lemma_box_cmp_spec<T: Ord>(a: &Box<T>, b: &Box<T>)
    ensures
        #![trigger <Box<T> as OrdSpec>::cmp_spec(a, b)]
        <Box<T> as OrdSpec>::cmp_spec(a, b) == <T as OrdSpec>::cmp_spec(&**a, &**b);

/// Proof that links `Rc<T>` `PartialEq` obedience to `T`.
pub broadcast axiom fn lemma_rc_obeys_eq_spec<T: PartialEq>()
    ensures
        #[trigger] <Rc<T> as PartialEqSpec>::obeys_eq_spec() == <T as PartialEqSpec>::obeys_eq_spec();

/// Proof that links `Rc<T>` equality with the pointee equality.
pub broadcast axiom fn lemma_rc_eq_spec<T: PartialEq>(a: &Rc<T>, b: &Rc<T>)
    ensures
        #![trigger <Rc<T> as PartialEqSpec>::eq_spec(a, b)]
        <Rc<T> as PartialEqSpec>::eq_spec(a, b) == <T as PartialEqSpec>::eq_spec(&**a, &**b);

/// Proof that links `Rc<T>` `PartialOrd` obedience to `T`.
pub broadcast axiom fn lemma_rc_obeys_partial_cmp_spec<T: PartialOrd>()
    ensures
        #[trigger] <Rc<T> as PartialOrdSpec>::obeys_partial_cmp_spec() == <T as PartialOrdSpec>::obeys_partial_cmp_spec();

/// Proof that links `Rc<T>` partial comparison with the pointee comparison.
pub broadcast axiom fn lemma_rc_partial_cmp_spec<T: PartialOrd>(a: &Rc<T>, b: &Rc<T>)
    ensures
        #![trigger <Rc<T> as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <Rc<T> as PartialOrdSpec>::partial_cmp_spec(a, b) == <T as PartialOrdSpec>::partial_cmp_spec(&**a, &**b);

/// Proof that links `Rc<T>` `Ord` obedience to `T`.
pub broadcast axiom fn lemma_rc_obeys_cmp_spec<T: Ord>()
    ensures
        #[trigger] <Rc<T> as OrdSpec>::obeys_cmp_spec() == <T as OrdSpec>::obeys_cmp_spec();

/// Proof that links `Rc<T>` total comparison with the pointee comparison.
pub broadcast axiom fn lemma_rc_cmp_spec<T: Ord>(a: &Rc<T>, b: &Rc<T>)
    ensures
        #![trigger <Rc<T> as OrdSpec>::cmp_spec(a, b)]
        <Rc<T> as OrdSpec>::cmp_spec(a, b) == <T as OrdSpec>::cmp_spec(&**a, &**b);

impl<T: PartialEqVerified> PartialEqVerified for Box<T> {
    proof fn lemma_obeys_eq_spec() {
        T::lemma_obeys_eq_spec();
        broadcast use group_pointer_ordering;
    }

    proof fn lemma_eq_symmetric(a: &Self, b: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_eq_symmetric(&**a, &**b);
    }

    proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_eq_transitive(&**a, &**b, &**c);
    }
}

impl<T: EqVerified> EqVerified for Box<T> {
    proof fn lemma_eq_reflexive(a: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_eq_reflexive(&**a);
    }
}

impl<T: PartialOrdVerified> PartialOrdVerified for Box<T> {
    proof fn lemma_obeys_partial_cmp_spec() {
        T::lemma_obeys_partial_cmp_spec();
        broadcast use group_pointer_ordering;
    }

    proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_cmp_eq_consistent(&**a, &**b);
        if a.partial_cmp_spec(b) == Some(Ordering::Equal) {
            assert forall|c: &Self| a.partial_cmp_spec(c) == b.partial_cmp_spec(c) by {
                broadcast use group_pointer_ordering;
                T::lemma_cmp_eq_consistent(&**a, &**b);
            }
        }
    }

    proof fn lemma_cmp_dual(a: &Self, b: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_cmp_dual(&**a, &**b);
    }

    proof fn lemma_cmp_transitive(a: &Self, b: &Self, c: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_cmp_transitive(&**a, &**b, &**c);
    }
}

impl<T: OrdVerified> OrdVerified for Box<T> {
    proof fn lemma_obeys_cmp_spec() {
        T::lemma_obeys_cmp_spec();
        broadcast use group_pointer_ordering;
    }

    proof fn lemma_cmp_consistent(a: &Self, b: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_cmp_consistent(&**a, &**b);
    }
}

impl<T: PartialEqVerified> PartialEqVerified for Rc<T> {
    proof fn lemma_obeys_eq_spec() {
        T::lemma_obeys_eq_spec();
        broadcast use group_pointer_ordering;
    }

    proof fn lemma_eq_symmetric(a: &Self, b: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_eq_symmetric(&**a, &**b);
    }

    proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_eq_transitive(&**a, &**b, &**c);
    }
}

impl<T: EqVerified> EqVerified for Rc<T> {
    proof fn lemma_eq_reflexive(a: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_eq_reflexive(&**a);
    }
}

impl<T: PartialOrdVerified> PartialOrdVerified for Rc<T> {
    proof fn lemma_obeys_partial_cmp_spec() {
        T::lemma_obeys_partial_cmp_spec();
        broadcast use group_pointer_ordering;
    }

    proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_cmp_eq_consistent(&**a, &**b);
        if a.partial_cmp_spec(b) == Some(Ordering::Equal) {
            assert forall|c: &Self| a.partial_cmp_spec(c) == b.partial_cmp_spec(c) by {
                broadcast use group_pointer_ordering;
                T::lemma_cmp_eq_consistent(&**a, &**b);
            }
        }
    }

    proof fn lemma_cmp_dual(a: &Self, b: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_cmp_dual(&**a, &**b);
    }

    proof fn lemma_cmp_transitive(a: &Self, b: &Self, c: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_cmp_transitive(&**a, &**b, &**c);
    }
}

impl<T: OrdVerified> OrdVerified for Rc<T> {
    proof fn lemma_obeys_cmp_spec() {
        T::lemma_obeys_cmp_spec();
        broadcast use group_pointer_ordering;
    }

    proof fn lemma_cmp_consistent(a: &Self, b: &Self) {
        broadcast use group_pointer_ordering;
        T::lemma_cmp_consistent(&**a, &**b);
    }
}

} // verus!
