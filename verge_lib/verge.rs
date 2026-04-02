//! The Verge library for [Verus](https://github.com/verus-lang/verus).
//! Contains extensions of the `vstd` standard library in various domains.
//!
//! # Unix-Only Support
//! Because of the semantic difference in APIs across various targets, supporting multiple 
//! targets burdens specification. Verge is currently a Unix-only crate.
//!
//! # `std` Specification
//! A core part of Verge is exposing much more of the Rust standard library API 
//! to Verus than supported in `vstd`. This process is deliberately kept minimal:
//! Verge adds only *specification*, not *implementation*. 
//! 
//! # Tests as Examples
//! Verge specifications come with unit tests (`mod tests`), in the form of private `exec fn`s
//! that use the Verge specs to specify and prove properties (automatically checked by Verus).
//! These tests also double as examples, showing how the Verge APIs can be used.

#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(unused_doc_comments)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(rustdoc::invalid_rust_codeblocks)]
#![feature(allocator_api)]
#![feature(sized_hierarchy)]

#[cfg(not(unix))]
compile_error!("Verge is a Unix-only library.");

use vstd::prelude::*;
use core::alloc::Allocator;
use std::rc::Rc;

#[macro_export]
macro_rules! impl_maybe_generic {
    // No generics
    ([] $($rest:tt)+) => {
        verus! { // needed for Verus syntax
        impl $($rest)+
        }
    };
    // With generics
    ([$($gen:tt)+] $($rest:tt)+) => {
        verus! { 
        impl<$($gen)+> $($rest)+
        }
    };
}

verus! {

pub mod env;
pub mod error;
pub mod fs;
pub mod io;
pub mod iter;
pub mod mem;
pub mod nt;
pub mod set;
pub mod str;

/// Enable the `AsRef` trait.
#[verifier::external_trait_specification]
pub trait ExAsRef<T: std::marker::PointeeSized>: std::marker::PointeeSized {
    type ExternalTraitSpecificationFor: std::convert::AsRef<T>;
}

/// Enable the `AsMut` trait.
#[verifier::external_trait_specification]
pub trait ExAsMut<T: std::marker::PointeeSized>: std::marker::PointeeSized {
    type ExternalTraitSpecificationFor: std::convert::AsMut<T>;
}

/// Used for a dummy one-term trigger.
pub uninterp spec fn dummy<A>(a: A) -> ();

/// Used for a dummy two-term trigger.
pub uninterp spec fn dummy2<A, B>(a: A, b: B) -> ();

/// Enables `Box::<T>::as_ref`.
pub uninterp spec fn box_as_ref<T: ?Sized, A: Allocator>(ptr: &Box<T, A>) -> &T;
#[verifier::when_used_as_spec(box_as_ref)]
pub assume_specification<T: ?Sized, A: Allocator>[ Box::<T, A>::as_ref ](this: &Box<T, A>) -> (ret: &T)
    ensures
        this == ret,
    no_unwind
;

/// Enables `Rc::<T>::as_ref`.
pub uninterp spec fn rc_as_ref<T: ?Sized, A: Allocator>(ptr: &Rc<T, A>) -> &T;
#[verifier::when_used_as_spec(rc_as_ref)]
pub assume_specification<T: ?Sized, A: Allocator>[ Rc::<T, A>::as_ref ](this: &Rc<T, A>) -> (ret: &T)
    ensures
        this == ret,
    no_unwind
;

}

#[cfg(not(verus_verify_core))]
#[doc(hidden)]
pub use crate as verge;