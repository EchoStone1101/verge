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
//! To be exact, Verge takes the following approach:
//! 
//! ## Specifying types, functions and methods
//! By default, Verge uses `#[verifier::external_type_specification]` to introduce types, 
//! and `assume_specification` to introduce both function calls and associated methods.
//! However, in certain cases it makes more sense to rename a function or alter its
//! signature for Verus. In this case, Verge adds a new function with `#[verifier::external_body]`, 
//! whose body contains minimal code that delegates the call to the actual function.
//! For associated methods, this is done by adding a helper trait that declares the 
//! altered method signature, then implementing the trait using `#[verifier::external_body]`.
//!
//! We give some examples that demonstrate the need for altering signature.
//! For one, `str::from_utf8_unchecked` is `unsafe` in `std` because it relies on 
//! a pre-condition that cannot be checked by the compiler, whereas Verus is fully 
//! capable of proving soundness given proper conditions. Thus, the API is renamed
//! to `str::from_utf8_verified` in Verge and is no longer `unsafe`.
//! For another, `String::find` takes a `pat: P where P: Pattern` argument in `std`, 
//! but specifying this API form adds unnecessary burden to the prover. Verge changes `String::find` 
//! to accept `pat: &str` - the most common case. 
//!
//! ## Specifying traits
//! Traits are introduced with `#[verifier::external_trait_specification]`. 
//! To add specifications, Verge then adds a new trait that contains only `spec` and
//! `proof` methods, then implement it as needed. For example, to specifiy `std::io::Read`, 
//! Verge adds the `ReadSpec` trait which crucially contains a `bytes()` spec function representing 
//! the byte sequence left in any reader instance. 
//!
//! When it comes to actually introducing trait methods, there are also two ways.
//! However, neither is the default here, because there are trade-offs for both of them.
//!
//! The first way is using `assume_specification` on specific implementations of
//! a trait method. The trade-off: calls to a trait method are resolved to 
//! the original trait, but the specification is not associated with the trait method, 
//! only to the implemetation. 
//! This is useful for traits like `core::iter::Iterator`, which is depended on by
//! core language constructs like the `for` loop - it is crucial that Verge introduces 
//! exactly the `core::iter::Iterator::next()` method. However, the downside is that `Iterator::next` 
//! remains unspecified (only implementations like `<Vec<T> as Iterator>::next` are), 
//! so specifying generic functions based on the `Iterator` trait is not possible.
//!
//! The second way is adding a new trait with matching methods, then have the implementations 
//! delegate the actual calls. This works the exact opposite way: the specification can now 
//! exist at the trait method level, but the trait method is no longer the original one. 
//! This is the case for `verge::io` traits (e.g., `Read` and `Write`).
//! It is also the only viable option when the signature needs to change.
//! 
//! In both cases, Verge uses macros to minimize boilerplace code. 
//! Note again that the specification is not associated with the original trait method either way;
//! `#[verifier::external_trait_specification]` requires trait bounds to be identical, 
//! so it is generally impossible to write useful specification given only the external traits 
//! (e.g., Verge cannot specify `std::io::Read::read`, because the trait knows nothing about `ReadSpec` 
//! at the trait level). 

#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(rustdoc::invalid_rust_codeblocks)]
#![feature(allocator_api)]

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