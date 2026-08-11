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
//! Verge specifications come with integration tests in the `verge_tests` crate, in the form of
//! private `exec fn`s that use the public Verge APIs to specify and prove properties
//! (automatically checked by Verus). These tests also double as examples, showing how the Verge
//! APIs can be used from a downstream crate.

#![allow(incomplete_features)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(unused_doc_comments)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(private_bounds)]
#![allow(rustdoc::invalid_rust_codeblocks)]
#![feature(allocator_api)]
#![feature(sized_hierarchy)]
#![feature(pattern)]
#![feature(specialization)]
#![feature(slice_index_methods)]

#[cfg(not(unix))]
compile_error!("Verge is a Unix-only library.");

use vstd::prelude::*;
use vstd::std_specs::core::IndexSpec;

use core::alloc::Allocator;
use std::rc::Rc;

pub mod prelude;

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

/// Shared marker trait used to seal internal traits.
pub(crate) trait Sealed {}

pub mod clone;
pub mod cmp;
pub mod env;
pub mod error;
pub mod func;
pub mod fs;
// pub mod index;
pub mod io;
pub mod iter;
pub mod mem;
pub mod nt;
pub mod seq;
pub mod set;
pub mod str;

#[verifier::broadcast_use_by_default_when_this_crate_is_imported]
pub broadcast group group_verge_lemmas {
    cmp::group_ordering_eq, // for `verge_tests`
    str::group_str_axioms,
    seq::group_seq_additional_lemmas,
}

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

/// The `VergeView` trait adds the `view` method to a type that otherwise 
/// does not implement `vstd::View`. 
/// Semantically it is equivalent to implement `view` as part of the type's `impl` block, 
/// but `VergeView` has the advantage of working as a trait bound.
pub trait VergeView {
    type V;

    spec fn view(&self) -> Self::V;
}

}

#[cfg(not(verus_verify_core))]
#[doc(hidden)]
pub use crate as verge;
