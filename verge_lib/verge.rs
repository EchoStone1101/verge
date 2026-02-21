//! The Verge library for [Verus](https://github.com/verus-lang/verus).
//! Contains extensions of the `vstd` standard library in various domains.
//!
//! # `std` Specification
//! A core part of Verge is exposing much more of the Rust standard library API 
//! to Verus than supported in `vstd`. This process is deliberately kept minimal:
//! Verge adds only *specification*, not *implementation*. 
//! To be exact, we take the following approach:
//! 
//! ## Specifying types, functions and methods
//! By default, we use `#[verifier::external_type_specification]` to introduce types, 
//! and `assume_specification` to introduce both function calls and associated methods.
//! However, in certain cases it makes more sense to rename a function or alter its
//! signature for Verus. In this case, we add a new function with `#[verifier::external_body]`, 
//! whose body contains only one line that delegates the call to the actual function.
//! For associated methods, this is done by adding a helper trait that declares the 
//! altered method signature, then implementing the trait using `#[verifier::external_body]`.
//!
//! We give some examples that demonstrate the need for altering signature.
//! For one, `str::from_utf8_unchecked` is `unsafe` in `std` because it relies on 
//! a precondition that cannot be checked by the compiler, whereas Verus is fully 
//! capable of proving soundness given proper specifications. Thus, it is renamed
//! to `str::from_utf8_verified` in Verge and is no longer `unsafe`.
//! For another, `String::find` takes a `pat: P where P: Pattern` argument in `std`, 
//! but specifying this API form adds unnecessary burden to the prover. In Verge, 
//! we change `String::find` to accept `pat: &str` - the most common case. 
//!
//! ## Specifying traits
//! Traits are introduced with `#[verifier::external_trait_specification]`. 
//! To add specifications, we then add a new trait that contains only `spec` and
//! `proof` methods, then implement it as needed. For example, to specifiy `std::io::Read`, 
//! we add the `ReadSpec` trait which crucially contains a `bytes()` spec function representing 
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
//! core language constructs like the `for` loop - it is crucial that we introduce to Verus 
//! exactly `core::iter::Iterator::next()`. However, the downside is that `Iterator::next` 
//! remains unspecified (only implementations like `<Vec<T> as Iterator>::next` are), 
//! so specifying generic functions based on the `Iterator` trait is not possible.
//!
//! The second way is adding a new trait with matching methods, then have the implementations 
//! delegate the actual calls. This works the exact opposite way: the specification can now 
//! exist at the trait method level, but the trait method is no longer the original one. 
//! This is also the only viable option when the signature needs to change.
//! 
//! In both cases, Verge makes use of macros to minimize boilerplace code. 
//! Note again that the specification is not associated with the original trait method either way;
//! `#[verifier::external_trait_specification]` requires trait bounds to be identical, 
//! so it is generally impossible to write useful specification given only the external traits 
//! (e.g., `std::io::Read` knows nothing about `ReadSpec` at the trait level). 

#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(rustdoc::invalid_rust_codeblocks)]

use vstd::prelude::*;

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

pub mod iter;
pub mod io;
pub mod mem;
pub mod nt;
// pub mod open;
pub mod range;
pub mod set;
pub mod str;

}

#[cfg(not(verus_verify_core))]
#[doc(hidden)]
pub use crate as verge;