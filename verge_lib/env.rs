//! Specifications for `std::env`, the program's environment.

use vstd::prelude::*;
use crate::iter::{IteratorView, impl_iterator_default};

pub use std::env::{Args, Vars};

verus! {

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExArgs(Args);

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExVars(Vars);

/// Specification for `env::Args` and `env::Vars`.
pub struct Env;

impl Env {
    /// Program arguments as a sequence of strings.
    pub uninterp spec fn args() -> Seq<Seq<char>>;

    /// Environment variables as a sequence of string pairs.
    pub uninterp spec fn vars() -> Seq<(Seq<char>, Seq<char>)>;
}

/// Enables `Args` as an iterator.
impl_iterator_default!(
    Args [] where Item = String
    [ std::env::args ] () -> |seq| {
        Env::args() =~~= seq.map(|i: int, arg: String| arg@)
    }
);

/// Enables `Vars` as an iterator.
impl_iterator_default!(
    Vars [] where Item = (String, String)
    [ std::env::vars ] () -> |seq| {
        Env::vars() =~~= seq.map(|i: int, var: (String, String)| (var.0@, var.1@))
    }
);

} // verus!