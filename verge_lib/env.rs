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

    /// Environment variables as a map from strings to strings.
    pub uninterp spec fn vars() -> Map<Seq<char>, Seq<char>>;
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
        Env::vars().kv_pairs().to_seq() =~~= seq.map(|i: int, var: (String, String)| (var.0@, var.1@))
    }
);

/// Enables `std::env::var`.
#[verifier::external_body]
pub fn var(key: &str) -> (ret: Option<String>)
    ensures
        ret.deep_view() == Env::vars().get(key@),
{
    std::env::var_os(key)
        .map(|s| unsafe { String::from_utf8_unchecked(s.into_encoded_bytes()) })
}

} // verus!