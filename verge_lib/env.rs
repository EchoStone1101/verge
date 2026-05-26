//! Specifications for `std::env`, the program's environment.

#![allow(unused)]
use vstd::prelude::*;
use vstd::std_specs::iter::*;
use crate::iter::*;

use std::env::{args, vars};
pub use std::env::{Args, Vars};

verus! {

/// Specification for `env::Args` and `env::Vars`.
pub struct Env;

impl Env {
    /// This function encodes program arguments as a sequence of strings.
    pub uninterp spec fn args() -> Seq<Seq<char>>;

    /// This function encodes environment variables as a map from strings to strings.
    pub uninterp spec fn vars() -> Map<Seq<char>, Seq<char>>;
}

/// Specifies the iterator `VergeArgs` which wraps `Args`, 
/// contructed via `args_iter()`.
impl_iterator!(
    Args[] as VergeArgs[] :: Item = String
    [ args_iter via args ] () -> |seq| {
        Env::args() =~~= seq.map(|i: int, arg: String| arg@)
    }
);
impl core::iter::Iterator for VergeArgs {
    type Item = <Self as VergeIteratorSpec>::Item;
    #[verifier::external_body]
    fn next(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
        { self.0.next() }
}

/// Specifies the iterator `VergeArgs` as a double-ended iterator.
impl_double_ended_iterator!(
    Args as VergeArgs [] :: Item = String
);
impl core::iter::DoubleEndedIterator for VergeArgs {
    #[verifier::external_body]
    fn next_back(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
        { self.0.next_back() }
}

/// Specifies the iterator `VergeVars` which wraps `Vars`, 
/// contructed via `vars_iter()`.
impl_iterator!(
    Vars[] as VergeVars[] :: Item = (String, String)
    [ vars_iter via vars ] () -> |seq| {
        Env::vars().kv_pairs().to_seq() =~~= seq.map(|i: int, var: (String, String)| (var.0@, var.1@))
    }
);
impl core::iter::Iterator for VergeVars {
    type Item = <Self as VergeIteratorSpec>::Item;
    #[verifier::external_body]
    fn next(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
        { self.0.next() }
}

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