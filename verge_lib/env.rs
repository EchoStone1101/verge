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
    Args<> as VergeArgs<> :: Item = String;

    args_iter via args () -> (iter: VergeArgs)
    ensures {
        Env::args() =~~= iter.seq().map(|i: int, arg: String| arg@)
    };
);

/// Specifies the iterator `VergeArgs` as a double-ended iterator.
impl_double_ended_iterator!(
    Args as VergeArgs [] :: Item = String
);

/// Specifies the iterator `VergeVars` which wraps `Vars`, 
/// contructed via `vars_iter()`.
impl_iterator!(
    Vars<> as VergeVars<> :: Item = (String, String)
    ;

    vars_iter via vars
    () -> (iter: VergeVars)
    ensures {
            Env::vars().kv_pairs().to_seq() =~~= iter.seq().map(|i: int, var: (String, String)| (var.0@, var.1@))
        }
    ;
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