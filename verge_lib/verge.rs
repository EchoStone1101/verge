//! The Verge library for [Verus](https://github.com/verus-lang/verus).
//! Contains extendsions of the `vstd` standard library in various domians.

#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(rustdoc::invalid_rust_codeblocks)]

use vstd::prelude::*;

verus! {

pub mod io;
pub mod open;
pub mod mem;
// pub mod mut_ref;
pub mod nt;
pub mod set;
pub mod ascii_string;

}

#[cfg(not(verus_verify_core))]
#[doc(hidden)]
pub use crate as verge;