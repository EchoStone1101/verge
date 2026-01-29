//! The Verge library for [Verus](https://github.com/verus-lang/verus).
//! Contains extendsions of the `vstd` standard library in various domians.

#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(rustdoc::invalid_rust_codeblocks)]

use vstd::prelude::*;
pub mod cart;
pub mod fs;
pub mod open;

verus! {}

#[cfg(not(verus_verify_core))]
#[doc(hidden)]
pub use crate as verge;