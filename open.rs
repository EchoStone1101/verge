//! Open version for closed specifications in `vstd`, useful for constant evaluation.
//!
//! For example, the following does not pass verification because `Set::new` and `Set::fold` are closed:
//! ```rust
//! assert(set!{1int}.fold(1, |prod: int, n: int| prod * n) == 1) by (compute);
//! ```
//! while the following does, because `Seq::new` and `Seq::fold_left` are open:
//! ```rust
//! assert(seq![1int].fold_left(1, |prod: int, n: int| prod * n) == 1) by (compute);
//! ```
//! 
//! This module provides equivalent `open spec` for `closed spec` in `vstd`, as well as
//! the `open!` macro which syntactically replaces the closed version with the open version, 
//! so that the following also works:
//! ```rust
//! assert(open!(set!{1int}.fold(1, |prod: int, n: int| prod * n) == 1)) by (compute);
//! ```

#[allow(unused_imports)]
use vstd::prelude::*;

pub mod bytes;
pub mod seq;
pub mod set; 

verus! {

pub proof fn placeholder() {}

// TODO: open!

} // verus!