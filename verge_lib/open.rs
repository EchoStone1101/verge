//! Open version for closed specifications in `vstd`, useful for constant evaluation.
//!
//! For example, the following does not pass verification without calling proof functions, 
//! because `Set::fold` is closed:
//! ```rust
//! assert(set!{1int}.fold(1, |prod: int, n: int| prod * n) == 1) by (compute);
//! ```
//! while the following does, because `Seq::fold_left` is open:
//! ```rust
//! assert(seq![1int].fold_left(1, |prod: int, n: int| prod * n) == 1) by (compute);
//! ```
//! 
//! This module provides equivalent `open spec`s for `closed spec`s in `vstd`, so that 
//! the following also works:
//! ```rust
//! assert(set_literal!{1int}.fold(1, |prod: int, n: int| prod * n) == 1) 
//! by { reveal_with_fuel(Seq::<_>::fold_left, 5); }
//! ```

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub mod bytes;
pub mod seq;
pub mod set; 

} // verus!