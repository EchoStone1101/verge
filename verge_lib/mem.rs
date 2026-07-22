//! Specifications and lemmas for memory-related operations.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::view::View;

verus! {

/// Enable `core::mem::forget`.
pub assume_specification<T> [core::mem::forget::<T>] (t: T)
    opens_invariants none
    no_unwind;

/// Enable `core::mem::replace`.
pub assume_specification<T> [core::mem::replace::<T>] (dest: &mut T, src: T) -> (ret: T)
    ensures
        *final(dest) == src,
        ret == *old(dest),
    opens_invariants none
    no_unwind;

} // verus!
