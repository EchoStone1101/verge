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
        *dest == src,
        ret == *old(dest),
    opens_invariants none
    no_unwind;

/// Enable `core::slice::copy_from_slice`, which is essentially `memcpy` in C.
pub assume_specification<T: Copy> [ <[T]>::copy_from_slice ] (dest: &mut [T], src: &[T])
    requires
        old(dest).len() == src.len(),
    ensures
        dest@ =~= src@,
    no_unwind;

} // verus!