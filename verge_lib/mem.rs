//! Specifications and lemmas for memory operations.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::view::View;
use vstd::raw_ptr::MemContents;
use vstd::slice::spec_slice_len;

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

/// Enable `core::slice::split_at`.
pub assume_specification<T> [ <[T]>::split_at ] (slice: &[T], mid: usize) -> (ret: (&[T], &[T]))
    requires
        0 <= mid <= slice.len(),
    ensures
        ret.0@ == slice@.subrange(0, mid as int),
        ret.1@ == slice@.subrange(mid as int, slice@.len() as int),
    no_unwind;

/// Enable `memchr::memchr`.
pub assume_specification [ memchr::memchr ] (needle: u8, haystack: &[u8]) -> (res: Option<usize>)
    ensures
        ({
            match res {
                Some(idx) => ({
                    &&& idx < spec_slice_len(haystack)
                    &&& forall |i: int| #![auto] 0 <= i < idx ==> haystack[i] != needle 
                    &&& haystack[idx as int] == needle
                }),
                None => forall |i: int| #![auto] 0 <= i < haystack@.len() ==> haystack[i] != needle,
            }
        }),
    no_unwind;

} // verus!