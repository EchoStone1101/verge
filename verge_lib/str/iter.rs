//! Iterator methods and types for strings.

#![allow(unused_imports)]
use super::*;

use std::str::{
    CharIndices,
};

// TODO: an iter module; provided methods in the Iterator trait

verus! {

// TODO: all of this can be made into an impl macro

/// This trait adds the `view()` method for any iterator.
pub trait IteratorView {
    type Item;

    spec fn view(&self) -> (int, Seq<Self::Item>);
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCharIndices<'a>(CharIndices<'a>);

impl<'a> IteratorView for CharIndices<'a> {
    type Item = (usize, char);

    uninterp spec fn view(&self) -> (int, Seq<Self::Item>);
}

/// Enable `str::char_indices`.
pub assume_specification [ str::char_indices ] (s: &str) -> (ret: CharIndices<'_>)
    ensures
        ({
            let (index, seq) = ret@;
            &&& index == 0
            &&& seq == s@.map(|i: int, c: char| (i as usize, c))
        }),
    no_unwind
;

pub assume_specification<'a>[ CharIndices::<'a>::next ]
    (char_indices: &mut CharIndices<'a>) -> (r: Option<(usize, char)>)
    ensures
        ({
            let (old_index, old_seq) = old(char_indices)@;
            match r {
                None => {
                    &&& char_indices@ == old(char_indices)@
                    &&& old_index >= old_seq.len()
                },
                Some(k) => {
                    let (new_index, new_seq) = char_indices@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& k == old_seq[old_index]
                },
            }
        }),
;


} // verus!