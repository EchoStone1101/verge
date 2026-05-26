//! Extended sequence specifications and lemmas for `Seq` in vstd.

use vstd::prelude::*;
use vstd::seq::*;

verus! {

/// Additional `spec` functions for `Seq`.
pub trait SeqAdditionalSpec {
    type A; // element type
    spec fn is_infix_of(self, other: Self) -> bool;
    spec fn is_subrange_of(self, other: Self) -> bool;
    spec fn count(self, pred: spec_fn(Self::A) -> bool) -> nat;
}

// TODO: broadcast lemmas for these

impl<A> SeqAdditionalSpec for Seq<A> {
    type A = A;

    /// Is true if the calling sequence is an infix of the given sequence `other`.
    open spec fn is_infix_of(self, other: Self) -> bool {
        &&& self.len() <= other.len() 
        &&& exists|i: int| 0 < i < other.len() - self.len()
            && self =~= #[trigger] other.subrange(i, i + self.len())
    }

    /// Is true if the calling sequence is a prefix, infix, or suffic of the 
    /// given sequence `other`.
    open spec fn is_subrange_of(self, other: Self) -> bool {
        ||| self.is_prefix_of(other)
        ||| self.is_suffix_of(other)
        ||| self.is_infix_of(other)
    }

    /// Returns the number of elements such that `pred(element)` is true.
    open spec fn count(self, pred: spec_fn(A) -> bool) -> nat
        { self.filter(pred).len() }
}

} // verus!