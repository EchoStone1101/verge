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
    spec fn skip_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<Self::A>;
    spec fn rskip_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<Self::A>;
    spec fn take_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<Self::A>;
    spec fn rtake_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<Self::A>;
    spec fn count_while(self, pred: spec_fn(Self::A) -> bool) -> nat;
    spec fn rcount_while(self, pred: spec_fn(Self::A) -> bool) -> nat;
    spec fn deep_view(self) -> Seq<<Self::A as View>::V>
        where Self::A: View;
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

    /// Returns the calling sequence with initial elements removed until `pred(element)` is false.
    open spec fn skip_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<A> 
        decreases self.len(),
    {
        if self.len() == 0 || !pred(self.first()) {
            self
        } else {
            self.drop_first().skip_while(pred)
        }
    }

    /// Returns the calling sequence with trailing elements removed until `pred(element)` is false.
    open spec fn rskip_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<A> 
        decreases self.len(),
    {
        if self.len() == 0 || !pred(self.last()) {
            self
        } else {
            self.drop_last().rskip_while(pred)
        }
    }

    /// Returns the initial elements of the calling sequence until `pred(element)` is false.
    open spec fn take_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<A> 
        { self.take(self.len() - self.skip_while(pred).len()) }

    /// Returns the trailing elements of the calling sequence until `pred(element)` is false.
    open spec fn rtake_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<A> 
        { self.skip(self.len() - self.rskip_while(pred).len()) }

    /// Counts the number of initial elements of the calling sequence until `pred(element)` is false.
    open spec fn count_while(self, pred: spec_fn(Self::A) -> bool) -> nat 
        { self.take_while(pred).len() }
    
    /// Counts the number of trailing elements of the calling sequence until `pred(element)` is false.
    open spec fn rcount_while(self, pred: spec_fn(Self::A) -> bool) -> nat 
        { self.rtake_while(pred).len() }
    
    /// Returns the sequence with `view` called on each elements.
    open spec fn deep_view(self) -> Seq<<Self::A as View>::V> 
    where Self::A: View,
        { Seq::new(self.len(), |i: int| self[i]@ ) }
}


} // verus!