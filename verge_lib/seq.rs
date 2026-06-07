//! Extended sequence specifications and lemmas for `Seq` in vstd.

use vstd::prelude::*;
use vstd::seq::*;

verus! {

// Additional `spec` functions for `Seq`

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

impl<A> SeqAdditionalSpec for Seq<A> {
    type A = A;

    /// Is true if the calling sequence is an infix of the given sequence `other`.
    open spec fn is_infix_of(self, other: Self) -> bool {
        &&& self.len() < other.len() 
        &&& exists|i: int| 0 < i < other.len() - self.len()
            && self =~= #[trigger] other.subrange(i, i + self.len())
    }

    /// Is true if the calling sequence is a subrange of the given sequence `other`.
    open spec fn is_subrange_of(self, other: Self) -> bool {
        &&& self.len() <= other.len() 
        &&& exists|i: int| 0 <= i <= other.len() - self.len()
            && self =~= #[trigger] other.subrange(i, i + self.len())
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

// Related lemmas

/// Proof that if `s1` is an infix of `s`, then any subrange of `s1` is also an infix of `s`.
pub broadcast proof fn lemma_seq_is_infix_subrange<A>(s: Seq<A>, s1: Seq<A>, i: int, j: int)
    requires
        s1.is_infix_of(s),
        0 <= i <= j <= s1.len(),
    ensures
        #[trigger] s1.subrange(i, j).is_infix_of(s),
{
    let k = choose|k: int| 0 < k < s.len() - s1.len()
        && s1 =~= #[trigger] s.subrange(k, k + s1.len());
    assert(s1.subrange(i, j) =~= s.subrange(k + i, k + i + s1.subrange(i, j).len())) by {
        s.lemma_slice_of_slice(k, k + s1.len(), i, j);
    }
}

/// Proof that if `s1` is a subrange of `s`, then any subrange of `s1` is also a subrange of `s`.
pub broadcast proof fn lemma_seq_is_subrange_subrange<A>(s: Seq<A>, s1: Seq<A>, i: int, j: int) 
    requires
        s1.is_subrange_of(s),
        0 <= i <= j <= s1.len(),
    ensures
        #[trigger] s1.subrange(i, j).is_subrange_of(s),
{
    let k = choose|k: int| 0 <= k <= s.len() - s1.len()
        && s1 =~= #[trigger] s.subrange(k, k + s1.len()); 
    assert(s1.subrange(i, j) =~= s.subrange(k + i, k + i + s1.subrange(i, j).len())) by {
        s.lemma_slice_of_slice(k, k + s1.len(), i, j);
    }
}

/// Proof that if `s1` is a subrange of `s`, then `s1` is a prefix, suffix, or infix.
pub broadcast proof fn lemma_seq_is_subrange_alt<A>(s: Seq<A>, s1: Seq<A>)
    ensures
        #[trigger] s1.is_subrange_of(s) <==> {
            ||| s1.is_prefix_of(s)
            ||| s1.is_suffix_of(s)
            ||| s1.is_infix_of(s)
        },
{
    if s1.is_subrange_of(s) {
        let k = choose|i: int| 0 <= i <= s.len() - s1.len()
            && s1 =~= #[trigger] s.subrange(i, i + s1.len());
        if k == 0 {
            assert(s1.is_prefix_of(s));
        } else if k == s.len() - s1.len() {
            assert(s1.is_suffix_of(s));
        } else {
            assert(s1.is_infix_of(s));
        }
    }
    if s1.is_prefix_of(s) {
        assert(s1 =~= s.subrange(0, 0 + s1.len() as int));
    }
    if s1.is_suffix_of(s) {
        assert(s1 =~= s.subrange(s.len() - s1.len(), (s.len() - s1.len()) + s1.len()));
    }
}

/// Proof that `s.skip_while(pred)` is no longer than `s` itself.
pub broadcast proof fn lemma_seq_skip_while_len<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #[trigger] s.skip_while(pred).len() <= s.len(),
    decreases
        s.len(),
{
    if s.len() == 0 || !pred(s.first()) { /* base case */ }
    else {
        lemma_seq_skip_while_len(s.drop_first(), pred);
        assert(s.drop_first().len() < s.len());
    }
}

/// Proof that `s.skip_while(pred)` is a suffix of `s`.
pub broadcast proof fn lemma_seq_skip_while_is_suffix<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #[trigger] s.skip_while(pred).is_suffix_of(s),
    decreases
        s.len(),
{
    if s.len() == 0 || !pred(s.first()) { /* base case */ }
    else {
        lemma_seq_skip_while_is_suffix(s.drop_first(), pred);
        assert(s.drop_first().skip_while(pred).is_suffix_of(s));
    }
}

/// Proof that `pred` does not hold on the first element of `s.skip_while(pred)`, 
/// if there exists one.
pub broadcast proof fn lemma_seq_skip_while_pred<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        s.skip_while(pred).len() > 0 ==> #[trigger] pred(s.skip_while(pred).first()) == false,
    decreases
        s.len(),
{
    if s.len() == 0 || !pred(s.first()) { /* base case */ }
    else {
        lemma_seq_skip_while_pred(s.drop_first(), pred);
    }
}

// take_while; take_while + skip_while
    

// xxx_while:
//      prefix/suffix relation
//      length relation
//      pred related stuff




} // verus!