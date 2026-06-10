//! Extended sequence specifications and lemmas for `Seq` in vstd.

use vstd::prelude::*;
use vstd::seq::*;
use vstd::{calc, assert_by_contradiction};

use crate::dummy;

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
        { self.skip(self.rskip_while(pred).len() as int) }

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

// --- Related lemmas ---
pub broadcast group group_seq_additional_lemmas {
    lemma_seq_is_infix_subrange,
    lemma_seq_is_subrange_subrange,
    lemma_seq_is_subrange_alt,
    lemma_seq_concat_while,
    lemma_seq_skip_while_ensures,
    lemma_seq_take_while_ensures,
    lemma_seq_skip_skip_while,
    lemma_seq_skip_take_while,
    lemma_seq_take_skip_while,
    lemma_seq_take_take_while,
    lemma_seq_rconcat_while,
    lemma_seq_rskip_while_ensures,
    lemma_seq_rtake_while_ensures,
    lemma_seq_take_rskip_while,
    lemma_seq_take_rtake_while,
    lemma_seq_skip_rskip_while,
    lemma_seq_skip_rtake_while,
    lemma_seq_rskip_while_reverse,
    lemma_seq_rtake_while_reverse,
    lemma_seq_count_while_upper_bound,
    lemma_seq_count_while_lower_bound,
    lemma_seq_rcount_while_upper_bound,
    lemma_seq_rcount_while_lower_bound,
}

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

/// Proof that `s.take_while(pred)` and `s.skip_while(pred)` add back to `s`.
pub broadcast proof fn lemma_seq_concat_while<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #[trigger] (s.take_while(pred) + s.skip_while(pred)) == s,
{
    lemma_seq_take_while_is_prefix(s, pred);
    lemma_seq_skip_while_is_suffix(s, pred);
}

/// Proof of `s.skip_while(pred)`'s properties.
pub broadcast proof fn lemma_seq_skip_while_ensures<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #![trigger s.skip_while(pred)] 
        s.skip_while(pred).is_suffix_of(s),
        s.skip_while(pred).len() > 0 ==> !pred(s.skip_while(pred).first()),
        forall|i: int| 0 <= i < s.len() - s.skip_while(pred).len() 
            ==> #[trigger] pred(s[i]),
{
    lemma_seq_skip_while_is_suffix(s, pred);
    lemma_seq_skip_while_pred(s, pred);
    lemma_seq_concat_while(s, pred);
    assert forall|i: int| 0 <= i < s.len() - s.skip_while(pred).len() 
    implies #[trigger] pred(s[i])
    by {
        lemma_seq_take_while_pred(s, pred, i);
        assert(s.take_while(pred)[i] == s[i]);
    }
}

/// Proof of `s.take_while(pred)`'s properties.
pub broadcast proof fn lemma_seq_take_while_ensures<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #![trigger s.take_while(pred)] 
        s.take_while(pred).is_prefix_of(s),
        s.take_while(pred).len() < s.len() ==> !pred(s[s.take_while(pred).len() as int]),
        forall|i: int| 0 <= i < s.take_while(pred).len() ==> #[trigger] pred(s.take_while(pred)[i]),
{
    lemma_seq_concat_while(s, pred);
    lemma_seq_skip_while_ensures(s, pred);
}

/// Proof of an alternative way to define `skip_while`.
pub proof fn lemma_seq_skip_while_defines<A>(s: Seq<A>, pred: spec_fn(A) -> bool, s1: Seq<A>)
    requires
        s1.is_suffix_of(s),
        s1.len() > 0 ==> !pred(s1.first()),
        forall|i: int| 0 <= i < s.len() - s1.len() ==> #[trigger] pred(s[i]),
    ensures
        s1 == s.skip_while(pred),
{
    lemma_seq_concat_while(s, pred);
    lemma_seq_count_while_lower_bound(s, pred, s.len() - s1.len());
    if s1.len() > 0 {
        lemma_seq_count_while_upper_bound(s, pred, s.len() - s1.len());
        assert(s1.first() == s[s.len() - s1.len()]);
    }
    lemma_seq_skip_while_is_suffix(s, pred);
}

/// Proof of an alternative way to define `take_while`.
pub proof fn lemma_seq_take_while_defines<A>(s: Seq<A>, pred: spec_fn(A) -> bool, s1: Seq<A>)
    requires
        s1.is_prefix_of(s),
        s1.len() < s.len() ==> !pred(s[s1.len() as int]),
        forall|i: int| 0 <= i < s1.len() ==> #[trigger] pred(s1[i]),
    ensures
        s1 == s.take_while(pred),
{
    lemma_seq_concat_while(s, pred);
    assert forall|i: int| 0 <= i < s1.len()
    implies #[trigger] s[i] == s1[i] by {}
    lemma_seq_skip_while_defines(s, pred, s.skip(s1.len() as int));
}

/// Proof that `s.skip(n).skip_while(pred) == s.skip_while(pred)` if `0 <= n <= s.take_while(pred).len()`.
pub broadcast proof fn lemma_seq_skip_skip_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.take_while(pred).len(),
    ensures 
        #[trigger] s.skip(n).skip_while(pred) == s.skip_while(pred),
{
    lemma_seq_take_while_ensures(s, pred);
    lemma_seq_skip_while_ensures(s.skip(n), pred);
    lemma_seq_take_while_ensures(s.skip(n), pred);
    assert(s.skip(n).skip_while(pred).is_suffix_of(s)) by {
        s.lemma_slice_of_slice(
            n, s.len() as int, 
            s.skip(n).len() - s.skip(n).skip_while(pred).len(), s.skip(n).len() as int,
        );
    }
    assert(s == s.take(n) + s.skip(n).take_while(pred) + s.skip(n).skip_while(pred)) by {
        assert(s == s.take(n) + s.skip(n));
        lemma_seq_concat_while(s.skip(n), pred);
    }
    lemma_seq_skip_while_defines(s, pred, s.skip(n).skip_while(pred));
}

/// Proof that `s.skip(n).take_while(pred) == s.take_while(pred).skip(n)` 
/// if `0 <= n <= s.take_while(pred).len()`.
pub broadcast proof fn lemma_seq_skip_take_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.take_while(pred).len(),
    ensures 
        #[trigger] s.skip(n).take_while(pred) == s.take_while(pred).skip(n),
{
    lemma_seq_take_while_ensures(s, pred);
    assert(s == s.take(n) + s.skip(n).take_while(pred) + s.skip(n).skip_while(pred)) by {
        assert(s == s.take(n) + s.skip(n));
        lemma_seq_concat_while(s.skip(n), pred);
    }
    assert(s.skip(n).skip_while(pred) == s.skip_while(pred)) by {
        lemma_seq_skip_skip_while(s, n, pred);
    }
    assert(s.take(n) + s.skip(n).take_while(pred) == s.take_while(pred)) by {
        lemma_seq_concat_while(s, pred);
    }
    assert(s.take_while(pred).skip(n) == s.skip(n).take_while(pred));
}

/// Proof that `s.take(n).skip_while(pred)` is 
/// (1) empty, if `n <= s.take_while(pred).len()`
/// (2) `s.skip_while(pred).take(n - s.take_while(pred).len())`, otherwise
pub broadcast proof fn lemma_seq_take_skip_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.len(),
    ensures 
        #![trigger s.take(n).skip_while(pred)]
        n <= s.take_while(pred).len() ==> s.take(n).skip_while(pred).len() == 0,
        n > s.take_while(pred).len() ==> 
            s.take(n).skip_while(pred) == s.skip_while(pred).take(n - s.take_while(pred).len()),
{
    if n <= s.take_while(pred).len() {
        lemma_seq_take_while_ensures(s, pred);
        lemma_seq_count_while_lower_bound(s.take(n), pred, n);
        lemma_seq_skip_while_is_suffix(s.take(n), pred);
        assert(s.take(n).skip_while(pred).len() == 0);
    } else {
        lemma_seq_take_while_ensures(s, pred);
        lemma_seq_skip_while_ensures(s, pred);
        lemma_seq_skip_while_defines(
            s.take(n), 
            pred, 
            s.skip_while(pred).take(n - s.take_while(pred).len()),
        );
    }
}

/// Proof that `s.take(n).take_while(pred)` is 
/// (1) `s.take(n)`, if `n <= s.take_while(pred).len()`
/// (2) `s.take_while(pred)`, otherwise
pub broadcast proof fn lemma_seq_take_take_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.len(),
    ensures 
        #![trigger s.take(n).take_while(pred)]
        n <= s.take_while(pred).len() ==> s.take(n).take_while(pred) == s.take(n),
        n > s.take_while(pred).len() ==> s.take(n).take_while(pred) == s.take_while(pred),
{
    if n <= s.take_while(pred).len() {
        lemma_seq_take_while_ensures(s, pred);
        lemma_seq_count_while_lower_bound(s.take(n), pred, n);
        lemma_seq_take_while_is_prefix(s.take(n), pred);
    } else {
        lemma_seq_take_while_ensures(s, pred);
        lemma_seq_skip_while_ensures(s, pred);
        lemma_seq_take_while_defines(
            s.take(n), 
            pred, 
            s.take_while(pred),
        );
    }
}

/// Proof that `s.rskip_while(pred)` and `s.rtake_while(pred)` add back to `s`.
pub broadcast proof fn lemma_seq_rconcat_while<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #[trigger] (s.rskip_while(pred) + s.rtake_while(pred)) == s,    
{
    lemma_seq_rskip_while_is_prefix(s, pred);
    lemma_seq_rtake_while_is_suffix(s, pred);
}

/// Proof of `s.rskip_while(pred)`'s properties.
pub broadcast proof fn lemma_seq_rskip_while_ensures<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #![trigger s.rskip_while(pred)] 
        s.rskip_while(pred).is_prefix_of(s),
        s.rskip_while(pred).len() > 0 ==> !pred(s.rskip_while(pred).last()),
        forall|i: int| s.rskip_while(pred).len() <= i < s.len()
            ==> #[trigger] pred(s[i]),
{
    lemma_seq_rskip_while_is_prefix(s, pred);
    lemma_seq_rskip_while_pred(s, pred);
    lemma_seq_rconcat_while(s, pred);
    assert forall|i: int| s.rskip_while(pred).len() <= i < s.len()
    implies #[trigger] pred(s[i])
    by {
        lemma_seq_rtake_while_pred(s, pred, i - s.rskip_while(pred).len());
        assert(s.rtake_while(pred)[i - s.rskip_while(pred).len()] == s[i]);
    }
}

/// Proof of `s.rtake_while(pred)`'s properties.
pub broadcast proof fn lemma_seq_rtake_while_ensures<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #![trigger s.rtake_while(pred)] 
        s.rtake_while(pred).is_suffix_of(s),
        s.rtake_while(pred).len() < s.len() ==> !pred(s[s.len() - 1 - s.rtake_while(pred).len()]),
        forall|i: int| 0 <= i < s.rtake_while(pred).len() ==> #[trigger] pred(s.rtake_while(pred)[i]),
{
    lemma_seq_rconcat_while(s, pred);
    lemma_seq_rskip_while_ensures(s, pred);
    if s.rtake_while(pred).len() < s.len() {
        assert(s[s.len() - 1 - s.rtake_while(pred).len()] == s.rskip_while(pred).last());
    }
}

/// Proof of an alternative way to define `rskip_while`.
pub proof fn lemma_seq_rskip_while_defines<A>(s: Seq<A>, pred: spec_fn(A) -> bool, s1: Seq<A>)
    requires
        s1.is_prefix_of(s),
        s1.len() > 0 ==> !pred(s1.last()),
        forall|i: int| s1.len() <= i < s.len() ==> #[trigger] pred(s[i]),
    ensures
        s1 == s.rskip_while(pred),
{
    lemma_seq_rconcat_while(s, pred);
    lemma_seq_rcount_while_lower_bound(s, pred, s1.len() as int);
    if s1.len() > 0 {
        lemma_seq_rcount_while_upper_bound(s, pred, s1.len() - 1);
        assert(s1.last() == s[s1.len() - 1]);
    }
    lemma_seq_rskip_while_is_prefix(s, pred);
}

/// Proof of an alternative way to define `take_while`.
pub proof fn lemma_seq_rtake_while_defines<A>(s: Seq<A>, pred: spec_fn(A) -> bool, s1: Seq<A>)
    requires
        s1.is_suffix_of(s),
        s1.len() < s.len() ==> !pred(s[s.len() - 1 - s1.len()]),
        forall|i: int| 0 <= i < s1.len() ==> #[trigger] pred(s1[i]),
    ensures
        s1 == s.rtake_while(pred),
{
    lemma_seq_rconcat_while(s, pred);
    assert forall|i: int| s.len() - s1.len() <= i < s.len()
    implies #[trigger] s[i] == s1[i - (s.len() - s1.len())] by {}
    lemma_seq_rskip_while_defines(s, pred, s.take(s.len() - s1.len()));
}

/// Proof that `s.take(n).rskip_while(pred) == s.rskip_while(pred)` if `n >= s.rskip_while(pred).len()`.
pub broadcast proof fn lemma_seq_take_rskip_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        s.rskip_while(pred).len() <= n <= s.len(),
    ensures 
        #[trigger] s.take(n).rskip_while(pred) == s.rskip_while(pred),
{
    calc!{
        (==)
        s.take(n).rskip_while(pred); {
            lemma_seq_rskip_while_reverse(s.take(n), pred);
        }
        s.take(n).reverse().skip_while(pred).reverse(); {
            assert(s.take(n).reverse() == s.reverse().skip(s.len() - n));
        }
        s.reverse().skip(s.len() - n).skip_while(pred).reverse(); {
            calc!{
                (==)
                s.reverse().take_while(pred).len(); {}
                s.reverse().take_while(pred).reverse().len(); {
                    lemma_seq_rtake_while_reverse(s, pred);
                }
                s.rtake_while(pred).len();
            }
            lemma_seq_rconcat_while(s, pred);
            lemma_seq_skip_skip_while(s.reverse(), s.len() - n, pred);
        }
        s.reverse().skip_while(pred).reverse(); {
            lemma_seq_rskip_while_reverse(s, pred);
        }
        s.rskip_while(pred);
    }
}

/// Proof that `s.take(n).rtake_while(pred) == s.rtake_while(pred).take(n - s.rskip_while(pred).len())` 
/// if `n >= s.rskip_while(pred).len()`.
pub broadcast proof fn lemma_seq_take_rtake_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        s.rskip_while(pred).len() <= n <= s.len(),
    ensures 
        #[trigger] s.take(n).rtake_while(pred) == s.rtake_while(pred).take(n - s.rskip_while(pred).len()),
{
    lemma_seq_rconcat_while(s, pred);
    calc!{
        (==)
        s.reverse().take_while(pred).len(); {}
        s.reverse().take_while(pred).reverse().len(); {
            lemma_seq_rtake_while_reverse(s, pred);
        }
        s.rtake_while(pred).len();
    }
    calc!{
        (==)
        s.take(n).rtake_while(pred); {
            lemma_seq_rtake_while_reverse(s.take(n), pred);
        }
        s.take(n).reverse().take_while(pred).reverse(); {
            assert(s.take(n).reverse() == s.reverse().skip(s.len() - n));
        }
        s.reverse().skip(s.len() - n).take_while(pred).reverse(); {
            lemma_seq_skip_take_while(s.reverse(), s.len() - n, pred);
        }
        s.reverse().take_while(pred).skip(s.len() - n).reverse(); {
            let s1 = s.reverse().take_while(pred);
            calc!{
                (==)
                s1.skip(s.len() - n).reverse(); {}
                s1.reverse().take(s1.len() - s.len() + n); {
                    assert(s.len() == s.rtake_while(pred).len() + s.rskip_while(pred).len());
                }
                s1.reverse().take(n - s.rskip_while(pred).len());
            }
        }
        s.reverse().take_while(pred).reverse().take(n - s.rskip_while(pred).len()); {
            lemma_seq_rtake_while_reverse(s, pred);
        }
        s.rtake_while(pred).take(n - s.rskip_while(pred).len());
    }
}

/// Proof that `s.skip(n).rskip_while(pred)` is 
/// (1) empty, if `n >= s.rskip_while(pred).len()`
/// (2) `s.rskip_while(pred).skip(n)`, otherwise
pub broadcast proof fn lemma_seq_skip_rskip_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.len(),
    ensures 
        #![trigger s.skip(n).rskip_while(pred)]
        n >= s.rskip_while(pred).len() ==> s.skip(n).rskip_while(pred).len() == 0,
        n < s.rskip_while(pred).len() ==> 
            s.skip(n).rskip_while(pred) == s.rskip_while(pred).skip(n),
{
    if n >= s.rskip_while(pred).len() {
        lemma_seq_rskip_while_ensures(s, pred);
        lemma_seq_rcount_while_lower_bound(s.skip(n), pred, 0);
        lemma_seq_rskip_while_is_prefix(s.skip(n), pred);
        assert(s.skip(n).rskip_while(pred).len() == 0);
    } else {
        lemma_seq_rtake_while_ensures(s, pred);
        lemma_seq_rskip_while_ensures(s, pred);
        lemma_seq_rskip_while_defines(
            s.skip(n), 
            pred, 
            s.rskip_while(pred).skip(n),
        );
    }
}

/// Proof that `s.skip(n).rtake_while(pred)` is 
/// (1) `s.skip(n)`, if `n >= s.rskip_while(pred).len()`
/// (2) `s.rtake_while(pred)`, otherwise
pub broadcast proof fn lemma_seq_skip_rtake_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.len(),
    ensures 
        #![trigger s.skip(n).rtake_while(pred)]
        n >= s.rskip_while(pred).len() ==> s.skip(n).rtake_while(pred) == s.skip(n),
        n < s.rskip_while(pred).len() ==> s.skip(n).rtake_while(pred) == s.rtake_while(pred),
{
    if n >= s.rskip_while(pred).len() {
        lemma_seq_rskip_while_ensures(s, pred);
        lemma_seq_rcount_while_lower_bound(s.skip(n), pred, 0);
        lemma_seq_rtake_while_is_suffix(s.skip(n), pred);
    } else {
        lemma_seq_rtake_while_ensures(s, pred);
        lemma_seq_rskip_while_ensures(s, pred);
        lemma_seq_rtake_while_defines(
            s.skip(n), 
            pred, 
            s.rtake_while(pred),
        );
    }
}

/// Proof that `s.rskip_while(pred)` is equal to `s.reverse().skip_while(pred).reverse()`.
pub broadcast proof fn lemma_seq_rskip_while_reverse<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #[trigger] s.rskip_while(pred) == s.reverse().skip_while(pred).reverse(),
{
    let s1 = s.reverse().skip_while(pred).reverse();
    lemma_seq_skip_while_ensures(s.reverse(), pred);
    assert forall|i: int| s1.len() <= i < s.len()
    implies #[trigger] pred(s[i])
    by {
        assert(s[i] == s.reverse()[s.len() - 1 - i]);
        assert(s.len() - 1 - i < s.reverse().len() - s.reverse().skip_while(pred).len());
    }
    lemma_seq_rskip_while_defines(s, pred, s1);
}

/// Proof that `s.rtake_while(pred)` is equal to `s.reverse().rtake_while(pred).reverse()`.
pub broadcast proof fn lemma_seq_rtake_while_reverse<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #[trigger] s.rtake_while(pred) == s.reverse().take_while(pred).reverse(),
{
    let s1 = s.reverse().take_while(pred).reverse();
    lemma_seq_take_while_ensures(s.reverse(), pred);
    lemma_seq_rtake_while_defines(s, pred, s1);
}

/// Proof that a negative witness (`!pred(s[i])`) gives an upper bound 
/// to the size of `s.take_while(pred)`.
pub broadcast proof fn lemma_seq_count_while_upper_bound<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int)
    requires
        0 <= i < s.len(),
        !pred(s[i]),
    ensures
        #![trigger s.take_while(pred).len(), pred(s[i])] 
        #![trigger s.skip_while(pred).len(), pred(s[i])] 
        s.take_while(pred).len() <= i,
        s.skip_while(pred).len() >= s.len() - i,
{
    assert_by_contradiction!(s.take_while(pred).len() <= i, {
        lemma_seq_take_while_ensures(s, pred);
        assert(s.take_while(pred)[i] == s[i]);
        assert(pred(s.take_while(pred)[i]) && !pred(s[i]));
    });
    assert(s.skip_while(pred).len() >= s.len() - i) by {
        lemma_seq_concat_while(s, pred);
    }
}

/// Proof that a postive witness (`forall|i| 0 <= i < k ==> pred(s[i])`) 
/// gives a lower bound to the size of `s.take_while(pred)`.
pub broadcast proof fn lemma_seq_count_while_lower_bound<A>(s: Seq<A>, pred: spec_fn(A) -> bool, k: int)
    requires
        0 <= k <= s.len(),
        forall|i: int| 0 <= i < k ==> #[trigger] pred(s[i]),
    ensures
        #![trigger s.take_while(pred).len(), pred(s[k])] 
        #![trigger s.skip_while(pred).len(), pred(s[k])] 
        s.take_while(pred).len() >= k,
        s.skip_while(pred).len() <= s.len() - k,
{
    assert_by_contradiction!(s.skip_while(pred).len() <= s.len() - k, {
        lemma_seq_skip_while_ensures(s, pred);
        assert(s.len() - s.skip_while(pred).len() < k);
        assert(s.skip_while(pred).first() == s[s.len() - s.skip_while(pred).len()]);
        assert(!pred(s.skip_while(pred).first()));
        assert(pred(s[s.len() - s.skip_while(pred).len()]));
    });
    assert(s.take_while(pred).len() >= k) by {
        lemma_seq_concat_while(s, pred);
    }
}

/// Proof that a negative witness (`!pred(s[i])`) gives an upper bound 
/// to the size of `s.rtake_while(pred)`.
pub broadcast proof fn lemma_seq_rcount_while_upper_bound<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int)
    requires
        0 <= i < s.len(),
        !pred(s[i]),
    ensures
        #![trigger s.rtake_while(pred).len(), pred(s[i])] 
        #![trigger s.rskip_while(pred).len(), pred(s[i])] 
        s.rtake_while(pred).len() <= s.len() - i - 1,
        s.rskip_while(pred).len() >= i + 1,
{
    assert_by_contradiction!(s.rtake_while(pred).len() <= s.len() - i - 1, {
        lemma_seq_rtake_while_ensures(s, pred);
        assert(s.rtake_while(pred)[i - (s.len() - s.rtake_while(pred).len())] == s[i]);
        assert(pred(s.rtake_while(pred)[i - (s.len() - s.rtake_while(pred).len())]));
        assert(!pred(s[i]));
    });
    assert(s.rskip_while(pred).len() >= i + 1) by {
        lemma_seq_rconcat_while(s, pred);
    }
}

/// Proof that a postive witness (`forall|i| k <= i < s.len() ==> pred(s[i])`) 
/// gives a lower bound to the size of `s.rtake_while(pred)`.
pub broadcast proof fn lemma_seq_rcount_while_lower_bound<A>(s: Seq<A>, pred: spec_fn(A) -> bool, k: int)
    requires
        0 <= k <= s.len(),
        forall|i: int| k <= i < s.len() ==> #[trigger] pred(s[i]),
    ensures
        #![trigger s.rtake_while(pred).len(), pred(s[k])] 
        #![trigger s.rskip_while(pred).len(), pred(s[k])] 
        s.rtake_while(pred).len() >= s.len() - k,
        s.rskip_while(pred).len() <= k,
{
    assert_by_contradiction!(s.rskip_while(pred).len() <= k, {
        assert(k <= s.rskip_while(pred).len() - 1);
        lemma_seq_rskip_while_ensures(s, pred);
        assert(!pred(s.skip_while(pred).last()));
        assert(pred(s[s.skip_while(pred).len() - 1]));
    });
    assert(s.rtake_while(pred).len() >= s.len() - k) by {
        lemma_seq_rconcat_while(s, pred);
    }
}

// --- Internal helper lemmas ---

proof fn lemma_seq_skip_while_is_suffix<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        s.skip_while(pred).is_suffix_of(s),
    decreases
        s.len(),
{
    if s.len() == 0 || !pred(s.first()) { /* base case */ }
    else {
        lemma_seq_skip_while_is_suffix(s.drop_first(), pred);
        assert(s.drop_first().skip_while(pred).is_suffix_of(s));
    }
}

proof fn lemma_seq_take_while_is_prefix<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        s.take_while(pred).is_prefix_of(s),
{
    lemma_seq_skip_while_is_suffix(s, pred);
}

proof fn lemma_seq_skip_while_pred<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        s.skip_while(pred).len() > 0 ==> !pred(s.skip_while(pred).first()),
    decreases
        s.len(),
{
    if s.len() == 0 || !pred(s.first()) { /* base case */ }
    else {
        lemma_seq_skip_while_pred(s.drop_first(), pred);
    }
}

proof fn lemma_seq_take_while_pred<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int)
    ensures 
        0 <= i < s.take_while(pred).len() ==> pred(s.take_while(pred)[i]),
    decreases
        s.len(),
{
    if i < 0 || i >= s.take_while(pred).len() 
        { return }
    if s.len() == 0 || !pred(s.first()) { 
        // base case
        assert(s.skip_while(pred) == s);
    } else {
        lemma_seq_concat_while(s, pred);
        if i == 0 {
            assert(s.take_while(pred)[0] == s[0]);
        } else {
            lemma_seq_take_while_pred(s.drop_first(), pred, i - 1);
            assert(s.take_while(pred)[i] == s.drop_first().take_while(pred)[i - 1]);
        }
    }
}

proof fn lemma_seq_rskip_while_is_prefix<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        s.rskip_while(pred).is_prefix_of(s),
    decreases
        s.len(),
{
    if s.len() == 0 || !pred(s.last()) { /* base case */ }
    else {
        lemma_seq_rskip_while_is_prefix(s.drop_last(), pred);
        assert(s.drop_last().rskip_while(pred).is_prefix_of(s));
    }
}

proof fn lemma_seq_rtake_while_is_suffix<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        s.rtake_while(pred).is_suffix_of(s),
{
    lemma_seq_rskip_while_is_prefix(s, pred);
}

proof fn lemma_seq_rskip_while_pred<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        s.rskip_while(pred).len() > 0 ==> !pred(s.rskip_while(pred).last()),
    decreases
        s.len(),
{
    if s.len() == 0 || !pred(s.last()) { /* base case */ }
    else {
        lemma_seq_rskip_while_pred(s.drop_last(), pred);
    }
}

proof fn lemma_seq_rtake_while_pred<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int)
    ensures 
        0 <= i < s.rtake_while(pred).len() ==> pred(s.rtake_while(pred)[i]),
    decreases
        s.len(),
{
    if i < 0 || i >= s.rtake_while(pred).len() 
        { return }
    if s.len() == 0 || !pred(s.last()) { 
        // base case
        assert(s.rskip_while(pred) == s);
    } else {
        lemma_seq_rconcat_while(s, pred);
        if i == s.rtake_while(pred).len() - 1 {
            assert(s.rtake_while(pred).last() == s.last());
        } else {
            lemma_seq_rtake_while_pred(s.drop_last(), pred, i);
            assert(s.rtake_while(pred)[i] == s.drop_last().rtake_while(pred)[i]);
        }
    }
}


// --- Tests ---

// proof fn test_count(s: Seq<int>, pred: spec_fn(int) -> bool)
//     requires
//         s.len() > 0,
//         !pred(s.first()),
// {
//     broadcast use {
//         lemma_seq_count_while_bound,
//         lemma_seq_skip_while_ensures,
//         lemma_seq_take_while_ensures,
//     };
//     // assert(!pred(s[0]));
//     // lemma_seq_count_while_bound(s, pred, 0);
//     // assert(s.take_while(pred) == Seq::<int>::empty());
//     assert(s.skip_while(pred) == s);
// }

} // verus!