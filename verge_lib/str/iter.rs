//! Iterator methods and types for strings.
//!
//! This module exposes iterator wrappers for string APIs. Pattern-specific
//! iterators use monomorphic constructor methods for supported pattern kinds
//! instead of Rust's generic `Pattern` surface.
#![allow(unused_imports)]
use super::*;
use crate::iter::*;
use crate::{is_deterministic, is_total};
use vstd::std_specs::iter::*;

use std::str::{
    Bytes, CharIndices, Lines,
    Split, SplitInclusive, SplitTerminator, SplitN,
    RSplit, RSplitTerminator, RSplitN,
    Matches, RMatches, MatchIndices, RMatchIndices,
    SplitWhitespace, SplitAsciiWhitespace,
};
use std::str::pattern::{Pattern, Searcher, ReverseSearcher, DoubleEndedSearcher};

verus! {

#[verifier::external_trait_specification]
pub trait ExPattern: Sized {
    type ExternalTraitSpecificationFor: Pattern;
}

#[verifier::external_trait_specification]
pub trait ExSearcher<'a> {
    type ExternalTraitSpecificationFor: Searcher<'a>;
}

#[verifier::external_trait_specification]
pub trait ExReverseSearcher<'a>: Searcher<'a> {
    type ExternalTraitSpecificationFor: ReverseSearcher<'a>;
}

#[verifier::external_trait_specification]
pub trait ExDoubleEndedSearcher<'a>: ReverseSearcher<'a> {
    type ExternalTraitSpecificationFor: DoubleEndedSearcher<'a>;
}

/// Specifies the iterator `VergeSplit` which wraps `Split`,
/// constructed via pattern-specialized string split methods.
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    Split<'a, P> as VergeSplit<'_, P> :: Item = &'a str
    where {
        P: Pattern
    };

    [str as View<V=Seq<char>>] :: split_ch_iter via split
    (&self, ch: char) -> (iter: VergeSplit<'_, char>)
    ensures {
        &&& iter.seq().len() > 0
        &&& forall |i: int| 0 <= i < iter.seq().len()
                ==> !(#[trigger] iter.seq()[i]@.contains(ch))
        &&& self@ == iter.seq().first()@
            + iter.seq().drop_first()
                .map_values(|ss: &str| ss@.insert(0, ch))
                .flatten()
    };

    [str as View<V=Seq<char>>] :: split_chars_iter via split <'b>
    (&self, chars: &'b [char]) -> (iter: VergeSplit<'_, &'b [char]>)
    ensures {
            &&& iter.seq().len() > 0
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> (#[trigger] iter.seq()[i]@).all(|c: char| !chars@.contains(c))
            &&& exists |delim: Seq<char>| #![trigger delim.len()] {
                &&& #[trigger] delim.len() == iter.seq().len() - 1
                &&& forall |i: int| 0 <= i < delim.len()
                        ==> #[trigger] chars@.contains(delim[i])
                &&& self@ == iter.seq().first()@
                    + iter.seq().drop_first()
                        .map(|i: int, ss: &str| ss@.insert(0, delim[i]))
                        .flatten()
            }
        }
    ;

    [str as View<V=Seq<char>>] :: split_fn_iter via split <F>
    (&self, f: F) -> (iter: VergeSplit<'_, F>)
    where {
        F: FnMut(char) -> bool
    }
    requires {
        is_deterministic(f) && is_total(f)
    }
    ensures {
        &&& iter.seq().len() > 0
        &&& forall |i: int| 0 <= i < iter.seq().len()
                ==> (#[trigger] iter.seq()[i]@).all(|c: char| call_ensures(f, (c,), false))
        &&& exists |delim: Seq<char>| #![trigger delim.len()] {
            &&& #[trigger] delim.len() == iter.seq().len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] call_ensures(f, (delim[i],), true)
            &&& self@ == iter.seq().first()@
                + iter.seq().drop_first()
                    .map(|i: int, ss: &str| ss@.insert(0, delim[i]))
                    .flatten()
        }
    };

    [str as View<V=Seq<char>>] :: split_str_iter via split <'b>
    (&self, pat: &'b str) -> (iter: VergeSplit<'_, &'b str>)
    requires {
    pat@.len() > 0
    }
    ensures {
            &&& iter.seq().len() > 0
            &&& forall |i: int| #![trigger iter.seq()[i]@]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i]@.len() > 0
                        ==> !pat@.is_prefix_of(iter.seq()[i]@ + pat@)
                            && !pat@.is_infix_of(iter.seq()[i]@ + pat@)
            &&& !(pat@.is_subrange_of(iter.seq().last()@))
            &&& self@ == iter.seq().first()@
                + iter.seq().drop_first()
                    .map_values(|ss: &str| pat@ + ss@)
                    .flatten()
        }
    ;
);

/// Specifies `VergeSplit` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    Split as VergeSplit ['a, P] :: Item = &'a str
        where P: Pattern,
);

/// Specifies the iterator `VergeSplitInclusive` which wraps `SplitInclusive`,
/// constructed via pattern-specialized string methods.
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    SplitInclusive<'a, P> as VergeSplitInclusive<'_, P> :: Item = &'a str
    where {
    P: Pattern
    }
    ;

    [str as View<V=Seq<char>>] :: split_inclusive_ch_iter via split_inclusive
    (&self, ch: char) -> (iter: VergeSplitInclusive<'_, char>)
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]@]
                    0 <= i < iter.seq().len()
                    ==> iter.seq()[i]@.len() > 0
                        && !iter.seq()[i]@.drop_last().contains(ch)
            &&& forall |i: int| 0 <= i < iter.seq().len() - 1
                    ==> #[trigger] iter.seq()[i]@.last() == ch
            &&& self@ == iter.seq().map_values(|ss: &str| ss@).flatten()
        }
    ;

    [str as View<V=Seq<char>>] :: split_inclusive_chars_iter via split_inclusive <'b>
    (&self, chars: &'b [char]) -> (iter: VergeSplitInclusive<'_, &'b [char]>)
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]@]
                    0 <= i < iter.seq().len()
                    ==> iter.seq()[i]@.len() > 0
                        && iter.seq()[i]@.drop_last().all(|c: char| !chars@.contains(c))
            &&& forall |i: int| 0 <= i < iter.seq().len() - 1
                    ==> #[trigger] chars@.contains(iter.seq()[i]@.last())
            &&& self@ == iter.seq().map_values(|ss: &str| ss@).flatten()
        }
    ;

    [str as View<V=Seq<char>>] :: split_inclusive_fn_iter via split_inclusive <F>
    (&self, f: F) -> (iter: VergeSplitInclusive<'_, F>)
    where {
    F: FnMut(char) -> bool
    }
    requires {
    is_deterministic(f) && is_total(f)
    }
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]@]
                    0 <= i < iter.seq().len()
                    ==> iter.seq()[i]@.len() > 0
                        && iter.seq()[i]@.drop_last()
                            .all(|c: char| call_ensures(f, (c,), false))
            &&& forall |i: int| 0 <= i < iter.seq().len() - 1
                    ==> #[trigger] call_ensures(f, (iter.seq()[i]@.last(),), true)
            &&& self@ == iter.seq().map_values(|ss: &str| ss@).flatten()
        }
    ;

    [str as View<V=Seq<char>>] :: split_inclusive_str_iter via split_inclusive <'b>
    (&self, pat: &'b str) -> (iter: VergeSplitInclusive<'_, &'b str>)
    requires {
    pat@.len() > 0
    }
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]@]
                    0 <= i < iter.seq().len()
                    ==> iter.seq()[i]@.len() > 0
                        && !pat@.is_subrange_of(iter.seq()[i]@.drop_last())
            &&& forall |i: int| 0 <= i < iter.seq().len() - 1
                    ==> #[trigger] pat@.is_suffix_of(iter.seq()[i]@)
            &&& self@ == iter.seq().map_values(|ss: &str| ss@).flatten()
        }
    ;
);

/// Specifies `VergeSplitInclusive` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    SplitInclusive as VergeSplitInclusive ['a, P] :: Item = &'a str
        where P: Pattern,
);


/// Specifies the iterator `VergeRSplit` which wraps `RSplit`,
/// constructed via pattern-specialized string methods.
impl_iterator!(
    #[specialized_next_reverse_searcher]
    #[verifier::reject_recursive_types(P)]
    RSplit<'a, P> as VergeRSplit<'_, P> :: Item = &'a str
    where {
        P: Pattern,
    }
    ;

    [str as View<V=Seq<char>>] :: rsplit_ch_iter via rsplit
    (&self, ch: char) -> (iter: VergeRSplit<'_, char>)
    ensures {
            &&& iter.seq().len() > 0
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> !(#[trigger] iter.seq()[i]@.contains(ch))
            &&& self@ == iter.seq().drop_first()
                .map_values(|ss: &str| ss@.push(ch))
                .reverse()
                .flatten() + iter.seq().first()@
        }
    ;

    [str as View<V=Seq<char>>] :: rsplit_chars_iter via rsplit <'b>
    (&self, chars: &'b [char]) -> (iter: VergeRSplit<'_, &'b [char]>)
    ensures {
            &&& iter.seq().len() > 0
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> (#[trigger] iter.seq()[i]@).all(|c: char| !chars@.contains(c))
            &&& exists |delim: Seq<char>| #![trigger delim.len()] {
                &&& #[trigger] delim.len() == iter.seq().len() - 1
                &&& forall |i: int| 0 <= i < delim.len()
                        ==> #[trigger] chars@.contains(delim[i])
                &&& self@ == iter.seq().drop_first()
                    .map(|i: int, ss: &str| ss@.push(delim[i]))
                    .reverse()
                    .flatten() + iter.seq().first()@
            }
        }
    ;

    [str as View<V=Seq<char>>] :: rsplit_fn_iter via rsplit <F>
    (&self, f: F) -> (iter: VergeRSplit<'_, F>)
    where {
    F: FnMut(char) -> bool
    }
    requires {
    is_deterministic(f) && is_total(f)
    }
    ensures {
            &&& iter.seq().len() > 0
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> (#[trigger] iter.seq()[i]@).all(|c: char| call_ensures(f, (c,), false))
            &&& exists |delim: Seq<char>| #![trigger delim.len()] {
                &&& #[trigger] delim.len() == iter.seq().len() - 1
                &&& forall |i: int| 0 <= i < delim.len()
                        ==> #[trigger] call_ensures(f, (delim[i],), true)
                &&& self@ == iter.seq().drop_first()
                    .map(|i: int, ss: &str| ss@.push(delim[i]))
                    .reverse()
                    .flatten() + iter.seq().first()@
            }
        }
    ;

    [str as View<V=Seq<char>>] :: rsplit_str_iter via rsplit <'b>
    (&self, pat: &'b str) -> (iter: VergeRSplit<'_, &'b str>)
    requires {
    pat@.len() > 0
    }
    ensures {
            &&& iter.seq().len() > 0
            &&& forall |i: int| #![trigger iter.seq()[i]@]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i]@.len() > 0
                        ==> !pat@.is_suffix_of(pat@ + iter.seq()[i]@)
                            && !pat@.is_infix_of(pat@ + iter.seq()[i]@)
            &&& !(pat@.is_subrange_of(iter.seq().last()@))
            &&& self@ == iter.seq().drop_first()
                .map_values(|ss: &str| ss@ + pat@)
                .reverse()
                .flatten() + iter.seq().first()@
        }
    ;
);

/// Specifies `VergeRSplit` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RSplit as VergeRSplit ['a, P] :: Item = &'a str
        where
            P: Pattern,
);


/// Specifies the iterator `VergeSplitTerminator` which wraps `SplitTerminator`,
/// constructed via pattern-specialized string methods.
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    SplitTerminator<'a, P> as VergeSplitTerminator<'_, P> :: Item = &'a str
    where {
    P: Pattern
    }
    ;

    [str as View<V=Seq<char>>] :: split_terminator_ch_iter via split_terminator
    (&self, ch: char) -> (iter: VergeSplitTerminator<'_, char>)
    ensures {
            &&& self@.len() == 0 <==> iter.seq().len() == 0
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> !(#[trigger] iter.seq()[i]@.contains(ch))
            &&& self@.len() > 0 && self@.last() == ch
                    <==> self@ == iter.seq()
                        .map_values(|ss: &str| ss@.push(ch))
                        .flatten()
            &&& self@.len() > 0 && self@.last() != ch
                    <==> self@ == iter.seq().drop_last()
                        .map_values(|ss: &str| ss@.push(ch))
                        .flatten() + iter.seq().last()@
        }
    ;

    [str as View<V=Seq<char>>] :: split_terminator_chars_iter via split_terminator <'b>
    (&self, chars: &'b [char]) -> (iter: VergeSplitTerminator<'_, &'b [char]>)
    ensures {
            &&& self@.len() == 0 <==> iter.seq().len() == 0
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> (#[trigger] iter.seq()[i]@).all(|c: char| !chars@.contains(c))
            &&& exists |delim: Seq<char>| #![trigger delim.len()] {
                &&& forall |i: int| 0 <= i < delim.len()
                        ==> #[trigger] chars@.contains(delim[i])
                &&& self@.len() > 0 && chars@.contains(self@.first())
                        <==> {
                            &&& delim.len() == iter.seq().len()
                            &&& self@ == iter.seq()
                                .map(|i: int, ss: &str| ss@.push(delim[i]))
                                .flatten()
                        }
                &&& self@.len() > 0 && !chars@.contains(self@.first())
                        <==> {
                            &&& delim.len() == iter.seq().len() - 1
                            &&& self@ == iter.seq().drop_last()
                                .map(|i: int, ss: &str| ss@.push(delim[i]))
                                .flatten() + iter.seq().last()@
                        }
            }
        }
    ;

    [str as View<V=Seq<char>>] :: split_terminator_fn_iter via split_terminator <F>
    (&self, f: F) -> (iter: VergeSplitTerminator<'_, F>)
    where {
    F: FnMut(char) -> bool
    }
    requires {
    is_deterministic(f) && is_total(f)
    }
    ensures {
            &&& self@.len() == 0 <==> iter.seq().len() == 0
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> (#[trigger] iter.seq()[i]@).all(|c: char| call_ensures(f, (c,), false))
            &&& exists |delim: Seq<char>| {
                &&& forall |i: int| 0 <= i < delim.len()
                        ==> call_ensures(f, (#[trigger] delim[i],), true)
                &&& self@.len() > 0 && call_ensures(f, (self@.last(),), true)
                        <==> {
                            &&& #[trigger] delim.len() == iter.seq().len()
                            &&& self@ == iter.seq()
                                .map(|i: int, ss: &str| ss@.push(delim[i]))
                                .flatten()
                        }
                &&& self@.len() > 0 && call_ensures(f, (self@.last(),), false)
                        <==> {
                            &&& delim.len() == iter.seq().len() - 1
                            &&& self@ == iter.seq().drop_last()
                                .map(|i: int, ss: &str| ss@.push(delim[i]))
                                .flatten() + iter.seq().last()@
                        }
            }
        }
    ;

    [str as View<V=Seq<char>>] :: split_terminator_str_iter via split_terminator <'b>
    (&self, pat: &'b str) -> (iter: VergeSplitTerminator<'_, &'b str>)
    requires {
    pat@.len() > 0
    }
    ensures {
            &&& self@.len() == 0 <==> iter.seq().len() == 0
            &&& forall |i: int| #![trigger iter.seq()[i]@]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i]@.len() > 0
                        ==> !pat@.is_prefix_of(iter.seq()[i]@ + pat@)
                            && !pat@.is_infix_of(iter.seq()[i]@ + pat@)
            &&& iter.seq().len() > 0 ==> !(pat@.is_subrange_of(iter.seq().last()@))
            &&& self@.len() > 0 ==> {
                ||| self@ == iter.seq()
                    .map_values(|ss: &str| ss@ + pat@)
                    .flatten()
                ||| iter.seq().last()@.len() > 0
                    && self@ == iter.seq().drop_last()
                        .map_values(|ss: &str| ss@ + pat@)
                        .flatten() + iter.seq().last()@
            }
        }
    ;
);

/// Specifies `VergeSplitTerminator` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    SplitTerminator as VergeSplitTerminator ['a, P] :: Item = &'a str
        where P: Pattern,
);


/// Specifies the iterator `VergeRSplitTerminator` which wraps `RSplitTerminator`,
/// constructed via pattern-specialized string methods.
impl_iterator!(
    #[specialized_next_reverse_searcher]
    #[verifier::reject_recursive_types(P)]
    RSplitTerminator<'a, P> as VergeRSplitTerminator<'_, P> :: Item = &'a str
    where {
        P: Pattern,
    }
    ;

    [str as View<V=Seq<char>>] :: rsplit_terminator_ch_iter via rsplit_terminator
    (&self, ch: char) -> (iter: VergeRSplitTerminator<'_, char>)
    ensures {
            &&& self@.len() == 0 <==> iter.seq().len() == 0
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> !(#[trigger] iter.seq()[i]@.contains(ch))
            &&& self@.len() > 0 && self@.last() == ch
                    <==> self@ == iter.seq()
                        .map_values(|ss: &str| ss@.push(ch))
                        .reverse()
                        .flatten()
            &&& self@.len() > 0 && self@.last() != ch
                    <==> self@ == iter.seq().drop_first()
                        .map_values(|ss: &str| ss@.push(ch))
                        .reverse()
                        .flatten() + iter.seq().first()@
        }
    ;

    [str as View<V=Seq<char>>] :: rsplit_terminator_chars_iter via rsplit_terminator <'b>
    (&self, chars: &'b [char]) -> (iter: VergeRSplitTerminator<'_, &'b [char]>)
    ensures {
            &&& self@.len() == 0 <==> iter.seq().len() == 0
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> (#[trigger] iter.seq()[i]@).all(|c: char| !chars@.contains(c))
            &&& exists |delim: Seq<char>| #![trigger delim.len()] {
                &&& forall |i: int| 0 <= i < delim.len()
                        ==> #[trigger] chars@.contains(delim[i])
                &&& self@.len() > 0 && chars@.contains(self@.first())
                        <==> {
                            &&& delim.len() == iter.seq().len()
                            &&& self@ == iter.seq()
                                .map(|i: int, ss: &str| ss@.push(delim[i]))
                                .reverse()
                                .flatten()
                        }
                &&& self@.len() > 0 && !chars@.contains(self@.first())
                        <==> {
                            &&& delim.len() == iter.seq().len() - 1
                            &&& self@ == iter.seq().drop_first()
                                .map(|i: int, ss: &str| ss@.push(delim[i]))
                                .reverse()
                                .flatten() + iter.seq().first()@
                        }
            }
        }
    ;

    [str as View<V=Seq<char>>] :: rsplit_terminator_fn_iter via rsplit_terminator <F>
    (&self, f: F) -> (iter: VergeRSplitTerminator<'_, F>)
    where {
    F: FnMut(char) -> bool
    }
    requires {
    is_deterministic(f) && is_total(f)
    }
    ensures {
            &&& self@.len() == 0 <==> iter.seq().len() == 0
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> (#[trigger] iter.seq()[i]@).all(|c: char| call_ensures(f, (c,), false))
            &&& exists |delim: Seq<char>| #![trigger delim.len()] {
                &&& forall |i: int| 0 <= i < delim.len()
                        ==> #[trigger] call_ensures(f, (delim[i],), true)
                &&& self@.len() > 0 && call_ensures(f, (self@.last(),), true)
                        <==> {
                            &&& delim.len() == iter.seq().len()
                            &&& self@ == iter.seq()
                                .map(|i: int, ss: &str| ss@.push(delim[i]))
                                .reverse()
                                .flatten()
                        }
                &&& self@.len() > 0 && call_ensures(f, (self@.last(),), false)
                        <==> {
                            &&& delim.len() == iter.seq().len() - 1
                            &&& self@ == iter.seq().drop_first()
                                .map(|i: int, ss: &str| ss@.push(delim[i]))
                                .reverse()
                                .flatten() + iter.seq().first()@
                        }
            }
        }
    ;

    [str as View<V=Seq<char>>] :: rsplit_terminator_str_iter via rsplit_terminator <'b>
    (&self, pat: &'b str) -> (iter: VergeRSplitTerminator<'_, &'b str>)
    requires {
    pat@.len() > 0
    }
    ensures {
            &&& self@.len() == 0 <==> iter.seq().len() == 0
            &&& forall |i: int| #![trigger iter.seq()[i]@]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i]@.len() > 0
                        ==> !pat@.is_suffix_of(pat@ + iter.seq()[i]@)
                            && !pat@.is_infix_of(pat@ + iter.seq()[i]@)
            &&& iter.seq().len() > 0 ==> !(pat@.is_subrange_of(iter.seq().last()@))
            &&& self@.len() > 0 ==> {
                ||| self@ == iter.seq()
                    .map_values(|ss: &str| ss@ + pat@)
                    .reverse()
                    .flatten()
                ||| iter.seq().first()@.len() > 0
                    && self@ == iter.seq().drop_first()
                        .map_values(|ss: &str| ss@ + pat@)
                        .reverse()
                        .flatten() + iter.seq().first()@
            }
        }
    ;
);

/// Specifies `VergeRSplitTerminator` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RSplitTerminator as VergeRSplitTerminator ['a, P] :: Item = &'a str
        where
            P: Pattern,
);


/// Specifies the iterator `VergeSplitN` which wraps `SplitN`,
/// constructed via pattern-specialized string methods.
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    SplitN<'a, P> as VergeSplitN<'_, P> :: Item = &'a str
    where {
    P: Pattern
    }
    ;

    [str as View<V=Seq<char>>] :: splitn_ch_iter via splitn
    (&self, n: usize, ch: char) -> (iter: VergeSplitN<'_, char>)
    ensures {
            &&& iter.seq().len() <= n && (n > 0 ==> iter.seq().len() > 0)
            &&& forall |i: int| 0 <= i < iter.seq().len() - 1
                    ==> !(#[trigger] iter.seq()[i]@.contains(ch))
            &&& iter.seq().len() < n ==> !iter.seq().last()@.contains(ch)
            &&& n > 0 ==> self@ == iter.seq().drop_last()
                .map_values(|ss: &str| ss@.push(ch))
                .flatten() + iter.seq().last()@
        }
    ;

    [str as View<V=Seq<char>>] :: splitn_chars_iter via splitn <'b>
    (&self, n: usize, chars: &'b [char]) -> (iter: VergeSplitN<'_, &'b [char]>)
    ensures {
            &&& iter.seq().len() <= n && (n > 0 ==> iter.seq().len() > 0)
            &&& forall |i: int| 0 <= i < iter.seq().len() - 1
                    ==> (#[trigger] iter.seq()[i]@).all(|c: char| !chars@.contains(c))
            &&& iter.seq().len() < n
                    ==> iter.seq().last()@.all(|c: char| !chars@.contains(c))
            &&& n > 0 ==> exists |delim: Seq<char>| #![trigger delim.len()] {
                &&& #[trigger] delim.len() == iter.seq().len() - 1
                &&& forall |i: int| 0 <= i < delim.len()
                        ==> #[trigger] chars@.contains(delim[i])
                &&& self@ == iter.seq().drop_last()
                    .map(|i: int, ss: &str| ss@.push(delim[i]))
                    .flatten() + iter.seq().last()@
            }
        }
    ;

    [str as View<V=Seq<char>>] :: splitn_fn_iter via splitn <F>
    (&self, n: usize, f: F) -> (iter: VergeSplitN<'_, F>)
    where {
    F: FnMut(char) -> bool
    }
    requires {
    is_deterministic(f) && is_total(f)
    }
    ensures {
            &&& iter.seq().len() <= n && (n > 0 ==> iter.seq().len() > 0)
            &&& forall |i: int| 0 <= i < iter.seq().len() - 1
                    ==> (#[trigger] iter.seq()[i]@).all(|c: char| call_ensures(f, (c,), false))
            &&& iter.seq().len() < n
                    ==> iter.seq().last()@.all(|c: char| call_ensures(f, (c,), false))
            &&& n > 0 ==> exists |delim: Seq<char>| #![trigger delim.len()] {
                &&& #[trigger] delim.len() == iter.seq().len() - 1
                &&& forall |i: int| 0 <= i < delim.len()
                        ==> #[trigger] call_ensures(f, (delim[i],), true)
                &&& self@ == iter.seq().drop_last()
                    .map(|i: int, ss: &str| ss@.push(delim[i]))
                    .flatten() + iter.seq().last()@
            }
        }
    ;

    [str as View<V=Seq<char>>] :: splitn_str_iter via splitn <'b>
    (&self, n: usize, pat: &'b str) -> (iter: VergeSplitN<'_, &'b str>)
    requires {
    pat@.len() > 0
    }
    ensures {
            &&& iter.seq().len() <= n && (n > 0 ==> iter.seq().len() > 0)
            &&& forall |i: int| #![trigger iter.seq()[i]@]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i]@.len() > 0
                        ==> !pat@.is_prefix_of(iter.seq()[i]@ + pat@)
                            && !pat@.is_infix_of(iter.seq()[i]@ + pat@)
            &&& iter.seq().len() < n
                    ==> !(pat@.is_subrange_of(iter.seq().last()@))
            &&& n > 0 ==> self@ == iter.seq().drop_last()
                .map(|i: int, ss: &str| ss@ + pat@)
                .flatten() + iter.seq().last()@
        }
    ;
);


/// Specifies the iterator `VergeRSplitN` which wraps `RSplitN`,
/// constructed via pattern-specialized string methods.
impl_iterator!(
    #[specialized_next_reverse_searcher]
    #[verifier::reject_recursive_types(P)]
    RSplitN<'a, P> as VergeRSplitN<'_, P> :: Item = &'a str
    where {
        P: Pattern,
    }
    ;

    [str as View<V=Seq<char>>] :: rsplitn_ch_iter via rsplitn
    (&self, n: usize, ch: char) -> (iter: VergeRSplitN<'_, char>)
    ensures {
            &&& iter.seq().len() <= n && (n > 0 ==> iter.seq().len() > 0)
            &&& forall |i: int| 0 <= i < iter.seq().len() - 1
                    ==> !(#[trigger] iter.seq()[i]@.contains(ch))
            &&& iter.seq().len() < n ==> !iter.seq().last()@.contains(ch)
            &&& n > 0 ==> self@ == iter.seq().last()@
                + iter.seq().drop_last()
                    .map_values(|ss: &str| ss@.insert(0, ch))
                    .reverse()
                    .flatten()
        }
    ;

    [str as View<V=Seq<char>>] :: rsplitn_chars_iter via rsplitn <'b>
    (&self, n: usize, chars: &'b [char]) -> (iter: VergeRSplitN<'_, &'b [char]>)
    ensures {
            &&& iter.seq().len() <= n && (n > 0 ==> iter.seq().len() > 0)
            &&& forall |i: int| 0 <= i < iter.seq().len() - 1
                    ==> (#[trigger] iter.seq()[i]@).all(|c: char| !chars@.contains(c))
            &&& iter.seq().len() < n
                    ==> iter.seq().last()@.all(|c: char| !chars@.contains(c))
            &&& n > 0 ==> exists |delim: Seq<char>| #![trigger delim.len()] {
                &&& #[trigger] delim.len() == iter.seq().len() - 1
                &&& forall |i: int| 0 <= i < delim.len()
                        ==> #[trigger] chars@.contains(delim[i])
                &&& self@ == iter.seq().last()@
                    + iter.seq().drop_last()
                        .map(|i: int, ss: &str| ss@.insert(0, delim[i]))
                        .reverse()
                        .flatten()
            }
        }
    ;

    [str as View<V=Seq<char>>] :: rsplitn_fn_iter via rsplitn <F>
    (&self, n: usize, f: F) -> (iter: VergeRSplitN<'_, F>)
    where {
    F: FnMut(char) -> bool
    }
    requires {
    is_deterministic(f) && is_total(f)
    }
    ensures {
            &&& iter.seq().len() <= n && (n > 0 ==> iter.seq().len() > 0)
            &&& forall |i: int| 0 <= i < iter.seq().len() - 1
                    ==> (#[trigger] iter.seq()[i]@).all(|c: char| call_ensures(f, (c,), false))
            &&& iter.seq().len() < n
                    ==> iter.seq().last()@.all(|c: char| call_ensures(f, (c,), false))
            &&& n > 0 ==> exists |delim: Seq<char>| #![trigger delim.len()] {
                &&& #[trigger] delim.len() == iter.seq().len() - 1
                &&& forall |i: int| 0 <= i < delim.len()
                        ==> #[trigger] call_ensures(f, (delim[i],), true)
                &&& self@ == iter.seq().last()@
                    + iter.seq().drop_last()
                        .map(|i: int, ss: &str| ss@.insert(0, delim[i]))
                        .reverse()
                        .flatten()
            }
        }
    ;

    [str as View<V=Seq<char>>] :: rsplitn_str_iter via rsplitn <'b>
    (&self, n: usize, pat: &'b str) -> (iter: VergeRSplitN<'_, &'b str>)
    requires {
    pat@.len() > 0
    }
    ensures {
            &&& iter.seq().len() <= n && (n > 0 ==> iter.seq().len() > 0)
            &&& forall |i: int| #![trigger iter.seq()[i]@]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i]@.len() > 0
                        ==> !pat@.is_suffix_of(pat@ + iter.seq()[i]@)
                            && !pat@.is_infix_of(pat@ + iter.seq()[i]@)
            &&& iter.seq().len() < n
                    ==> !(pat@.is_subrange_of(iter.seq().last()@))
            &&& n > 0 ==> self@ == iter.seq().last()@
                + iter.seq().drop_last()
                    .map(|i: int, ss: &str| pat@ + ss@)
                    .reverse()
                    .flatten()
        }
    ;
);


/// Specifies the iterator `VergeMatches` which wraps `Matches`,
/// constructed via pattern-specialized string methods.
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    Matches<'a, P> as VergeMatches<'_, P> :: Item = &'a str
    where {
    P: Pattern
    }
    ;

    [str as View<V=Seq<char>>] :: matches_ch_iter via matches
    (&self, ch: char) -> (iter: VergeMatches<'_, char>)
    ensures {
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> #[trigger] iter.seq()[i]@ == seq![ch]
            &&& iter.seq().len() == self@.count(|c: char| c == ch)
        }
    ;

    [str as View<V=Seq<char>>] :: matches_chars_iter via matches <'b>
    (&self, chars: &'b [char]) -> (iter: VergeMatches<'_, &'b [char]>)
    ensures {
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> #[trigger] iter.seq()[i]@.len() == 1
                        && chars@.contains(iter.seq()[i]@[0])
            &&& iter.seq().len() == self@.count(|c: char| chars@.contains(c))
        }
    ;

    [str as View<V=Seq<char>>] :: matches_fn_iter via matches <F>
    (&self, f: F) -> (iter: VergeMatches<'_, F>)
    where {
    F: FnMut(char) -> bool
    }
    requires {
    is_deterministic(f) && is_total(f)
    }
    ensures {
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> #[trigger] iter.seq()[i]@.len() == 1
                        && call_ensures(f, (iter.seq()[i]@[0],), true)
            &&& iter.seq().len()
                    == self@.count(|c: char| call_ensures(f, (c,), true))
        }
    ;

    [str as View<V=Seq<char>>] :: matches_str_iter via matches <'b>
    (&self, pat: &'b str) -> (iter: VergeMatches<'_, &'b str>)
    requires {
    pat@.len() > 0
    }
    ensures {
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> #[trigger] iter.seq()[i]@ == pat@
            &&& iter.seq().len() == 0 <==> !pat@.is_subrange_of(self@)
            &&& exists |gap: Seq<Seq<char>>| {
                &&& #[trigger] gap.len() == iter.seq().len() + 1
                &&& forall |i: int| #![trigger gap[i]]
                        0 <= i < gap.len() - 1
                        ==> gap[i].len() > 0
                            ==> !pat@.is_prefix_of(gap[i] + pat@)
                                && !pat@.is_infix_of(gap[i] + pat@)
                &&& !pat@.is_subrange_of(gap.last())
                &&& self@ == iter.seq()
                    .map(|i: int, ss: &str| gap[i] + ss@)
                    .flatten() + gap.last()
            }
        }
    ;
);

/// Specifies `VergeMatches` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    Matches as VergeMatches ['a, P] :: Item = &'a str
        where P: Pattern,
);


/// Specifies the iterator `VergeRMatches` which wraps `RMatches`,
/// constructed via pattern-specialized string methods.
impl_iterator!(
    #[specialized_next_reverse_searcher]
    #[verifier::reject_recursive_types(P)]
    RMatches<'a, P> as VergeRMatches<'_, P> :: Item = &'a str
    where {
        P: Pattern,
    }
    ;

    [str as View<V=Seq<char>>] :: rmatches_ch_iter via rmatches
    (&self, ch: char) -> (iter: VergeRMatches<'_, char>)
    ensures {
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> #[trigger] iter.seq()[i]@ == seq![ch]
            &&& iter.seq().len() == self@.count(|c: char| c == ch)
        }
    ;

    [str as View<V=Seq<char>>] :: rmatches_chars_iter via rmatches <'b>
    (&self, chars: &'b [char]) -> (iter: VergeRMatches<'_, &'b [char]>)
    ensures {
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> #[trigger] iter.seq()[i]@.len() == 1
                        && chars@.contains(iter.seq()[i]@[0])
            &&& iter.seq().len() == self@.count(|c: char| chars@.contains(c))
        }
    ;

    [str as View<V=Seq<char>>] :: rmatches_fn_iter via rmatches <F>
    (&self, f: F) -> (iter: VergeRMatches<'_, F>)
    where {
    F: FnMut(char) -> bool
    }
    requires {
    is_deterministic(f) && is_total(f)
    }
    ensures {
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> #[trigger] iter.seq()[i]@.len() == 1
                        && call_ensures(f, (iter.seq()[i]@[0],), true)
            &&& iter.seq().len()
                    == self@.count(|c: char| call_ensures(f, (c,), true))
        }
    ;

    [str as View<V=Seq<char>>] :: rmatches_str_iter via rmatches <'b>
    (&self, pat: &'b str) -> (iter: VergeRMatches<'_, &'b str>)
    requires {
    pat@.len() > 0
    }
    ensures {
            &&& forall |i: int| 0 <= i < iter.seq().len()
                    ==> #[trigger] iter.seq()[i]@ == pat@
            &&& iter.seq().len() == 0 <==> !pat@.is_subrange_of(self@)
            &&& exists |gap: Seq<Seq<char>>| {
                &&& #[trigger] gap.len() == iter.seq().len() + 1
                &&& forall |i: int| #![trigger gap[i]]
                        0 <= i < gap.len() - 1
                        ==> gap[i].len() > 0
                            ==> !pat@.is_suffix_of(pat@ + gap[i])
                                && !pat@.is_infix_of(pat@ + gap[i])
                &&& !pat@.is_subrange_of(gap.last())
                &&& self@ == gap.last()
                    + iter.seq()
                        .map(|i: int, ss: &str| ss@ + gap[i])
                        .reverse()
                        .flatten()
            }
        }
    ;
);

/// Specifies `VergeRMatches` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RMatches as VergeRMatches ['a, P] :: Item = &'a str
        where
            P: Pattern,
);


/// Specifies the iterator `VergeMatchIndices` which wraps `MatchIndices`,
/// constructed via pattern-specialized string methods.
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    MatchIndices<'a, P> as VergeMatchIndices<'_, P> :: Item = (usize, &'a str)
    where {
    P: Pattern
    }
    ;

    [str as View<V=Seq<char>>] :: match_indices_ch_iter via match_indices
    (&self, ch: char) -> (iter: VergeMatchIndices<'_, char>)
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len()
                    ==> {
                        let (idx, ss) = iter.seq()[i];
                        let idx_ch = decode_utf8(self@.as_bytes().take(idx as int)).len() as int;
                        &&& ss@ == seq![ch]
                        &&& is_char_boundary(self@.as_bytes(), idx as int)
                            && idx < self@.as_bytes().len()
                        &&& ss@[0] == self@[idx_ch]
                    }
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i].0 < iter.seq()[i + 1].0
            &&& iter.seq().len() == self@.count(|c: char| c == ch)
        }
    ;

    [str as View<V=Seq<char>>] :: match_indices_chars_iter via match_indices <'b>
    (&self, chars: &'b [char]) -> (iter: VergeMatchIndices<'_, &'b [char]>)
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len()
                    ==> {
                        let (idx, ss) = iter.seq()[i];
                        let idx_ch = decode_utf8(self@.as_bytes().take(idx as int)).len() as int;
                        &&& ss@.len() == 1 && chars@.contains(ss@[0])
                        &&& is_char_boundary(self@.as_bytes(), idx as int)
                            && idx < self@.as_bytes().len()
                        &&& ss@[0] == self@[idx_ch]
                    }
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i].0 < iter.seq()[i + 1].0
            &&& iter.seq().len() == self@.count(|c: char| chars@.contains(c))
        }
    ;

    [str as View<V=Seq<char>>] :: match_indices_fn_iter via match_indices <F>
    (&self, f: F) -> (iter: VergeMatchIndices<'_, F>)
    where {
    F: FnMut(char) -> bool
    }
    requires {
    is_deterministic(f) && is_total(f)
    }
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len()
                    ==> {
                        let (idx, ss) = iter.seq()[i];
                        let idx_ch = decode_utf8(self@.as_bytes().take(idx as int)).len() as int;
                        &&& ss@.len() == 1
                            && call_ensures(f, (ss@[0],), true)
                        &&& is_char_boundary(self@.as_bytes(), idx as int)
                            && idx < self@.as_bytes().len()
                        &&& ss@[0] == self@[idx_ch]
                    }
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i].0 < iter.seq()[i + 1].0
            &&& iter.seq().len()
                    == self@.count(|c: char| call_ensures(f, (c,), true))
        }
    ;

    [str as View<V=Seq<char>>] :: match_indices_str_iter via match_indices <'b>
    (&self, pat: &'b str) -> (iter: VergeMatchIndices<'_, &'b str>)
    requires {
    pat@.len() > 0
    }
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len()
                    ==> {
                        let (idx, ss) = iter.seq()[i];
                        &&& ss@ == pat@
                        &&& is_char_boundary(self@.as_bytes(), idx as int)
                            && idx <= self@.as_bytes().len() - pat@.as_bytes().len()
                        &&& self@.as_bytes()
                            .subrange(idx as int, idx + pat@.as_bytes().len() as int)
                            == pat@.as_bytes()
                    }
            &&& iter.seq().len() == 0 <==> !pat@.is_subrange_of(self@)
            &&& exists |gap: Seq<Seq<char>>| {
                &&& #[trigger] gap.len() == iter.seq().len() + 1
                &&& forall |i: int| #![trigger gap[i]]
                        0 <= i < gap.len() - 1
                        ==> gap[i].len() > 0
                            ==> !pat@.is_prefix_of(gap[i] + pat@)
                                && !pat@.is_infix_of(gap[i] + pat@)
                &&& !pat@.is_subrange_of(gap.last())
                &&& self@ == iter.seq()
                    .map(|i: int, item: (usize, &str)| gap[i] + item.1@)
                    .flatten() + gap.last()
                &&& iter.seq().len() > 0
                    ==> iter.seq().first().0 == gap.first().as_bytes().len()
                &&& forall |i: int| #![trigger iter.seq()[i].0]
                        1 <= i < iter.seq().len()
                        ==> iter.seq()[i].0 == iter.seq()[i - 1].0
                            + pat@.as_bytes().len() + gap[i].as_bytes().len()
            }
        }
    ;
);

/// Specifies `VergeMatchIndices` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    MatchIndices as VergeMatchIndices ['a, P] :: Item = (usize, &'a str)
        where P: Pattern,
);


/// Specifies the iterator `VergeRMatchIndices` which wraps `RMatchIndices`,
/// constructed via pattern-specialized string methods.
impl_iterator!(
    #[specialized_next_reverse_searcher]
    #[verifier::reject_recursive_types(P)]
    RMatchIndices<'a, P> as VergeRMatchIndices<'_, P> :: Item = (usize, &'a str)
    where {
        P: Pattern,
    }
    ;

    [str as View<V=Seq<char>>] :: rmatch_indices_ch_iter via rmatch_indices
    (&self, ch: char) -> (iter: VergeRMatchIndices<'_, char>)
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len()
                    ==> {
                        let (idx, ss) = iter.seq()[i];
                        let idx_ch = decode_utf8(self@.as_bytes().take(idx as int)).len() as int;
                        &&& ss@ == seq![ch]
                        &&& is_char_boundary(self@.as_bytes(), idx as int)
                            && idx < self@.as_bytes().len()
                        &&& ss@[0] == self@[idx_ch]
                    }
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i].0 > iter.seq()[i + 1].0
            &&& iter.seq().len() == self@.count(|c: char| c == ch)
        }
    ;

    [str as View<V=Seq<char>>] :: rmatch_indices_chars_iter via rmatch_indices <'b>
    (&self, chars: &'b [char]) -> (iter: VergeRMatchIndices<'_, &'b [char]>)
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len()
                    ==> {
                        let (idx, ss) = iter.seq()[i];
                        let idx_ch = decode_utf8(self@.as_bytes().take(idx as int)).len() as int;
                        &&& ss@.len() == 1 && chars@.contains(ss@[0])
                        &&& is_char_boundary(self@.as_bytes(), idx as int)
                            && idx < self@.as_bytes().len()
                        &&& ss@[0] == self@[idx_ch]
                    }
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i].0 > iter.seq()[i + 1].0
            &&& iter.seq().len() == self@.count(|c: char| chars@.contains(c))
        }
    ;

    [str as View<V=Seq<char>>] :: rmatch_indices_fn_iter via rmatch_indices <F>
    (&self, f: F) -> (iter: VergeRMatchIndices<'_, F>)
    where {
    F: FnMut(char) -> bool
    }
    requires {
    is_deterministic(f) && is_total(f)
    }
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len()
                    ==> {
                        let (idx, ss) = iter.seq()[i];
                        let idx_ch = decode_utf8(self@.as_bytes().take(idx as int)).len() as int;
                        &&& ss@.len() == 1
                            && call_ensures(f, (ss@[0],), true)
                        &&& is_char_boundary(self@.as_bytes(), idx as int)
                            && idx < self@.as_bytes().len()
                        &&& ss@[0] == self@[idx_ch]
                    }
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len() - 1
                    ==> iter.seq()[i].0 > iter.seq()[i + 1].0
            &&& iter.seq().len()
                    == self@.count(|c: char| call_ensures(f, (c,), true))
        }
    ;

    [str as View<V=Seq<char>>] :: rmatch_indices_str_iter via rmatch_indices <'b>
    (&self, pat: &'b str) -> (iter: VergeRMatchIndices<'_, &'b str>)
    requires {
    pat@.len() > 0
    }
    ensures {
            &&& forall |i: int| #![trigger iter.seq()[i]]
                    0 <= i < iter.seq().len()
                    ==> {
                        let (idx, ss) = iter.seq()[i];
                        &&& ss@ == pat@
                        &&& is_char_boundary(self@.as_bytes(), idx as int)
                            && idx <= self@.as_bytes().len() - pat@.as_bytes().len()
                        &&& self@.as_bytes()
                            .subrange(idx as int, idx + pat@.as_bytes().len() as int)
                            == pat@.as_bytes()
                    }
            &&& iter.seq().len() == 0 <==> !pat@.is_subrange_of(self@)
            &&& exists |gap: Seq<Seq<char>>| {
                &&& #[trigger] gap.len() == iter.seq().len() + 1
                &&& forall |i: int| #![trigger gap[i]]
                        0 <= i < gap.len() - 1
                        ==> gap[i].len() > 0
                            ==> !pat@.is_suffix_of(pat@ + gap[i])
                                && !pat@.is_infix_of(pat@ + gap[i])
                &&& !pat@.is_subrange_of(gap.last())
                &&& self@ == gap.last()
                    + iter.seq()
                        .map(|i: int, item: (usize, &str)| item.1@ + gap[i])
                        .reverse()
                        .flatten()
                &&& iter.seq().len() > 0
                    ==> iter.seq().last().0 == gap.last().as_bytes().len()
                &&& forall |i: int| #![trigger iter.seq()[i].0]
                        0 <= i < iter.seq().len() - 1
                        ==> iter.seq()[i].0 == iter.seq()[i + 1].0
                            + pat@.as_bytes().len() + gap[i + 1].as_bytes().len()
            }
        }
    ;
);

/// Specifies `VergeRMatchIndices` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RMatchIndices as VergeRMatchIndices ['a, P] :: Item = (usize, &'a str)
        where
            P: Pattern,
);


/// Specifies the iterator `VergeBytes` which wraps `Bytes`,
/// contructed via `str::bytes_iter()`.
impl_iterator!(
    Bytes<'a> as VergeBytes<'_> :: Item = u8
    ;

    [str as View<V=Seq<char>>] :: bytes_iter via bytes
    (&self,) -> (iter: VergeBytes<'_>)
    ensures {
            iter.seq() == self@.as_bytes()
        }
    ;
);

/// Specifies the iterator `VergeBytes` as a double-ended iterator.
impl_double_ended_iterator!(
    Bytes as VergeBytes ['a] :: Item = u8
);

/// Specifies the iterator `VergeCharIndices` which wraps `CharIndices`,
/// contructed via `str::char_indices_iter()`.
impl_iterator!(
    CharIndices<'a> as VergeCharIndices<'_> :: Item = (usize, char)
    ;

    [str as View<V=Seq<char>>] :: char_indices_iter via char_indices
    (&self,) -> (iter: VergeCharIndices<'_>)
    ensures {
            iter.seq() == self@.map(|i: int, c: char| (self@.take(i).as_bytes().len() as usize, c))
        }
    ;
);

/// Specifies the iterator `VergeCharIndices` as a double-ended iterator.
impl_double_ended_iterator!(
    CharIndices as VergeCharIndices ['a] :: Item = (usize, char)
);

/// Specifies the iterator `VergeLines` which wraps `Lines`,
/// contructed via `str::lines_iter()`.
impl_iterator!(
    Lines<'a> as VergeLines<'_> :: Item = &'a str
    ;

    [str as View<V=Seq<char>>] :: lines_iter via lines
    (&self,) -> (iter: VergeLines<'_>)
    ensures {
            // lines cannot have `\n`
            &&& forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                    forall |j: int| #![trigger iter.seq()[i]@[j]] 0 <= j < iter.seq()[i]@.len() ==>
                        !(iter.seq()[i]@[j] == '\n')
            &&& exists |nls: Seq<Seq<char>>| #![trigger nls.len()] {
                &&& nls.len() == iter.seq().len() || nls.len() + 1 == iter.seq().len()
                &&& nls.len() + 1 == iter.seq().len() ==> iter.seq().last()@.len() > 0
                // delimeters are all `\n` or `\r\n`
                &&& forall |j: int| #![trigger nls[j]] 0 <= j < nls.len() ==> {
                    &&& nls[j] == seq!['\n'] || nls[j] == seq!['\r', '\n'] || (j == nls.len() - 1 && nls[j].len() == 0 )
                    &&& nls[j] == seq!['\n'] ==> !seq!['\r'].is_suffix_of(iter.seq()[j]@)
                }
                // delimeters and lines make up the original string
                &&& self@ =~= join(Seq::new(iter.seq().len(), |j: int| iter.seq()[j]@) + seq![Seq::<char>::empty()], nls)
            }
        }
    ;
);

/// Specifies the iterator `VergeLines` as a double-ended iterator.
impl_double_ended_iterator!(
    Lines as VergeLines ['a] :: Item = &'a str
);

/// Specifies the iterator `VergeSplitWhitespace` which wraps `SplitWhitespace`, 
/// contructed via `str::split_whitespace_iter()`.
impl_iterator!(
    SplitWhitespace<'a> as VergeSplitWhitespace<'_> :: Item = &'a str
    ;

    [str as View<V=Seq<char>>] :: split_whitespace_iter via split_whitespace
    (&self,) -> (iter: VergeSplitWhitespace<'_>)
    ensures {
            // splits are non-empty
            &&& forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                    iter.seq()[i]@.len() > 0
            // splits cannot have whitespaces
            &&& forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                    forall |j: int| #![trigger iter.seq()[i]@[j]] 0 <= j < iter.seq()[i]@.len() ==>
                        !vstd::std_specs::char::is_white_space(iter.seq()[i]@[j])
            &&& exists |sps: Seq<Seq<char>>| #![trigger sps.len()] {
                &&& sps.len() == iter.seq().len() + 1
                // delimeters are all whitespaces
                &&& forall |i: int| #![trigger sps[i]] 0 <= i < sps.len() ==>
                        forall |j: int| #![trigger sps[i][j]] 0 <= j < sps[i].len() ==>
                            vstd::std_specs::char::is_white_space(sps[i][j])
                &&& forall |i: int| #![trigger sps[i]] 1 <= i < sps.len() - 1 ==>
                        sps[i].len() > 0
                // delimeters and lines make up the original string
                &&& self@ =~= join(Seq::new(iter.seq().len(), |j: int| iter.seq()[j]@), sps)
            }
        }
    ;
);

/// Specifies the iterator `VergeSplitWhitespace` as a double-ended iterator.
impl_double_ended_iterator!(
    SplitWhitespace as VergeSplitWhitespace ['a] :: Item = &'a str
);

/// Specifies the iterator `VergeSplitAsciiWhitespace` which wraps `SplitAsciiWhitespace`, 
/// contructed via `str::split_ascii_whitespace_iter()`.
impl_iterator!(
    SplitAsciiWhitespace<'a> as VergeSplitAsciiWhitespace<'_> :: Item = &'a str
    ;

    [str as View<V=Seq<char>>] :: split_ascii_whitespace_iter via split_ascii_whitespace
    (&self,) -> (iter: VergeSplitAsciiWhitespace<'_>)
    ensures {
            // splits are non-empty
            &&& forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                    iter.seq()[i]@.len() > 0
            // splits cannot have ASCII whitespaces
            &&& forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                    forall |j: int| #![trigger iter.seq()[i]@[j]] 0 <= j < iter.seq()[i]@.len() ==>
                        !iter.seq()[i]@[j].is_ascii_whitespace()
            &&& exists |sps: Seq<Seq<char>>| #![trigger sps.len()] {
                &&& sps.len() == iter.seq().len() + 1
                // delimeters are all ASCII whitespaces
                &&& forall |i: int| #![trigger sps[i]] 0 <= i < sps.len() ==>
                        forall |j: int| #![trigger sps[i][j]] 0 <= j < sps[i].len() ==>
                            sps[i][j].is_ascii_whitespace()
                &&& forall |i: int| #![trigger sps[i]] 1 <= i < sps.len() - 1 ==>
                        sps[i].len() > 0
                // delimeters and lines make up the original string
                &&& self@ =~= join(Seq::new(iter.seq().len(), |j: int| iter.seq()[j]@), sps)
            }
        }
    ;
);

/// Specifies the iterator `VergeSplitAsciiWhitespace` as a double-ended iterator.
impl_double_ended_iterator!(
    SplitAsciiWhitespace as VergeSplitAsciiWhitespace ['a] :: Item = &'a str
);

} // verus!
