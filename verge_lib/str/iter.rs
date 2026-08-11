//! Iterator methods and types for strings.

#![allow(unused_imports)]
use super::*;
use crate::iter::*;
use crate::str::pattern::*;
use vstd::std_specs::iter::*;

use std::str::{
    Bytes, CharIndices, Lines, 
    Split, SplitInclusive, SplitTerminator, SplitN,
    RSplit, RSplitTerminator, RSplitN, 
    Matches, RMatches, MatchIndices, RMatchIndices,
    SplitWhitespace, SplitAsciiWhitespace, 
    pattern::{
        Pattern, Searcher, ReverseSearcher, DoubleEndedSearcher,
    }
};

verus! {

/// Specifies the iterator `VergeBytes` which wraps `Bytes`, 
/// contructed via `str::bytes_iter()`.
impl_iterator!(
    [ Bytes['a] as VergeBytes['_] :: Item = u8 ]
    [ [str as View<V=Seq<char>>] :: bytes_iter via bytes ] 
    (&self,) -> |iter| {
        iter.seq() == self@.as_bytes()
    } 
);

/// Specifies the iterator `VergeBytes` as a double-ended iterator.
impl_double_ended_iterator!(
    Bytes as VergeBytes ['a] :: Item = u8
);

/// Specifies the iterator `VergeCharIndices` which wraps `CharIndices`, 
/// contructed via `str::char_indices_iter()`.
impl_iterator!(
    [ CharIndices['a] as VergeCharIndices['_] :: Item = (usize, char) ]
    [ [str as View<V=Seq<char>>] :: char_indices_iter via char_indices ] 
    (&self,) -> |iter| {
        iter.seq() == self@.map(|i: int, c: char| (self@.take(i).as_bytes().len() as usize, c))
    } 
);

/// Specifies the iterator `VergeCharIndices` as a double-ended iterator.
impl_double_ended_iterator!(
    CharIndices as VergeCharIndices ['a] :: Item = (usize, char)
);

/// Specifies the iterator `VergeLines` which wraps `Lines`, 
/// contructed via `str::lines_iter()`.
impl_iterator!(
    [ Lines['a] as VergeLines['_] :: Item = &'a str ]
    [ [str as View<V=Seq<char>>] :: lines_iter via lines ] 
    (&self,) -> |iter| {
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
);

/// Specifies the iterator `VergeLines` as a double-ended iterator.
impl_double_ended_iterator!(
    Lines as VergeLines ['a] :: Item = &'a str
);

/// Specifies the iterator `VergeSplit` which wraps `Split`, 
/// contructed via `str::split_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ Split['a, P] as VergeSplit['_, P] :: Item = &'a str 
        where P: Pattern, 
    ] [ [str as View<V=Seq<char>>] :: split_iter via split ] 
    (&self, pat: P) -> |iter| {
        str_split_iter_post(self@, pat, iter.seq())
    }
);

/// Specifies the iterator `VergeSplit` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    Split as VergeSplit ['a, P] :: Item = &'a str
        where P: Pattern, 
);

/// Specifies the iterator `VergeSplitInclusive` which wraps `SplitInclusive`, 
/// contructed via `str::split_inclusive_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ SplitInclusive['a, P] as VergeSplitInclusive['_, P] :: Item = &'a str
        where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: split_inclusive_iter via split_inclusive
    ] (&self, pat: P) -> |iter| {
        str_split_inclusive_iter_post(self@, pat, iter.seq())
    }
);

/// Specifies the iterator `VergeSplitInclusive` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    SplitInclusive as VergeSplitInclusive ['a, P] :: Item = &'a str
        where P: Pattern, 
);

/// Specifies the iterator `VergeRSplit` which wraps `RSplit`, 
/// contructed via `str::rsplit_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ RSplit['a, P] as VergeRSplit['_, P] :: Item = &'a str 
        where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: rsplit_iter via rsplit 
        where for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ] 
    #[specialized_next(<P as Pattern>::Searcher<'a>: ReverseSearcher<'a>)]
    (&self, pat: P) -> |iter| {
        str_rsplit_iter_post(self@, pat, iter.seq())
    }
);

/// Specifies the iterator `VergeRSplit` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RSplit as VergeRSplit ['a, P] :: Item = &'a str
        where P: Pattern, 
);

/// Specifies the iterator `VergeSplitTerminator` which wraps `SplitTerminator`, 
/// contructed via `str::split_terminator_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ SplitTerminator['a, P] as VergeSplitTerminator['_, P] :: Item = &'a str
        where P: Pattern, 
    ] [ [str as View<V=Seq<char>>] :: split_terminator_iter via split_terminator
    ] (&self, pat: P) -> |iter| {
        str_split_terminator_iter_post(self@, pat, iter.seq())
    }
);

/// Specifies the iterator `VergeSplitTerminator` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    SplitTerminator as VergeSplitTerminator ['a, P] :: Item = &'a str
        where P: Pattern, 
);

/// Specifies the iterator `VergeRSplitTerminator` which wraps `RSplitTerminator`, 
/// contructed via `str::rsplit_terminator_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ RSplitTerminator['a, P] as VergeRSplitTerminator['_, P] :: Item = &'a str 
        where P: Pattern,
    ] [ [str as View<V=Seq<char>>] :: rsplit_terminator_iter via rsplit_terminator 
        where for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ] 
    #[specialized_next(<P as Pattern>::Searcher<'a>: ReverseSearcher<'a>)]
    (&self, pat: P) -> |iter| {
        str_rsplit_terminator_iter_post(self@, pat, iter.seq())
    }
);

/// Specifies the iterator `VergeRSplitTerminator` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RSplitTerminator as VergeRSplitTerminator ['a, P] :: Item = &'a str
        where P: Pattern, 
);

/// Specifies the iterator `VergeSplitN` which wraps `SplitN`, 
/// contructed via `str::splitn_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ SplitN['a, P] as VergeSplitN['_, P] :: Item = &'a str
        where P: Pattern, 
    ] [ [str as View<V=Seq<char>>] :: splitn_iter via splitn
    ] (&self, n: usize, pat: P) -> |iter| {
        str_splitn_iter_post(self@, n, pat, iter.seq())
    }
);

/// Specifies the iterator `VergeRSplitN` which wraps `RSplitN`, 
/// contructed via `str::rsplitn_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ RSplitN['a, P] as VergeRSplitN['_, P] :: Item = &'a str
        where P: Pattern, 
    ] [ [str as View<V=Seq<char>>] :: rsplitn_iter via rsplitn
        where for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ] 
    #[specialized_next(<P as Pattern>::Searcher<'a>: ReverseSearcher<'a>)]
    (&self, n: usize, pat: P) -> |iter| {
        str_rsplitn_iter_post(self@, n, pat, iter.seq())
    }
);

/// Specifies the iterator `VergeMatches` which wraps `Matches`, 
/// contructed via `str::matches_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ Matches['a, P] as VergeMatches['_, P] :: Item = &'a str 
        where P: Pattern, 
    ] [ [str as View<V=Seq<char>>] :: matches_iter via matches ] 
    (&self, pat: P) -> |iter| {
        str_matches_iter_post(self@, pat, iter.seq())
    }
);

/// Specifies the iterator `VergeMatches` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    Matches as VergeMatches ['a, P] :: Item = &'a str
        where P: Pattern, 
);

/// Specifies the iterator `VergeRMatches` which wraps `RMatches`, 
/// contructed via `str::rmatches_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ RMatches['a, P] as VergeRMatches['_, P] :: Item = &'a str 
        where P: Pattern, 
    ] [ [str as View<V=Seq<char>>] :: rmatches_iter via rmatches 
        where for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ] 
    #[specialized_next(<P as Pattern>::Searcher<'a>: ReverseSearcher<'a>)]
    (&self, pat: P) -> |iter| {
        str_rmatches_iter_post(self@, pat, iter.seq())
    }
);

/// Specifies the iterator `VergeRMatches` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RMatches as VergeRMatches ['a, P] :: Item = &'a str
        where P: Pattern, 
);

/// Specifies the iterator `VergeMatchIndices` which wraps `MatchIndices`, 
/// contructed via `str::match_indices_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ MatchIndices['a, P] as VergeMatchIndices['_, P] :: Item = (usize, &'a str)
        where P: Pattern, 
    ] [ [str as View<V=Seq<char>>] :: match_indices_iter via match_indices ] 
    (&self, pat: P) -> |iter| {
        str_match_indices_iter_post(self@, pat, iter.seq())
    }
);

/// Specifies the iterator `VergeMatchIndices` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    MatchIndices as VergeMatchIndices ['a, P] :: Item = (usize, &'a str)
        where P: Pattern, 
);

/// Specifies the iterator `VergeRMatchIndices` which wraps `RMatchIndices`, 
/// contructed via `str::rmatch_indices_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    [ RMatchIndices['a, P] as VergeRMatchIndices['_, P] :: Item = (usize, &'a str)
        where P: Pattern, 
    ] [ [str as View<V=Seq<char>>] :: rmatch_indices_iter via rmatch_indices
        where for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ] 
    #[specialized_next(<P as Pattern>::Searcher<'a>: ReverseSearcher<'a>)]
    (&self, pat: P) -> |iter| {
        str_rmatch_indices_iter_post(self@, pat, iter.seq())
    }
);

/// Specifies the iterator `VergeRMatchIndices` as a double-ended iterator.
impl_double_ended_iterator!(
    #[specialized_next(<P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>)]
    RMatchIndices as VergeRMatchIndices ['a, P] :: Item = (usize, &'a str)
        where P: Pattern, 
);

/// Specifies the iterator `VergeSplitWhitespace` which wraps `SplitWhitespace`, 
/// contructed via `str::split_whitespace_iter()`.
impl_iterator!(
    [ SplitWhitespace['a] as VergeSplitWhitespace['_] :: Item = &'a str ]
    [ [str as View<V=Seq<char>>] :: split_whitespace_iter via split_whitespace ] 
    (&self,) -> |iter| {
        // splits are non-empty
        &&& forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                iter.seq()[i]@.len() > 0
        // splits cannot have whitespaces
        &&& forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                forall |j: int| #![trigger iter.seq()[i]@[j]] 0 <= j < iter.seq()[i]@.len() ==>
                    !iter.seq()[i]@[j].is_whitespace()
        &&& exists |sps: Seq<Seq<char>>| #![trigger sps.len()] {
            &&& sps.len() == iter.seq().len() + 1
            // delimeters are all whitespaces
            &&& forall |i: int| #![trigger sps[i]] 0 <= i < sps.len() ==>
                    forall |j: int| #![trigger sps[i][j]] 0 <= j < sps[i].len() ==>
                        sps[i][j].is_whitespace()
            &&& forall |i: int| #![trigger sps[i]] 1 <= i < sps.len() - 1 ==>
                    sps[i].len() > 0
            // delimeters and lines make up the original string
            &&& self@ =~= join(Seq::new(iter.seq().len(), |j: int| iter.seq()[j]@), sps)
        }
    }
);

/// Specifies the iterator `VergeSplitWhitespace` as a double-ended iterator.
impl_double_ended_iterator!(
    SplitWhitespace as VergeSplitWhitespace ['a] :: Item = &'a str
);

/// Specifies the iterator `VergeSplitAsciiWhitespace` which wraps `SplitAsciiWhitespace`, 
/// contructed via `str::split_ascii_whitespace_iter()`.
impl_iterator!(
    [ SplitAsciiWhitespace['a] as VergeSplitAsciiWhitespace['_] :: Item = &'a str ]
    [ [str as View<V=Seq<char>>] :: split_ascii_whitespace_iter via split_ascii_whitespace ] 
    (&self,) -> |iter| {
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
);

/// Specifies the iterator `VergeSplitAsciiWhitespace` as a double-ended iterator.
impl_double_ended_iterator!(
    SplitAsciiWhitespace as VergeSplitAsciiWhitespace ['a] :: Item = &'a str
);



} // verus!
