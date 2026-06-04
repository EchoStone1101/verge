//! Specifications and lemmas for string pattern related operations.
//!
//! ## Specification Methodology
//! To specify `str::split`, `str::contains`, and other methods that make use of 
//! the `std::str::Pattern` trait, Verge directly models the `Pattern` trait by
//! adding the core specs (`matches` and `rmatches`) as extension to the trait, 
//! which are used to derive the general post-condition specs (e.g., `str_contains_post`) 
//! regardless of the pattern type. Then, broadcast lemmas use the general 
//! specs as triggers to automatically introduce actual specs per pattern type 
//! (e.g., `lemma_str_contains_str` for `&str` patterns, `lemma_str_contains_char` 
//! for `char` patterns). This design minimizes both spec redundancy and user burden.

use super::*;
use crate::seq::*;
use crate::iter::*;
use std::str::pattern::*;

verus! {

/// Enables `std::str::pattern::Pattern`.
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(PatternSpec via PatternSpecImpl)]
pub trait ExPattern: Sized {
    type ExternalTraitSpecificationFor: Pattern;

    /// Post-conditions for forward matching using this pattern.
    /// 
    /// Semantically, this function specifies the uninterpreted spec function `spec_matches`,
    /// where the matches are captured as `seq` and the delimiters are captured as `gap`.
    /// Other forward pattern-matching methods receive specs derived from this.
    spec fn matches_post(self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>) -> bool;

    /// Post-conditions for backward matching using this pattern.
    /// 
    /// Semantically, this function specifies the uninterpreted spec function `spec_rmatches`, 
    /// where the matches are captured as `seq` and the delimiters are captured as `gap`.
    /// Other backward pattern-matching methods receive specs derived from this.
    spec fn rmatches_post(self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>) -> bool;
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

// ---------- Inline helper specs ----------
// These exist purely for deduplicating shared specs.

/// Forward joining `seq` and `gap`.
#[verifier::inline]
pub open spec fn join(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>) -> Seq<char>
    recommends
        seq.len() + 1 == gap.len(),
{
    gap.first()
    + gap
        .drop_first()
        .map(|i: int, ss: Seq<char>| seq[i] + ss)
        .flatten()
}

/// Backward joining `seq` and `gap`.
#[verifier::inline]
pub open spec fn rjoin(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>) -> Seq<char>
    recommends
        seq.len() + 1 == gap.len(),
{
    gap
        .drop_first()
        .map(|i: int, ss: Seq<char>| ss + seq[i])
        .reverse()
        .flatten()
    + gap.first()
}

/// Post-conditions for matching by the `char` pattern, aside from the joining.
#[verifier::inline]
pub open spec fn char_matches_post(
    s: Seq<char>, c: char, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
) -> bool 
{
    // gaps are never empty
    &&& gap.len() > 0
    // gaps cannot contain the pattern
    &&& forall |i: int| 0 <= i < gap.len() ==> !(#[trigger] gap[i].contains(c))
    // matches have one item less than gaps
    &&& seq.len() + 1 == gap.len() 
    // matches match the pattern
    &&& forall |i: int| 0 <= i < seq.len() ==> #[trigger] (seq[i] =~= seq![c])
}

/// Post-conditions for matching by the closure pattern, aside from the joining.
#[verifier::inline]
pub open spec fn closure_matches_post<F>(
    s: Seq<char>, f: F, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
) -> bool 
where F: FnMut(char) -> bool
{
    // gaps are never empty
    &&& gap.len() > 0
    // gaps cannot contain the pattern
    &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() ==> 
        gap[i].all(|c: char| call_ensures(f, (c,), false))
    // matches have one item less than gaps
    &&& seq.len() + 1 == gap.len() 
    // matches match the pattern
    &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> 
        seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true)
}

/// Post-conditions for matching by the char slice pattern, aside from the joining.
#[verifier::inline]
pub open spec fn chars_matches_post(
    s: Seq<char>, chars: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
) -> bool 
{
    // gaps are never empty
    &&& gap.len() > 0
    // gaps cannot contain the pattern
    &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() ==> 
        chars.all(|c: char| !gap[i].contains(c))
    // matches have one item less than gaps
    &&& seq.len() + 1 == gap.len() 
    // matches match the pattern
    &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> 
        chars.any(|c: char| seq[i] == seq![c])
}

/// Post-conditions for matching by the empty string pattern, aside from the joining.
#[verifier::inline]
pub open spec fn empty_string_matches_post(
    s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
) -> bool 
{
    // "ab..z" => gap = ["", "a", "b", ..., "z", ""]
    &&& seq.len() == s.len() + 1
    &&& gap.len() == s.len() + 2
    &&& forall |i: int| 0 <= i < seq.len() ==> 
        #[trigger] seq[i].len() == 0
    &&& gap.first().len() == 0 && gap.last().len() == 0
    &&& forall |i: int| 1 <= i < gap.len() - 1 ==> 
        #[trigger] gap[i] == seq![s[i-1]]
}

/// Post-conditions for forward matching by the string pattern, aside from the joining.
#[verifier::inline]
pub open spec fn string_matches_post(
    s: Seq<char>, pat: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
) -> bool 
{
    // corner case: empty string matching 
    &&& pat.len() == 0 ==> empty_string_matches_post(s, seq, gap)
    // general matching
    &&& pat.len() > 0 ==> {
        // gaps are never empty
        &&& gap.len() > 0
        // `gap + pat` (apart from the last) cannot have `pat` as a prefix or infix
        &&& forall |i: int| 0 <= i < gap.len() - 1 ==> 
            !(#[trigger] pat.is_prefix_of(gap[i] + pat) || #[trigger] pat.is_infix_of(gap[i] + pat))
        // last gap cannot have `pat` as a substring
        &&& !(pat.is_subrange_of(gap.last()))
        // matches have one item less than gaps
        &&& seq.len() + 1 == gap.len() 
        // matches match the pattern
        &&& forall |i: int| 0 <= i < seq.len() ==> #[trigger] (seq[i] =~= pat)
    }
}

/// Post-conditions for backward matching by the string pattern, aside from the joining.
#[verifier::inline]
pub open spec fn string_rmatches_post(
    s: Seq<char>, pat: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
) -> bool 
{
    // corner case: empty string matching 
    &&& pat.len() == 0 ==> empty_string_matches_post(s, seq, gap)
    // general matching
    &&& pat.len() > 0 ==> {
        // gaps are never empty, and there are at most `n` splits
        &&& gap.len() > 0
        // `pat + gap` (apart from the last) cannot have `pat` as a suffix or infix
        &&& forall |i: int| 0 <= i < gap.len() - 1 ==> 
            !(#[trigger] pat.is_suffix_of(pat + gap[i]) || #[trigger] pat.is_infix_of(pat + gap[i]))
        // last gap cannot have `pat` as a substring
        &&& !(pat.is_subrange_of(gap.last()))
        // matches have one item less than gaps
        &&& seq.len() + 1 == gap.len() 
        // matches match the pattern
        &&& forall |i: int| 0 <= i < seq.len() ==> #[trigger] (seq[i] =~= pat)
    }
}

// ---------- Trigger specs ----------
// These exist as triggers for the per-type lemmas.

/// Encodes forward matching `s` by the general pattern `pat`,
/// returning the matches and gaps.
pub uninterp spec fn spec_matches<P: Pattern>(s: Seq<char>, pat: P) -> (Seq<Seq<char>>, Seq<Seq<char>>);

/// Encodes backward matching `s` by the general pattern `pat`,
/// returning the matches and gaps.
pub uninterp spec fn spec_rmatches<P: Pattern>(s: Seq<char>, pat: P) -> (Seq<Seq<char>>, Seq<Seq<char>>);

/// Encodes `str::contains` for general patterns.
#[verifier::opaque]
pub open spec fn str_contains_post<P: Pattern>(s: Seq<char>, pat: P, ret: bool) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        ret == (seq.len() > 0)
    }
}

/// Encodes `str::starts_with` for general patterns.
#[verifier::opaque]
pub open spec fn str_starts_with_post<P: Pattern>(s: Seq<char>, pat: P, ret: bool) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        ret == (seq.len() > 0 && gap.first().len() == 0)
    }
}

/// Encodes `str::ends_with` for general patterns.
#[verifier::opaque]
pub open spec fn str_ends_with_post<P>(s: Seq<char>, pat: P, ret: bool) -> bool 
    where 
        P: Pattern,
        for<'b> <P as Pattern>::Searcher<'b>: ReverseSearcher<'b>,
{
    let (seq, gap) = spec_rmatches(s, pat);
    pat.rmatches_post(s, seq, gap) ==> {
        ret == (seq.len() > 0 && gap.first().len() == 0)
    }
}

/// Encodes `str::find` for general patterns.
#[verifier::opaque]
pub open spec fn str_find_post<P: Pattern>(s: Seq<char>, pat: P, ret: Option<usize>) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        &&& ret is None ==> seq.len() == 0
        &&& ret is Some ==> 
            seq.len() > 0 
            && ret->0 == gap.first().as_bytes().len()
    }
}

/// Encodes `str::rfind` for general patterns.
#[verifier::opaque]
pub open spec fn str_rfind_post<P>(s: Seq<char>, pat: P, ret: Option<usize>) -> bool 
    where 
        P: Pattern,
        for<'a> <P as Pattern>::Searcher<'a>: ReverseSearcher<'a>,
{
    let (seq, gap) = spec_matches(s, pat);
    pat.rmatches_post(s, seq, gap) ==> {
        &&& ret is None ==> seq.len() == 0
        &&& ret is Some ==> 
            seq.len() > 0 
            && ret->0 == s.as_bytes().len() - gap.first().as_bytes().len() - seq.first().as_bytes().len()
    }
}

/// Encodes `str::split_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_iter_post<'a, P: Pattern>(s: Seq<char>, pat: P, iter_seq: Seq<&'a str>) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        &&& iter_seq.len() == gap.len()
        &&& forall |i: int| 0 <= i < iter_seq.len() ==>
                #[trigger] iter_seq[i]@ == gap[i]
    }
}

/// Encodes `str::split_inclusive_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_inclusive_iter_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, iter_seq: Seq<&'a str>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        &&& forall |i: int| 0 <= i < seq.len() ==>
            #[trigger] iter_seq[i]@ == gap[i] + seq[i]
        &&& gap.last().len() == 0 ==> iter_seq.len() == seq.len()
        &&& gap.last().len() > 0 ==> 
            iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last()
    }
}

/// Encodes `str::rsplit_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_rsplit_iter_post<'a, P>(s: Seq<char>, pat: P, iter_seq: Seq<&'a str>) -> bool 
where 
    P: Pattern,
    <P as Pattern>::Searcher<'a>: ReverseSearcher<'a>,
{
    let (seq, gap) = spec_rmatches(s, pat);
    pat.rmatches_post(s, seq, gap) ==> {
        &&& iter_seq.len() == gap.len()
        &&& forall |i: int| 0 <= i < iter_seq.len() ==>
                #[trigger] iter_seq[i]@ == gap[i]
    }
}

/// Encodes `str::split_terminator_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_terminator_iter_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, iter_seq: Seq<&'a str>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        &&& forall |i: int| 0 <= i < seq.len() ==>
            #[trigger] iter_seq[i]@ == gap[i]
        &&& gap.last().len() == 0 ==> iter_seq.len() == seq.len()
        &&& gap.last().len() > 0 ==> 
            iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last()
    }
}

/// Encodes `str::rsplit_terminator_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_rsplit_terminator_iter_post<'a, P>(
    s: Seq<char>, pat: P, iter_seq: Seq<&'a str>,
) -> bool 
where
    P: Pattern,
    for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
{
    let (seq, gap) = spec_rmatches(s, pat);
    pat.rmatches_post(s, seq, gap) ==> {
        &&& forall |i: int| 0 <= i < seq.len() ==>
            #[trigger] iter_seq[i]@ == gap[i]
        &&& gap.last().len() == 0 ==> iter_seq.len() == seq.len()
        &&& gap.last().len() > 0 ==> 
            iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last()
    }
}

/// Encodes `str::splitn_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_splitn_iter_post<'a, P: Pattern>(
    s: Seq<char>, n: usize, pat: P, iter_seq: Seq<&'a str>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        &&& iter_seq.len() == n 
        &&& forall |i: int| 0 <= i < n - 1 ==>
            #[trigger] iter_seq[i]@ == gap[i]
        &&& n > 0 ==> iter_seq.last()@ =~= join(seq.skip((n - 1) as int), gap.skip((n - 1) as int))
    }
}

/// Encodes `str::rsplitn_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_rsplitn_iter_post<'a, P>(
    s: Seq<char>, n: usize, pat: P, iter_seq: Seq<&'a str>,
) -> bool 
where
    P: Pattern,
    for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
{
    let (seq, gap) = spec_rmatches(s, pat);
    pat.rmatches_post(s, seq, gap) ==> {
        &&& iter_seq.len() == n 
        &&& forall |i: int| 0 <= i < n - 1 ==>
            #[trigger] iter_seq[i]@ == gap[i]
        &&& n > 0 ==> iter_seq.last()@ =~= rjoin(seq.skip((n - 1) as int), gap.skip((n - 1) as int))
    }
}

/// Encodes `str::split_once` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_once_post<'a, P: Pattern>(
    s: Seq<char>, delimiter: P, ret: Option<(&'a str, &'a str)>,
) -> bool {
    let (seq, gap) = spec_matches(s, delimiter);
    delimiter.matches_post(s, seq, gap) ==> {
        &&& ret is None ==> seq.len() == 0
        &&& ret is Some ==> {
            let (head, tail) = ret->0;
            &&& seq.len() > 0
            &&& head@ == gap.first()
            &&& tail@ =~= join(seq.skip(1), gap.skip(1))
        }
    }
}

/// Encodes `str::rsplit_once` for general patterns.
#[verifier::opaque]
pub open spec fn str_rsplit_once_post<'a, P>(
    s: Seq<char>, delimiter: P, ret: Option<(&'a str, &'a str)>,
) -> bool 
where
    P: Pattern,
    for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
{
    let (seq, gap) = spec_rmatches(s, delimiter);
    delimiter.rmatches_post(s, seq, gap) ==> {
        &&& ret is None ==> seq.len() == 0
        &&& ret is Some ==> {
            let (head, tail) = ret->0;
            &&& seq.len() > 0
            &&& head@ == gap.first()
            &&& tail@ =~= rjoin(seq.skip(1), gap.skip(1))
        }
    }
}

/// Encodes `str::split_whitespace_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_whitespace_iter_post<'a>(
    s: Seq<char>, iter_seq: Seq<&'a str>,
) -> bool {
    let pat = |c: char| c.is_whitespace();
    let (seq, gap) = spec_matches(s, pat);
    PatternSpec::matches_post(pat, s, seq, gap) ==> {
        &&& iter_seq.len() == gap.count(|seg: Seq<char>| seg.len() > 0)
        &&& forall |i: int| 0 <= i < iter_seq.len() ==>
                #[trigger] iter_seq[i]@ == gap.filter(|seg: Seq<char>| seg.len() > 0)[i]
    }
}

/// Encodes `str::split_ascii_whitespace_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_ascii_whitespace_iter_post<'a>(
    s: Seq<char>, iter_seq: Seq<&'a str>,
) -> bool {
    let pat = |c: char| c.is_ascii_whitespace();
    let (seq, gap) = spec_matches(s, pat);
    PatternSpec::matches_post(pat, s, seq, gap) ==> {
        &&& iter_seq.len() == gap.count(|seg: Seq<char>| seg.len() > 0)
        &&& forall |i: int| 0 <= i < iter_seq.len() ==>
                #[trigger] iter_seq[i]@ == gap.filter(|seg: Seq<char>| seg.len() > 0)[i]
    }
}

/// Encodes `str::matches_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_matches_iter_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, iter_seq: Seq<&'a str>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        &&& iter_seq.len() == seq.len()
        &&& forall |i: int| 0 <= i < iter_seq.len() ==>
                #[trigger] iter_seq[i]@ == seq[i]
    }
}

/// Encodes `str::rmatches_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_rmatches_iter_post<'a, P>(
    s: Seq<char>, pat: P, iter_seq: Seq<&'a str>,
) -> bool 
where 
    P: Pattern,
    <P as Pattern>::Searcher<'a>: ReverseSearcher<'a>,
{
    let (seq, gap) = spec_rmatches(s, pat);
    pat.rmatches_post(s, seq, gap) ==> {
        &&& iter_seq.len() == seq.len()
        &&& forall |i: int| 0 <= i < iter_seq.len() ==>
                #[trigger] iter_seq[i]@ == seq[i]
    }
}

/// Encodes `str::match_indices_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_match_indices_iter_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, iter_seq: Seq<(usize, &'a str)>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        &&& iter_seq.len() == seq.len()
        &&& forall |i: int| 0 <= i < iter_seq.len() ==>
                #[trigger] iter_seq[i].0 == join(seq.take(i), gap.take(i + 1)).as_bytes().len()
                && #[trigger] iter_seq[i].1@ == seq[i]
    }
}

/// Encodes `str::rmatch_indices_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_rmatch_indices_iter_post<'a, P>(
    s: Seq<char>, pat: P, iter_seq: Seq<(usize, &'a str)>,
) -> bool 
where 
    P: Pattern,
    <P as Pattern>::Searcher<'a>: ReverseSearcher<'a>,
{
    let (seq, gap) = spec_rmatches(s, pat);
    pat.rmatches_post(s, seq, gap) ==> {
        &&& iter_seq.len() == seq.len()
        &&& forall |i: int| 0 <= i < iter_seq.len() ==>
                #[trigger] iter_seq[i].0 == 
                    s.as_bytes().len() - join(seq.take(i), gap.take(i + 1)).as_bytes().len()
                && #[trigger] iter_seq[i].1@ == seq[i]
    }
}

/// Encodes `str::trim_matches` for general patterns.
#[verifier::opaque]
pub open spec fn str_trim_matches_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, ret: Seq<char>,
) -> bool 
where 
    P: Pattern,
    <P as Pattern>::Searcher<'a>: DoubleEndedSearcher<'a>,
{
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        if gap.all(|ss: Seq<char>| ss.len() == 0) {
            ret.len() == 0
        } else {
            let head = gap.count_while(|ss: Seq<char>| ss.len() == 0);
            let tail = gap.rcount_while(|ss: Seq<char>| ss.len() == 0);
            ret == join(
                seq.subrange(head as int, seq.len() - tail), 
                gap.subrange(head as int, gap.len() - tail),
            )
        }
    }
}

/// Encodes `str::trim_start_matches` for general patterns.
#[verifier::opaque]
pub open spec fn str_trim_start_matches_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, ret: Seq<char>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        let head = gap.count_while(|ss: Seq<char>| ss.len() == 0);
        ret == join(
            seq.skip(head as int), 
            gap.skip(head as int),
        )
    }
}

/// Encodes `str::trim_end_matches` for general patterns.
#[verifier::opaque]
pub open spec fn str_trim_end_matches_post<'a, P>(
    s: Seq<char>, pat: P, ret: Seq<char>,
) -> bool 
where 
    P: Pattern,
    <P as Pattern>::Searcher<'a>: ReverseSearcher<'a>,
{
    let (seq, gap) = spec_rmatches(s, pat);
    pat.rmatches_post(s, seq, gap) ==> {
        let head = gap.count_while(|ss: Seq<char>| ss.len() == 0);
        ret == rjoin(
            seq.skip(head as int), 
            gap.skip(head as int),
        )
    }
}

/// Encodes `str::strip_prefix` for general patterns.
#[verifier::opaque]
pub open spec fn str_strip_prefix_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, ret: Option<&'a str>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    pat.matches_post(s, seq, gap) ==> {
        match ret {
            Some(o) => 
                seq.len() > 0 
                && gap.first().len() == 0
                && o@ == join(seq.skip(1), gap.skip(1)),
            None => seq.len() == 0 || gap.first().len() > 0,
        }
    }
}

/// Encodes `str::strip_suffix` for general patterns.
#[verifier::opaque]
pub open spec fn str_strip_suffix_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, ret: Option<&'a str>,
) -> bool 
where 
    P: Pattern,
    <P as Pattern>::Searcher<'a>: ReverseSearcher<'a>,
{
    let (seq, gap) = spec_rmatches(s, pat);
    pat.rmatches_post(s, seq, gap) ==> {
        match ret {
            Some(o) => 
                seq.len() > 0 
                && gap.first().len() == 0
                && o@ == rjoin(seq.skip(1), gap.skip(1)),
            None => seq.len() == 0 || gap.first().len() > 0,
        }
    }
}

/// Encodes `str::replace` for general patterns.
#[verifier::opaque]
pub open spec fn str_replace_post<'a, P: Pattern>(
    s: Seq<char>, from: P, to: Seq<char>, ret: Seq<char>,
) -> bool {
    let (seq, gap) = spec_matches(s, from);
    from.matches_post(s, seq, gap) ==> {
        ret == join(Seq::new(seq.len(), |i: int| to), gap)
    }
}

/// Encodes `str::replacen` for general patterns.
#[verifier::opaque]
pub open spec fn str_replacen_post<'a, P: Pattern>(
    s: Seq<char>, from: P, to: Seq<char>, count: nat, ret: Seq<char>,
) -> bool {
    let (seq, gap) = spec_matches(s, from);
    from.matches_post(s, seq, gap) ==> {
        ret == join(
            Seq::new(seq.len(), |i: int| if i < count { to } else { seq[i] }), 
            gap,
        )
    }
}

// ---------- Specs for `Pattern` ----------

// `char`

impl PatternSpecImpl for char {
    /// Forward matching with the `char` pattern.
    open spec fn matches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& char_matches_post(s, self, seq, gap)
        &&& s =~= join(seq, gap)
    }

    /// Backward matching with the `char` pattern.
    open spec fn rmatches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& char_matches_post(s, self, seq, gap)
        &&& s =~= rjoin(seq, gap)
    }
}

// closure

impl<F> PatternSpecImpl for F 
    where F: FnMut(char) -> bool
{
    /// Forward matching with the closure pattern.
    open spec fn matches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& closure_matches_post(s, self, seq, gap)
        &&& s =~= join(seq, gap)
    }

    /// Backward matching with the closure pattern.
    open spec fn rmatches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& closure_matches_post(s, self, seq, gap)
        &&& s =~= rjoin(seq, gap)
    }
}

// `&[char]` / `&[char; N]` / `[char; N]`

impl<'b> PatternSpecImpl for &'b [char] {
    /// Forward matching with the `&[char]` pattern.
    open spec fn matches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& chars_matches_post(s, self@, seq, gap)
        &&& s =~= join(seq, gap)
    }

    /// Backward matching with the `&[char]` pattern.
    open spec fn rmatches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& chars_matches_post(s, self@, seq, gap)
        &&& s =~= rjoin(seq, gap)
    }
}

impl<'b, const N: usize> PatternSpecImpl for &'b [char; N] {
    /// Forward matching with the `&[char; N]` pattern.
    open spec fn matches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& chars_matches_post(s, self@, seq, gap)
        &&& s =~= join(seq, gap)
    }

    /// Backward matching with the `&[char; N]` pattern.
    open spec fn rmatches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& chars_matches_post(s, self@, seq, gap)
        &&& s =~= rjoin(seq, gap)
    }
}

impl<const N: usize> PatternSpecImpl for [char; N] {
    /// Forward matching with the `[char; N]` pattern.
    open spec fn matches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& chars_matches_post(s, self@, seq, gap)
        &&& s =~= join(seq, gap)
    }

    /// Backward matching with the `[char; N]` pattern.
    open spec fn rmatches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& chars_matches_post(s, self@, seq, gap)
        &&& s =~= rjoin(seq, gap)
    }
}

// `&str` / `&String` / `&&str`

impl<'b> PatternSpecImpl for &'b str {
    /// Forward matching with the `&str` pattern.
    open spec fn matches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& string_matches_post(s, self@, seq, gap)
        &&& s =~= join(seq, gap)
    }

    /// Backward matching with the `&str` pattern.
    open spec fn rmatches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& string_rmatches_post(s, self@, seq, gap)
        &&& s =~= rjoin(seq, gap)
    }
}

impl<'b> PatternSpecImpl for &'b String {
    /// Forward matching with the `&String` pattern.
    open spec fn matches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& string_matches_post(s, self@, seq, gap)
        &&& s =~= join(seq, gap)
    }

    /// Backward matching with the `&String` pattern.
    open spec fn rmatches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& string_rmatches_post(s, self@, seq, gap)
        &&& s =~= rjoin(seq, gap)
    }
}

impl<'b, 'c> PatternSpecImpl for &'c &'b str {
    /// Forward matching with the `&&str` pattern.
    open spec fn matches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& string_matches_post(s, self@, seq, gap)
        &&& s =~= join(seq, gap)
    }

    /// Backward matching with the `&&str` pattern.
    open spec fn rmatches_post(
        self, s: Seq<char>, seq: Seq<Seq<char>>, gap: Seq<Seq<char>>,
    ) -> bool 
    {
        &&& string_rmatches_post(s, self@, seq, gap)
        &&& s =~= rjoin(seq, gap)
    }
}

// TODO: linking lemmas; document the linking lemma pattern?


}