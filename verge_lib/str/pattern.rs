//! Specifications and lemmas for string pattern related operations.
//!
//! ## Specification Methodology
//! To specify `str::split`, `str::contains`, and other methods that make use of 
//! the `std::str::Pattern` trait, Verus adopts the "linking lemma" pattern,
//! where generic post-conditions are captured via `uninterp spec` functions
//! (e.g., `str_contains_post`). Then, broadcast lemmas use the general 
//! specs as triggers to automatically introduce actual specs per pattern type 
//! (e.g., `lemma_str_contains_str` for `&str` patterns, `lemma_str_contains_char` 
//! for `char` patterns). This design minimizes both spec redundancy and user burden 
//! (thanks to automatic broadcasting).
//!
//! Additionally, all the immediate post-conditions are internally derived from 
//! the forward and backward pattern matching operations (`spec_matches` and `spec_rmatches`). 
//! By default this is hidden by `#[verifier::opaque]`, but could be `reveal`-ed 
//! to help prove consistency between APIs (e.g., `str::split` and `str::matches` join 
//! into the original string).

use super::*;
use crate::{is_deterministic, is_total};
use crate::seq::*;
use crate::iter::*;
use std::str::pattern::*;


verus! {

/// Enables `std::str::pattern::Pattern`.
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

/// Marker trait for any `Pattern` that works like a char slice.
pub trait CharsPattern: Pattern + View<V = Seq<char>> {}

impl<'b> CharsPattern for &'b [char] {}
impl<'b, const N: usize> CharsPattern for &'b [char; N] {}
impl<const N: usize> CharsPattern for [char; N] {}

/// Marker trait for any `Pattern` that works like a string.
pub trait StringPattern: Pattern + View<V = Seq<char>> {}

impl<'b> StringPattern for &'b str {}
impl<'b> StringPattern for &'b String {}
impl<'b, 'c> StringPattern for &'c &'b str {}

// ---------- Specs for differnt patterns ----------

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
    where 
        F: FnMut(char) -> bool,
    recommends
        is_deterministic(f) && is_total(f),
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
        gap[i].all(|c: char| !chars.contains(c))
    // matches have one item less than gaps
    &&& seq.len() + 1 == gap.len() 
    // matches match the pattern
    &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> 
        seq[i].len() == 1 && chars.contains(seq[i][0])
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
        &&& forall |i: int| 
            #![trigger pat.is_prefix_of(gap[i] + pat)]
            #![trigger pat.is_infix_of(gap[i] + pat)] 
            0 <= i < gap.len() - 1 ==> 
                gap[i].len() > 0 ==> !pat.is_prefix_of(gap[i] + pat) && !pat.is_infix_of(gap[i] + pat)
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
        &&& forall |i: int|
            #![trigger pat.is_suffix_of(pat + gap[i])]
            #![trigger pat.is_infix_of(pat + gap[i])] 
            0 <= i < gap.len() - 1 ==> 
                gap[i].len() > 0 ==> !pat.is_suffix_of(pat + gap[i]) && !pat.is_infix_of(pat + gap[i])
        // last gap cannot have `pat` as a substring
        &&& !(pat.is_subrange_of(gap.last()))
        // matches have one item less than gaps
        &&& seq.len() + 1 == gap.len() 
        // matches match the pattern
        &&& forall |i: int| 0 <= i < seq.len() ==> #[trigger] (seq[i] =~= pat)
    }
}

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
    ret == (seq.len() > 0)
}

/// Encodes `str::starts_with` for general patterns.
#[verifier::opaque]
pub open spec fn str_starts_with_post<P: Pattern>(s: Seq<char>, pat: P, ret: bool) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    ret == (seq.len() > 0 && gap.first().len() == 0)
}

/// Encodes `str::ends_with` for general patterns.
#[verifier::opaque]
pub open spec fn str_ends_with_post<P>(s: Seq<char>, pat: P, ret: bool) -> bool 
    where 
        P: Pattern,
        for<'b> <P as Pattern>::Searcher<'b>: ReverseSearcher<'b>,
{
    let (seq, gap) = spec_rmatches(s, pat);
    ret == (seq.len() > 0 && gap.first().len() == 0)
}

/// Encodes `str::find` for general patterns.
#[verifier::opaque]
pub open spec fn str_find_post<P: Pattern>(s: Seq<char>, pat: P, ret: Option<usize>) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    &&& ret is None ==> seq.len() == 0
    &&& ret is Some ==> (seq.len() > 0 && ret->0 == gap.first().as_bytes().len())
}

/// Encodes `str::rfind` for general patterns.
#[verifier::opaque]
pub open spec fn str_rfind_post<P>(s: Seq<char>, pat: P, ret: Option<usize>) -> bool 
    where 
        P: Pattern,
        for<'a> <P as Pattern>::Searcher<'a>: ReverseSearcher<'a>,
{
    let (seq, gap) = spec_matches(s, pat);
    &&& ret is None ==> seq.len() == 0
    &&& ret is Some ==> (seq.len() > 0 && ret->0 == s.as_bytes().len() - gap.first().as_bytes().len() - seq.first().as_bytes().len())
}

/// Encodes `str::split_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_iter_post<'a, P: Pattern>(s: Seq<char>, pat: P, iter_seq: Seq<&'a str>) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    &&& iter_seq.len() == gap.len()
    &&& forall |i: int| 0 <= i < iter_seq.len() ==>
            #[trigger] iter_seq[i]@ == gap[i]
}

/// Encodes `str::split_inclusive_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_inclusive_iter_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, iter_seq: Seq<&'a str>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    &&& forall |i: int| 0 <= i < seq.len() ==>
            #[trigger] iter_seq[i]@ == gap[i] + seq[i]
    &&& gap.last().len() == 0 ==> iter_seq.len() == seq.len()
    &&& gap.last().len() > 0 ==> 
            iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last()
}

/// Encodes `str::rsplit_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_rsplit_iter_post<'a, P>(s: Seq<char>, pat: P, iter_seq: Seq<&'a str>) -> bool 
where 
    P: Pattern,
    <P as Pattern>::Searcher<'a>: ReverseSearcher<'a>,
{
    let (seq, gap) = spec_rmatches(s, pat);
    &&& iter_seq.len() == gap.len()
    &&& forall |i: int| 0 <= i < iter_seq.len() ==>
            #[trigger] iter_seq[i]@ == gap[i]
}

/// Encodes `str::split_terminator_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_terminator_iter_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, iter_seq: Seq<&'a str>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    &&& forall |i: int| 0 <= i < seq.len() ==>
            #[trigger] iter_seq[i]@ == gap[i]
    &&& gap.last().len() == 0 ==> iter_seq.len() == seq.len()
    &&& gap.last().len() > 0 ==> 
            iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last()
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
    &&& forall |i: int| 0 <= i < seq.len() ==>
            #[trigger] iter_seq[i]@ == gap[i]
    &&& gap.last().len() == 0 ==> iter_seq.len() == seq.len()
    &&& gap.last().len() > 0 ==> 
            iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last()
}

/// Encodes `str::splitn_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_splitn_iter_post<'a, P: Pattern>(
    s: Seq<char>, n: usize, pat: P, iter_seq: Seq<&'a str>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    &&& iter_seq.len() == n 
    &&& forall |i: int| 0 <= i < n - 1 ==>
            #[trigger] iter_seq[i]@ == gap[i]
    &&& n > 0 ==> iter_seq.last()@ =~= join(seq.skip((n - 1) as int), gap.skip((n - 1) as int))
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
    &&& iter_seq.len() == n 
    &&& forall |i: int| 0 <= i < n - 1 ==>
            #[trigger] iter_seq[i]@ == gap[i]
    &&& n > 0 ==> iter_seq.last()@ =~= rjoin(seq.skip((n - 1) as int), gap.skip((n - 1) as int))
}

/// Encodes `str::split_once` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_once_post<'a, P: Pattern>(
    s: Seq<char>, delimiter: P, ret: Option<(&'a str, &'a str)>,
) -> bool {
    let (seq, gap) = spec_matches(s, delimiter);
    &&& ret is None ==> seq.len() == 0
    &&& ret is Some ==> {
        let (head, tail) = ret->0;
        &&& seq.len() > 0
        &&& head@ == gap.first()
        &&& tail@ =~= join(seq.skip(1), gap.skip(1))
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
    &&& ret is None ==> seq.len() == 0
    &&& ret is Some ==> {
        let (head, tail) = ret->0;
        &&& seq.len() > 0
        &&& head@ == gap.first()
        &&& tail@ =~= rjoin(seq.skip(1), gap.skip(1))
    }
}

/// Encodes `str::split_whitespace_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_whitespace_iter_post<'a>(
    s: Seq<char>, iter_seq: Seq<&'a str>,
) -> bool {
    let pat = |c: char| c.is_whitespace();
    let (seq, gap) = spec_matches(s, pat);
    &&& iter_seq.len() == gap.count(|seg: Seq<char>| seg.len() > 0)
    &&& forall |i: int| 0 <= i < iter_seq.len() ==>
            #[trigger] iter_seq[i]@ == gap.filter(|seg: Seq<char>| seg.len() > 0)[i]
}

/// Encodes `str::split_ascii_whitespace_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_split_ascii_whitespace_iter_post<'a>(
    s: Seq<char>, iter_seq: Seq<&'a str>,
) -> bool {
    let pat = |c: char| c.is_ascii_whitespace();
    let (seq, gap) = spec_matches(s, pat);
    &&& iter_seq.len() == gap.count(|seg: Seq<char>| seg.len() > 0)
    &&& forall |i: int| 0 <= i < iter_seq.len() ==>
            #[trigger] iter_seq[i]@ == gap.filter(|seg: Seq<char>| seg.len() > 0)[i]
}

/// Encodes `str::matches_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_matches_iter_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, iter_seq: Seq<&'a str>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    &&& iter_seq.len() == seq.len()
    &&& forall |i: int| 0 <= i < iter_seq.len() ==>
            #[trigger] iter_seq[i]@ == seq[i]
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
    &&& iter_seq.len() == seq.len()
    &&& forall |i: int| 0 <= i < iter_seq.len() ==>
            #[trigger] iter_seq[i]@ == seq[i]
}

/// Encodes `str::match_indices_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_match_indices_iter_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, iter_seq: Seq<(usize, &'a str)>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    &&& iter_seq.len() == seq.len()
    &&& forall |i: int| 0 <= i < iter_seq.len() ==>
            #[trigger] iter_seq[i].0 == join(seq.take(i), gap.take(i + 1)).as_bytes().len()
            && #[trigger] iter_seq[i].1@ == seq[i]
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
    &&& iter_seq.len() == seq.len()
    &&& forall |i: int| 0 <= i < iter_seq.len() ==>
            #[trigger] iter_seq[i].0 == s.as_bytes().len() - join(seq.take(i), gap.take(i + 1)).as_bytes().len()
            && #[trigger] iter_seq[i].1@ == seq[i]
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

/// Encodes `str::trim_start_matches` for general patterns.
#[verifier::opaque]
pub open spec fn str_trim_start_matches_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, ret: Seq<char>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    let head = gap.count_while(|ss: Seq<char>| ss.len() == 0);
    ret == join(
        seq.skip(head as int), 
        gap.skip(head as int),
    )
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
    let head = gap.count_while(|ss: Seq<char>| ss.len() == 0);
    ret == rjoin(
        seq.skip(head as int), 
        gap.skip(head as int),
    )
}

/// Encodes `str::strip_prefix` for general patterns.
#[verifier::opaque]
pub open spec fn str_strip_prefix_post<'a, P: Pattern>(
    s: Seq<char>, pat: P, ret: Option<&'a str>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    match ret {
        Some(o) => 
            seq.len() > 0 
            && gap.first().len() == 0
            && o@ == join(seq.skip(1), gap.skip(1)),
        None => seq.len() == 0 || gap.first().len() > 0,
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
    match ret {
        Some(o) => 
            seq.len() > 0 
            && gap.first().len() == 0
            && o@ == rjoin(seq.skip(1), gap.skip(1)),
        None => seq.len() == 0 || gap.first().len() > 0,
    }
}

/// Encodes `str::replace` for general patterns.
#[verifier::opaque]
pub open spec fn str_replace_post<'a, P: Pattern>(
    s: Seq<char>, from: P, to: Seq<char>, ret: Seq<char>,
) -> bool {
    let (seq, gap) = spec_matches(s, from);
    ret == join(Seq::new(seq.len(), |i: int| to), gap)
}

/// Encodes `str::replacen` for general patterns.
#[verifier::opaque]
pub open spec fn str_replacen_post<'a, P: Pattern>(
    s: Seq<char>, from: P, to: Seq<char>, count: nat, ret: Seq<char>,
) -> bool {
    let (seq, gap) = spec_matches(s, from);
    ret == join(
        Seq::new(seq.len(), |i: int| if i < count { to } else { seq[i] }), 
        gap,
    )
}

// --- Linking lemmas ---

/// Axiom that links `spec_matches` with concrete specs for the `char` pattern.
pub broadcast axiom fn axiom_char_matches_post(s: Seq<char>, pat: char)
    ensures
        #![trigger spec_matches(s, pat)]
        ({
            let (seq, gap) = spec_matches(s, pat);
            &&& char_matches_post(s, pat, seq, gap)
            &&& s == join(seq, gap)
        });
        
/// Axiom that links `spec_rmatches` with concrete specs for the `char` pattern.
pub broadcast axiom fn axiom_spec_rmatches_post(s: Seq<char>, pat: char)
    ensures
        #![trigger spec_rmatches(s, pat)]
        ({
            let (seq, gap) = spec_rmatches(s, pat);
            &&& char_matches_post(s, pat, seq, gap)
            &&& s == rjoin(seq, gap)
        });

/// Axiom that links `spec_matches` with concrete specs for the closure pattern.
pub broadcast axiom fn axiom_closure_matches_post<F: FnMut(char) -> bool>(s: Seq<char>, pat: F)
    requires
        is_deterministic(pat) && is_total(pat),
    ensures
        #![trigger spec_matches(s, pat)]
        ({
            let (seq, gap) = spec_matches(s, pat);
            &&& closure_matches_post(s, pat, seq, gap)
            &&& s == join(seq, gap)
        });
        
/// Axiom that links `spec_rmatches` with concrete specs for the closure pattern.
pub broadcast axiom fn axiom_closure_rmatches_post<F: FnMut(char) -> bool>(s: Seq<char>, pat: F)
    requires
        is_deterministic(pat) && is_total(pat),
    ensures
        #![trigger spec_rmatches(s, pat)]
        ({
            let (seq, gap) = spec_rmatches(s, pat);
            &&& closure_matches_post(s, pat, seq, gap)
            &&& s == rjoin(seq, gap)
        });

/// Axiom that links `spec_matches` with concrete specs for the chars pattern.
pub broadcast axiom fn axiom_chars_matches_post<P: CharsPattern>(s: Seq<char>, pat: P)
    ensures
        #![trigger spec_matches(s, pat)]
        ({
            let (seq, gap) = spec_matches(s, pat);
            &&& chars_matches_post(s, pat@, seq, gap)
            &&& s == join(seq, gap)
        });
        
/// Axiom that links `spec_rmatches` with concrete specs for the chars pattern.
pub broadcast axiom fn axiom_chars_rmatches_post<P: CharsPattern>(s: Seq<char>, pat: P)
    ensures
        #![trigger spec_rmatches(s, pat)]
        ({
            let (seq, gap) = spec_rmatches(s, pat);
            &&& chars_matches_post(s, pat@, seq, gap)
            &&& s == rjoin(seq, gap)
        });

/// Axiom that links `spec_matches` with concrete specs for the string pattern.
pub broadcast axiom fn axiom_string_matches_post<P: StringPattern>(s: Seq<char>, pat: P)
    ensures
        #![trigger spec_matches(s, pat)]
        ({
            let (seq, gap) = spec_matches(s, pat);
            &&& string_matches_post(s, pat@, seq, gap)
            &&& s == join(seq, gap)
        });
        
/// Axiom that links `spec_rmatches` with concrete specs for the string pattern.
pub broadcast axiom fn axiom_string_rmatches_post<P: StringPattern>(s: Seq<char>, pat: P)
    ensures
        #![trigger spec_rmatches(s, pat)]
        ({
            let (seq, gap) = spec_rmatches(s, pat);
            &&& string_rmatches_post(s, pat@, seq, gap)
            &&& s == rjoin(seq, gap)
        });

/// Proof that links the full spec to `str::contains` with a `char` pattern.
pub broadcast proof fn lemma_str_contains_char(s: Seq<char>, ch: char, ret: bool)
    requires
        #[trigger] str_contains_post(s, ch, ret),
    ensures
        ret <==> s.contains(ch),
{
    axiom_char_matches_post(s, ch);
    reveal(str_contains_post);
    let (seq, gap) = spec_matches(s, ch);
    if ret {
        assert(seq.first() == seq![ch]);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[gap.first().len() as int] == ch);
    }
    if s.contains(ch) {
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(gap.first().contains(ch));
        });
    }
}

/// Proof that links the full spec to `str::contains` with a closure pattern.
pub broadcast proof fn lemma_str_contains_closure<F>(s: Seq<char>, f: F, ret: bool)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_contains_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret <==> exists|i: int| 0 <= i < s.len() && #[trigger] call_ensures(f, (s[i],), true),
{
    axiom_closure_matches_post(s, f);
    reveal(str_contains_post);
    let (seq, gap) = spec_matches(s, f);
    if ret {
        assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[gap.first().len() as int] == seq.first()[0]);
    }
    if exists|i: int| 0 <= i < s.len() && #[trigger] call_ensures(f, (s[i],), true) {
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(
                exists |i: int| 0 <= i < gap.first().len() 
                    && #[trigger] call_ensures(f, (gap.first()[i],), true)
            );
            let k = choose |i: int| 0 <= i < gap.first().len() 
                && #[trigger] call_ensures(f, (gap.first()[i],), true);
            let pred = |c: char| call_ensures(f, (c,), false);
            assert(
                forall |i: int| 0 <= i < gap.first().len() 
                    ==> #[trigger] pred(gap.first()[i])
            );
            assert(pred(gap.first()[k]));
            assert(call_ensures(f, (gap.first()[k],), false));
            assert(call_ensures(f, (gap.first()[k],), true));
        });
    }
}

/// Proof that links the full spec to `str::contains` with a chars pattern.
pub broadcast proof fn lemma_str_contains_char_slice<P: CharsPattern>(s: Seq<char>, chars: P, ret: bool)
    requires
        #[trigger] str_contains_post(s, chars, ret),
    ensures
        ret <==> exists|i: int| 0 <= i < s.len() && #[trigger] chars@.contains(s[i]),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_contains_post);
    let (seq, gap) = spec_matches(s, chars);
    if ret {
        assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[gap.first().len() as int] == seq.first()[0]);
    }
    if exists|i: int| 0 <= i < s.len() && #[trigger] chars@.contains(s[i]) {
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(
                exists |i: int| 0 <= i < gap.first().len() 
                    && #[trigger] chars@.contains(gap.first()[i])
            );
            let k = choose |i: int| 0 <= i < gap.first().len() 
                && #[trigger] chars@.contains(gap.first()[i]);
            let pred = |c: char| !chars@.contains(c);
            assert(
                forall |i: int| 0 <= i < gap.first().len() 
                    ==> #[trigger] pred(gap.first()[i])
            );
            assert(pred(gap.first()[k]));
        });
    }
}

/// Proof that links the full spec to `str::contains` with a string pattern.
pub broadcast proof fn lemma_str_contains_string<P: StringPattern>(s: Seq<char>, pat: P, ret: bool)
    requires
        #[trigger] str_contains_post(s, pat, ret),
    ensures
        ret <==> pat@.is_subrange_of(s),
{
    axiom_string_matches_post(s, pat);
    reveal(str_contains_post);
    let (seq, gap) = spec_matches(s, pat);
    if ret {
        assert(seq.first() == pat@);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(
            s.subrange(gap.first().len() as int, gap.first().len() + seq.first().len() as int) 
                == seq.first()
        );
    } 
    if pat@.is_subrange_of(s) {
        if pat@.len() == 0 {
            assert(seq.len() > 0);
        } else {
            assert_by_contradiction!(seq.len() > 0, {
                assert(gap.len() == 1);
                reveal_with_fuel(Seq::<_>::flatten, 2);
                assert(gap.last() == s);
                assert(!pat@.is_subrange_of(gap.last()));
            });
        }
    }
}

/// Proof that links the full spec to `str::starts_with` with a `char` pattern.
pub broadcast proof fn lemma_str_starts_with_char(s: Seq<char>, ch: char, ret: bool)
    requires
        #[trigger] str_starts_with_post(s, ch, ret),
    ensures
        ret <==> s.len() > 0 && s.first() == ch,
{
    axiom_char_matches_post(s, ch);
    reveal(str_starts_with_post);
    let (seq, gap) = spec_matches(s, ch);
    if ret {
        assert(seq.first() == seq![ch] && gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[0] == seq.first()[0]);
    }
    if s.len() > 0 && s.first() == ch {
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.first() == s);
            assert(gap.first()[0] == ch);
            assert(!gap.first().contains(ch));
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            assert(s.first() == gap.first()[0]);
            assert(gap.first()[0] == ch);
            assert(!gap.first().contains(ch));
        });
    }
}

/// Proof that links the full spec to `str::starts_with` with a closure pattern.
pub broadcast proof fn lemma_str_starts_with_closure<F>(s: Seq<char>, f: F, ret: bool)
    where 
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_starts_with_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret <==> s.len() > 0 && call_ensures(f, (s.first(),), true),
{
    axiom_closure_matches_post(s, f);
    reveal(str_starts_with_post);
    let (seq, gap) = spec_matches(s, f);
    if ret {
        assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
        assert(gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[0] == seq.first()[0]);
    }
    if s.len() > 0 && call_ensures(f, (s.first(),), true) {
        reveal_with_fuel(Seq::<_>::flatten, 2);
        let pred = |c: char| call_ensures(f, (c,), false);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.first() == s);
            assert(gap.first()[0] == s.first());
            assert(pred(gap.first()[0]));
            assert(call_ensures(f, (gap.first()[0],), false));
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            assert(s.first() == gap.first()[0]);
            assert(pred(gap.first()[0]));
            assert(call_ensures(f, (gap.first()[0],), false));
        });
    }
}

/// Proof that links the full spec to `str::starts_with` with a chars pattern.
pub broadcast proof fn lemma_str_starts_with_chars<P: CharsPattern>(s: Seq<char>, chars: P, ret: bool)
    requires
        #[trigger] str_starts_with_post(s, chars, ret),
    ensures
        ret <==> s.len() > 0 && chars@.contains(s.first()),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_starts_with_post);
    let (seq, gap) = spec_matches(s, chars);
    if ret {
        assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
        assert(gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[0] == seq.first()[0]);
    }
    if s.len() > 0 && chars@.contains(s.first()) {
        reveal_with_fuel(Seq::<_>::flatten, 2);
        let pred = |c: char| !chars@.contains(c);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.first() == s);
            assert(gap.first()[0] == s.first());
            assert(pred(gap.first()[0]));
            assert(!chars@.contains(gap.first()[0]));
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            assert(s.first() == gap.first()[0]);
            assert(pred(gap.first()[0]));
            assert(!chars@.contains(gap.first()[0]));
        });
    }
}

/// Proof that links the full spec to `str::starts_with` with a string pattern.
pub broadcast proof fn lemma_str_starts_with_string<P: StringPattern>(s: Seq<char>, pat: P, ret: bool)
    requires
        #[trigger] str_starts_with_post(s, pat, ret),
    ensures
        ret <==> pat@.is_prefix_of(s),
{
    axiom_string_matches_post(s, pat);
    reveal(str_starts_with_post);
    let (seq, gap) = spec_matches(s, pat);
    if ret {
        if pat@.len() == 0 {
            assert(pat@.is_prefix_of(s));
        } else {
            assert(seq.first() == pat@);
            assert(gap.first().len() == 0);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(pat@.is_prefix_of(s));
        }
    }
    if pat@.is_prefix_of(s) {
        if pat@.len() == 0 {
            assert(seq.len() > 0 || gap.first().len() == 0);
            return;
        }
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.last() == s);
            assert(!pat@.is_subrange_of(gap.last()));
            lemma_seq_is_subrange_alt(gap.last(), pat@);
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(seq.first() == pat@);
            assert((gap[0] + pat@ + gap[1]).is_prefix_of(s));
            assert(pat@.is_prefix_of(gap[0] + pat@));
            assert(!pat@.is_prefix_of(gap[0] + pat@));
        }); 
    }
}


}