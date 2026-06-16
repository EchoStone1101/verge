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
//! Additionally, while the lemma post-conditions are meant to be complete (in that they
//! uniquely define the output), Verge cannot predict all forms of wanted specs,
//! which can be particularly a problem for the more intricate APIs (e.g., `str::split`
//! with `&str` patterns). In this case, it is helpful to understand that all the
//! immediate post-conditions are internally derived from the forward and backward
//! pattern matching operations (`spec_matches` and `spec_rmatches`), serving as
//! a complete and basic spec foundation.
//! By default this is hidden by `#[verifier::opaque]`, but could be `reveal`-ed
//! to help prove alternative specs in certain contexts (e.g., more intuitive `str::split`
//! specs when `pat@.len() == 1`), or show consistency between APIs (e.g., `str::split` and
//! `str::matches` join into the original string).

use super::*;
use crate::{is_deterministic, is_total, VergeView};
use crate::seq::*;
use crate::iter::*;
use vstd::{calc, assert_seqs_equal};
use vstd::arithmetic::mul::*;
use vstd::seq_lib::{
    lemma_flatten_concat, lemma_concat_associative,
};

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
        &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1
            ==> gap[i].len() > 0
                ==> !pat.is_prefix_of(gap[i] + pat) && !pat.is_infix_of(gap[i] + pat)
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
        &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1
            ==> gap[i].len() > 0
                ==> !pat.is_suffix_of(pat + gap[i]) && !pat.is_infix_of(pat + gap[i])
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
        .flatten_alt()
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
    let (seq, gap) = spec_rmatches(s, pat);
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
///
/// CAVEAT: compared to `str::rsplit`, `str::rsplit_terminator` skips the
/// "last" item if it is empty. While the matching happens in reverse,
/// the term "last" still refers to the left-to-right order.
/// In other words, `str::rsplit_terminator` actually skips the *first* item
/// that `str::rsplit` would yield if it is empty. For example:
/// ```ignore
/// let vec = "aaaaa".rsplit_terminator("aa").collect::<Vec<_>>();
/// assert(vec == vec!["", "a"]); // ^ skipped the first from `["", "", "a"]`
/// ```
#[verifier::opaque]
pub open spec fn str_rsplit_terminator_iter_post<'a, P>(
    s: Seq<char>, pat: P, iter_seq: Seq<&'a str>,
) -> bool
where
    P: Pattern,
    for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
{
    let (seq, gap) = spec_rmatches(s, pat);
    &&& gap.first().len() == 0 ==>
        iter_seq.len() == gap.len() - 1
        && forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@ == gap[i+1]
    &&& gap.first().len() > 0 ==>
        iter_seq.len() == gap.len()
        && forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@ == gap[i]
}

/// Encodes `str::splitn_iter` for general patterns.
#[verifier::opaque]
pub open spec fn str_splitn_iter_post<'a, P: Pattern>(
    s: Seq<char>, n: usize, pat: P, iter_seq: Seq<&'a str>,
) -> bool {
    let (seq, gap) = spec_matches(s, pat);
    &&& iter_seq.len() == min(n as int, gap.len() as int)
    &&& forall |i: int| 0 <= i < iter_seq.len() - 1 ==>
            #[trigger] iter_seq[i]@ == gap[i]
    &&& n > 0 ==> {
        &&& iter_seq.len() > 0
        &&& iter_seq.last()@ =~= join(seq.skip(iter_seq.len() - 1), gap.skip(iter_seq.len() - 1))
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
    &&& iter_seq.len() == min(n as int, gap.len() as int)
    &&& forall |i: int| 0 <= i < iter_seq.len() - 1 ==>
            #[trigger] iter_seq[i]@ == gap[i]
    &&& n > 0 ==> {
        &&& iter_seq.len() > 0
        &&& iter_seq.last()@ =~= rjoin(seq.skip(iter_seq.len() - 1), gap.skip(iter_seq.len() - 1))
    }
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
        &&& head@ == rjoin(seq.skip(1), gap.skip(1))
        &&& tail@ =~= gap.first()
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
            #[trigger] iter_seq[i].0 == rjoin(seq.skip(i+1), gap.skip(i+1)).as_bytes().len()
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
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        ret.len() == 0
    } else {
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
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        ret.len() == 0
    } else {
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

// --- Linking lemmas ---

// TODO: split_inclusive, split_terminator, rsplit_terminator,
// splitn, rsplitn, matches_iter_string,
// rmatches_iter_string, match_indices, rmatch_indices,
// trim_matches, trim_start_matches, trim_end_matches,

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
pub broadcast axiom fn axiom_char_rmatches_post(s: Seq<char>, pat: char)
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
pub broadcast axiom fn axiom_chars_matches_post<'b>(s: Seq<char>, pat: &'b [char])
    ensures
        #![trigger spec_matches(s, pat)]
        ({
            let (seq, gap) = spec_matches(s, pat);
            &&& chars_matches_post(s, pat@, seq, gap)
            &&& s == join(seq, gap)
        });

/// Axiom that links `spec_rmatches` with concrete specs for the chars pattern.
pub broadcast axiom fn axiom_chars_rmatches_post<'b>(s: Seq<char>, pat: &'b [char])
    ensures
        #![trigger spec_rmatches(s, pat)]
        ({
            let (seq, gap) = spec_rmatches(s, pat);
            &&& chars_matches_post(s, pat@, seq, gap)
            &&& s == rjoin(seq, gap)
        });

/// Axiom that links `spec_matches` with concrete specs for the string pattern.
pub broadcast axiom fn axiom_string_matches_post<'b>(s: Seq<char>, pat: &'b str)
    ensures
        #![trigger spec_matches(s, pat)]
        ({
            let (seq, gap) = spec_matches(s, pat);
            &&& string_matches_post(s, pat@, seq, gap)
            &&& s == join(seq, gap)
        });

/// Axiom that links `spec_rmatches` with concrete specs for the string pattern.
pub broadcast axiom fn axiom_string_rmatches_post<'b>(s: Seq<char>, pat: &'b str)
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

/// Proof that links the full spec to `str::contains` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_contains_chars<'b>(s: Seq<char>, chars: &'b [char], ret: bool)
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
pub broadcast proof fn lemma_str_contains_string<'b>(s: Seq<char>, pat: &'b str, ret: bool)
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

/// Proof that links the full spec to `str::starts_with` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_starts_with_chars<'b>(s: Seq<char>, chars: &'b [char], ret: bool)
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
pub broadcast proof fn lemma_str_starts_with_string<'b>(s: Seq<char>, pat: &'b str, ret: bool)
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

/// Proof that links the full spec to `str::ends_with` with a `char` pattern.
pub broadcast proof fn lemma_str_ends_with_char(s: Seq<char>, ch: char, ret: bool)
    requires
        #[trigger] str_ends_with_post(s, ch, ret),
    ensures
        ret <==> s.len() > 0 && s.last() == ch,
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_ends_with_post);
    let (seq, gap) = spec_rmatches(s, ch);
    if ret {
        assert(seq.first() == seq![ch] && gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        assert(s.last() == seq.first()[0]);
    }
    if s.len() > 0 && s.last() == ch {
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.first() == s);
            assert(gap.first().last() == ch);
            assert(!gap.first().contains(ch));
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            assert(s.last() == gap.first().last());
            assert(gap.first().last() == ch);
            assert(!gap.first().contains(ch));
        });
    }
}

/// Proof that links the full spec to `str::ends_with` with a closure pattern.
pub broadcast proof fn lemma_str_ends_with_closure<F>(s: Seq<char>, f: F, ret: bool)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_ends_with_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret <==> s.len() > 0 && call_ensures(f, (s.last(),), true),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_ends_with_post);
    let (seq, gap) = spec_rmatches(s, f);
    if ret {
        assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
        assert(gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        assert(s.last() == seq.first()[0]);
        assert(call_ensures(f, (s.last(),), true));
    }
    if s.len() > 0 && call_ensures(f, (s.last(),), true) {
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        let pred = |c: char| call_ensures(f, (c,), false);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.first() == s);
            assert(gap.first().last() == s.last());
            assert(pred(gap.first().last()));
            assert(call_ensures(f, (gap.first().last(),), false));
            assert(call_ensures(f, (gap.first().last(),), true));
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            assert(s.last() == gap.first().last());
            assert(pred(gap.first().last()));
            assert(call_ensures(f, (gap.first().last(),), false));
            assert(call_ensures(f, (gap.first().last(),), true));
        });
    }
}

/// Proof that links the full spec to `str::ends_with` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_ends_with_chars<'b>(s: Seq<char>, chars: &'b [char], ret: bool)
    requires
        #[trigger] str_ends_with_post(s, chars, ret),
    ensures
        ret <==> s.len() > 0 && chars@.contains(s.last()),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_ends_with_post);
    let (seq, gap) = spec_rmatches(s, chars);
    if ret {
        assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
        assert(gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        assert(s.last() == seq.first()[0]);
        assert(chars@.contains(s.last()));
    }
    if s.len() > 0 && chars@.contains(s.last()) {
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        let pred = |c: char| !chars@.contains(c);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.first() == s);
            assert(gap.first().last() == s.last());
            assert(pred(gap.first().last()));
            assert(!chars@.contains(gap.first().last()));
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            assert(s.last() == gap.first().last());
            assert(pred(gap.first().last()));
            assert(!chars@.contains(gap.first().last()));
        });
    }
}

/// Proof that links the full spec to `str::ends_with` with a string pattern.
pub broadcast proof fn lemma_str_ends_with_string<'b>(s: Seq<char>, pat: &'b str, ret: bool)
    requires
        #[trigger] str_ends_with_post(s, pat, ret),
    ensures
        ret <==> pat@.is_suffix_of(s),
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_ends_with_post);
    let (seq, gap) = spec_rmatches(s, pat);
    if ret {
        if pat@.len() == 0 {
            assert(pat@.is_suffix_of(s));
        } else {
            assert(seq.first() == pat@);
            assert(gap.first().len() == 0);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(pat@.is_suffix_of(s));
        }
    }
    if pat@.is_suffix_of(s) {
        if pat@.len() == 0 {
            assert(seq.len() > 0 || gap.first().len() == 0);
            return;
        }
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.last() == s);
            assert(!pat@.is_subrange_of(gap.last()));
            lemma_seq_is_subrange_alt(gap.last(), pat@);
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.first() == pat@);
            assert((gap[1] + pat@ + gap[0]).is_suffix_of(s));
            assert(pat@.is_suffix_of(pat@ + gap[0]));
            assert(!pat@.is_suffix_of(pat@ + gap[0]));
        });
    }
}

/// Proof that links the full spec to `str::find` with a `char` pattern.
pub broadcast proof fn lemma_str_find_char(s: Seq<char>, ch: char, ret: Option<usize>)
    requires
        #[trigger] str_find_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => !s.contains(ch),
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch < s.len()
                    &&& s[k_ch] == ch
                    &&& forall |i: int| 0 <= i < k_ch ==> #[trigger] s[i] != ch
                },
            }
        }),
{
    axiom_char_matches_post(s, ch);
    reveal(str_find_post);
    let (seq, gap) = spec_matches(s, ch);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(!s.contains(ch));
        },
        Some(k) => {
            let tail = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss).flatten();
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s == gap.first() + tail);
            lemma_str_concat_lower(gap.first(), tail);
            assert(s.as_bytes().take(k as int) == gap.first().as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(gap.first());
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(gap.first());
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == gap.first().len());
            assert(seq.first() == seq![ch]);
            assert(s[k_ch] == seq.first()[0]);
            assert forall |i: int| 0 <= i < k_ch implies #[trigger] s[i] != ch by {
                assert(s[i] == gap.first()[i]);
                assert_by_contradiction!(s[i] != ch, {
                    assert(gap.first()[i] == ch);
                    assert(gap.first().contains(ch));
                });
            }
        },
    }
}

/// Proof that links the full spec to `str::find` with a closure pattern.
pub broadcast proof fn lemma_str_find_closure<F>(s: Seq<char>, f: F, ret: Option<usize>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_find_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ({
            match ret {
                None => {
                    forall |i: int| 0 <= i < s.len()
                        ==> #[trigger] call_ensures(f, (s[i],), false)
                },
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch < s.len()
                    &&& call_ensures(f, (s[k_ch],), true)
                    &&& forall |i: int| 0 <= i < k_ch
                            ==> #[trigger] call_ensures(f, (s[i],), false)
                },
            }
        }),
{
    axiom_closure_matches_post(s, f);
    reveal(str_find_post);
    let (seq, gap) = spec_matches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < s.len()
                implies #[trigger] call_ensures(f, (s[i],), false) by {
                assert(pred(gap.first()[i]));
                assert(call_ensures(f, (gap.first()[i],), false));
            }
        },
        Some(k) => {
            let tail = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss).flatten();
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s == gap.first() + tail);
            lemma_str_concat_lower(gap.first(), tail);
            assert(s.as_bytes().take(k as int) == gap.first().as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(gap.first());
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(gap.first());
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == gap.first().len());
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(s[k_ch] == seq.first()[0]);
            assert(call_ensures(f, (s[k_ch],), true));
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < k_ch
                implies #[trigger] call_ensures(f, (s[i],), false) by {
                assert(s[i] == gap.first()[i]);
                assert(pred(gap.first()[i]));
                assert(call_ensures(f, (gap.first()[i],), false));
            }
        },
    }
}

/// Proof that links the full spec to `str::find` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_find_chars<'b>(s: Seq<char>, chars: &'b [char], ret: Option<usize>)
    requires
        #[trigger] str_find_post(s, chars, ret),
    ensures
        ({
            match ret {
                None => {
                    forall |i: int| 0 <= i < s.len()
                        ==> !(#[trigger] chars@.contains(s[i]))
                },
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch < s.len()
                    &&& chars@.contains(s[k_ch])
                    &&& forall |i: int| 0 <= i < k_ch
                            ==> !(#[trigger] chars@.contains(s[i]))
                },
            }
        }),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_find_post);
    let (seq, gap) = spec_matches(s, chars);
    let pred = |c: char| !chars@.contains(c);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < s.len()
                implies !(#[trigger] chars@.contains(s[i])) by {
                assert(pred(gap.first()[i]));
                assert(!chars@.contains(gap.first()[i]));
            }
        },
        Some(k) => {
            let tail = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss).flatten();
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s == gap.first() + tail);
            lemma_str_concat_lower(gap.first(), tail);
            assert(s.as_bytes().take(k as int) == gap.first().as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(gap.first());
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(gap.first());
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == gap.first().len());
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(s[k_ch] == seq.first()[0]);
            assert(chars@.contains(s[k_ch]));
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < k_ch
                implies !(#[trigger] chars@.contains(s[i])) by {
                assert(s[i] == gap.first()[i]);
                assert(pred(gap.first()[i]));
                assert(!chars@.contains(gap.first()[i]));
            }
        },
    }
}

/// Proof that links the full spec to `str::find` with a string pattern.
pub broadcast proof fn lemma_str_find_string<'b>(s: Seq<char>, pat: &'b str, ret: Option<usize>)
    requires
        #[trigger] str_find_post(s, pat, ret),
    ensures
        ({
            match ret {
                None => !pat@.is_subrange_of(s),
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch <= s.len() - pat@.len()
                    &&& pat@ == s.subrange(k_ch, k_ch + pat@.len())
                    &&& forall |i: int| 0 <= i < k_ch
                            ==> pat@ != #[trigger] s.subrange(i, i + pat@.len())
                },
            }
        }),
{
    axiom_string_matches_post(s, pat);
    reveal(str_find_post);
    let (seq, gap) = spec_matches(s, pat);
    match ret {
        None => {
            if pat@.len() == 0 {
                assert(seq.len() == s.len() + 1);
            } else {
                assert(gap.len() == 1);
                reveal_with_fuel(Seq::<_>::flatten, 2);
                assert(gap.last() == s);
                assert(!pat@.is_subrange_of(s));
            }
        },
        Some(k) => {
            let tail = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss).flatten();
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s == gap.first() + tail);
            lemma_str_concat_lower(gap.first(), tail);
            assert(s.as_bytes().take(k as int) == gap.first().as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(gap.first());
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(gap.first());
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == gap.first().len());
            if pat@.len() == 0 {
                assert(gap.first().len() == 0);
                assert(pat@ == s.subrange(0, 0));
            } else {
                assert(seq.first() == pat@);
                assert(s.subrange(k_ch, k_ch + pat@.len()) == pat@);
                assert(k_ch <= s.len() - pat@.len());
                assert forall |i: int| 0 <= i < k_ch
                    implies pat@ != #[trigger] s.subrange(i, i + pat@.len()) by {
                    assert_by_contradiction!(pat@ != s.subrange(i, i + pat@.len()), {
                        assert(s.subrange(i, i + pat@.len())
                            == (gap.first() + pat@).subrange(i, i + pat@.len()));
                        assert(pat@.is_subrange_of(gap.first() + pat@));
                        lemma_seq_is_subrange_alt(gap.first() + pat@, pat@);
                        if i == 0 {
                            assert(pat@.is_prefix_of(gap.first() + pat@));
                        } else {
                            assert(pat@.is_infix_of(gap.first() + pat@));
                        }
                    });
                }
            }
        },
    }
}

/// Proof that links the full spec to `str::rfind` with a `char` pattern.
pub broadcast proof fn lemma_str_rfind_char(s: Seq<char>, ch: char, ret: Option<usize>)
    requires
        #[trigger] str_rfind_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => !s.contains(ch),
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch < s.len()
                    &&& s[k_ch] == ch
                    &&& forall |i: int| k_ch < i < s.len() ==> #[trigger] s[i] != ch
                },
            }
        }),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rfind_post);
    let (seq, gap) = spec_rmatches(s, ch);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(gap.first() == s);
            assert(!s.contains(ch));
        },
        Some(k) => {
            let rest = rjoin(seq.skip(1), gap.skip(1));
            reveal_with_fuel(Seq::<_>::flatten_alt, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
            assert(parts.len() > 0);
            assert(parts.first() == gap[1] + seq[0]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
            assert(parts.reverse().last() == parts.first());
            assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
            assert(s == parts.reverse().flatten_alt() + gap[0]);
            lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
            assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
            assert(s == rest + seq[0] + gap[0]);
            assert(seq[0] == seq![ch]);
            lemma_concat_associative(rest, seq[0], gap[0]);
            assert(s == rest + (seq[0] + gap[0]));
            lemma_str_concat_lower(seq[0], gap[0]);
            lemma_str_concat_lower(rest, seq[0] + gap[0]);
            assert(s.as_bytes() == rest.as_bytes() + seq[0].as_bytes() + gap[0].as_bytes());
            assert(k as int == rest.as_bytes().len());
            assert(s.as_bytes().take(k as int) == rest.as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(rest);
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(rest);
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == rest.len());
            assert(s[k_ch] == seq[0][0]);
            assert(s[k_ch] == ch);
            assert forall |i: int| k_ch < i < s.len() implies #[trigger] s[i] != ch by {
                assert(seq[0].len() == 1);
                assert(k_ch + 1 <= i);
                assert(s[i] == gap[0][i - k_ch - 1]);
                assert(!gap[0].contains(ch));
                assert_by_contradiction!(s[i] != ch, {
                    assert(gap[0][i - k_ch - 1] == ch);
                    assert(gap[0].contains(ch));
                });
            }
        },
    }
}

/// Proof that links the full spec to `str::rfind` with a closure pattern.
pub broadcast proof fn lemma_str_rfind_closure<F>(s: Seq<char>, f: F, ret: Option<usize>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rfind_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ({
            match ret {
                None => {
                    forall |i: int| 0 <= i < s.len()
                        ==> #[trigger] call_ensures(f, (s[i],), false)
                },
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch < s.len()
                    &&& call_ensures(f, (s[k_ch],), true)
                    &&& forall |i: int| k_ch < i < s.len()
                            ==> #[trigger] call_ensures(f, (s[i],), false)
                },
            }
        }),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rfind_post);
    let (seq, gap) = spec_rmatches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < s.len()
                implies #[trigger] call_ensures(f, (s[i],), false) by {
                assert(pred(gap.first()[i]));
                assert(call_ensures(f, (gap.first()[i],), false));
            }
        },
        Some(k) => {
            let rest = rjoin(seq.skip(1), gap.skip(1));
            reveal_with_fuel(Seq::<_>::flatten_alt, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
            assert(parts.len() > 0);
            assert(parts.first() == gap[1] + seq[0]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
            assert(parts.reverse().last() == parts.first());
            assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
            assert(s == parts.reverse().flatten_alt() + gap[0]);
            lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
            assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
            assert(s == rest + seq[0] + gap[0]);
            assert(seq[0].len() == 1 && call_ensures(f, (seq[0][0],), true));
            lemma_concat_associative(rest, seq[0], gap[0]);
            assert(s == rest + (seq[0] + gap[0]));
            lemma_str_concat_lower(seq[0], gap[0]);
            lemma_str_concat_lower(rest, seq[0] + gap[0]);
            assert(s.as_bytes() == rest.as_bytes() + seq[0].as_bytes() + gap[0].as_bytes());
            assert(k as int == rest.as_bytes().len());
            assert(s.as_bytes().take(k as int) == rest.as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(rest);
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(rest);
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == rest.len());
            assert(s[k_ch] == seq[0][0]);
            assert(call_ensures(f, (s[k_ch],), true));
            assert(gap[0].all(pred));
            assert forall |i: int| k_ch < i < s.len()
                implies #[trigger] call_ensures(f, (s[i],), false) by {
                assert(seq[0].len() == 1);
                assert(k_ch + 1 <= i);
                assert(s[i] == gap[0][i - k_ch - 1]);
                assert(pred(gap[0][i - k_ch - 1]));
                assert(call_ensures(f, (gap[0][i - k_ch - 1],), false));
            }
        },
    }
}

/// Proof that links the full spec to `str::rfind` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_rfind_chars<'b>(s: Seq<char>, chars: &'b [char], ret: Option<usize>)
    requires
        #[trigger] str_rfind_post(s, chars, ret),
    ensures
        ({
            match ret {
                None => {
                    forall |i: int| 0 <= i < s.len()
                        ==> !(#[trigger] chars@.contains(s[i]))
                },
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch < s.len()
                    &&& chars@.contains(s[k_ch])
                    &&& forall |i: int| k_ch < i < s.len()
                            ==> !(#[trigger] chars@.contains(s[i]))
                },
            }
        }),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rfind_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let pred = |c: char| !chars@.contains(c);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < s.len()
                implies !(#[trigger] chars@.contains(s[i])) by {
                assert(pred(gap.first()[i]));
                assert(!chars@.contains(gap.first()[i]));
            }
        },
        Some(k) => {
            let rest = rjoin(seq.skip(1), gap.skip(1));
            reveal_with_fuel(Seq::<_>::flatten_alt, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
            assert(parts.len() > 0);
            assert(parts.first() == gap[1] + seq[0]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
            assert(parts.reverse().last() == parts.first());
            assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
            assert(s == parts.reverse().flatten_alt() + gap[0]);
            lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
            assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
            assert(s == rest + seq[0] + gap[0]);
            assert(seq[0].len() == 1 && chars@.contains(seq[0][0]));
            lemma_concat_associative(rest, seq[0], gap[0]);
            assert(s == rest + (seq[0] + gap[0]));
            lemma_str_concat_lower(seq[0], gap[0]);
            lemma_str_concat_lower(rest, seq[0] + gap[0]);
            assert(s.as_bytes() == rest.as_bytes() + seq[0].as_bytes() + gap[0].as_bytes());
            assert(k as int == rest.as_bytes().len());
            assert(s.as_bytes().take(k as int) == rest.as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(rest);
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(rest);
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == rest.len());
            assert(s[k_ch] == seq[0][0]);
            assert(chars@.contains(s[k_ch]));
            assert(gap[0].all(pred));
            assert forall |i: int| k_ch < i < s.len()
                implies !(#[trigger] chars@.contains(s[i])) by {
                assert(seq[0].len() == 1);
                assert(k_ch + 1 <= i);
                assert(s[i] == gap[0][i - k_ch - 1]);
                assert(pred(gap[0][i - k_ch - 1]));
                assert(!chars@.contains(gap[0][i - k_ch - 1]));
            }
        },
    }
}

/// Proof that links the full spec to `str::rfind` with a string pattern.
pub broadcast proof fn lemma_str_rfind_string<'b>(s: Seq<char>, pat: &'b str, ret: Option<usize>)
    requires
        #[trigger] str_rfind_post(s, pat, ret),
    ensures
        ({
            match ret {
                None => !pat@.is_subrange_of(s),
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch <= s.len() - pat@.len()
                    &&& pat@ == s.subrange(k_ch, k_ch + pat@.len())
                    &&& forall |i: int| k_ch < i <= s.len() - pat@.len()
                            ==> pat@ != #[trigger] s.subrange(i, i + pat@.len())
                },
            }
        }),
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rfind_post);
    let (seq, gap) = spec_rmatches(s, pat);
    match ret {
        None => {
            if pat@.len() == 0 {
                assert(seq.len() == s.len() + 1);
                assert(false);
            } else {
                assert(gap.len() == 1);
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                assert(gap.last() == s);
                assert(!pat@.is_subrange_of(s));
            }
        },
        Some(k) => {
            if pat@.len() == 0 {
                assert_seqs_equal!(seq[0] == pat@);
                assert(gap.first().len() == 0);
                assert(gap.first().as_bytes().len() == 0);
                assert(seq.first().as_bytes().len() == 0);
                assert(k as int == s.as_bytes().len());
                assert(s.as_bytes().take(k as int) == s.as_bytes());
                lemma_str_is_utf8(s);
                lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
                lemma_str_lower_lift(s);
                let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                assert(k_ch == s.len());
                assert(k_ch <= s.len() - pat@.len());
                assert(pat@ == s.subrange(k_ch, k_ch + pat@.len()));
                assert forall |i: int| k_ch < i <= s.len() - pat@.len()
                    implies pat@ != #[trigger] s.subrange(i, i + pat@.len()) by {
                    assert(false);
                }
            } else {
                let rest = rjoin(seq.skip(1), gap.skip(1));
                reveal_with_fuel(Seq::<_>::flatten_alt, 4);
                let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
                let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
                assert(parts.len() > 0);
                assert(parts.first() == gap[1] + seq[0]);
                assert_seqs_equal!(parts.drop_first() == rest_parts);
                assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
                assert(parts.reverse().last() == parts.first());
                assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
                assert(s == parts.reverse().flatten_alt() + gap[0]);
                lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
                assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
                assert(s == rest + seq[0] + gap[0]);
                assert(seq[0] == pat@);
                lemma_concat_associative(rest, seq[0], gap[0]);
                assert(s == rest + (seq[0] + gap[0]));
                lemma_str_concat_lower(seq[0], gap[0]);
                lemma_str_concat_lower(rest, seq[0] + gap[0]);
                assert(s.as_bytes() == rest.as_bytes() + seq[0].as_bytes() + gap[0].as_bytes());
                assert(k as int == rest.as_bytes().len());
                assert(s.as_bytes().take(k as int) == rest.as_bytes());
                lemma_str_is_utf8(s);
                lemma_str_is_utf8(rest);
                lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
                lemma_str_lower_lift(rest);
                let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                assert(k_ch == rest.len());
                assert(s.subrange(k_ch, k_ch + pat@.len()) == pat@);
                assert(k_ch <= s.len() - pat@.len());
                assert forall |i: int| k_ch < i <= s.len() - pat@.len()
                    implies pat@ != #[trigger] s.subrange(i, i + pat@.len()) by {
                    let j = i - k_ch;
                    assert(0 < j <= gap[0].len());
                    assert(gap[0].len() > 0);
                    assert(s.subrange(i, i + pat@.len())
                        == (pat@ + gap[0]).subrange(j, j + pat@.len()));
                    assert_by_contradiction!(pat@ != s.subrange(i, i + pat@.len()), {
                        assert(pat@.is_subrange_of(pat@ + gap[0]));
                        lemma_seq_is_subrange_alt(pat@ + gap[0], pat@);
                        if j == gap[0].len() {
                            assert(pat@.is_suffix_of(pat@ + gap[0]));
                        } else {
                            assert(j < gap[0].len());
                            assert(pat@.is_infix_of(pat@ + gap[0]));
                        }
                        assert(gap[0].len() > 0 ==> !pat@.is_suffix_of(pat@ + gap[0]) && !pat@.is_infix_of(pat@ + gap[0]));
                    });
                }
            }
        },
    }
}

/// Proof that links the full spec to `str::split` with a `char` pattern.
pub broadcast proof fn lemma_str_split_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_iter_post(s, ch, iter_seq),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // splits cannot contain `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> !(#[trigger] iter_seq[i]@.contains(ch)),
        // delimiters and splits make up the original string
        s == iter_seq.first()@ + iter_seq.drop_first()
            .map_values(|ss: &'a str| ss@.insert(0, ch))
            .flatten()
{
    axiom_char_matches_post(s, ch);
    reveal(str_split_iter_post);
    let (seq, gap) = spec_matches(s, ch);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| 0 <= i < iter_seq.len()
        implies !(#[trigger] iter_seq[i]@.contains(ch))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(!gap[i].contains(ch));
    }

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
    let iter_parts = iter_seq.drop_first().map_values(|ss: &'a str| ss@.insert(0, ch));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(seq[i] =~= seq![ch]);
        assert(seq[i] == seq![ch]);
        g.insert_ensures(0, ch);
        assert_seqs_equal!(g.insert(0, ch) == seq![ch] + g);
    });
    reveal_with_fuel(Seq::<_>::flatten, 2);
    assert(s == gap.first() + join_parts.flatten());
    assert(iter_seq.first()@ == gap.first());
}

/// Proof that links the full spec to `str::split` with a closure pattern.
pub broadcast proof fn lemma_str_split_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_split_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // splits cannot match `f`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] call_ensures(f, (delim[i],), true)
            &&& s == iter_seq.first()@ + iter_seq.drop_first()
                    .map(|i: int, ss: &'a str| ss@.insert(0, delim[i]))
                    .flatten()
        },
{
    axiom_closure_matches_post(s, f);
    reveal(str_split_iter_post);
    let (seq, gap) = spec_matches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| 0 <= i < iter_seq.len()
        implies (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(pred));
    }

    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);
    assert(delim.len() == iter_seq.len() - 1);
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] call_ensures(f, (delim[i],), true)
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
    }

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
    let iter_parts = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.insert(0, delim[i]));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        let d = delim[i];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(d == seq[i][0]);
        assert(seq[i].len() == 1);
        assert_seqs_equal!(seq[i] == seq![d]);
        g.insert_ensures(0, d);
        assert_seqs_equal!(g.insert(0, d) == seq![d] + g);
    });
    reveal_with_fuel(Seq::<_>::flatten, 2);
    assert(s == gap.first() + join_parts.flatten());
    assert(iter_seq.first()@ == gap.first());
}

/// Proof that links the full spec to `str::split` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_split_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_iter_post(s, chars, iter_seq),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // splits cannot match `chars`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] chars@.contains(delim[i])
            &&& s == iter_seq.first()@ + iter_seq.drop_first()
                    .map(|i: int, ss: &'a str| ss@.insert(0, delim[i]))
                    .flatten()
        },
{
    axiom_chars_matches_post(s, chars);
    reveal(str_split_iter_post);
    let (seq, gap) = spec_matches(s, chars);
    let pred = |c: char| !chars@.contains(c);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| 0 <= i < iter_seq.len()
        implies (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(pred));
    }

    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);
    assert(delim.len() == iter_seq.len() - 1);
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] chars@.contains(delim[i])
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
    }

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
    let iter_parts = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.insert(0, delim[i]));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        let d = delim[i];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(d == seq[i][0]);
        assert(seq[i].len() == 1);
        assert_seqs_equal!(seq[i] == seq![d]);
        g.insert_ensures(0, d);
        assert_seqs_equal!(g.insert(0, d) == seq![d] + g);
    });
    reveal_with_fuel(Seq::<_>::flatten, 2);
    assert(s == gap.first() + join_parts.flatten());
    assert(iter_seq.first()@ == gap.first());
}

/// Proof that links the full spec to `str::split` with a string pattern.
pub broadcast proof fn lemma_str_split_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_split_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_split_iter_post(s, pat, iter_seq),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@),
        // last split cannot have `pat` as a substring
        !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        s == iter_seq.first()@ + iter_seq.drop_first()
                .map_values(|ss: &'a str| pat@ + ss@)
                .flatten(),
{
    axiom_string_matches_post(s, pat);
    reveal(str_split_iter_post);
    let (seq, gap) = spec_matches(s, pat);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@)
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].len() > 0 ==> !pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@));
    }
    assert(iter_seq.last()@ == gap.last());
    assert(!(pat@.is_subrange_of(gap.last())));

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
    let iter_parts = iter_seq.drop_first().map_values(|ss: &'a str| pat@ + ss@);
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(seq[i] =~= pat@);
        assert(seq[i] == pat@);
    });
    reveal_with_fuel(Seq::<_>::flatten, 2);
    assert(s == gap.first() + join_parts.flatten());
    assert(iter_seq.first()@ == gap.first());
}

/// Proof that links the full spec to `str::split_inclusive` with a `char` pattern.
pub broadcast proof fn lemma_str_split_inclusive_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_inclusive_iter_post(s, ch, iter_seq),
    ensures
        // splits are not empty and cannot contain `ch` except at the end
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len()
            ==> iter_seq[i]@.len() > 0
                && !iter_seq[i]@.drop_last().contains(ch),
        // splits except the last must end with `ch`
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> #[trigger] iter_seq[i]@.last() == ch,
        // splits make up the original string
        s == iter_seq.map_values(|ss: &'a str| ss@).flatten(),
{
    axiom_char_matches_post(s, ch);
    reveal(str_split_inclusive_iter_post);
    let (seq, gap) = spec_matches(s, ch);
    // #1
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| #![trigger iter_seq[i]@] 0 <= i < seq.len()
    implies iter_seq[i]@.len() > 0 && !iter_seq[i]@.drop_last().contains(ch)
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(iter_seq[i]@.len() > 0) by { assert(seq[i] =~= seq![ch]) }
        assert(!iter_seq[i]@.drop_last().contains(ch)) by {
            assert(!gap[i].contains(ch));
            assert(iter_seq[i]@.drop_last() == gap[i]);
        }
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@.len() > 0 && !iter_seq.last()@.drop_last().contains(ch)) by {
            assert(iter_seq.last()@ == gap.last());
            assert(!gap.last().drop_last().contains(ch)) by {
                assert(!gap.last().contains(ch));
            }
        }
    }
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies #[trigger] iter_seq[i]@.last() == ch
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(seq[i] =~= seq![ch]);
    }
    // #3
    assert(s == iter_seq.map_values(|ss: &'a str| ss@).flatten()) by {
        if iter_seq.len() == seq.len() {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    assert(gap.last().len() == 0);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        } else {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    let s1 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    s1.lemma_flatten_and_flatten_alt_are_equivalent();
                    assert(gap.last() == iter_seq.last()@);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten_alt() + iter_seq.last()@; {
                    reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                    assert_seqs_equal!(iter_seq.drop_last().map_values(|ss: &'a str| ss@) == iter_seq.map_values(|ss: &'a str| ss@).drop_last());
                    assert(iter_seq.map_values(|ss: &'a str| ss@).last() == iter_seq.last()@);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten_alt(); {
                    iter_seq.map_values(|ss: &'a str| ss@).lemma_flatten_and_flatten_alt_are_equivalent();
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        }
    }
}

/// Proof that links the full spec to `str::split_inclusive` with a closure pattern.
pub broadcast proof fn lemma_str_split_inclusive_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_split_inclusive_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // splits are not empty and cannot match `f` except at the end
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len()
            ==> iter_seq[i]@.len() > 0
                && iter_seq[i]@.drop_last().all(|c: char| call_ensures(f, (c,), false)),
        // splits except the last must match `f` at the end
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> #[trigger] call_ensures(f, (iter_seq[i]@.last(),), true),
        // splits make up the original string
        s == iter_seq.map_values(|ss: &'a str| ss@).flatten(),
{
    axiom_closure_matches_post(s, f);
    reveal(str_split_inclusive_iter_post);
    let (seq, gap) = spec_matches(s, f);
    // #1
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| #![trigger iter_seq[i]@] 0 <= i < seq.len()
    implies iter_seq[i]@.len() > 0 && iter_seq[i]@.drop_last().all(|c: char| call_ensures(f, (c,), false))
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(iter_seq[i]@.len() > 0) by { assert(seq[i].len() == 1) }
        assert(iter_seq[i]@.drop_last() == gap[i]) by {
            assert(seq[i].len() == 1);
        }
        assert(gap[i].all(|c: char| call_ensures(f, (c,), false)));
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@.len() > 0 && iter_seq.last()@.drop_last().all(|c: char| call_ensures(f, (c,), false))) by {
            assert(iter_seq.last()@ == gap.last());
            assert(gap.last().all(|c: char| call_ensures(f, (c,), false)));
            assert(iter_seq.last()@.drop_last().all(|c: char| call_ensures(f, (c,), false)));
        }
    }
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies #[trigger] call_ensures(f, (iter_seq[i]@.last(),), true)
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
        assert(iter_seq[i]@.last() == seq[i][0]);
    }
    // #3
    assert(s == iter_seq.map_values(|ss: &'a str| ss@).flatten()) by {
        if iter_seq.len() == seq.len() {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    assert(gap.last().len() == 0);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        } else {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    let s1 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    s1.lemma_flatten_and_flatten_alt_are_equivalent();
                    assert(gap.last() == iter_seq.last()@);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten_alt() + iter_seq.last()@; {
                    reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                    assert_seqs_equal!(iter_seq.drop_last().map_values(|ss: &'a str| ss@) == iter_seq.map_values(|ss: &'a str| ss@).drop_last());
                    assert(iter_seq.map_values(|ss: &'a str| ss@).last() == iter_seq.last()@);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten_alt(); {
                    iter_seq.map_values(|ss: &'a str| ss@).lemma_flatten_and_flatten_alt_are_equivalent();
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        }
    }
}

/// Proof that links the full spec to `str::split_inclusive` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_split_inclusive_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_inclusive_iter_post(s, chars, iter_seq),
    ensures
        // splits are not empty and cannot match `chars` except at the end
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len()
            ==> iter_seq[i]@.len() > 0
                && iter_seq[i]@.drop_last().all(|c: char| !chars@.contains(c)),
        // splits except the last must match `chars` at the end
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> #[trigger] chars@.contains(iter_seq[i]@.last()),
        // splits make up the original string
        s == iter_seq.map_values(|ss: &'a str| ss@).flatten(),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_split_inclusive_iter_post);
    let (seq, gap) = spec_matches(s, chars);
    // #1
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| #![trigger iter_seq[i]@] 0 <= i < seq.len()
    implies iter_seq[i]@.len() > 0 && iter_seq[i]@.drop_last().all(|c: char| !chars@.contains(c))
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(iter_seq[i]@.len() > 0) by { assert(seq[i].len() == 1) }
        assert(iter_seq[i]@.drop_last() == gap[i]) by {
            assert(seq[i].len() == 1);
        }
        assert(gap[i].all(|c: char| !chars@.contains(c)));
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@.len() > 0 && iter_seq.last()@.drop_last().all(|c: char| !chars@.contains(c))) by {
            assert(iter_seq.last()@ == gap.last());
            assert(gap.last().all(|c: char| !chars@.contains(c)));
            assert(iter_seq.last()@.drop_last().all(|c: char| !chars@.contains(c)));
        }
    }
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies #[trigger] chars@.contains(iter_seq[i]@.last())
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
        assert(iter_seq[i]@.last() == seq[i][0]);
    }
    // #3
    assert(s == iter_seq.map_values(|ss: &'a str| ss@).flatten()) by {
        if iter_seq.len() == seq.len() {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    assert(gap.last().len() == 0);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        } else {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    let s1 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    s1.lemma_flatten_and_flatten_alt_are_equivalent();
                    assert(gap.last() == iter_seq.last()@);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten_alt() + iter_seq.last()@; {
                    reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                    assert_seqs_equal!(iter_seq.drop_last().map_values(|ss: &'a str| ss@) == iter_seq.map_values(|ss: &'a str| ss@).drop_last());
                    assert(iter_seq.map_values(|ss: &'a str| ss@).last() == iter_seq.last()@);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten_alt(); {
                    iter_seq.map_values(|ss: &'a str| ss@).lemma_flatten_and_flatten_alt_are_equivalent();
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        }
    }
}

/// Proof that links the full spec to `str::split_inclusive` with a string pattern.
pub broadcast proof fn lemma_str_split_inclusive_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_split_inclusive_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_split_inclusive_iter_post(s, pat, iter_seq),
    ensures
        // splits are not empty and cannot match `pat` except at the end
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len()
            ==> iter_seq[i]@.len() > 0 && !pat@.is_subrange_of(iter_seq[i]@.drop_last()),
        // splits except the last must match `pat` at the end
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> #[trigger] pat@.is_suffix_of(iter_seq[i]@),
        // splits make up the original string
        s == iter_seq.map_values(|ss: &'a str| ss@).flatten(),
{
    axiom_string_matches_post(s, pat);
    reveal(str_split_inclusive_iter_post);
    let (seq, gap) = spec_matches(s, pat);
    // #1
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| #![trigger iter_seq[i]@] 0 <= i < seq.len()
    implies iter_seq[i]@.len() > 0 && !pat@.is_subrange_of(iter_seq[i]@.drop_last())
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(seq[i] =~= pat@);
        assert(seq[i] == pat@);
        assert(iter_seq[i]@ == gap[i] + pat@);
        assert(iter_seq[i]@.len() > 0);
        if gap[i].len() == 0 {
            assert(iter_seq[i]@.drop_last().len() < pat@.len());
            assert(!pat@.is_subrange_of(iter_seq[i]@.drop_last()));
        } else {
            assert(gap[i].len() > 0 ==> !pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@));
            assert_by_contradiction!(!pat@.is_subrange_of(iter_seq[i]@.drop_last()), {
                let part = iter_seq[i]@;
                let dl = part.drop_last();
                let k = choose |k: int| 0 <= k <= dl.len() - pat@.len()
                    && pat@ =~= #[trigger] dl.subrange(k, k + pat@.len());
                assert(dl == part.subrange(0, part.len() - 1));
                assert(dl.subrange(k, k + pat@.len()) == part.subrange(k, k + pat@.len())) by {
                    part.lemma_slice_of_slice(0, part.len() - 1, k, k + pat@.len());
                }
                assert(pat@ =~= part.subrange(k, k + pat@.len()));
                assert(pat@.is_subrange_of(part));
                lemma_seq_is_subrange_alt(part, pat@);
                if k == 0 {
                    assert(pat@.is_prefix_of(part));
                } else {
                    assert(k < part.len() - pat@.len());
                    assert(pat@.is_infix_of(part));
                }
                assert(!pat@.is_prefix_of(part) && !pat@.is_infix_of(part));
            });
        }
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@.len() > 0 && !pat@.is_subrange_of(iter_seq.last()@.drop_last())) by {
            assert(iter_seq.last()@ == gap.last());
            assert(!(pat@.is_subrange_of(gap.last())));
            assert_by_contradiction!(!pat@.is_subrange_of(iter_seq.last()@.drop_last()), {
                let part = iter_seq.last()@;
                let dl = part.drop_last();
                let k = choose |k: int| 0 <= k <= dl.len() - pat@.len()
                    && pat@ =~= #[trigger] dl.subrange(k, k + pat@.len());
                assert(dl == part.subrange(0, part.len() - 1));
                assert(dl.subrange(k, k + pat@.len()) == part.subrange(k, k + pat@.len())) by {
                    part.lemma_slice_of_slice(0, part.len() - 1, k, k + pat@.len());
                }
                assert(pat@ =~= part.subrange(k, k + pat@.len()));
                assert(pat@.is_subrange_of(part));
            });
        }
    }
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies #[trigger] pat@.is_suffix_of(iter_seq[i]@)
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(seq[i] =~= pat@);
        assert(seq[i] == pat@);
        assert(iter_seq[i]@ == gap[i] + pat@);
        assert(pat@.is_suffix_of(iter_seq[i]@));
    }
    // #3
    assert(s == iter_seq.map_values(|ss: &'a str| ss@).flatten()) by {
        if iter_seq.len() == seq.len() {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    assert(gap.last().len() == 0);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        } else {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    let s1 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    s1.lemma_flatten_and_flatten_alt_are_equivalent();
                    assert(gap.last() == iter_seq.last()@);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten_alt() + iter_seq.last()@; {
                    reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                    assert_seqs_equal!(iter_seq.drop_last().map_values(|ss: &'a str| ss@) == iter_seq.map_values(|ss: &'a str| ss@).drop_last());
                    assert(iter_seq.map_values(|ss: &'a str| ss@).last() == iter_seq.last()@);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten_alt(); {
                    iter_seq.map_values(|ss: &'a str| ss@).lemma_flatten_and_flatten_alt_are_equivalent();
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        }
    }
}

/// Proof that links the full spec to `str::rsplit` with a `char` pattern.
pub broadcast proof fn lemma_str_rsplit_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplit_iter_post(s, ch, iter_seq),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // splits cannot contain `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> !(#[trigger] iter_seq[i]@.contains(ch)),
        // delimiters and splits make up the original string
        s == iter_seq.drop_first().map_values(|ss: &'a str| ss@.push(ch))
                .reverse().flatten() + iter_seq.first()@,
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rsplit_iter_post);
    let (seq, gap) = spec_rmatches(s, ch);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| 0 <= i < iter_seq.len()
        implies !(#[trigger] iter_seq[i]@.contains(ch))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(!gap[i].contains(ch));
    }

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let iter_parts = iter_seq.drop_first().map_values(|ss: &'a str| ss@.push(ch));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(seq[i] =~= seq![ch]);
        assert(seq[i] == seq![ch]);
        assert_seqs_equal!(g.push(ch) == g + seq![ch]);
    });
    assert(s == join_parts.reverse().flatten_alt() + gap.first());
    assert(join_parts.reverse() == iter_parts.reverse());
    iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
    assert(iter_parts.reverse().flatten() == iter_parts.reverse().flatten_alt());
    assert(iter_seq.first()@ == gap.first());
}

/// Proof that links the full spec to `str::rsplit` with a closure pattern.
pub broadcast proof fn lemma_str_rsplit_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rsplit_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // splits cannot match `f`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] call_ensures(f, (delim[i],), true)
            &&& s == iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]))
                        .reverse().flatten() + iter_seq.first()@
        },
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rsplit_iter_post);
    let (seq, gap) = spec_rmatches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| 0 <= i < iter_seq.len()
        implies (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(pred));
    }

    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);
    assert(delim.len() == iter_seq.len() - 1);
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] call_ensures(f, (delim[i],), true)
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
    }

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let iter_parts = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        let d = delim[i];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(d == seq[i][0]);
        assert(seq[i].len() == 1);
        assert_seqs_equal!(seq[i] == seq![d]);
        assert_seqs_equal!(g.push(d) == g + seq![d]);
    });
    assert(s == join_parts.reverse().flatten_alt() + gap.first());
    assert(join_parts.reverse() == iter_parts.reverse());
    iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
    assert(iter_parts.reverse().flatten() == iter_parts.reverse().flatten_alt());
    assert(iter_seq.first()@ == gap.first());
}

/// Proof that links the full spec to `str::rsplit` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_rsplit_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplit_iter_post(s, chars, iter_seq),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // splits cannot match `chars`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] chars@.contains(delim[i])
            &&& s == iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]))
                        .reverse().flatten() + iter_seq.first()@
        },
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rsplit_iter_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let pred = |c: char| !chars@.contains(c);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| 0 <= i < iter_seq.len()
        implies (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(pred));
    }

    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);
    assert(delim.len() == iter_seq.len() - 1);
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] chars@.contains(delim[i])
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
    }

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let iter_parts = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        let d = delim[i];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(d == seq[i][0]);
        assert(seq[i].len() == 1);
        assert_seqs_equal!(seq[i] == seq![d]);
        assert_seqs_equal!(g.push(d) == g + seq![d]);
    });
    assert(s == join_parts.reverse().flatten_alt() + gap.first());
    assert(join_parts.reverse() == iter_parts.reverse());
    iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
    assert(iter_parts.reverse().flatten() == iter_parts.reverse().flatten_alt());
    assert(iter_seq.first()@ == gap.first());
}

/// Proof that links the full spec to `str::rsplit` with a string pattern.
pub broadcast proof fn lemma_str_rsplit_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_rsplit_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_rsplit_iter_post(s, pat, iter_seq),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // `pat + split` (apart from the last) cannot have `pat` as a suffix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@),
        // last split cannot have `pat` as a substring
        !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        s == iter_seq.drop_first().map_values(|ss: &'a str| ss@ + pat@)
                .reverse().flatten() + iter_seq.first()@,
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rsplit_iter_post);
    let (seq, gap) = spec_rmatches(s, pat);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@)
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].len() > 0 ==> !pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i]));
    }
    assert(iter_seq.last()@ == gap.last());
    assert(!(pat@.is_subrange_of(gap.last())));

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let iter_parts = iter_seq.drop_first().map_values(|ss: &'a str| ss@ + pat@);
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(seq[i] =~= pat@);
        assert(seq[i] == pat@);
    });
    assert(s == join_parts.reverse().flatten_alt() + gap.first());
    assert(join_parts.reverse() == iter_parts.reverse());
    iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
    assert(iter_parts.reverse().flatten() == iter_parts.reverse().flatten_alt());
    assert(iter_seq.first()@ == gap.first());
}

/// Proof that links the full spec to `str::split_terminator` with a `char` pattern.
pub broadcast proof fn lemma_str_split_terminator_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_terminator_iter_post(s, ch, iter_seq),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // splits cannot contain `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> !(#[trigger] iter_seq[i]@.contains(ch)),
        // delimiters and splits make up the original string
        s.len() > 0 && s.last() == ch
            ==> s == iter_seq.map_values(|ss: &'a str| ss@.push(ch)).flatten(),
        s.len() > 0 && s.last() != ch
            ==> s == iter_seq.drop_last().map_values(|ss: &'a str| ss@.push(ch)).flatten() + iter_seq.last()@,
{
    axiom_char_matches_post(s, ch);
    reveal(str_split_terminator_iter_post);
    let (seq, gap) = spec_matches(s, ch);
    // #1
    if s.len() == 0 {
        lemma_join_alt(seq, gap);
        assert(gap.last().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            assert(seq[0] =~= seq![ch]);
            assert(s[gap.first().len() as int] == ch);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        assert(seq.len() == 0);
    }
    // #2
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < seq.len()
    implies !(#[trigger] iter_seq[i]@.contains(ch))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(!gap[i].contains(ch));
    }
    if iter_seq.len() == seq.len() + 1 {
        iter_seq.last()@ == gap.last();
        assert(!iter_seq.last()@.contains(ch));
    }
    // #3
    if s.len() == 0 { return }
    assert(s.last() == ch <==> gap.last().len() == 0) by {
        lemma_join_alt(seq, gap);
        if gap.last().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
            s1.lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.last() =~= seq![ch]);
            assert(s.last() == seq.last().last());
            assert(s.last() == ch);
        }
        if s.last() == ch {
            assert_by_contradiction!(gap.last().len() == 0, {
                assert(s.last() == gap.last().last());
                assert(!gap.last().contains(ch));
            });
        }
    }
    calc!{
        (==)
        s; {}
        join(seq, gap); { lemma_join_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
    if s.last() == ch {
        let s2 = iter_seq.map_values(|ss: &'a str| ss@.push(ch));
        assert(iter_seq.len() == seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            assert(seq[i] =~= seq![ch]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten();
        }
    } else {
        let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@.push(ch));
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last());
        assert_seqs_equal!(s1 == s2, i => {
            assert(seq[i] =~= seq![ch]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten() + iter_seq.last()@;
        }
    }
}

/// Proof that links the full spec to `str::split_terminator` with a closure pattern.
pub broadcast proof fn lemma_str_split_terminator_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_split_terminator_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // splits cannot match `f`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] call_ensures(f, (delim[i],), true)
            &&& s.len() > 0 && call_ensures(f, (s.last(),), true)
                    ==> {
                        &&& delim.len() == iter_seq.len()
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten()
                    }
            &&& s.len() > 0 && call_ensures(f, (s.last(),), false)
                    ==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten() + iter_seq.last()@
                    }
        },
{
    axiom_closure_matches_post(s, f);
    reveal(str_split_terminator_iter_post);
    let (seq, gap) = spec_matches(s, f);
    let gap_pred = |c: char| call_ensures(f, (c,), false);
    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);

    // #1
    if s.len() == 0 {
        lemma_join_alt(seq, gap);
        assert(gap.last().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            assert(seq[0].len() == 1 && call_ensures(f, (seq[0][0],), true));
            assert(s[gap.first().len() as int] == seq[0][0]);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        assert(seq.len() == 0);
    }
    // #2
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < seq.len()
    implies (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@ == gap.last());
        assert(iter_seq.last()@.all(|c: char| call_ensures(f, (c,), false)));
    }
    // #3
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] call_ensures(f, (delim[i],), true)
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
    }
    if s.len() == 0 { return }
    assert(call_ensures(f, (s.last(),), true) <==> gap.last().len() == 0) by {
        lemma_join_alt(seq, gap);
        if gap.last().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
            s1.lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.last().len() == 1 && call_ensures(f, (seq.last()[0],), true));
            assert(s.last() == seq.last()[0]);
            assert(call_ensures(f, (s.last(),), true));
        }
        if call_ensures(f, (s.last(),), true) {
            assert_by_contradiction!(gap.last().len() == 0, {
                assert(s.last() == gap.last().last());
                assert(gap.last().all(gap_pred));
                assert(gap_pred(gap.last()[gap.last().len() - 1]));
                assert(call_ensures(f, (gap.last()[gap.last().len() - 1],), false));
                gap.last().lemma_index_contains(gap.last().len() - 1);
                assert(gap.last().contains(gap.last().last()));
                assert(call_ensures(f, (gap.last().last(),), false));
                assert(call_ensures(f, (gap.last().last(),), true));
            });
        }
    }
    calc!{
        (==)
        s; {}
        join(seq, gap); { lemma_join_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
    if call_ensures(f, (s.last(),), true) {
        let s2 = iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(iter_seq.len() == seq.len());
        assert(delim.len() == iter_seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i].push(d) == gap[i] + seq![d]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten();
        }
    } else {
        let s2 = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last());
        assert(delim.len() == iter_seq.len() - 1);
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i].push(d) == gap[i] + seq![d]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten() + iter_seq.last()@;
        }
    }
}

/// Proof that links the full spec to `str::split_terminator` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_split_terminator_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_terminator_iter_post(s, chars, iter_seq),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // splits cannot match `chars`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] chars@.contains(delim[i])
            &&& s.len() > 0 && chars@.contains(s.last())
                    ==> {
                        &&& delim.len() == iter_seq.len()
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten()
                    }
            &&& s.len() > 0 && !chars@.contains(s.last())
                    ==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten() + iter_seq.last()@
                    }
        },
{
    axiom_chars_matches_post(s, chars);
    reveal(str_split_terminator_iter_post);
    let (seq, gap) = spec_matches(s, chars);
    let gap_pred = |c: char| !chars@.contains(c);
    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);

    // #1
    if s.len() == 0 {
        lemma_join_alt(seq, gap);
        assert(gap.last().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            assert(seq[0].len() == 1 && chars@.contains(seq[0][0]));
            assert(s[gap.first().len() as int] == seq[0][0]);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        assert(seq.len() == 0);
    }
    // #2
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < seq.len()
    implies (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@ == gap.last());
        assert(iter_seq.last()@.all(|c: char| !chars@.contains(c)));
    }
    // #3
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] chars@.contains(delim[i])
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
    }
    if s.len() == 0 { return }
    assert(chars@.contains(s.last()) <==> gap.last().len() == 0) by {
        lemma_join_alt(seq, gap);
        if gap.last().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
            s1.lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.last().len() == 1 && chars@.contains(seq.last()[0]));
            assert(s.last() == seq.last()[0]);
            assert(chars@.contains(s.last()));
        }
        if chars@.contains(s.last()) {
            assert_by_contradiction!(gap.last().len() == 0, {
                assert(s.last() == gap.last().last());
                assert(gap.last().all(gap_pred));
                assert(gap_pred(gap.last()[gap.last().len() - 1]));
                assert(!chars@.contains(gap.last()[gap.last().len() - 1]));
                gap.last().lemma_index_contains(gap.last().len() - 1);
                assert(gap.last().contains(gap.last().last()));
                assert(!chars@.contains(gap.last().last()));
                assert(chars@.contains(gap.last().last()));
            });
        }
    }
    calc!{
        (==)
        s; {}
        join(seq, gap); { lemma_join_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
    if chars@.contains(s.last()) {
        let s2 = iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(iter_seq.len() == seq.len());
        assert(delim.len() == iter_seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i].push(d) == gap[i] + seq![d]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten();
        }
    } else {
        let s2 = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last());
        assert(delim.len() == iter_seq.len() - 1);
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i].push(d) == gap[i] + seq![d]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten() + iter_seq.last()@;
        }
    }
}

/// Proof that links the full spec to `str::split_terminator` with a string pattern.
pub broadcast proof fn lemma_str_split_terminator_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_split_terminator_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_split_terminator_iter_post(s, pat, iter_seq),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@),
        // last split cannot have `pat` as a substring
        iter_seq.len() > 0 ==> !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        s.len() > 0 ==> {
            ||| s == iter_seq.map_values(|ss: &'a str| ss@ + pat@).flatten()
            ||| iter_seq.last()@.len() > 0 && s == iter_seq.drop_last().map_values(|ss: &'a str| ss@ + pat@).flatten() + iter_seq.last()@
        },
{
    axiom_string_matches_post(s, pat);
    reveal(str_split_terminator_iter_post);
    let (seq, gap) = spec_matches(s, pat);

    // #1
    if s.len() == 0 {
        assert_by_contradiction!(seq.len() == 0, {
            lemma_join_uncons(seq, gap);
            assert(seq[0] =~= pat@);
            assert(seq[0] == pat@);
            assert(s == gap[0] + seq[0] + join(seq.skip(1), gap.skip(1)));
            assert(s.len() >= pat@.len());
        });
        assert(gap.last().len() == 0);
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        assert(seq.len() == 0);
        lemma_join_alt(seq, gap);
        assert(s == gap.last());
        assert(gap.last().len() == 0);
        assert(s.len() == 0);
    }

    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);

    // #2
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@)
    by {
        assert(i < seq.len());
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].len() > 0 ==> !pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@));
    }
    if iter_seq.len() > 0 {
        if iter_seq.len() == seq.len() + 1 {
            assert(iter_seq.last()@ == gap.last());
            assert(!(pat@.is_subrange_of(gap.last())));
        } else {
            assert(iter_seq.len() == seq.len());
            assert(gap.last().len() == 0);
            assert(iter_seq.last()@ == gap[seq.len() - 1]);
            assert_by_contradiction!(!(pat@.is_subrange_of(iter_seq.last()@)), {
                let g = iter_seq.last()@;
                let k = choose |k: int| 0 <= k <= g.len() - pat@.len()
                    && pat@ =~= #[trigger] g.subrange(k, k + pat@.len());
                assert(g == gap[seq.len() - 1]);
                assert(g.len() > 0 || g.len() == 0);
                if k == 0 {
                    assert(pat@.is_prefix_of(g + pat@));
                } else {
                    assert(0 < k < (g + pat@).len() - pat@.len());
                    assert((g + pat@).subrange(k, k + pat@.len()) == g.subrange(k, k + pat@.len()));
                    assert(pat@ =~= (g + pat@).subrange(k, k + pat@.len()));
                    assert(pat@.is_infix_of(g + pat@));
                }
                assert(g.len() > 0 ==> !pat@.is_prefix_of(g + pat@) && !pat@.is_infix_of(g + pat@));
                if g.len() == 0 {
                    assert(false);
                }
            });
        }
    }

    // #3
    if s.len() == 0 { return }
    calc!{
        (==)
        s; {}
        join(seq, gap); { lemma_join_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
    if gap.last().len() == 0 {
        let s2 = iter_seq.map_values(|ss: &'a str| ss@ + pat@);
        assert(iter_seq.len() == seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i]@ == gap[i]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten();
        }
    } else {
        let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@ + pat@);
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i]@ == gap[i]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten() + iter_seq.last()@;
        }
    }
}

/// Proof that links the full spec to `str::rsplit_terminator` with a `char` pattern.
pub broadcast proof fn lemma_str_rsplit_terminator_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplit_terminator_iter_post(s, ch, iter_seq),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // splits cannot contain `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> !(#[trigger] iter_seq[i]@.contains(ch)),
        // delimiters and splits make up the original string
        s.len() > 0 && s.last() == ch
            ==> s == iter_seq.map_values(|ss: &'a str| ss@.push(ch)).reverse().flatten(),
        s.len() > 0 && s.last() != ch
            ==> s == iter_seq.drop_first().map_values(|ss: &'a str| ss@.push(ch)).reverse().flatten() + iter_seq.first()@,
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rsplit_terminator_iter_post);
    let (seq, gap) = spec_rmatches(s, ch);

    // #1
    if s.len() == 0 {
        lemma_rjoin_alt(seq, gap);
        assert(gap.first().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            lemma_rjoin_uncons(seq, gap);
            assert(seq[0] =~= seq![ch]);
            assert(s.len() > 0);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        if gap.first().len() == 0 {
            assert(gap.len() == 1);
            assert(seq.len() == 0);
            assert(s == rjoin(seq, gap));
            assert(s == gap.first());
            assert(s.len() == 0);
        } else {
            assert(gap.len() > 0);
            assert(false);
        }
    }
    // #2
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < iter_seq.len()
    implies !(#[trigger] iter_seq[i]@.contains(ch))
    by {
        if gap.first().len() == 0 {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(!gap[i + 1].contains(ch));
        } else {
            assert(iter_seq[i]@ == gap[i]);
            assert(!gap[i].contains(ch));
        }
    }
    // #3
    if s.len() == 0 { return }
    assert(s.last() == ch <==> gap.first().len() == 0) by {
        lemma_rjoin_alt(seq, gap);
        if gap.first().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
            s1.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.first() =~= seq![ch]);
            assert(s.last() == seq.first().last());
            assert(s.last() == ch);
        }
        if s.last() == ch {
            assert_by_contradiction!(gap.first().len() == 0, {
                assert(s.last() == gap.first().last());
                assert(!gap.first().contains(ch));
            });
        }
    }
    calc!{
        (==)
        s; {}
        rjoin(seq, gap); { lemma_rjoin_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss).reverse().flatten_alt() + gap.first();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
    if s.last() == ch {
        let s2 = iter_seq.map_values(|ss: &'a str| ss@.push(ch));
        assert(gap.first().len() == 0);
        assert(iter_seq.len() == seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(seq[i] =~= seq![ch]);
            assert(seq[i] == seq![ch]);
            assert_seqs_equal!(gap[i + 1].push(ch) == gap[i + 1] + seq![ch]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten_alt(); {}
            s2.reverse().flatten();
        }
    } else {
        let s2 = iter_seq.drop_first().map_values(|ss: &'a str| ss@.push(ch));
        assert(gap.first().len() > 0);
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.first()@ == gap.first());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
            assert(iter_seq[i + 1]@ == gap[i + 1]);
            assert(seq[i] =~= seq![ch]);
            assert(seq[i] == seq![ch]);
            assert_seqs_equal!(gap[i + 1].push(ch) == gap[i + 1] + seq![ch]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten() + iter_seq.first()@;
        }
    }
}

/// Proof that links the full spec to `str::rsplit_terminator` with a closure pattern.
pub broadcast proof fn lemma_str_rsplit_terminator_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rsplit_terminator_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // splits cannot match `f`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] call_ensures(f, (delim[i],), true)
            &&& s.len() > 0 && call_ensures(f, (s.last(),), true)
                    ==> {
                        &&& delim.len() == iter_seq.len()
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten()
                    }
            &&& s.len() > 0 && call_ensures(f, (s.last(),), false)
                    ==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten() + iter_seq.first()@
                    }
        },
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rsplit_terminator_iter_post);
    let (seq, gap) = spec_rmatches(s, f);
    let gap_pred = |c: char| call_ensures(f, (c,), false);
    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);

    if s.len() == 0 {
        lemma_rjoin_alt(seq, gap);
        assert(gap.first().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            lemma_rjoin_uncons(seq, gap);
            assert(seq[0].len() == 1 && call_ensures(f, (seq[0][0],), true));
            assert(s.len() > 0);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        if gap.first().len() == 0 {
            assert(gap.len() == 1);
            assert(seq.len() == 0);
            assert(s == rjoin(seq, gap));
            assert(s == gap.first());
            assert(s.len() == 0);
        } else {
            assert(gap.len() > 0);
            assert(false);
        }
    }
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < iter_seq.len()
    implies (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false))
    by {
        if gap.first().len() == 0 {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(gap[i + 1].all(gap_pred));
        } else {
            assert(iter_seq[i]@ == gap[i]);
            assert(gap[i].all(gap_pred));
        }
    }
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] call_ensures(f, (delim[i],), true)
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
    }
    if s.len() == 0 { return }
    assert(call_ensures(f, (s.last(),), true) <==> gap.first().len() == 0) by {
        lemma_rjoin_alt(seq, gap);
        if gap.first().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
            s1.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(s.last() == seq.first()[0]);
            assert(call_ensures(f, (s.last(),), true));
        }
        if call_ensures(f, (s.last(),), true) {
            assert_by_contradiction!(gap.first().len() == 0, {
                assert(s.last() == gap.first().last());
                assert(gap.first().all(gap_pred));
                assert(gap_pred(gap.first()[gap.first().len() - 1]));
                assert(call_ensures(f, (gap.first()[gap.first().len() - 1],), false));
                gap.first().lemma_index_contains(gap.first().len() - 1);
                assert(gap.first().contains(gap.first().last()));
                assert(call_ensures(f, (gap.first().last(),), false));
                assert(call_ensures(f, (gap.first().last(),), true));
            });
        }
    }
    calc!{
        (==)
        s; {}
        rjoin(seq, gap); { lemma_rjoin_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss).reverse().flatten_alt() + gap.first();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
    if call_ensures(f, (s.last(),), true) {
        let s2 = iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(gap.first().len() == 0);
        assert(iter_seq.len() == seq.len());
        assert(delim.len() == iter_seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i + 1].push(d) == gap[i + 1] + seq![d]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten_alt(); {}
            s2.reverse().flatten();
        }
    } else {
        let s2 = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(gap.first().len() > 0);
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.first()@ == gap.first());
        assert(delim.len() == iter_seq.len() - 1);
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
            assert(iter_seq[i + 1]@ == gap[i + 1]);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i + 1].push(d) == gap[i + 1] + seq![d]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten() + iter_seq.first()@;
        }
    }
}

/// Proof that links the full spec to `str::rsplit_terminator` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_rsplit_terminator_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplit_terminator_iter_post(s, chars, iter_seq),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // splits cannot match `chars`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] chars@.contains(delim[i])
            &&& s.len() > 0 && chars@.contains(s.last())
                    ==> {
                        &&& delim.len() == iter_seq.len()
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten()
                    }
            &&& s.len() > 0 && !chars@.contains(s.last())
                    ==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten() + iter_seq.first()@
                    }
        },
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rsplit_terminator_iter_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let gap_pred = |c: char| !chars@.contains(c);
    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);

    if s.len() == 0 {
        lemma_rjoin_alt(seq, gap);
        assert(gap.first().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            lemma_rjoin_uncons(seq, gap);
            assert(seq[0].len() == 1 && chars@.contains(seq[0][0]));
            assert(s.len() > 0);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        if gap.first().len() == 0 {
            assert(gap.len() == 1);
            assert(seq.len() == 0);
            assert(s == rjoin(seq, gap));
            assert(s == gap.first());
            assert(s.len() == 0);
        } else {
            assert(gap.len() > 0);
            assert(false);
        }
    }
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < iter_seq.len()
    implies (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c))
    by {
        if gap.first().len() == 0 {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(gap[i + 1].all(gap_pred));
        } else {
            assert(iter_seq[i]@ == gap[i]);
            assert(gap[i].all(gap_pred));
        }
    }
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] chars@.contains(delim[i])
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
    }
    if s.len() == 0 { return }
    assert(chars@.contains(s.last()) <==> gap.first().len() == 0) by {
        lemma_rjoin_alt(seq, gap);
        if gap.first().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
            s1.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(s.last() == seq.first()[0]);
            assert(chars@.contains(s.last()));
        }
        if chars@.contains(s.last()) {
            assert_by_contradiction!(gap.first().len() == 0, {
                assert(s.last() == gap.first().last());
                assert(gap.first().all(gap_pred));
                assert(gap_pred(gap.first()[gap.first().len() - 1]));
                assert(!chars@.contains(gap.first()[gap.first().len() - 1]));
                gap.first().lemma_index_contains(gap.first().len() - 1);
                assert(gap.first().contains(gap.first().last()));
                assert(!chars@.contains(gap.first().last()));
                assert(chars@.contains(gap.first().last()));
            });
        }
    }
    calc!{
        (==)
        s; {}
        rjoin(seq, gap); { lemma_rjoin_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss).reverse().flatten_alt() + gap.first();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
    if chars@.contains(s.last()) {
        let s2 = iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(gap.first().len() == 0);
        assert(iter_seq.len() == seq.len());
        assert(delim.len() == iter_seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i + 1].push(d) == gap[i + 1] + seq![d]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten_alt(); {}
            s2.reverse().flatten();
        }
    } else {
        let s2 = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(gap.first().len() > 0);
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.first()@ == gap.first());
        assert(delim.len() == iter_seq.len() - 1);
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
            assert(iter_seq[i + 1]@ == gap[i + 1]);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i + 1].push(d) == gap[i + 1] + seq![d]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten() + iter_seq.first()@;
        }
    }
}

/// Proof that links the full spec to `str::rsplit_terminator` with a string pattern.
pub broadcast proof fn lemma_str_rsplit_terminator_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_rsplit_terminator_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_rsplit_terminator_iter_post(s, pat, iter_seq),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // `pat + split` (apart from the last) cannot have `pat` as a suffix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@),
        // last split cannot have `pat` as a substring
        iter_seq.len() > 0 ==> !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        s.len() > 0 ==> {
            ||| s == iter_seq.map_values(|ss: &'a str| ss@ + pat@).reverse().flatten()
            ||| iter_seq.first()@.len() > 0 && s == iter_seq.drop_first().map_values(|ss: &'a str| ss@ + pat@).reverse().flatten() + iter_seq.first()@
        },
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rsplit_terminator_iter_post);
    let (seq, gap) = spec_rmatches(s, pat);

    if s.len() == 0 {
        assert_by_contradiction!(seq.len() == 0, {
            lemma_rjoin_uncons(seq, gap);
            assert(seq[0] =~= pat@);
            assert(seq[0] == pat@);
            assert(s.len() >= pat@.len());
        });
        assert(gap.first().len() == 0);
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        if gap.first().len() == 0 {
            assert(gap.len() == 1);
            assert(seq.len() == 0);
            assert(s == rjoin(seq, gap));
            assert(s == gap.first());
            assert(s.len() == 0);
        } else {
            assert(gap.len() > 0);
            assert(false);
        }
    }
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@)
    by {
        if gap.first().len() == 0 {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(gap[i + 1].len() > 0 ==> !pat@.is_suffix_of(pat@ + gap[i + 1]) && !pat@.is_infix_of(pat@ + gap[i + 1]));
        } else {
            assert(iter_seq[i]@ == gap[i]);
            assert(gap[i].len() > 0 ==> !pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i]));
        }
    }
    if iter_seq.len() > 0 {
        if gap.first().len() == 0 {
            assert(iter_seq.last()@ == gap.last());
            assert(!(pat@.is_subrange_of(gap.last())));
        } else if iter_seq.len() == seq.len() + 1 {
            assert(iter_seq.last()@ == gap.last());
            assert(!(pat@.is_subrange_of(gap.last())));
        } else {
            assert(false);
        }
    }
    if s.len() == 0 { return }
    calc!{
        (==)
        s; {}
        rjoin(seq, gap); { lemma_rjoin_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss).reverse().flatten_alt() + gap.first();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
    if gap.first().len() == 0 {
        let s2 = iter_seq.map_values(|ss: &'a str| ss@ + pat@);
        assert(iter_seq.len() == seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten_alt(); {}
            s2.reverse().flatten();
        }
    } else {
        let s2 = iter_seq.drop_first().map_values(|ss: &'a str| ss@ + pat@);
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.first()@ == gap.first());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
            assert(iter_seq[i + 1]@ == gap[i + 1]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten() + iter_seq.first()@;
        }
    }
}

/// Proof that links the full spec to `str::splitn` with a `char` pattern.
pub broadcast proof fn lemma_str_splitn_iter_char<'a>(s: Seq<char>, n: usize, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_splitn_iter_post(s, n, ch, iter_seq),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // splits (apart from the last) cannot contain `ch`
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> !(#[trigger] iter_seq[i]@.contains(ch)),
        // last split (if not the `n`th) cannot contain `ch` as well
        iter_seq.len() < n ==> !iter_seq.last()@.contains(ch),
        // delimiters and splits make up the original string
        n > 0 ==>
            s == iter_seq.drop_last()
                    .map_values(|ss: &'a str| ss@.push(ch))
                    .flatten() + iter_seq.last()@,
{
    axiom_char_matches_post(s, ch);
    reveal(str_splitn_iter_post);
    let (seq, gap) = spec_matches(s, ch);
    // #1
    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies !(#[trigger] iter_seq[i]@.contains(ch))
    by { assert(!gap[i].contains(ch)) }
    // #3
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            join(seq.skip(iter_seq.len() - 1), gap.skip(iter_seq.len() - 1)); {}
            join(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
            gap.last();
        }
        assert(!gap.last().contains(ch));
    }
    // #4
    if n > 0 {
        let k = iter_seq.len() - 1;
        assert(0 <= k <= seq.len());
        lemma_join_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss);
        let iter_parts = iter_seq.drop_last().map_values(|ss: &'a str| ss@.push(ch));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == gap[i]);
            assert(seq[i] =~= seq![ch]);
        });
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, k); }
            join_parts.flatten() + join(seq.skip(k), gap.skip(k)); {}
            iter_parts.flatten() + iter_seq.last()@;
        }
    }
}

/// Proof that links the full spec to `str::splitn` with a closure pattern.
pub broadcast proof fn lemma_str_splitn_iter_closure<'a, F>(s: Seq<char>, n: usize, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_splitn_iter_post(s, n, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // splits (apart from the last) cannot match `f`
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false)),
        // last split (if not the `n`th) cannot match `f` as well
        iter_seq.len() < n ==> iter_seq.last()@.all(|c: char| call_ensures(f, (c,), false)),
        // delimiters and splits make up the original string
        n > 0 ==> exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] call_ensures(f, (delim[i],), true)
            &&& s == iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.push(delim[i]))
                    .flatten() + iter_seq.last()@
        },
{
    axiom_closure_matches_post(s, f);
    reveal(str_splitn_iter_post);
    let (seq, gap) = spec_matches(s, f);
    let gap_pred = |c: char| call_ensures(f, (c,), false);
    // #1
    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    // #3
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            join(seq.skip(iter_seq.len() - 1), gap.skip(iter_seq.len() - 1)); {}
            join(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
            gap.last();
        }
        assert(gap.last().all(gap_pred));
    }
    // #4
    if n > 0 {
        let delim = Seq::<char>::new((iter_seq.len() - 1) as nat, |i: int| seq[i][0]);
        assert forall |i: int| 0 <= i < delim.len()
            implies #[trigger] call_ensures(f, (delim[i],), true)
        by {
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
        }
        let k = iter_seq.len() - 1;
        assert(0 <= k <= seq.len());
        lemma_join_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == gap[i]);
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![delim[i]]);
        });
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, k); }
            join_parts.flatten() + join(seq.skip(k), gap.skip(k)); {}
            iter_parts.flatten() + iter_seq.last()@;
        }
        assert(delim.len() == iter_seq.len() - 1);
        assert(exists |d: Seq<char>| {
            &&& #[trigger] d.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < d.len()
                    ==> #[trigger] call_ensures(f, (d[i],), true)
            &&& s == iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.push(d[i]))
                    .flatten() + iter_seq.last()@
        });
    }
}

/// Proof that links the full spec to `str::splitn` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_splitn_iter_chars<'a, 'b>(s: Seq<char>, n: usize, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_splitn_iter_post(s, n, chars, iter_seq),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // splits (apart from the last) cannot match `chars`
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c)),
        // last split (if not the `n`th) cannot match `chars` as well
        iter_seq.len() < n ==> iter_seq.last()@.all(|c: char| !chars@.contains(c)),
        // delimiters and splits make up the original string
        n > 0 ==> exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] chars@.contains(delim[i])
            &&& s == iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.push(delim[i]))
                    .flatten() + iter_seq.last()@
        },
{
    axiom_chars_matches_post(s, chars);
    reveal(str_splitn_iter_post);
    let (seq, gap) = spec_matches(s, chars);
    let gap_pred = |c: char| !chars@.contains(c);
    // #1
    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    // #3
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            join(seq.skip(iter_seq.len() - 1), gap.skip(iter_seq.len() - 1)); {}
            join(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
            gap.last();
        }
        assert(gap.last().all(gap_pred));
    }
    // #4
    if n > 0 {
        let delim = Seq::<char>::new((iter_seq.len() - 1) as nat, |i: int| seq[i][0]);
        assert forall |i: int| 0 <= i < delim.len()
            implies #[trigger] chars@.contains(delim[i])
        by {
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
        }
        let k = iter_seq.len() - 1;
        assert(0 <= k <= seq.len());
        lemma_join_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == gap[i]);
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![delim[i]]);
        });
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, k); }
            join_parts.flatten() + join(seq.skip(k), gap.skip(k)); {}
            iter_parts.flatten() + iter_seq.last()@;
        }
        assert(delim.len() == iter_seq.len() - 1);
        assert(exists |d: Seq<char>| {
            &&& #[trigger] d.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < d.len()
                    ==> #[trigger] chars@.contains(d[i])
            &&& s == iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.push(d[i]))
                    .flatten() + iter_seq.last()@
        });
    }
}

/// Proof that links the full spec to `str::splitn` with a string pattern.
pub broadcast proof fn lemma_str_splitn_iter_string<'a, 'b>(s: Seq<char>, n: usize, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_splitn_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_splitn_iter_post(s, n, pat, iter_seq),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@),
        // last split (if not the `n`th) cannot match `pat` as well
        iter_seq.len() < n ==> !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        n > 0 ==> s == iter_seq.drop_last().map(|i: int, ss: &'a str| ss@ + pat@).flatten() + iter_seq.last()@,
{
    axiom_string_matches_post(s, pat);
    reveal(str_splitn_iter_post);
    let (seq, gap) = spec_matches(s, pat);
    // #1
    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    // #2
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@)
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].len() > 0 ==> !pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@));
    }
    // #3
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            join(seq.skip(iter_seq.len() - 1), gap.skip(iter_seq.len() - 1)); {}
            join(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
            gap.last();
        }
        assert(!(pat@.is_subrange_of(gap.last())));
    }
    // #4
    if n > 0 {
        let k = iter_seq.len() - 1;
        assert(0 <= k <= seq.len());
        lemma_join_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@ + pat@);
        assert_seqs_equal!(join_parts == iter_parts, i => {
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == gap[i]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, k); }
            join_parts.flatten() + join(seq.skip(k), gap.skip(k)); {}
            iter_parts.flatten() + iter_seq.last()@;
        }
    }
}

/// Proof that links the full spec to `str::rsplitn` with a `char` pattern.
pub broadcast proof fn lemma_str_rsplitn_iter_char<'a>(s: Seq<char>, n: usize, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplitn_iter_post(s, n, ch, iter_seq),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // splits (apart from the last) cannot contain `ch`
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> !(#[trigger] iter_seq[i]@.contains(ch)),
        // last split (if not the `n`th) cannot contain `ch` as well
        iter_seq.len() < n ==> !iter_seq.last()@.contains(ch),
        // delimiters and splits make up the original string
        n > 0 ==>
            s == iter_seq.last()@ + iter_seq.drop_last()
                    .map_values(|ss: &'a str| ss@.insert(0, ch))
                    .reverse().flatten(),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rsplitn_iter_post);
    let (seq, gap) = spec_rmatches(s, ch);
    let k = iter_seq.len() - 1;

    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
        implies !(#[trigger] iter_seq[i]@.contains(ch))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(!gap[i].contains(ch));
    }
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            rjoin(seq.skip(k), gap.skip(k)); {}
            rjoin(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            }
            gap.last();
        }
        assert(!gap.last().contains(ch));
    }
    if n > 0 {
        assert(0 <= k <= seq.len());
        lemma_rjoin_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
        let iter_parts = iter_seq.drop_last().map_values(|ss: &'a str| ss@.insert(0, ch));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            let g = gap[i];
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == g);
            assert(seq[i] =~= seq![ch]);
            assert(seq[i] == seq![ch]);
            g.insert_ensures(0, ch);
            assert_seqs_equal!(g.insert(0, ch) == seq![ch] + g);
        });
        assert(join_parts.reverse() == iter_parts.reverse());
        iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_at(seq, gap, k); }
            rjoin(seq.skip(k), gap.skip(k)) + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten();
        }
    }
}

/// Proof that links the full spec to `str::rsplitn` with a closure pattern.
pub broadcast proof fn lemma_str_rsplitn_iter_closure<'a, F>(s: Seq<char>, n: usize, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rsplitn_iter_post(s, n, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // splits (apart from the last) cannot match `f`
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false)),
        // last split (if not the `n`th) cannot match `f` as well
        iter_seq.len() < n ==> iter_seq.last()@.all(|c: char| call_ensures(f, (c,), false)),
        // delimiters and splits make up the original string
        n > 0 ==> exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] call_ensures(f, (delim[i],), true)
            &&& s == iter_seq.last()@ + iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.insert(0, delim[i]))
                    .reverse().flatten()
        },
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rsplitn_iter_post);
    let (seq, gap) = spec_rmatches(s, f);
    let gap_pred = |c: char| call_ensures(f, (c,), false);
    let k = iter_seq.len() - 1;

    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
        implies (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            rjoin(seq.skip(k), gap.skip(k)); {}
            rjoin(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            }
            gap.last();
        }
        assert(gap.last().all(gap_pred));
    }
    if n > 0 {
        assert(0 <= k <= seq.len());
        let delim = Seq::<char>::new(k as nat, |i: int| seq[i][0]);
        assert(delim.len() == iter_seq.len() - 1);
        assert forall |i: int| 0 <= i < delim.len()
            implies #[trigger] call_ensures(f, (delim[i],), true)
        by {
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
        }

        lemma_rjoin_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.insert(0, delim[i]));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            let g = gap[i];
            let d = delim[i];
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == g);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            g.insert_ensures(0, d);
            assert_seqs_equal!(g.insert(0, d) == seq![d] + g);
        });
        assert(join_parts.reverse() == iter_parts.reverse());
        iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_at(seq, gap, k); }
            rjoin(seq.skip(k), gap.skip(k)) + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten();
        }
    }
}

/// Proof that links the full spec to `str::rsplitn` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_rsplitn_iter_chars<'a, 'b>(s: Seq<char>, n: usize, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplitn_iter_post(s, n, chars, iter_seq),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // splits (apart from the last) cannot match `chars`
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c)),
        // last split (if not the `n`th) cannot match `chars` as well
        iter_seq.len() < n ==> iter_seq.last()@.all(|c: char| !chars@.contains(c)),
        // delimiters and splits make up the original string
        n > 0 ==> exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] chars@.contains(delim[i])
            &&& s == iter_seq.last()@ + iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.insert(0, delim[i]))
                    .reverse().flatten()
        },
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rsplitn_iter_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let gap_pred = |c: char| !chars@.contains(c);
    let k = iter_seq.len() - 1;

    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
        implies (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            rjoin(seq.skip(k), gap.skip(k)); {}
            rjoin(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            }
            gap.last();
        }
        assert(gap.last().all(gap_pred));
    }
    if n > 0 {
        assert(0 <= k <= seq.len());
        let delim = Seq::<char>::new(k as nat, |i: int| seq[i][0]);
        assert(delim.len() == iter_seq.len() - 1);
        assert forall |i: int| 0 <= i < delim.len()
            implies #[trigger] chars@.contains(delim[i])
        by {
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
        }

        lemma_rjoin_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.insert(0, delim[i]));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            let g = gap[i];
            let d = delim[i];
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == g);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            g.insert_ensures(0, d);
            assert_seqs_equal!(g.insert(0, d) == seq![d] + g);
        });
        assert(join_parts.reverse() == iter_parts.reverse());
        iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_at(seq, gap, k); }
            rjoin(seq.skip(k), gap.skip(k)) + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten();
        }
    }
}

/// Proof that links the full spec to `str::rsplitn` with a string pattern.
pub broadcast proof fn lemma_str_rsplitn_iter_string<'a, 'b>(s: Seq<char>, n: usize, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_rsplitn_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_rsplitn_iter_post(s, n, pat, iter_seq),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // `pat + split` (apart from the last) cannot have `pat` as a suffix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@),
        // last split (if not the `n`th) cannot match `pat` as well
        iter_seq.len() < n ==> !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        n > 0 ==> s == iter_seq.last()@ + iter_seq.drop_last()
                        .map(|i: int, ss: &'a str| pat@ + ss@)
                        .reverse().flatten(),
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rsplitn_iter_post);
    let (seq, gap) = spec_rmatches(s, pat);
    let k = iter_seq.len() - 1;

    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@)
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].len() > 0 ==> !pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i]));
    }
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            rjoin(seq.skip(k), gap.skip(k)); {}
            rjoin(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            }
            gap.last();
        }
        assert(!(pat@.is_subrange_of(gap.last())));
    }
    if n > 0 {
        assert(0 <= k <= seq.len());
        lemma_rjoin_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| pat@ + ss@);
        assert_seqs_equal!(join_parts == iter_parts, i => {
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == gap[i]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        assert(join_parts.reverse() == iter_parts.reverse());
        iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_at(seq, gap, k); }
            rjoin(seq.skip(k), gap.skip(k)) + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten();
        }
    }
}

/// Proof that links the full spec to `str::split_once` with a `char` pattern.
pub broadcast proof fn lemma_str_split_once_char<'a>(s: Seq<char>, ch: char, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_split_once_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => !s.contains(ch),
                Some((head, tail)) => {
                    // `head` does not contain `ch`
                    &&& !head@.contains(ch)
                    // `head` and `tail` make up the original string
                    &&& s == head@.push(ch) + tail@
                },
            }
        }),
{
    axiom_char_matches_post(s, ch);
    reveal(str_split_once_post);
    let (seq, gap) = spec_matches(s, ch);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(!s.contains(ch));
        },
        Some((head, tail)) => {
            assert(head@ == gap.first());
            assert(!head@.contains(ch));
            assert(seq.first() == seq![ch]);
            assert(tail@ == join(seq.skip(1), gap.skip(1)));
            let rest = join(seq.skip(1), gap.skip(1));
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == gap.first() + parts.flatten());
            assert(s == gap.first() + seq[0] + rest);
            assert_seqs_equal!(head@.push(ch) == gap.first() + seq![ch]);
            assert(s == head@.push(ch) + tail@);
        },
    }
}

/// Proof that links the full spec to `str::split_once` with a closure pattern.
pub broadcast proof fn lemma_str_split_once_closure<'a, F>(s: Seq<char>, f: F, ret: Option<(&'a str, &'a str)>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_split_once_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ({
            match ret {
                None => forall|i: int| 0 <= i < s.len() ==> #[trigger] call_ensures(f, (s[i],), false),
                Some((head, tail)) => {
                    // `head` does not match `f`
                    &&& forall|i: int| 0 <= i < head@.len() ==> #[trigger] call_ensures(f, (head@[i],), false)
                    // `head` and `tail` make up the original string
                    &&& head@.is_prefix_of(s)
                    &&& tail@.is_suffix_of(s)
                    &&& head@.len() + tail@.len() == s.len() - 1
                    &&& call_ensures(f, (s[head@.len() as int],), true)
                },
            }
        }),
{
    axiom_closure_matches_post(s, f);
    reveal(str_split_once_post);
    let (seq, gap) = spec_matches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < s.len()
                implies #[trigger] call_ensures(f, (s[i],), false)
            by {
                assert(s[i] == gap.first()[i]);
                assert(pred(gap.first()[i]));
            }
        },
        Some((head, tail)) => {
            assert(head@ == gap.first());
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < head@.len()
                implies #[trigger] call_ensures(f, (head@[i],), false)
            by {
                assert(pred(gap.first()[i]));
            }
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(tail@ == join(seq.skip(1), gap.skip(1)));
            let rest = join(seq.skip(1), gap.skip(1));
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == gap.first() + parts.flatten());
            assert(s == head@ + seq[0] + tail@);
            let d = seq[0][0];
            assert_seqs_equal!(seq[0] == seq![d]);
            assert(s == head@ + seq![d] + tail@);
            assert(head@.is_prefix_of(s));
            assert(tail@.is_suffix_of(s));
            assert(head@.len() + tail@.len() == s.len() - 1);
            assert(s[head@.len() as int] == d);
            assert(call_ensures(f, (s[head@.len() as int],), true));
        },
    }
}

/// Proof that links the full spec to `str::split_once` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_split_once_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_split_once_post(s, chars, ret),
    ensures
        ({
            match ret {
                None => forall|i: int| 0 <= i < s.len() ==> !(#[trigger] chars@.contains(s[i])),
                Some((head, tail)) => {
                    // `head` does not match `chars`
                    &&& forall|i: int| 0 <= i < head@.len() ==> !(#[trigger] chars@.contains(head@[i]))
                    // `head` and `tail` make up the original string
                    &&& head@.is_prefix_of(s)
                    &&& tail@.is_suffix_of(s)
                    &&& head@.len() + tail@.len() == s.len() - 1
                    &&& chars@.contains(s[head@.len() as int])
                },
            }
        }),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_split_once_post);
    let (seq, gap) = spec_matches(s, chars);
    let pred = |c: char| !chars@.contains(c);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < s.len()
                implies !(#[trigger] chars@.contains(s[i]))
            by {
                assert(s[i] == gap.first()[i]);
                assert(pred(gap.first()[i]));
            }
        },
        Some((head, tail)) => {
            assert(head@ == gap.first());
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < head@.len()
                implies !(#[trigger] chars@.contains(head@[i]))
            by {
                assert(pred(gap.first()[i]));
            }
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(tail@ == join(seq.skip(1), gap.skip(1)));
            let rest = join(seq.skip(1), gap.skip(1));
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == gap.first() + parts.flatten());
            assert(s == head@ + seq[0] + tail@);
            let d = seq[0][0];
            assert_seqs_equal!(seq[0] == seq![d]);
            assert(s == head@ + seq![d] + tail@);
            assert(head@.is_prefix_of(s));
            assert(tail@.is_suffix_of(s));
            assert(head@.len() + tail@.len() == s.len() - 1);
            assert(s[head@.len() as int] == d);
            assert(chars@.contains(s[head@.len() as int]));
        },
    }
}

/// Proof that links the full spec to `str::split_once` with a string pattern.
pub broadcast proof fn lemma_str_split_once_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_split_once_post(s, pat, ret),
    ensures
        ({
            match (ret, pat@.len() > 0) {
                (None, _) => !pat@.is_subrange_of(s),
                (Some((head, tail)), false) => head@.len() == 0 && tail@ == s,
                (Some((head, tail)), true) => {
                    // `head + pat` does not match `pat` except at the end
                    &&& head@.len() > 0 ==>
                            !pat@.is_prefix_of(head@ + pat@) && !pat@.is_infix_of(head@ + pat@)
                    // `head` and `tail` make up the original string
                    &&& s == head@ + pat@ + tail@
                },
            }
        }),
{
    axiom_string_matches_post(s, pat);
    reveal(str_split_once_post);
    let (seq, gap) = spec_matches(s, pat);
    match (ret, pat@.len() > 0) {
        (None, _) => {
            assert_by_contradiction!(!pat@.is_subrange_of(s), {
                reveal_with_fuel(Seq::<_>::flatten, 2);
                assert(s == gap.last());
                assert(!pat@.is_subrange_of(gap.last()));
            });
        },
        (Some((head, tail)), pat_empty) => {
            assert(head@ == gap.first());
            assert(head@.len() > 0 ==> !pat@.is_prefix_of(head@ + pat@) && !pat@.is_infix_of(head@ + pat@));
            calc!{
                (==)
                s; {}
                join(seq, gap); {
                    lemma_join_uncons(seq, gap);
                    assert(gap[0] == head@);
                    assert(seq[0] =~= pat@);
                }
                head@ + pat@ + join(seq.skip(1), gap.skip(1)); {}
                head@ + pat@ + tail@;
            }
            if pat_empty {
                assert(head@.len() > 0 ==> !pat@.is_prefix_of(head@ + pat@) && !pat@.is_infix_of(head@ + pat@));
            } else {
                assert(head@.len() == 0);
                assert(tail@ == s);
            }
        },
    }
}

/// Proof that links the full spec to `str::rsplit_once` with a `char` pattern.
pub broadcast proof fn lemma_str_rsplit_once_char<'a>(s: Seq<char>, ch: char, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_rsplit_once_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => !s.contains(ch),
                Some((head, tail)) => {
                    // `tail` does not contain `ch`
                    &&& !tail@.contains(ch)
                    // `head` and `tail` make up the original string
                    &&& s == head@.push(ch) + tail@
                },
            }
        }),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rsplit_once_post);
    let (seq, gap) = spec_rmatches(s, ch);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(gap.first() == s);
            assert(!s.contains(ch));
        },
        Some((head, tail)) => {
            assert(tail@ == gap.first());
            assert(!tail@.contains(ch));
            assert(seq.first() == seq![ch]);
            assert(head@ == rjoin(seq.skip(1), gap.skip(1)));
            lemma_rjoin_uncons(seq, gap);
            assert(s == head@ + seq[0] + tail@);
            assert_seqs_equal!(head@.push(ch) == head@ + seq![ch]);
            assert(s == head@.push(ch) + tail@);
        },
    }
}

/// Proof that links the full spec to `str::rsplit_once` with a closure pattern.
pub broadcast proof fn lemma_str_rsplit_once_closure<'a, F>(s: Seq<char>, f: F, ret: Option<(&'a str, &'a str)>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rsplit_once_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ({
            match ret {
                None => forall|i: int| 0 <= i < s.len() ==> #[trigger] call_ensures(f, (s[i],), false),
                Some((head, tail)) => {
                    // `tail` does not match `f`
                    &&& forall|i: int| 0 <= i < tail@.len() ==> #[trigger] call_ensures(f, (tail@[i],), false)
                    // `head` and `tail` make up the original string
                    &&& head@.is_prefix_of(s)
                    &&& tail@.is_suffix_of(s)
                    &&& head@.len() + tail@.len() == s.len() - 1
                    &&& call_ensures(f, (s[head@.len() as int],), true)
                },
            }
        }),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rsplit_once_post);
    let (seq, gap) = spec_rmatches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < s.len()
                implies #[trigger] call_ensures(f, (s[i],), false)
            by {
                assert(s[i] == gap.first()[i]);
                assert(pred(gap.first()[i]));
            }
        },
        Some((head, tail)) => {
            assert(tail@ == gap.first());
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < tail@.len()
                implies #[trigger] call_ensures(f, (tail@[i],), false)
            by {
                assert(pred(gap.first()[i]));
            }
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(head@ == rjoin(seq.skip(1), gap.skip(1)));
            lemma_rjoin_uncons(seq, gap);
            assert(s == head@ + seq[0] + tail@);
            let d = seq[0][0];
            assert_seqs_equal!(seq[0] == seq![d]);
            assert(s == head@ + seq![d] + tail@);
            assert(head@.is_prefix_of(s));
            assert(tail@.is_suffix_of(s));
            assert(head@.len() + tail@.len() == s.len() - 1);
            assert(s[head@.len() as int] == d);
            assert(call_ensures(f, (s[head@.len() as int],), true));
        },
    }
}

/// Proof that links the full spec to `str::rsplit_once` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_rsplit_once_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_rsplit_once_post(s, chars, ret),
    ensures
        ({
            match ret {
                None => forall|i: int| 0 <= i < s.len() ==> !(#[trigger] chars@.contains(s[i])),
                Some((head, tail)) => {
                    // `tail` does not match `chars`
                    &&& forall|i: int| 0 <= i < tail@.len() ==> !(#[trigger] chars@.contains(tail@[i]))
                    // `head` and `tail` make up the original string
                    &&& head@.is_prefix_of(s)
                    &&& tail@.is_suffix_of(s)
                    &&& head@.len() + tail@.len() == s.len() - 1
                    &&& chars@.contains(s[head@.len() as int])
                },
            }
        }),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rsplit_once_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let pred = |c: char| !chars@.contains(c);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < s.len()
                implies !(#[trigger] chars@.contains(s[i]))
            by {
                assert(s[i] == gap.first()[i]);
                assert(pred(gap.first()[i]));
            }
        },
        Some((head, tail)) => {
            assert(tail@ == gap.first());
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < tail@.len()
                implies !(#[trigger] chars@.contains(tail@[i]))
            by {
                assert(pred(gap.first()[i]));
            }
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(head@ == rjoin(seq.skip(1), gap.skip(1)));
            lemma_rjoin_uncons(seq, gap);
            assert(s == head@ + seq[0] + tail@);
            let d = seq[0][0];
            assert_seqs_equal!(seq[0] == seq![d]);
            assert(s == head@ + seq![d] + tail@);
            assert(head@.is_prefix_of(s));
            assert(tail@.is_suffix_of(s));
            assert(head@.len() + tail@.len() == s.len() - 1);
            assert(s[head@.len() as int] == d);
            assert(chars@.contains(s[head@.len() as int]));
        },
    }
}

/// Proof that links the full spec to `str::rsplit_once` with a string pattern.
pub broadcast proof fn lemma_str_rsplit_once_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_rsplit_once_post(s, pat, ret),
    ensures
        ({
            match (ret, pat@.len() > 0) {
                (None, _) => !pat@.is_subrange_of(s),
                (Some((head, tail)), false) => tail@.len() == 0 && head@ == s,
                (Some((head, tail)), true) => {
                    // `pat + tail` does not match `pat` except at the front
                    &&& tail@.len() > 0 ==>
                            !pat@.is_suffix_of(pat@ + tail@) && !pat@.is_infix_of(pat@ + tail@)
                    // `head` and `tail` make up the original string
                    &&& s == head@ + pat@ + tail@
                },
            }
        }),
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rsplit_once_post);
    let (seq, gap) = spec_rmatches(s, pat);
    match ret {
        None => {
            if pat@.len() == 0 {
                assert(seq.len() == s.len() + 1);
                assert(false);
            } else {
                assert(gap.len() == 1);
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                assert(gap.first() == s);
                assert(gap.last() == s);
                assert(!pat@.is_subrange_of(gap.last()));
                assert(!pat@.is_subrange_of(s));
            }
        },
        Some((head, tail)) => {
            assert(tail@ == gap.first());
            assert(head@ == rjoin(seq.skip(1), gap.skip(1)));
            lemma_rjoin_uncons(seq, gap);
            assert(s == head@ + seq[0] + tail@);
            if pat@.len() == 0 {
                assert(seq[0].len() == 0);
                assert(gap.first().len() == 0);
                assert_seqs_equal!(seq[0] == pat@);
                assert_seqs_equal!(gap[0] == Seq::<char>::empty());
                assert(tail@.len() == 0);
                assert(s == head@ + Seq::<char>::empty() + Seq::<char>::empty());
                assert(head@ == s);
            } else {
                assert(seq[0] == pat@);
                assert(s == head@ + pat@ + tail@);
                assert(tail@.len() > 0 ==> !pat@.is_suffix_of(pat@ + tail@) && !pat@.is_infix_of(pat@ + tail@));
            }
        },
    }
}

/// Proof that links the full spec to `str::matches` with a `char` pattern.
pub broadcast proof fn lemma_str_matches_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_matches_iter_post(s, ch, iter_seq),
    ensures
        // matches all match `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@ == seq![ch],
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| c == ch),
{
    axiom_char_matches_post(s, ch);
    reveal(str_matches_iter_post);
    let (seq, gap) = spec_matches(s, ch);
    let pred = |c: char| c == ch;
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c)) by {
        assert forall |j: int| 0 <= j < gap[i].len()
            implies !pred(gap[i][j]) by {
            if pred(gap[i][j]) {
                assert(gap[i].contains(ch));
            }
        }
    }
    assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0]) by {
        assert(seq[i] =~= seq![ch]);
    }
    lemma_str_matches_count(seq, gap, pred);
}

/// Proof that links the full spec to `str::matches` with a closure pattern.
pub broadcast proof fn lemma_str_matches_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_matches_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // matches all match `f`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@.len() == 1
                && #[trigger] call_ensures(f, (iter_seq[i]@[0],), true),
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true)),
{
    axiom_closure_matches_post(s, f);
    reveal(str_matches_iter_post);
    let (seq, gap) = spec_matches(s, f);
    let pred = |c: char| call_ensures(f, (c,), true);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c)) by {
        let neg_pred = |c: char| call_ensures(f, (c,), false);
        assert(gap[i].all(neg_pred));
        assert forall |j: int| 0 <= j < gap[i].len()
            implies !pred(gap[i][j]) by {
            assert(neg_pred(gap[i][j]));
            if pred(gap[i][j]) {
                assert(call_ensures(f, (gap[i][j],), false));
                assert(call_ensures(f, (gap[i][j],), true));
            }
        }
    }
    assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0]) by {
    }
    lemma_str_matches_count(seq, gap, pred);
}

/// Proof that links the full spec to `str::matches` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_matches_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_matches_iter_post(s, chars, iter_seq),
    ensures
        // matches all match `chars`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@.len() == 1
                && #[trigger] chars@.contains(iter_seq[i]@[0]),
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| chars@.contains(c)),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_matches_iter_post);
    let (seq, gap) = spec_matches(s, chars);
    let pred = |c: char| chars@.contains(c);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c)) by {
        let neg_pred = |c: char| !chars@.contains(c);
        assert(gap[i].all(neg_pred));
        assert forall |j: int| 0 <= j < gap[i].len()
            implies !pred(gap[i][j]) by {
            assert(neg_pred(gap[i][j]));
        }
    }
    assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0]) by {
    }
    lemma_str_matches_count(seq, gap, pred);
}

/// Proof that links the full spec to `str::matches` with a string pattern.
pub broadcast proof fn lemma_str_matches_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_matches_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_matches_iter_post(s, pat, iter_seq),
    ensures
        // matches all match `pat`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@ == pat@,
        // matches are empty if none matches `pat`
        iter_seq.len() == 0 <==> !pat@.is_subrange_of(s),
        // delimiters and splits make up the original string
        exists |gap: Seq<Seq<char>>| {
            &&& #[trigger] gap.len() == iter_seq.len() + 1
            &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1
                    ==> gap[i].len() > 0
                        ==> (!pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@))
            &&& !pat@.is_subrange_of(gap.last())
            &&& s == iter_seq.map(|i: int, ss: &'a str| gap[i] + ss@).flatten() + gap.last()
        },
{
    axiom_string_matches_post(s, pat);
    reveal(str_matches_iter_post);
    let (seq, gap) = spec_matches(s, pat);
    // #1
    assert forall |i: int| 0 <= i < iter_seq.len()
    implies #[trigger] iter_seq[i]@ == pat@
    by { assert(iter_seq[i]@ =~= pat@) }
    // #2
    assert(iter_seq.len() == 0 <==> !pat@.is_subrange_of(s)) by {
        assert(iter_seq.len() == seq.len());
        reveal(str_contains_post);
        lemma_str_contains_string(s, pat, seq.len() > 0);
    }
    // #3
    assert(gap.len() == iter_seq.len() + 1);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1 && gap[i].len() > 0
    implies !pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@)
    by {}
    assert(s == iter_seq.map(|i: int, ss: &'a str| gap[i] + ss@).flatten() + gap.last()) by {
        lemma_join_alt(seq, gap);
        let s1 = iter_seq.map(|i: int, ss: &'a str| gap[i] + ss@);
        let s2 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
        assert_seqs_equal!(s1 == s2);
    }
}

/// Proof that links the full spec to `str::rmatches` with a `char` pattern.
pub broadcast proof fn lemma_str_rmatches_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rmatches_iter_post(s, ch, iter_seq),
    ensures
        // matches all match `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@ == seq![ch],
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| c == ch),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rmatches_iter_post);
    let (seq, gap) = spec_rmatches(s, ch);
    let pred = |c: char| c == ch;
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c)) by {
        assert forall |j: int| 0 <= j < gap[i].len()
            implies !pred(gap[i][j]) by {
            if pred(gap[i][j]) {
                assert(gap[i].contains(ch));
            }
        }
    }
    assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0]) by {
        assert(seq[i] =~= seq![ch]);
    }
    lemma_str_rmatches_count(seq, gap, pred);
}

/// Proof that links the full spec to `str::rmatches` with a closure pattern.
pub broadcast proof fn lemma_str_rmatches_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rmatches_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // matches all match `f`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@.len() == 1
                && #[trigger] call_ensures(f, (iter_seq[i]@[0],), true),
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true)),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rmatches_iter_post);
    let (seq, gap) = spec_rmatches(s, f);
    let pred = |c: char| call_ensures(f, (c,), true);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c)) by {
        let neg_pred = |c: char| call_ensures(f, (c,), false);
        assert(gap[i].all(neg_pred));
        assert forall |j: int| 0 <= j < gap[i].len()
            implies !pred(gap[i][j]) by {
            assert(neg_pred(gap[i][j]));
            if pred(gap[i][j]) {
                assert(call_ensures(f, (gap[i][j],), false));
                assert(call_ensures(f, (gap[i][j],), true));
            }
        }
    }
    assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0]) by {
    }
    lemma_str_rmatches_count(seq, gap, pred);
}

/// Proof that links the full spec to `str::rmatches` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_rmatches_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rmatches_iter_post(s, chars, iter_seq),
    ensures
        // matches all match `chars`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@.len() == 1
                && #[trigger] chars@.contains(iter_seq[i]@[0]),
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| chars@.contains(c)),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rmatches_iter_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let pred = |c: char| chars@.contains(c);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c)) by {
        let neg_pred = |c: char| !chars@.contains(c);
        assert(gap[i].all(neg_pred));
        assert forall |j: int| 0 <= j < gap[i].len()
            implies !pred(gap[i][j]) by {
            assert(neg_pred(gap[i][j]));
        }
    }
    assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0]) by {
    }
    lemma_str_rmatches_count(seq, gap, pred);
}

/// Proof that links the full spec to `str::rmatches` with a string pattern.
pub broadcast proof fn lemma_str_rmatches_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_rmatches_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_rmatches_iter_post(s, pat, iter_seq),
    ensures
        // matches all match `pat`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@ == pat@,
        // matches are empty if none matches `pat`
        iter_seq.len() == 0 <==> !pat@.is_subrange_of(s),
        // delimiters and splits make up the original string
        exists |gap: Seq<Seq<char>>| {
            &&& #[trigger] gap.len() == iter_seq.len() + 1
            &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1
                    ==> gap[i].len() > 0
                        ==> (!pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i]))
            &&& !pat@.is_subrange_of(gap.last())
            &&& s == gap.last() + iter_seq.map(|i: int, ss: &'a str| ss@ + gap[i]).reverse().flatten()
        },
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rmatches_iter_post);
    let (seq, gap) = spec_rmatches(s, pat);
    // #1
    assert forall |i: int| 0 <= i < iter_seq.len()
    implies #[trigger] iter_seq[i]@ == pat@
    by {
        assert(iter_seq[i]@ == seq[i]);
        assert(seq[i] =~= pat@);
    }
    // #2
    assert(iter_seq.len() == 0 <==> !pat@.is_subrange_of(s)) by {
        assert(iter_seq.len() == seq.len());
        if iter_seq.len() == 0 {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(s == gap.last());
            assert(!pat@.is_subrange_of(gap.last()));
        }
        if !pat@.is_subrange_of(s) {
            assert_by_contradiction!(iter_seq.len() == 0, {
                assert(seq.len() > 0);
                assert(seq[0] == pat@);
                lemma_rjoin_uncons(seq, gap);
                let rest = rjoin(seq.skip(1), gap.skip(1));
                lemma_concat_associative(rest, seq[0], gap[0]);
                assert(s == rest + (seq[0] + gap[0]));
                assert(seq[0] =~= s.subrange(rest.len() as int, rest.len() + seq[0].len() as int));
                assert(seq[0].is_subrange_of(s)) by {
                    assert(exists |i: int| 0 <= i <= s.len() - seq[0].len()
                        && seq[0] =~= #[trigger] s.subrange(i, i + seq[0].len()));
                }
                assert(pat@.is_subrange_of(s));
            });
        }
    }
    // #3
    assert(gap.len() == iter_seq.len() + 1);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1 && gap[i].len() > 0
    implies !pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i])
    by {}
    assert(s == gap.last() + iter_seq.map(|i: int, ss: &'a str| ss@ + gap[i]).reverse().flatten()) by {
        lemma_rjoin_alt_for_matches(seq, gap);
        let s1 = iter_seq.map(|i: int, ss: &'a str| ss@ + gap[i]);
        let s2 = seq.map(|i: int, ss: Seq<char>| ss + gap[i]);
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i]@ == seq[i]);
            assert(seq[i] == pat@);
        });
        assert(s1.reverse() == s2.reverse());
        s1.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        assert(s2.reverse().flatten_alt() == s1.reverse().flatten());
    }
}

/// Proof that links the full spec to `str::match_indices` with a `char` pattern.
pub broadcast proof fn lemma_str_match_indices_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<(usize, &'a str)>)
    requires
        #[trigger] str_match_indices_iter_post(s, ch, iter_seq),
    ensures
        // matches all match `ch`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
                &&& ss@ == seq![ch]
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
                &&& ss@[0] == s[idx_ch]
            },
        // indices are non-overlapping
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i].0 < iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| c == ch),
{
    axiom_char_matches_post(s, ch);
    reveal(str_match_indices_iter_post);
    let (seq, gap) = spec_matches(s, ch);
    assert(iter_seq.len() == seq.len());
    // #1
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        &&& ss@ == seq![ch]
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
        &&& ss@[0] == s[idx_ch]
    } by {
        let (idx, ss) = iter_seq[i];
        // #1.1
        assert(ss@ == seq[i]);
        assert(seq[i] =~= seq![ch]);
        // #1.2 & 1.3
        assert(idx == join(seq.take(i), gap.take(i + 1)).as_bytes().len());
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        let tail = gap.skip(i).drop_first().map(|k: int, ss: Seq<char>| seq.skip(i)[k] + ss).flatten();
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, i) }
            seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss).flatten()
                + join(seq.skip(i), gap.skip(i));
                {
                    let s1 = seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss);
                    let s2 = seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss);
                    assert_seqs_equal!(s1 == s2);
                }
            seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss).flatten()
                + gap.skip(i).first() + tail;
                {
                    lemma_join_alt(seq.take(i), gap.take(i+1));
                    assert(gap.take(i+1).last() == gap.skip(i).first());
                }
            join(seq.take(i), gap.take(i+1)) + tail;
        }
        assert(s.as_bytes() == join(seq.take(i), gap.take(i + 1)).as_bytes() + tail.as_bytes()) by {
            lemma_str_concat_lower(join(seq.take(i), gap.take(i + 1)), tail);
        }
        assert(s.as_bytes().take(idx as int) == join(seq.take(i), gap.take(i + 1)).as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(join(seq.take(i), gap.take(i + 1)));
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + tail.as_bytes().len() == s.as_bytes().len());
        assert(idx_ch == join(seq.take(i), gap.take(i + 1)).len()) by {
            lemma_str_lower_lift(join(seq.take(i), gap.take(i + 1)));
        }
        assert(s[idx_ch] == tail[0]);
        assert(gap.skip(i).drop_first().len() > 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(seq.skip(i)[0] == seq[i]);
        assert(tail[0] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 < iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let s1 = join(seq.take(i), gap.take(i+1));
        let s2 = join(seq.take(i+1), gap.take(i+2));
        lemma_join_runcons(seq.take(i+1), gap.take(i+2));
        assert(seq.take(i+1).drop_last() == seq.take(i));
        assert(gap.take(i+2).drop_last() == gap.take(i+1));
        assert(idx1 == s1.as_bytes().len());
        assert(idx2 == s2.as_bytes().len());
        assert(s1.as_bytes() + seq.take(i+1).last().as_bytes() + gap.take(i+2).last().as_bytes() == s2.as_bytes()) by {
            lemma_str_concat_lower(s1, seq.take(i+1).last());
            lemma_str_concat_lower(s1 + seq.take(i+1).last(), gap.take(i+2).last());
        }
        assert(seq.take(i+1).last() =~= seq![ch]);
        assert(seq.take(i+1).last().as_bytes().len() > 0);
    }
    // #3
    assert(iter_seq.len() == s.count(|c: char| c == ch)) by {
        let pred = |c: char| c == ch;
        assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c))
        by { assert(!gap[i].contains(ch)); }
        assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0])
        by { assert(seq[i] =~= seq![ch]) }
        lemma_str_matches_count(seq, gap, pred);
    }
}

/// Proof that links the full spec to `str::match_indices` with a closure pattern.
pub broadcast proof fn lemma_str_match_indices_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<(usize, &'a str)>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_match_indices_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // matches all match `f`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
                &&& ss@.len() == 1 && call_ensures(f, (ss@[0],), true)
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
                &&& ss@[0] == s[idx_ch]
            },
        // indices are non-overlapping
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i].0 < iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true)),
{
    axiom_closure_matches_post(s, f);
    reveal(str_match_indices_iter_post);
    let (seq, gap) = spec_matches(s, f);
    assert(iter_seq.len() == seq.len());
    // #1
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        &&& ss@.len() == 1 && call_ensures(f, (ss@[0],), true)
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
        &&& ss@[0] == s[idx_ch]
    } by {
        let (idx, ss) = iter_seq[i];
        // #1.1
        assert(ss@ == seq[i]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
        // #1.2 & 1.3
        assert(idx == join(seq.take(i), gap.take(i + 1)).as_bytes().len());
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        let tail = gap.skip(i).drop_first().map(|k: int, ss: Seq<char>| seq.skip(i)[k] + ss).flatten();
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, i) }
            seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss).flatten()
                + join(seq.skip(i), gap.skip(i));
                {
                    let s1 = seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss);
                    let s2 = seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss);
                    assert_seqs_equal!(s1 == s2);
                }
            seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss).flatten()
                + gap.skip(i).first() + tail;
                {
                    lemma_join_alt(seq.take(i), gap.take(i+1));
                    assert(gap.take(i+1).last() == gap.skip(i).first());
                }
            join(seq.take(i), gap.take(i+1)) + tail;
        }
        assert(s.as_bytes() == join(seq.take(i), gap.take(i + 1)).as_bytes() + tail.as_bytes()) by {
            lemma_str_concat_lower(join(seq.take(i), gap.take(i + 1)), tail);
        }
        assert(s.as_bytes().take(idx as int) == join(seq.take(i), gap.take(i + 1)).as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(join(seq.take(i), gap.take(i + 1)));
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + tail.as_bytes().len() == s.as_bytes().len());
        assert(idx_ch == join(seq.take(i), gap.take(i + 1)).len()) by {
            lemma_str_lower_lift(join(seq.take(i), gap.take(i + 1)));
        }
        assert(s[idx_ch] == tail[0]);
        assert(gap.skip(i).drop_first().len() > 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(seq.skip(i)[0] == seq[i]);
        assert(tail[0] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 < iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let s1 = join(seq.take(i), gap.take(i+1));
        let s2 = join(seq.take(i+1), gap.take(i+2));
        lemma_join_runcons(seq.take(i+1), gap.take(i+2));
        assert(seq.take(i+1).drop_last() == seq.take(i));
        assert(gap.take(i+2).drop_last() == gap.take(i+1));
        assert(idx1 == s1.as_bytes().len());
        assert(idx2 == s2.as_bytes().len());
        assert(s1.as_bytes() + seq.take(i+1).last().as_bytes() + gap.take(i+2).last().as_bytes() == s2.as_bytes()) by {
            lemma_str_concat_lower(s1, seq.take(i+1).last());
            lemma_str_concat_lower(s1 + seq.take(i+1).last(), gap.take(i+2).last());
        }
        assert(seq.take(i+1).last().len() == 1);
        assert(seq.take(i+1).last().as_bytes().len() > 0);
    }
    // #3
    assert(iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true))) by {
        let pred = |c: char| call_ensures(f, (c,), true);
        assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c))
        by {
            let neg_pred = |c: char| call_ensures(f, (c,), false);
            assert(gap[i].all(neg_pred));
            assert forall |j: int| 0 <= j < gap[i].len()
                implies !pred(gap[i][j]) by {
                assert(neg_pred(gap[i][j]));
                if pred(gap[i][j]) {
                    assert(call_ensures(f, (gap[i][j],), false));
                    assert(call_ensures(f, (gap[i][j],), true));
                }
            }
        }
        assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0])
        by {}
        lemma_str_matches_count(seq, gap, pred);
    }
}

/// Proof that links the full spec to `str::match_indices` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_match_indices_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<(usize, &'a str)>)
    requires
        #[trigger] str_match_indices_iter_post(s, chars, iter_seq),
    ensures
        // matches all match `chars`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
                &&& ss@.len() == 1 && chars@.contains(ss@[0])
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
                &&& ss@[0] == s[idx_ch]
            },
        // indices are non-overlapping
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i].0 < iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| chars@.contains(c)),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_match_indices_iter_post);
    let (seq, gap) = spec_matches(s, chars);
    assert(iter_seq.len() == seq.len());
    // #1
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        &&& ss@.len() == 1 && chars@.contains(ss@[0])
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
        &&& ss@[0] == s[idx_ch]
    } by {
        let (idx, ss) = iter_seq[i];
        // #1.1
        assert(ss@ == seq[i]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
        // #1.2 & 1.3
        assert(idx == join(seq.take(i), gap.take(i + 1)).as_bytes().len());
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        let tail = gap.skip(i).drop_first().map(|k: int, ss: Seq<char>| seq.skip(i)[k] + ss).flatten();
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, i) }
            seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss).flatten()
                + join(seq.skip(i), gap.skip(i));
                {
                    let s1 = seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss);
                    let s2 = seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss);
                    assert_seqs_equal!(s1 == s2);
                }
            seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss).flatten()
                + gap.skip(i).first() + tail;
                {
                    lemma_join_alt(seq.take(i), gap.take(i+1));
                    assert(gap.take(i+1).last() == gap.skip(i).first());
                }
            join(seq.take(i), gap.take(i+1)) + tail;
        }
        assert(s.as_bytes() == join(seq.take(i), gap.take(i + 1)).as_bytes() + tail.as_bytes()) by {
            lemma_str_concat_lower(join(seq.take(i), gap.take(i + 1)), tail);
        }
        assert(s.as_bytes().take(idx as int) == join(seq.take(i), gap.take(i + 1)).as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(join(seq.take(i), gap.take(i + 1)));
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + tail.as_bytes().len() == s.as_bytes().len());
        assert(idx_ch == join(seq.take(i), gap.take(i + 1)).len()) by {
            lemma_str_lower_lift(join(seq.take(i), gap.take(i + 1)));
        }
        assert(s[idx_ch] == tail[0]);
        assert(gap.skip(i).drop_first().len() > 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(seq.skip(i)[0] == seq[i]);
        assert(tail[0] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 < iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let s1 = join(seq.take(i), gap.take(i+1));
        let s2 = join(seq.take(i+1), gap.take(i+2));
        lemma_join_runcons(seq.take(i+1), gap.take(i+2));
        assert(seq.take(i+1).drop_last() == seq.take(i));
        assert(gap.take(i+2).drop_last() == gap.take(i+1));
        assert(idx1 == s1.as_bytes().len());
        assert(idx2 == s2.as_bytes().len());
        assert(s1.as_bytes() + seq.take(i+1).last().as_bytes() + gap.take(i+2).last().as_bytes() == s2.as_bytes()) by {
            lemma_str_concat_lower(s1, seq.take(i+1).last());
            lemma_str_concat_lower(s1 + seq.take(i+1).last(), gap.take(i+2).last());
        }
        assert(seq.take(i+1).last().len() == 1);
        assert(seq.take(i+1).last().as_bytes().len() > 0);
    }
    // #3
    assert(iter_seq.len() == s.count(|c: char| chars@.contains(c))) by {
        let pred = |c: char| chars@.contains(c);
        assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c))
        by {
            let neg_pred = |c: char| !chars@.contains(c);
            assert(gap[i].all(neg_pred));
            assert forall |j: int| 0 <= j < gap[i].len()
                implies !pred(gap[i][j]) by {
                assert(neg_pred(gap[i][j]));
            }
        }
        assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0])
        by {}
        lemma_str_matches_count(seq, gap, pred);
    }
}

/// Proof that links the full spec to `str::match_indices` with a string pattern.
pub broadcast proof fn lemma_str_match_indices_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<(usize, &'a str)>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_match_indices_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_match_indices_iter_post(s, pat, iter_seq),
    ensures
        // matches all match `pat`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                &&& ss@ == pat@
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx <= s.as_bytes().len() - pat@.as_bytes().len()
                &&& s.as_bytes().subrange(idx as int, idx + pat@.as_bytes().len() as int) == pat@.as_bytes()
            },
        // matches are empty if none matches `pat`
        iter_seq.len() == 0 <==> !pat@.is_subrange_of(s),
        // gaps and matches make up the original string
        exists |gap: Seq<Seq<char>>| {
            &&& #[trigger] gap.len() == iter_seq.len() + 1
            &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1
                    ==> gap[i].len() > 0
                        ==> (!pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@))
            &&& !pat@.is_subrange_of(gap.last())
            &&& s == iter_seq.map(|i: int, item: (usize, &'a str)| gap[i] + item.1@).flatten() + gap.last()
            // ..and defines the indices
            &&& iter_seq.len() > 0 ==> iter_seq.first().0 == gap.first().as_bytes().len()
            &&& forall |i: int| #![trigger iter_seq[i].0] 1 <= i < iter_seq.len()
                ==> iter_seq[i].0 == iter_seq[i-1].0 + pat@.as_bytes().len() + gap[i].as_bytes().len()
        },
{
    axiom_string_matches_post(s, pat);
    reveal(str_match_indices_iter_post);
    let (seq, gap) = spec_matches(s, pat);
    assert(iter_seq.len() == seq.len());
    // #1
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        &&& ss@ == pat@
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx <= s.as_bytes().len() - pat@.as_bytes().len()
        &&& s.as_bytes().subrange(idx as int, idx + pat@.as_bytes().len() as int) == pat@.as_bytes()
    } by {
        let (idx, ss) = iter_seq[i];
        assert(ss@ == seq[i]);
        assert(seq[i] =~= pat@);
        assert(idx == join(seq.take(i), gap.take(i + 1)).as_bytes().len());
        let prefix = join(seq.take(i), gap.take(i + 1));
        let rest = join(seq.skip(i + 1), gap.skip(i + 1));
        lemma_join_split_match_at(seq, gap, i);
        assert(s == prefix + seq[i] + rest);
        assert(s.as_bytes() == prefix.as_bytes() + seq[i].as_bytes() + rest.as_bytes()) by {
            lemma_str_concat_lower(prefix, seq[i]);
            lemma_str_concat_lower(prefix + seq[i], rest);
        }
        assert(s.as_bytes().take(idx as int) == prefix.as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(prefix);
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(seq[i].as_bytes() == pat@.as_bytes());
        assert(pat@.as_bytes().len() > 0);
        assert(idx + pat@.as_bytes().len() <= s.as_bytes().len());
        assert(s.as_bytes().subrange(idx as int, idx + pat@.as_bytes().len() as int) == pat@.as_bytes());
    }
    // #2
    assert(iter_seq.len() == 0 <==> !pat@.is_subrange_of(s)) by {
        assert(iter_seq.len() == seq.len());
        reveal(str_contains_post);
        lemma_str_contains_string(s, pat, seq.len() > 0);
    }
    // #3
    assert(gap.len() == iter_seq.len() + 1);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1 && gap[i].len() > 0
    implies !pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@)
    by {}
    assert(s == iter_seq.map(|i: int, item: (usize, &'a str)| gap[i] + item.1@).flatten() + gap.last()) by {
        lemma_join_alt(seq, gap);
        let s1 = iter_seq.map(|i: int, item: (usize, &'a str)| gap[i] + item.1@);
        let s2 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i].1@ == seq[i]);
        });
    }
    assert(iter_seq.len() > 0 ==> iter_seq.first().0 == gap.first().as_bytes().len()) by {
        if iter_seq.len() > 0 {
            assert(iter_seq.first() == iter_seq[0]);
            assert(iter_seq[0].0 == join(seq.take(0), gap.take(1)).as_bytes().len());
            assert(join(seq.take(0), gap.take(1)) == gap.first()) by {
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
        }
    }
    assert forall |i: int| #![trigger iter_seq[i].0] 1 <= i < iter_seq.len()
    implies iter_seq[i].0 == iter_seq[i-1].0 + pat@.as_bytes().len() + gap[i].as_bytes().len()
    by {
        let idx1 = iter_seq[i-1].0 as int;
        let idx2 = iter_seq[i].0 as int;
        let s1 = join(seq.take(i-1), gap.take(i));
        let s2 = join(seq.take(i), gap.take(i+1));
        lemma_join_runcons(seq.take(i), gap.take(i+1));
        assert(seq.take(i).drop_last() == seq.take(i-1));
        assert(gap.take(i+1).drop_last() == gap.take(i));
        assert(seq.take(i).last() == seq[i-1]);
        assert(gap.take(i+1).last() == gap[i]);
        assert(idx1 == s1.as_bytes().len());
        assert(idx2 == s2.as_bytes().len());
        assert(seq[i-1] == pat@);
        assert(s1.as_bytes() + seq[i-1].as_bytes() + gap[i].as_bytes() == s2.as_bytes()) by {
            lemma_str_concat_lower(s1, seq[i-1]);
            lemma_str_concat_lower(s1 + seq[i-1], gap[i]);
        }
    }
}

/// Proof that links the full spec to `str::rmatch_indices` with a `char` pattern.
pub broadcast proof fn lemma_str_rmatch_indices_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<(usize, &'a str)>)
    requires
        #[trigger] str_rmatch_indices_iter_post(s, ch, iter_seq),
    ensures
        // matches all match `ch`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
                &&& ss@ == seq![ch]
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
                &&& ss@[0] == s[idx_ch]
            },
        // indices are non-overlapping
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i].0 > iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| c == ch),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rmatch_indices_iter_post);
    let (seq, gap) = spec_rmatches(s, ch);
    assert(iter_seq.len() == seq.len());
    // #1
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        &&& ss@ == seq![ch]
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
        &&& ss@[0] == s[idx_ch]
    } by {
        let (idx, ss) = iter_seq[i];
        assert(ss@ == seq[i]);
        assert(seq[i] =~= seq![ch]);
        assert(idx == rjoin(seq.skip(i + 1), gap.skip(i + 1)).as_bytes().len());
        let prefix = rjoin(seq.skip(i + 1), gap.skip(i + 1));
        let suffix = rjoin(seq.take(i), gap.take(i + 1));
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_match_at(seq, gap, i) }
            prefix + seq[i] + suffix;
        }
        assert(s.as_bytes() == prefix.as_bytes() + seq[i].as_bytes() + suffix.as_bytes()) by {
            lemma_str_concat_lower(prefix, seq[i]);
            lemma_str_concat_lower(prefix + seq[i], suffix);
        }
        assert(s.as_bytes().take(idx as int) == prefix.as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(prefix);
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + seq[i].as_bytes().len() <= s.as_bytes().len());
        assert(idx_ch == prefix.len()) by {
            lemma_str_lower_lift(prefix);
        }
        assert(s[idx_ch] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 > iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let prefix1 = rjoin(seq.skip(i+1), gap.skip(i+1));
        let prefix2 = rjoin(seq.skip(i+2), gap.skip(i+2));
        lemma_rjoin_uncons(seq.skip(i+1), gap.skip(i+1));
        assert(seq.skip(i+1)[0] == seq[i+1]);
        assert(gap.skip(i+1)[0] == gap[i+1]);
        assert(seq.skip(i+1).skip(1) == seq.skip(i+2));
        assert(gap.skip(i+1).skip(1) == gap.skip(i+2));
        assert(prefix1 == prefix2 + seq[i+1] + gap[i+1]);
        assert(idx1 == prefix1.as_bytes().len());
        assert(idx2 == prefix2.as_bytes().len());
        assert(prefix2.as_bytes() + seq[i+1].as_bytes() + gap[i+1].as_bytes() == prefix1.as_bytes()) by {
            lemma_str_concat_lower(prefix2, seq[i+1]);
            lemma_str_concat_lower(prefix2 + seq[i+1], gap[i+1]);
        }
        assert(seq[i+1] =~= seq![ch]);
        assert(seq[i+1].as_bytes().len() > 0);
    }
    // #3
    assert(iter_seq.len() == s.count(|c: char| c == ch)) by {
        let pred = |c: char| c == ch;
        assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c))
        by { assert(!gap[i].contains(ch)); }
        assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0])
        by { assert(seq[i] =~= seq![ch]) }
        lemma_str_rmatches_count(seq, gap, pred);
    }
}

/// Proof that links the full spec to `str::rmatch_indices` with a closure pattern.
pub broadcast proof fn lemma_str_rmatch_indices_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<(usize, &'a str)>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rmatch_indices_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // matches all match `f`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
                &&& ss@.len() == 1 && call_ensures(f, (ss@[0],), true)
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
                &&& ss@[0] == s[idx_ch]
            },
        // indices are non-overlapping
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i].0 > iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true)),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rmatch_indices_iter_post);
    let (seq, gap) = spec_rmatches(s, f);
    assert(iter_seq.len() == seq.len());
    // #1
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        &&& ss@.len() == 1 && call_ensures(f, (ss@[0],), true)
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
        &&& ss@[0] == s[idx_ch]
    } by {
        let (idx, ss) = iter_seq[i];
        assert(ss@ == seq[i]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
        assert(idx == rjoin(seq.skip(i + 1), gap.skip(i + 1)).as_bytes().len());
        let prefix = rjoin(seq.skip(i + 1), gap.skip(i + 1));
        let suffix = rjoin(seq.take(i), gap.take(i + 1));
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_match_at(seq, gap, i) }
            prefix + seq[i] + suffix;
        }
        assert(s.as_bytes() == prefix.as_bytes() + seq[i].as_bytes() + suffix.as_bytes()) by {
            lemma_str_concat_lower(prefix, seq[i]);
            lemma_str_concat_lower(prefix + seq[i], suffix);
        }
        assert(s.as_bytes().take(idx as int) == prefix.as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(prefix);
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + seq[i].as_bytes().len() <= s.as_bytes().len());
        assert(idx_ch == prefix.len()) by {
            lemma_str_lower_lift(prefix);
        }
        assert(s[idx_ch] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 > iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let prefix1 = rjoin(seq.skip(i+1), gap.skip(i+1));
        let prefix2 = rjoin(seq.skip(i+2), gap.skip(i+2));
        lemma_rjoin_uncons(seq.skip(i+1), gap.skip(i+1));
        assert(seq.skip(i+1)[0] == seq[i+1]);
        assert(gap.skip(i+1)[0] == gap[i+1]);
        assert(seq.skip(i+1).skip(1) == seq.skip(i+2));
        assert(gap.skip(i+1).skip(1) == gap.skip(i+2));
        assert(prefix1 == prefix2 + seq[i+1] + gap[i+1]);
        assert(idx1 == prefix1.as_bytes().len());
        assert(idx2 == prefix2.as_bytes().len());
        assert(prefix2.as_bytes() + seq[i+1].as_bytes() + gap[i+1].as_bytes() == prefix1.as_bytes()) by {
            lemma_str_concat_lower(prefix2, seq[i+1]);
            lemma_str_concat_lower(prefix2 + seq[i+1], gap[i+1]);
        }
        assert(seq[i+1].len() == 1);
        assert(seq[i+1].as_bytes().len() > 0);
    }
    // #3
    assert(iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true))) by {
        let pred = |c: char| call_ensures(f, (c,), true);
        assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c)) by {
            let neg_pred = |c: char| call_ensures(f, (c,), false);
            assert(gap[i].all(neg_pred));
            assert forall |j: int| 0 <= j < gap[i].len()
                implies !pred(gap[i][j]) by {
                assert(neg_pred(gap[i][j]));
                if pred(gap[i][j]) {
                    assert(call_ensures(f, (gap[i][j],), false));
                    assert(call_ensures(f, (gap[i][j],), true));
                }
            }
        }
        assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0]) by {}
        lemma_str_rmatches_count(seq, gap, pred);
    }
}

/// Proof that links the full spec to `str::rmatch_indices` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_rmatch_indices_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<(usize, &'a str)>)
    requires
        #[trigger] str_rmatch_indices_iter_post(s, chars, iter_seq),
    ensures
        // matches all match `chars`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
                &&& ss@.len() == 1 && chars@.contains(ss@[0])
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
                &&& ss@[0] == s[idx_ch]
            },
        // indices are non-overlapping
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i].0 > iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| chars@.contains(c)),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rmatch_indices_iter_post);
    let (seq, gap) = spec_rmatches(s, chars);
    assert(iter_seq.len() == seq.len());
    // #1
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        &&& ss@.len() == 1 && chars@.contains(ss@[0])
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
        &&& ss@[0] == s[idx_ch]
    } by {
        let (idx, ss) = iter_seq[i];
        assert(ss@ == seq[i]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
        assert(idx == rjoin(seq.skip(i + 1), gap.skip(i + 1)).as_bytes().len());
        let prefix = rjoin(seq.skip(i + 1), gap.skip(i + 1));
        let suffix = rjoin(seq.take(i), gap.take(i + 1));
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_match_at(seq, gap, i) }
            prefix + seq[i] + suffix;
        }
        assert(s.as_bytes() == prefix.as_bytes() + seq[i].as_bytes() + suffix.as_bytes()) by {
            lemma_str_concat_lower(prefix, seq[i]);
            lemma_str_concat_lower(prefix + seq[i], suffix);
        }
        assert(s.as_bytes().take(idx as int) == prefix.as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(prefix);
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + seq[i].as_bytes().len() <= s.as_bytes().len());
        assert(idx_ch == prefix.len()) by {
            lemma_str_lower_lift(prefix);
        }
        assert(s[idx_ch] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 > iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let prefix1 = rjoin(seq.skip(i+1), gap.skip(i+1));
        let prefix2 = rjoin(seq.skip(i+2), gap.skip(i+2));
        lemma_rjoin_uncons(seq.skip(i+1), gap.skip(i+1));
        assert(seq.skip(i+1)[0] == seq[i+1]);
        assert(gap.skip(i+1)[0] == gap[i+1]);
        assert(seq.skip(i+1).skip(1) == seq.skip(i+2));
        assert(gap.skip(i+1).skip(1) == gap.skip(i+2));
        assert(prefix1 == prefix2 + seq[i+1] + gap[i+1]);
        assert(idx1 == prefix1.as_bytes().len());
        assert(idx2 == prefix2.as_bytes().len());
        assert(prefix2.as_bytes() + seq[i+1].as_bytes() + gap[i+1].as_bytes() == prefix1.as_bytes()) by {
            lemma_str_concat_lower(prefix2, seq[i+1]);
            lemma_str_concat_lower(prefix2 + seq[i+1], gap[i+1]);
        }
        assert(seq[i+1].len() == 1);
        assert(seq[i+1].as_bytes().len() > 0);
    }
    // #3
    assert(iter_seq.len() == s.count(|c: char| chars@.contains(c))) by {
        let pred = |c: char| chars@.contains(c);
        assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c)) by {
            let neg_pred = |c: char| !chars@.contains(c);
            assert(gap[i].all(neg_pred));
            assert forall |j: int| 0 <= j < gap[i].len()
                implies !pred(gap[i][j]) by {
                assert(neg_pred(gap[i][j]));
            }
        }
        assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0]) by {}
        lemma_str_rmatches_count(seq, gap, pred);
    }
}

/// Proof that links the full spec to `str::rmatch_indices` with a string pattern.
pub broadcast proof fn lemma_str_rmatch_indices_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<(usize, &'a str)>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_rmatch_indices_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_rmatch_indices_iter_post(s, pat, iter_seq),
    ensures
        // matches all match `pat`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                &&& ss@ == pat@
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx <= s.as_bytes().len() - pat@.as_bytes().len()
                &&& s.as_bytes().subrange(idx as int, idx + pat@.as_bytes().len() as int) == pat@.as_bytes()
            },
        // matches are empty if none matches `pat`
        iter_seq.len() == 0 <==> !pat@.is_subrange_of(s),
        // gaps and matches make up the original string
        exists |gap: Seq<Seq<char>>| {
            &&& #[trigger] gap.len() == iter_seq.len() + 1
            &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1
                    ==> gap[i].len() > 0
                        ==> (!pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i]))
            &&& !pat@.is_subrange_of(gap.last())
            &&& s == gap.last() + iter_seq.map(|i: int, item: (usize, &'a str)| item.1@ + gap[i]).reverse().flatten()
            // ..and defines the indices
            &&& iter_seq.len() > 0 ==> iter_seq.last().0 == gap.last().as_bytes().len()
            &&& forall |i: int| #![trigger iter_seq[i].0] 0 <= i < iter_seq.len() - 1
                ==> iter_seq[i].0 == iter_seq[i+1].0 + pat@.as_bytes().len() + gap[i+1].as_bytes().len()
        },
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rmatch_indices_iter_post);
    let (seq, gap) = spec_rmatches(s, pat);
    assert(iter_seq.len() == seq.len());
    // #1: per-match postconditions
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        &&& ss@ == pat@
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx <= s.as_bytes().len() - pat@.as_bytes().len()
        &&& s.as_bytes().subrange(idx as int, idx + pat@.as_bytes().len() as int) == pat@.as_bytes()
    } by {
        let (idx, ss) = iter_seq[i];
        assert(ss@ == seq[i]);
        assert(seq[i] =~= pat@);
        assert(idx == rjoin(seq.skip(i + 1), gap.skip(i + 1)).as_bytes().len());
        let prefix = rjoin(seq.skip(i + 1), gap.skip(i + 1));
        let suffix = rjoin(seq.take(i), gap.take(i + 1));
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_match_at(seq, gap, i) }
            prefix + seq[i] + suffix;
        }
        assert(s.as_bytes() == prefix.as_bytes() + seq[i].as_bytes() + suffix.as_bytes()) by {
            lemma_str_concat_lower(prefix, seq[i]);
            lemma_str_concat_lower(prefix + seq[i], suffix);
        }
        assert(s.as_bytes().take(idx as int) == prefix.as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(prefix);
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(seq[i].as_bytes() == pat@.as_bytes());
        assert(pat@.as_bytes().len() > 0);
        assert(idx + pat@.as_bytes().len() <= s.as_bytes().len());
        assert(s.as_bytes().subrange(idx as int, idx + pat@.as_bytes().len() as int) == pat@.as_bytes());
    }
    // #2: empty iff no subrange
    assert(iter_seq.len() == 0 <==> !pat@.is_subrange_of(s)) by {
        assert(iter_seq.len() == seq.len());
        if iter_seq.len() == 0 {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(s == gap.last());
            assert(!pat@.is_subrange_of(gap.last()));
        }
        if !pat@.is_subrange_of(s) {
            assert_by_contradiction!(iter_seq.len() == 0, {
                assert(seq.len() > 0);
                assert(seq[0] == pat@);
                lemma_rjoin_uncons(seq, gap);
                let rest = rjoin(seq.skip(1), gap.skip(1));
                lemma_concat_associative(rest, seq[0], gap[0]);
                assert(s == rest + (seq[0] + gap[0]));
                assert(seq[0] =~= s.subrange(rest.len() as int, rest.len() + seq[0].len() as int));
                assert(seq[0].is_subrange_of(s)) by {
                    assert(exists |i: int| 0 <= i <= s.len() - seq[0].len()
                        && seq[0] =~= #[trigger] s.subrange(i, i + seq[0].len()));
                }
                assert(pat@.is_subrange_of(s));
            });
        }
    }
    // #3: gap reconstruction
    assert(gap.len() == iter_seq.len() + 1);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1 && gap[i].len() > 0
    implies !pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i])
    by {}
    assert(s == gap.last() + iter_seq.map(|i: int, item: (usize, &'a str)| item.1@ + gap[i]).reverse().flatten()) by {
        lemma_rjoin_alt_for_matches(seq, gap);
        let s1 = iter_seq.map(|i: int, item: (usize, &'a str)| item.1@ + gap[i]);
        let s2 = seq.map(|i: int, ss: Seq<char>| ss + gap[i]);
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i].1@ == seq[i]);
            assert(seq[i] == pat@);
        });
        assert(s1.reverse() == s2.reverse());
        s1.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        assert(s2.reverse().flatten_alt() == s1.reverse().flatten());
    }
    // #4: index definitions
    assert(iter_seq.len() > 0 ==> iter_seq.last().0 == gap.last().as_bytes().len()) by {
        if iter_seq.len() > 0 {
            let i = iter_seq.len() - 1;
            assert(iter_seq.last() == iter_seq[i]);
            assert(iter_seq[i].0 == rjoin(seq.skip(i + 1), gap.skip(i + 1)).as_bytes().len());
            assert(seq.skip(i + 1).len() == 0);
            assert(gap.skip(i + 1).len() == 1);
            assert(rjoin(seq.skip(i + 1), gap.skip(i + 1)) == gap.last()) by {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            }
        }
    }
    assert forall |i: int| #![trigger iter_seq[i].0] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 == iter_seq[i+1].0 + pat@.as_bytes().len() + gap[i+1].as_bytes().len()
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let prefix1 = rjoin(seq.skip(i+1), gap.skip(i+1));
        let prefix2 = rjoin(seq.skip(i+2), gap.skip(i+2));
        lemma_rjoin_uncons(seq.skip(i+1), gap.skip(i+1));
        assert(seq.skip(i+1)[0] == seq[i+1]);
        assert(gap.skip(i+1)[0] == gap[i+1]);
        assert(seq.skip(i+1).skip(1) == seq.skip(i+2));
        assert(gap.skip(i+1).skip(1) == gap.skip(i+2));
        assert(prefix1 == prefix2 + seq[i+1] + gap[i+1]);
        assert(idx1 == prefix1.as_bytes().len());
        assert(idx2 == prefix2.as_bytes().len());
        assert(seq[i+1] == pat@);
        assert(prefix2.as_bytes() + seq[i+1].as_bytes() + gap[i+1].as_bytes() == prefix1.as_bytes()) by {
            lemma_str_concat_lower(prefix2, seq[i+1]);
            lemma_str_concat_lower(prefix2 + seq[i+1], gap[i+1]);
        }
    }
}


/// Proof that links the full spec to `str::trim_matches` with a `char` pattern.
pub broadcast proof fn lemma_str_trim_matches_char(s: Seq<char>, ch: char, ret: Seq<char>)
    requires
        #[trigger] str_trim_matches_post(s, ch, ret),
    ensures
        ret.is_subrange_of(s),
        ret.len() > 0 ==>
            ret.first() != ch && ret.last() != ch,
        ret == s.skip_while(|c: char| c == ch).rskip_while(|c: char| c == ch),
{
    axiom_char_matches_post(s, ch);
    reveal(str_trim_matches_post);
    let (seq, gap) = spec_matches(s, ch);
    let pred = |c: char| c == ch;
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        lemma_join_empty_gap(seq, gap);
        assert(s == seq.flatten());
        assert forall |i: int| 0 <= i < seq.len() 
        implies #[trigger] seq[i] == seq![ch]
        by { assert(seq[i] =~= seq![ch]) }
        lemma_seq_flatten_same_length(seq, 1);

        assert(seq.len() == s.len());
        assert forall |i: int| 0 <= i < s.len()
        implies #[trigger] pred(s[i])
        by {
            assert(s[i] == s.subrange(i * 1, (i + 1) * 1)[0]);
            assert(s.subrange(i * 1, (i + 1) * 1) == seq[i]);
        }
        assert(s.skip_while(pred).len() == 0) by {
            lemma_seq_count_while_lower_bound(s, pred, s.len() as int);
        }
        assert(s.skip_while(pred).rskip_while(pred).len() == 0) by {
            lemma_seq_rskip_while_ensures(s.skip_while(pred), pred);
        }
        assert(ret.len() == 0);
        lemma_seq_is_subrange_alt(s, ret);
    } else {
        let pred2 = |ss: Seq<char>| ss.len() == 0;
        let head = gap.count_while(pred2) as int;
        let tail = gap.rcount_while(pred2) as int;
        lemma_seq_take_while_ensures(gap, pred2);
        lemma_seq_rtake_while_ensures(gap, pred2);
        assert(head + tail < gap.len()) by {
            let k = choose|i: int| 0 <= i < gap.len() && !(#[trigger] pred2(gap[i]));
            lemma_seq_count_while_upper_bound(gap, pred2, k);
            lemma_seq_rcount_while_upper_bound(gap, pred2, k);
        };

        // TODO: ret == join(...); need to show ret.len() > 0 because it contains at least
        // one non-empty gap

        // decompose `s`
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, head) }
            seq.take(head).map(|i: int, ss: Seq<char>| gap[i] + ss).flatten()
                + join(seq.skip(head), gap.skip(head));
                {
                    let s1 = seq.take(head).map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = seq![seq![ch]; head as nat];
                    assert_seqs_equal!(s1 == s2, j => {
                        assert(pred2(gap.take_while(pred2)[j]));
                        assert(gap.take_while(pred2)[j] == gap[j]);
                        assert(seq[j] =~= seq![ch]);
                    });
                }
            seq![seq![ch]; head as nat].flatten()
                + join(seq.skip(head), gap.skip(head)); 
                { 
                    lemma_join_split_at_alt(seq.skip(head), gap.skip(head), seq.len() - head - tail);
                    assert(seq.skip(head).take(seq.len() - head - tail) == seq.subrange(head, seq.len() - tail));
                    assert(gap.skip(head).take(seq.len() - head - tail + 1) == gap.subrange(head, gap.len() - tail));
                    assert(seq.skip(head).skip(seq.len() - head - tail) == seq.skip(seq.len() - tail));
                    assert(gap.skip(head).skip(seq.len() - head - tail + 1) == gap.skip(gap.len() - tail));
                }
            seq![seq![ch]; head as nat].flatten() + ret + seq.skip(seq.len() - tail)
                .map(|i: int, ss: Seq<char>| ss + gap.skip(gap.len() - tail)[i])
                .flatten();
                {
                    let s1 = seq.skip(seq.len() - tail).map(|i: int, ss: Seq<char>| ss + gap.skip(gap.len() - tail)[i]);
                    let s2 = seq![seq![ch]; tail as nat];
                    assert_seqs_equal!(s1 == s2, j => {
                        assert(pred2(gap.rtake_while(pred2)[j]));
                        assert(gap.rtake_while(pred2)[j] == gap[gap.len() - tail + j]);
                        assert(seq[seq.len() - tail + j] =~= seq![ch]);
                    });
                }
            seq![seq![ch]; head as nat].flatten() + ret + seq![seq![ch]; tail as nat].flatten(); {
                lemma_seq_flatten_same_length(seq![seq![ch]; head as nat], 1);
                assert_seqs_equal!(seq![seq![ch]; head as nat].flatten() == seq![ch; head as nat], i => {
                    assert(seq![seq![ch]; head as nat].flatten().subrange(i*1, (i+1)*1)[0] == seq![seq![ch]; head as nat].flatten()[i]);
                    assert(seq![seq![ch]; head as nat].flatten().subrange(i*1, (i+1)*1)[0] == seq![seq![ch]; head as nat][i][0]);
                });
                lemma_seq_flatten_same_length(seq![seq![ch]; tail as nat], 1);
                assert_seqs_equal!(seq![seq![ch]; tail as nat].flatten() == seq![ch; tail as nat], i => {
                    assert(seq![seq![ch]; tail as nat].flatten().subrange(i*1, (i+1)*1)[0] == seq![seq![ch]; tail as nat].flatten()[i]);
                    assert(seq![seq![ch]; tail as nat].flatten().subrange(i*1, (i+1)*1)[0] == seq![seq![ch]; tail as nat][i][0]);
                });
            }
            seq![ch; head as nat] + ret + seq![ch; tail as nat];
        }
        // #1
        assert(ret.is_subrange_of(s)) by {
            assert(ret == s.subrange(head, s.len() - tail));
            lemma_seq_is_subrange_alt(s, ret);
        }
        // #2
        if ret.len() > 0 { // TODO
            assert(!gap[head].contains(ch));
            assert(!gap[gap.len() - tail - 1].contains(ch));
            assert(gap.subrange(head as int, gap.len() - tail).first() == gap[head]);
            lemma_join_alt(seq.subrange(head as int, seq.len() - tail), gap.subrange(head as int, gap.len() - tail));
            assert(gap.subrange(head as int, gap.len() - tail).last() == gap[gap.len() - tail - 1]);
            assert(ret.first() != ch) by {
                assert(ret.first() == gap.subrange(head as int, gap.len() - tail).first()[0]);
            }
            assert(ret.last() != ch) by {
                assert(ret.last() == gap.subrange(head as int, gap.len() - tail).last().last());
            }
        }
        
        // #3
        // TODO: this now doesn't work because of rlimit issues
        // calc!{
        //     (==)
        //     s.skip_while(pred).rskip_while(pred); {
        //         lemma_seq_skip_while_defines(s, pred, ret + seq![ch; tail as nat]);
        //     }
        //     (ret + seq![ch; tail as nat]).rskip_while(pred); {
        //         lemma_seq_take_while_defines(ret + seq![ch; tail as nat], pred, ret);
        //     }
        //     ret;
        // }
        assume(ret == s.skip_while(pred).rskip_while(pred));
    }
}

/// Proof that links the full spec to `str::trim_matches` with a closure pattern.
pub broadcast proof fn lemma_str_trim_matches_closure<F>(s: Seq<char>, f: F, ret: Seq<char>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_trim_matches_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret.is_subrange_of(s),
        ret.len() > 0 ==>
            call_ensures(f, (ret.first(),), false)
            && call_ensures(f, (ret.last(),), false),
        ret == s.skip_while(|c: char| call_ensures(f, (c,), true))
                .rskip_while(|c: char| call_ensures(f, (c,), true)),
{
    admit()
}

/// Proof that links the full spec to `str::trim_matches` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_trim_matches_chars<'b>(s: Seq<char>, chars: &'b [char], ret: Seq<char>)
    requires
        #[trigger] str_trim_matches_post(s, chars, ret),
    ensures
        ret.is_subrange_of(s),
        ret.len() > 0 ==>
            !chars@.contains(ret.first()) && !chars@.contains(ret.last()),
        ret == s.skip_while(|c: char| chars@.contains(c))
                .rskip_while(|c: char| chars@.contains(c)),
{
    admit()
}

/// Proof that links the full spec to `str::trim_start_matches` with a `char` pattern.
pub broadcast proof fn lemma_str_trim_start_matches_char(s: Seq<char>, ch: char, ret: Seq<char>)
    requires
        #[trigger] str_trim_start_matches_post(s, ch, ret),
    ensures
        ret.is_suffix_of(s),
        ret.len() > 0 ==> ret.first() != ch,
        forall|i: int| 0 <= i < s.len() - ret.len()
            ==> #[trigger] s[i] == ch,
{
    axiom_char_matches_post(s, ch);
    reveal(str_trim_start_matches_post);
    let (seq, gap) = spec_matches(s, ch);
    admit()
}

/// Proof that links the full spec to `str::trim_start_matches` with a closure pattern.
pub broadcast proof fn lemma_str_trim_start_matches_closure<F>(s: Seq<char>, f: F, ret: Seq<char>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_trim_start_matches_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret.is_suffix_of(s),
        ret.len() > 0 ==> call_ensures(f, (ret.first(),), false),
        forall|i: int| 0 <= i < s.len() - ret.len()
            ==> #[trigger] call_ensures(f, (s[i],), true),
{
    axiom_closure_matches_post(s, f);
    reveal(str_trim_start_matches_post);
    let (seq, gap) = spec_matches(s, f);
    admit()
}

/// Proof that links the full spec to `str::trim_start_matches` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_trim_start_matches_chars<'b>(s: Seq<char>, chars: &'b [char], ret: Seq<char>)
    requires
        #[trigger] str_trim_start_matches_post(s, chars, ret),
    ensures
        ret.is_suffix_of(s),
        ret.len() > 0 ==> !chars@.contains(ret.first()),
        forall|i: int| 0 <= i < s.len() - ret.len()
            ==> #[trigger] chars@.contains(s[i]),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_trim_start_matches_post);
    let (seq, gap) = spec_matches(s, chars);
    admit()
}

/// Proof that links the full spec to `str::trim_start_matches` with a string pattern.
pub broadcast proof fn lemma_str_trim_start_matches_string<'b>(s: Seq<char>, pat: &'b str, ret: Seq<char>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_trim_start_matches_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_trim_start_matches_post(s, pat, ret),
    ensures
        ret.is_suffix_of(s),
        ret.len() > 0 ==> !pat@.is_prefix_of(ret),
        (s.len() - ret.len()) % pat@.len() as int == 0,
        forall|i: int| 0 <= i < s.len() - ret.len() && i % pat@.len() as int == 0
            ==> #[trigger] s.subrange(i, i + pat@.len()) == pat@,
{
    admit()
}

/// Proof that links the full spec to `str::trim_end_matches` with a `char` pattern.
pub broadcast proof fn lemma_str_trim_end_matches_char(s: Seq<char>, ch: char, ret: Seq<char>)
    requires
        #[trigger] str_trim_end_matches_post(s, ch, ret),
    ensures
        ret.is_prefix_of(s),
        ret.len() > 0 ==> ret.last() != ch,
        forall|i: int| ret.len() <= i < s.len()
            ==> #[trigger] s[i] == ch,
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_trim_end_matches_post);
    let (seq, gap) = spec_rmatches(s, ch);
    admit()
}

/// Proof that links the full spec to `str::trim_end_matches` with a closure pattern.
pub broadcast proof fn lemma_str_trim_end_matches_closure<F>(s: Seq<char>, f: F, ret: Seq<char>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_trim_end_matches_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret.is_prefix_of(s),
        ret.len() > 0 ==> call_ensures(f, (ret.last(),), false),
        forall|i: int| ret.len() <= i < s.len()
            ==> #[trigger] call_ensures(f, (s[i],), true),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_trim_end_matches_post);
    let (seq, gap) = spec_rmatches(s, f);
    admit()
}

/// Proof that links the full spec to `str::trim_end_matches` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_trim_end_matches_chars<'b>(s: Seq<char>, chars: &'b [char], ret: Seq<char>)
    requires
        #[trigger] str_trim_end_matches_post(s, chars, ret),
    ensures
        ret.is_prefix_of(s),
        ret.len() > 0 ==> !chars@.contains(ret.last()),
        forall|i: int| ret.len() <= i < s.len()
            ==> #[trigger] chars@.contains(s[i]),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_trim_end_matches_post);
    let (seq, gap) = spec_rmatches(s, chars);
    admit()
}

/// Proof that links the full spec to `str::trim_end_matches` with a string pattern.
pub broadcast proof fn lemma_str_trim_end_matches_string<'b>(s: Seq<char>, pat: &'b str, ret: Seq<char>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_trim_end_matches_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_trim_end_matches_post(s, pat, ret),
    ensures
        ret.is_prefix_of(s),
        ret.len() > 0 ==> !pat@.is_suffix_of(ret),
        (s.len() - ret.len()) % pat@.len() as int == 0,
        forall|i: int| 0 <= i < s.len() - ret.len() && i % pat@.len() as int == 0
            ==> #[trigger] s.subrange(ret.len() + i, ret.len() + i + pat@.len()) == pat@,
{
    admit()
}

/// Proof that links the full spec to `str::strip_prefix` with a `char` pattern.
pub broadcast proof fn lemma_str_strip_prefix_char<'a>(s: Seq<char>, ch: char, ret: Option<&'a str>)
    requires
        #[trigger] str_strip_prefix_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && s.first() != ch),
                Some(o) => {
                    &&& s.len() > 0
                    &&& s.first() == ch
                    &&& o@ == s.drop_first()
                },
            }
        }),
{
    axiom_char_matches_post(s, ch);
    reveal(str_strip_prefix_post);
    let (seq, gap) = spec_matches(s, ch);
    match ret {
        None => {
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
        },
        Some(o) => {
            assert(seq.first() == seq![ch] && gap.first().len() == 0);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s[0] == seq.first()[0]);
            assert(s.len() > 0);
            let rest = join(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == parts.flatten());
            assert(s == seq[0] + rest);
            assert(s == seq![ch] + rest);
            assert((seq![ch] + rest).drop_first() == rest);
            assert(o@ == s.drop_first());
        },
    }
}

/// Proof that links the full spec to `str::strip_prefix` with a closure pattern.
pub broadcast proof fn lemma_str_strip_prefix_closure<'a, F>(s: Seq<char>, f: F, ret: Option<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_strip_prefix_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && call_ensures(f, (s.first(),), false)),
                Some(o) => {
                    &&& s.len() > 0
                    &&& call_ensures(f, (s.first(),), true)
                    &&& o@ == s.drop_first()
                },
            }
        }),
{
    axiom_closure_matches_post(s, f);
    reveal(str_strip_prefix_post);
    let (seq, gap) = spec_matches(s, f);
    match ret {
        None => {
            if s.len() > 0 {
                reveal_with_fuel(Seq::<_>::flatten, 2);
                let pred = |c: char| call_ensures(f, (c,), false);
                if seq.len() == 0 {
                    assert(gap.len() == 1);
                    assert(gap.first() == s);
                    assert(gap.first()[0] == s.first());
                    assert(pred(gap.first()[0]));
                    assert(call_ensures(f, (gap.first()[0],), false));
                } else {
                    assert(gap.first().len() > 0);
                    assert(s.first() == gap.first()[0]);
                    assert(pred(gap.first()[0]));
                    assert(call_ensures(f, (gap.first()[0],), false));
                }
            }
        },
        Some(o) => {
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(gap.first().len() == 0);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s[0] == seq.first()[0]);
            assert(s.len() > 0);
            let rest = join(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == parts.flatten());
            assert(s == seq[0] + rest);
            assert((seq[0] + rest).drop_first() == rest);
            assert(o@ == s.drop_first());
        },
    }
}

/// Proof that links the full spec to `str::strip_prefix` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_strip_prefix_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], ret: Option<&'a str>)
    requires
        #[trigger] str_strip_prefix_post(s, chars, ret),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && !chars@.contains(s.first())),
                Some(o) => {
                    &&& s.len() > 0
                    &&& chars@.contains(s.first())
                    &&& o@ == s.drop_first()
                },
            }
        }),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_strip_prefix_post);
    let (seq, gap) = spec_matches(s, chars);
    match ret {
        None => {
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
        },
        Some(o) => {
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(gap.first().len() == 0);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s[0] == seq.first()[0]);
            assert(s.len() > 0);
            let rest = join(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == parts.flatten());
            assert(s == seq[0] + rest);
            assert((seq[0] + rest).drop_first() == rest);
            assert(o@ == s.drop_first());
        },
    }
}

/// Proof that links the full spec to `str::strip_prefix` with a string pattern.
pub broadcast proof fn lemma_str_strip_prefix_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<&'a str>)
    requires
        #[trigger] str_strip_prefix_post(s, pat, ret),
    ensures
        ({
            match ret {
                None => !pat@.is_prefix_of(s),
                Some(o) => {
                    &&& pat@.is_prefix_of(s)
                    &&& o@ == s.skip(pat@.len() as int)
                },
            }
        }),
{
    axiom_string_matches_post(s, pat);
    reveal(str_strip_prefix_post);
    let (seq, gap) = spec_matches(s, pat);
    match ret {
        None => {
            if pat@.is_prefix_of(s) {
                if pat@.len() == 0 {
                    assert(seq.len() == s.len() + 1);
                    assert(gap.first().len() == 0);
                } else {
                    reveal_with_fuel(Seq::<_>::flatten, 4);
                    assert_by_contradiction!(seq.len() > 0, {
                        assert(gap.len() == 1);
                        assert(gap.last() == s);
                        assert(!pat@.is_subrange_of(gap.last()));
                        lemma_seq_is_subrange_alt(gap.last(), pat@);
                    });
                    assert_by_contradiction!(gap.first().len() == 0, {
                        assert(seq.first() == pat@);
                        assert(gap.first().len() > 0);
                        assert(gap.len() > 1);
                        assert(gap.first().len() > 0 ==> !pat@.is_prefix_of(gap.first() + pat@) && !pat@.is_infix_of(gap.first() + pat@));
                        let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
                        assert(parts.len() > 0);
                        assert(parts.first() == seq[0] + gap[1]);
                        assert(s == gap[0] + parts.flatten());
                        lemma_concat_associative(gap[0], seq[0], gap[1]);
                        assert(s == (gap[0] + pat@ + gap[1]) + parts.drop_first().flatten());
                        assert((gap[0] + pat@).is_prefix_of(s));
                        assert(pat@.is_prefix_of(gap[0] + pat@));
                        assert(!pat@.is_prefix_of(gap[0] + pat@));
                    });
                }
            }
        },
        Some(o) => {
            if pat@.len() == 0 {
                assert_seqs_equal!(seq[0] == pat@);
            } else {
                assert(seq.first() == pat@);
            }
            assert(gap.first().len() == 0);
            let rest = join(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == gap[0] + parts.flatten());
            assert(gap[0] == Seq::<char>::empty());
            assert(seq[0] == pat@);
            assert(s == pat@ + rest);
            assert(pat@.is_prefix_of(s));
            assert((pat@ + rest).skip(pat@.len() as int) == rest);
            assert(o@ == s.skip(pat@.len() as int));
        },
    }
}

/// Proof that links the full spec to `str::strip_suffix` with a `char` pattern.
pub broadcast proof fn lemma_str_strip_suffix_char<'a>(s: Seq<char>, ch: char, ret: Option<&'a str>)
    requires
        #[trigger] str_strip_suffix_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && s.last() != ch),
                Some(o) => {
                    &&& s.len() > 0
                    &&& s.last() == ch
                    &&& o@ == s.drop_last()
                },
            }
        }),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_strip_suffix_post);
    let (seq, gap) = spec_rmatches(s, ch);
    match ret {
        None => {
            if s.len() > 0 && s.last() == ch {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                assert_by_contradiction!(seq.len() > 0, {
                    assert(gap.len() == 1);
                    assert(gap.first() == s);
                    assert(gap.first().last() == ch);
                    assert(!gap.first().contains(ch));
                });
                assert_by_contradiction!(gap.first().len() == 0, {
                    assert(s.last() == gap.first().last());
                    assert(gap.first().last() == ch);
                    assert(!gap.first().contains(ch));
                });
            }
        },
        Some(o) => {
            assert(seq.first() == seq![ch] && gap.first().len() == 0);
            let rest = rjoin(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten_alt, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
            assert(parts.len() > 0);
            assert(parts.first() == gap[1] + seq[0]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
            assert(parts.reverse().last() == parts.first());
            assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
            assert(s == parts.reverse().flatten_alt() + gap[0]);
            lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
            assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
            assert(s == rest + seq[0] + gap[0]);
            assert(gap[0] == Seq::<char>::empty());
            assert(seq[0] == seq![ch]);
            assert(s == rest + seq![ch]);
            assert(s.last() == ch);
            assert((rest + seq![ch]).drop_last() == rest);
            assert(o@ == s.drop_last());
        },
    }
}

/// Proof that links the full spec to `str::strip_suffix` with a closure pattern.
pub broadcast proof fn lemma_str_strip_suffix_closure<'a, F>(s: Seq<char>, f: F, ret: Option<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_strip_suffix_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && call_ensures(f, (s.last(),), false)),
                Some(o) => {
                    &&& s.len() > 0
                    &&& call_ensures(f, (s.last(),), true)
                    &&& o@ == s.drop_last()
                },
            }
        }),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_strip_suffix_post);
    let (seq, gap) = spec_rmatches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);
    match ret {
        None => {
            if s.len() > 0 {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                if seq.len() == 0 {
                    assert(gap.len() == 1);
                    assert(gap.first() == s);
                    assert(gap.first().last() == s.last());
                    assert(gap.first().all(pred));
                    assert(pred(gap.first().last()));
                    assert(call_ensures(f, (gap.first().last(),), false));
                } else {
                    assert(gap.first().len() > 0);
                    assert(s.last() == gap.first().last());
                    assert(gap.first().all(pred));
                    assert(pred(gap.first().last()));
                    assert(call_ensures(f, (gap.first().last(),), false));
                }
            }
        },
        Some(o) => {
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(gap.first().len() == 0);
            let rest = rjoin(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten_alt, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
            assert(parts.len() > 0);
            assert(parts.first() == gap[1] + seq[0]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
            assert(parts.reverse().last() == parts.first());
            assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
            assert(s == parts.reverse().flatten_alt() + gap[0]);
            lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
            assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
            assert(s == rest + seq[0] + gap[0]);
            assert(gap[0] == Seq::<char>::empty());
            let last_ch = seq[0][0];
            assert_seqs_equal!(seq[0] == seq![last_ch]);
            assert(s == rest + seq![last_ch]);
            assert(s.last() == last_ch);
            assert(call_ensures(f, (s.last(),), true));
            assert((rest + seq![last_ch]).drop_last() == rest);
            assert(o@ == s.drop_last());
        },
    }
}

/// Proof that links the full spec to `str::strip_suffix` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_strip_suffix_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], ret: Option<&'a str>)
    requires
        #[trigger] str_strip_suffix_post(s, chars, ret),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && !chars@.contains(s.last())),
                Some(o) => {
                    &&& s.len() > 0
                    &&& chars@.contains(s.last())
                    &&& o@ == s.drop_last()
                },
            }
        }),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_strip_suffix_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let pred = |c: char| !chars@.contains(c);
    match ret {
        None => {
            if s.len() > 0 && chars@.contains(s.last()) {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                assert_by_contradiction!(seq.len() > 0, {
                    assert(gap.len() == 1);
                    assert(gap.first() == s);
                    assert(gap.first().last() == s.last());
                    assert(gap.first().all(pred));
                    assert(pred(gap.first().last()));
                    assert(!chars@.contains(gap.first().last()));
                });
                assert_by_contradiction!(gap.first().len() == 0, {
                    assert(s.last() == gap.first().last());
                    assert(gap.first().all(pred));
                    assert(pred(gap.first().last()));
                    assert(!chars@.contains(gap.first().last()));
                });
            }
        },
        Some(o) => {
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(gap.first().len() == 0);
            let rest = rjoin(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten_alt, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
            assert(parts.len() > 0);
            assert(parts.first() == gap[1] + seq[0]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
            assert(parts.reverse().last() == parts.first());
            assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
            assert(s == parts.reverse().flatten_alt() + gap[0]);
            lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
            assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
            assert(s == rest + seq[0] + gap[0]);
            assert(gap[0] == Seq::<char>::empty());
            let last_ch = seq[0][0];
            assert_seqs_equal!(seq[0] == seq![last_ch]);
            assert(s == rest + seq![last_ch]);
            assert(s.last() == last_ch);
            assert(chars@.contains(s.last()));
            assert((rest + seq![last_ch]).drop_last() == rest);
            assert(o@ == s.drop_last());
        },
    }
}

/// Proof that links the full spec to `str::strip_suffix` with a string pattern.
pub broadcast proof fn lemma_str_strip_suffix_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<&'a str>)
    requires
        #[trigger] str_strip_suffix_post(s, pat, ret),
    ensures
        ({
            match ret {
                None => !pat@.is_suffix_of(s),
                Some(o) => {
                    &&& pat@.is_suffix_of(s)
                    &&& o@ == s.take(s.len() - pat@.len())
                },
            }
        }),
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_strip_suffix_post);
    let (seq, gap) = spec_rmatches(s, pat);
    match ret {
        None => {
            if pat@.is_suffix_of(s) {
                if pat@.len() == 0 {
                    assert(seq.len() == s.len() + 1);
                    assert(gap.first().len() == 0);
                } else {
                    reveal_with_fuel(Seq::<_>::flatten_alt, 4);
                    assert_by_contradiction!(seq.len() > 0, {
                        assert(gap.len() == 1);
                        assert(gap.last() == s);
                        assert(!pat@.is_subrange_of(gap.last()));
                        lemma_seq_is_subrange_alt(gap.last(), pat@);
                    });
                    assert_by_contradiction!(gap.first().len() == 0, {
                        assert(seq.first() == pat@);
                        assert(gap.first().len() > 0);
                        assert(gap.len() > 1);
                        assert(gap.first().len() > 0 ==> !pat@.is_suffix_of(pat@ + gap.first()) && !pat@.is_infix_of(pat@ + gap.first()));
                        let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
                        assert(parts.len() > 0);
                        assert(parts.first() == gap[1] + seq[0]);
                        assert(parts.reverse().last() == parts.first());
                        assert(parts.reverse().flatten_alt() == parts.reverse().drop_last().flatten_alt() + parts.reverse().last());
                        assert(s == parts.reverse().flatten_alt() + gap[0]);
                        lemma_concat_associative(parts.reverse().drop_last().flatten_alt(), gap[1], seq[0]);
                        assert(s == (parts.reverse().drop_last().flatten_alt() + gap[1]) + pat@ + gap[0]);
                        assert((pat@ + gap[0]).is_suffix_of(s));
                        assert(pat@.is_suffix_of(pat@ + gap[0]));
                        assert(!pat@.is_suffix_of(pat@ + gap[0]));
                    });
                }
            }
        },
        Some(o) => {
            if pat@.len() == 0 {
                assert_seqs_equal!(seq[0] == pat@);
            } else {
                assert(seq.first() == pat@);
            }
            assert(gap.first().len() == 0);
            let rest = rjoin(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten_alt, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
            assert(parts.len() > 0);
            assert(parts.first() == gap[1] + seq[0]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
            assert(parts.reverse().last() == parts.first());
            assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
            assert(s == parts.reverse().flatten_alt() + gap[0]);
            lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
            assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
            assert(s == rest + seq[0] + gap[0]);
            assert(gap[0] == Seq::<char>::empty());
            assert(seq[0] == pat@);
            assert(s == rest + pat@);
            assert(pat@.is_suffix_of(s));
            assert(s.len() == rest.len() + pat@.len());
            assert(s.len() - pat@.len() == rest.len());
            assert((rest + pat@).take(rest.len() as int) == rest);
            assert(o@ == s.take(s.len() - pat@.len()));
        },
    }
}

// --- Private helper lemmas for str::pattern linking proofs ---

proof fn lemma_join_uncons(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() > 0,
        seq.len() + 1 == gap.len(),
    ensures
        join(seq, gap) == gap[0] + seq[0] + join(seq.skip(1), gap.skip(1)),
{
    reveal_with_fuel(Seq::<_>::flatten, 3);
    let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
    let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
    let rest = join(seq.skip(1), gap.skip(1));
    assert(parts.len() > 0);
    assert(parts.first() == seq[0] + gap[1]);
    assert_seqs_equal!(parts.drop_first() == rest_parts);
    assert(rest == gap[1] + rest_parts.flatten());
    lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
    assert(parts.flatten() == seq[0] + rest);
    assert(join(seq, gap) == gap[0] + parts.flatten());
    lemma_concat_associative(gap[0], seq[0], rest);
    assert(join(seq, gap) == gap[0] + seq[0] + rest);
}

proof fn lemma_join_runcons(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() > 0,
        seq.len() + 1 == gap.len(),
    ensures
        join(seq, gap) == join(seq.drop_last(), gap.drop_last()) + seq.last() + gap.last(),
    decreases
        seq.len(),
{
    reveal_with_fuel(Seq::<_>::flatten, 3);
    if seq.len() == 1 {
        calc!{
            (==)
            join(seq, gap); {}
            gap[0] + seq[0] + gap[1]; {}
            join(seq.drop_last(), gap.drop_last()) + seq.last() + gap.last();
        }
    } else {
        calc!{
            (==)
            join(seq, gap); { lemma_join_uncons(seq, gap) }
            gap[0] + seq[0] + join(seq.skip(1), gap.skip(1)); { lemma_join_runcons(seq.skip(1), gap.skip(1)) }
            gap[0] + seq[0] + join(seq.skip(1).drop_last(), gap.skip(1).drop_last())
                + seq.skip(1).last() + gap.skip(1).last();
                {
                    lemma_join_uncons(seq.drop_last(), gap.drop_last());
                    assert(seq.drop_last().skip(1) == seq.skip(1).drop_last());
                    assert(gap.drop_last().skip(1) == gap.skip(1).drop_last());
                    assert(seq.skip(1).last() == seq.last());
                    assert(gap.skip(1).last() == gap.last());
                }
            join(seq.drop_last(), gap.drop_last()) + seq.last() + gap.last();
        }
    }
}

proof fn lemma_rjoin_uncons(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() > 0,
        seq.len() + 1 == gap.len(),
    ensures
        rjoin(seq, gap) == rjoin(seq.skip(1), gap.skip(1)) + seq[0] + gap[0],
{
    reveal_with_fuel(Seq::<_>::flatten_alt, 4);
    let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
    let rest = rjoin(seq.skip(1), gap.skip(1));
    assert(parts.len() > 0);
    assert(parts.first() == gap[1] + seq[0]);
    assert_seqs_equal!(parts.drop_first() == rest_parts);
    assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
    assert(parts.reverse().last() == parts.first());
    assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
    lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
    assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
    assert(rjoin(seq, gap) == parts.reverse().flatten_alt() + gap[0]);
    assert(rjoin(seq, gap) == rest + seq[0] + gap[0]);
}

proof fn lemma_rjoin_runcons(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() > 0,
        seq.len() + 1 == gap.len(),
    ensures
        rjoin(seq, gap) == gap.last() + seq.last() + rjoin(seq.drop_last(), gap.drop_last()),
    decreases
        seq.len(),
{
    if seq.len() == 1 {
        reveal_with_fuel(Seq::<_>::flatten_alt, 3);
        assert(gap.last() == gap[1]);
        assert(gap.drop_last().last() == gap[0]);
        assert_seqs_equal!(seq.drop_last() == seq![]);
        calc!{
            (==)
            rjoin(seq, gap); {}
            gap[1] + seq[0] + gap[0]; {}
            gap.last() + seq.last() + rjoin(seq.drop_last(), gap.drop_last());
        }
    } else {
        let rest_seq = seq.skip(1);
        let rest_gap = gap.skip(1);
        lemma_rjoin_uncons(seq, gap);
        lemma_rjoin_runcons(rest_seq, rest_gap);
        lemma_rjoin_uncons(seq.drop_last(), gap.drop_last());
        assert(rest_seq.drop_last() == seq.skip(1).drop_last());
        assert(gap.skip(1).drop_last() == gap.drop_last().skip(1));
        assert(seq.drop_last().skip(1) == seq.skip(1).drop_last());
        assert(rest_seq.last() == seq.last());
        assert(rest_gap.last() == gap.last());
        let middle = rjoin(seq.skip(1).drop_last(), gap.skip(1).drop_last());
        calc!{
            (==)
            rjoin(seq, gap); {}
            rjoin(rest_seq, rest_gap) + seq[0] + gap[0]; {}
            (gap.last() + seq.last() + middle) + seq[0] + gap[0];
                {
                    assert(rjoin(rest_seq, rest_gap) == gap.last() + seq.last() + middle);
                }
            gap.last() + seq.last() + (middle + seq[0] + gap[0]);
                {
                    lemma_concat_associative(gap.last(), seq.last(), middle);
                    lemma_concat_associative(gap.last() + seq.last(), middle, seq[0]);
                    lemma_concat_associative(gap.last() + seq.last() + middle, seq[0], gap[0]);
                    lemma_concat_associative(middle, seq[0], gap[0]);
                    lemma_concat_associative(gap.last(), seq.last(), middle + seq[0] + gap[0]);
                    assert(rjoin(seq.drop_last(), gap.drop_last()) == middle + seq[0] + gap[0]);
                }
            gap.last() + seq.last() + rjoin(seq.drop_last(), gap.drop_last());
        }
    }
}

proof fn lemma_join_alt(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
    ensures
        join(seq, gap) == seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(),
    decreases
        seq.len(),
{
    if seq.len() == 0 {
        assert(join(seq, gap) == gap.last());
        assert(seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten().len() == 0);
    } else {
        calc!{
            (==)
            join(seq, gap); { lemma_join_uncons(seq, gap) }
            gap[0] + seq[0] + join(seq.skip(1), gap.skip(1)); { lemma_join_alt(seq.skip(1), gap.skip(1)) }
            (gap[0] + seq[0]) + seq.skip(1).map(|i: int, ss: Seq<char>| gap.skip(1)[i] + ss).flatten() + gap.last(); {
                assert(seq.map(|i: int, ss: Seq<char>| gap[i] + ss).first() == gap[0] + seq[0]);
                assert(seq.map(|i: int, ss: Seq<char>| gap[i] + ss).drop_first() == seq.skip(1).map(|i: int, ss: Seq<char>| gap.skip(1)[i] + ss));
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
            seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last();
        }
    }
}

proof fn lemma_join_split_at(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k <= seq.len(),
    ensures
        join(seq, gap) == seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss).flatten()
            + join(seq.skip(k), gap.skip(k)),
    decreases
        k,
{
    if k == 0 {
        assert_seqs_equal!(seq.skip(k) == seq);
        assert_seqs_equal!(gap.skip(k) == gap);
        assert(seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss).len() == 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
    } else {
        let rest_seq = seq.skip(1);
        let rest_gap = gap.skip(1);
        lemma_join_uncons(seq, gap);
        lemma_join_split_at(rest_seq, rest_gap, k - 1);

        let parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss);
        let rest_parts = rest_seq.take(k - 1).map(|i: int, ss: Seq<char>| rest_gap[i] + ss);
        assert(parts.len() > 0);
        assert(parts.first() == gap[0] + seq[0]);
        assert_seqs_equal!(parts.drop_first() == rest_parts, i => {
            assert(parts.drop_first()[i] == parts[i + 1]);
            assert(seq.take(k)[i + 1] == seq[i + 1]);
            assert(rest_seq.take(k - 1)[i] == rest_seq[i]);
            assert(rest_seq[i] == seq[i + 1]);
            assert(rest_gap[i] == gap[i + 1]);
        });
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(parts.flatten() == (gap[0] + seq[0]) + rest_parts.flatten());
        assert(join(seq, gap) == (gap[0] + seq[0]) + join(rest_seq, rest_gap));
        assert(join(rest_seq, rest_gap) == rest_parts.flatten() + join(rest_seq.skip(k - 1), rest_gap.skip(k - 1)));
        assert_seqs_equal!(rest_seq.skip(k - 1) == seq.skip(k));
        assert_seqs_equal!(rest_gap.skip(k - 1) == gap.skip(k));
        lemma_concat_associative(gap[0] + seq[0], rest_parts.flatten(), join(seq.skip(k), gap.skip(k)));
        assert(join(seq, gap) == parts.flatten() + join(seq.skip(k), gap.skip(k)));
    }
}

proof fn lemma_join_split_at_alt(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k <= seq.len(),
    ensures
        join(seq, gap) == join(seq.take(k), gap.take(k + 1))
            + seq.skip(k).map(|i: int, ss: Seq<char>| ss + gap.skip(k + 1)[i]).flatten()
{
    if k == seq.len() {
        assert(seq.skip(k).len() == 0);
        assert(seq.take(k) == seq);
        assert(gap.take(k + 1) == gap);
    } else {
        lemma_join_split_match_at(seq, gap, k);
        calc!{
            (==)
            seq[k] + join(seq.skip(k + 1), gap.skip(k + 1)); {}
            seq[k] + gap.skip(k + 1)[0]
                + gap.skip(k + 1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(k + 1)[i] + ss).flatten();
                {
                    let s1 = gap.skip(k + 1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(k + 1)[i] + ss);
                    let s2 = seq.skip(k).map(|i: int, ss: Seq<char>| ss + gap.skip(k + 1)[i]).drop_first();
                    assert_seqs_equal!(s1 == s2);
                    assert(seq[k] + gap.skip(k + 1)[0] == seq.skip(k).map(|i: int, ss: Seq<char>| ss + gap.skip(k + 1)[i]).first());
                }
            seq.skip(k).map(|i: int, ss: Seq<char>| ss + gap.skip(k + 1)[i]).flatten();
        }
    }
}

proof fn lemma_join_split_match_at(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k < seq.len(),
    ensures
        join(seq, gap) == join(seq.take(k), gap.take(k + 1))
            + seq[k] + join(seq.skip(k + 1), gap.skip(k + 1)),
{
    lemma_join_split_at(seq, gap, k);
    lemma_join_uncons(seq.skip(k), gap.skip(k));
    lemma_join_alt(seq.take(k), gap.take(k + 1));
    let parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss).flatten();
    let prefix = join(seq.take(k), gap.take(k + 1));
    let rest = join(seq.skip(k + 1), gap.skip(k + 1));
    assert(seq.skip(k)[0] == seq[k]);
    assert(gap.skip(k)[0] == gap[k]);
    assert(seq.skip(k).skip(1) == seq.skip(k + 1));
    assert(gap.skip(k).skip(1) == gap.skip(k + 1));
    assert(join(seq.skip(k), gap.skip(k)) == gap[k] + seq[k] + rest);
    assert(gap.take(k + 1).last() == gap[k]);
    lemma_join_alt(seq.take(k), gap.take(k + 1));
    let prefix_parts = seq.take(k).map(|i: int, ss: Seq<char>| gap.take(k + 1)[i] + ss).flatten();
    assert_seqs_equal!(seq.take(k).map(|i: int, ss: Seq<char>| gap.take(k + 1)[i] + ss)
        == seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss), i => {
        assert(gap.take(k + 1)[i] == gap[i]);
    });
    assert_seqs_equal!(prefix_parts == parts);
    assert_seqs_equal!(prefix == parts + gap[k]);
    lemma_concat_associative(parts, gap[k], seq[k] + rest);
    lemma_concat_associative(parts + gap[k], seq[k], rest);
    assert(join(seq, gap) == prefix + seq[k] + rest);
}

proof fn lemma_rjoin_alt(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
    ensures
        rjoin(seq, gap) == seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss).reverse().flatten_alt() + gap.first(),
{
    let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let alt_parts = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
    assert_seqs_equal!(parts == alt_parts, i => {
        assert(gap.drop_first()[i] == gap[i + 1]);
    });
}

proof fn lemma_rjoin_alt_for_matches(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
    ensures
        rjoin(seq, gap) == gap.last() + seq.map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().flatten_alt(),
    decreases
        seq.len(),
{
    if seq.len() == 0 {
        assert(gap.last() == gap.first());
        assert(seq.map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
    } else {
        lemma_rjoin_uncons(seq, gap);
        lemma_rjoin_alt_for_matches(seq.skip(1), gap.skip(1));

        let parts = seq.map(|i: int, ss: Seq<char>| ss + gap[i]);
        let rest_parts = seq.skip(1).map(|i: int, ss: Seq<char>| ss + gap.skip(1)[i]);
        assert(parts.len() > 0);
        assert(parts.first() == seq[0] + gap[0]);
        assert_seqs_equal!(parts.drop_first() == rest_parts, i => {
            assert(parts.drop_first()[i] == parts[i + 1]);
            assert(seq.skip(1)[i] == seq[i + 1]);
            assert(gap.skip(1)[i] == gap[i + 1]);
        });
        assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
        assert(parts.reverse().last() == parts.first());
        assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (seq[0] + gap[0]));
        assert(rjoin(seq.skip(1), gap.skip(1)) == gap.last() + rest_parts.reverse().flatten_alt());
        lemma_concat_associative(gap.last(), rest_parts.reverse().flatten_alt(), seq[0] + gap[0]);
        assert(rjoin(seq, gap) == gap.last() + parts.reverse().flatten_alt());
    }
}

proof fn lemma_rjoin_split_at(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k <= seq.len(),
    ensures
        rjoin(seq, gap) == rjoin(seq.skip(k), gap.skip(k))
            + seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().flatten_alt(),
    decreases
        k,
{
    if k == 0 {
        assert_seqs_equal!(seq.skip(k) == seq);
        assert_seqs_equal!(gap.skip(k) == gap);
        assert(seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
    } else {
        let rest_seq = seq.skip(1);
        let rest_gap = gap.skip(1);
        lemma_rjoin_uncons(seq, gap);
        lemma_rjoin_split_at(rest_seq, rest_gap, k - 1);

        let parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
        let rest_parts = rest_seq.take(k - 1).map(|i: int, ss: Seq<char>| ss + rest_gap[i]);
        assert(parts.len() > 0);
        assert(parts.first() == seq[0] + gap[0]);
        assert_seqs_equal!(parts.drop_first() == rest_parts, i => {
            assert(parts.drop_first()[i] == parts[i + 1]);
            assert(seq.take(k)[i + 1] == seq[i + 1]);
            assert(rest_seq.take(k - 1)[i] == rest_seq[i]);
            assert(rest_seq[i] == seq[i + 1]);
            assert(rest_gap[i] == gap[i + 1]);
        });
        assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
        assert(parts.reverse().last() == parts.first());
        assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (seq[0] + gap[0]));
        assert(rjoin(seq, gap) == rjoin(rest_seq, rest_gap) + seq[0] + gap[0]);
        assert(rjoin(rest_seq, rest_gap) == rjoin(rest_seq.skip(k - 1), rest_gap.skip(k - 1)) + rest_parts.reverse().flatten_alt());
        assert_seqs_equal!(rest_seq.skip(k - 1) == seq.skip(k));
        assert_seqs_equal!(rest_gap.skip(k - 1) == gap.skip(k));
        lemma_concat_associative(rjoin(seq.skip(k), gap.skip(k)), rest_parts.reverse().flatten_alt(), seq[0] + gap[0]);
        assert(rjoin(seq, gap) == rjoin(seq.skip(k), gap.skip(k)) + parts.reverse().flatten_alt());
    }
}

proof fn lemma_rjoin_split_match_at(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k < seq.len(),
    ensures
        rjoin(seq, gap) == rjoin(seq.skip(k + 1), gap.skip(k + 1))
            + seq[k] + rjoin(seq.take(k), gap.take(k + 1)),
{
    lemma_rjoin_split_at(seq, gap, k);
    lemma_rjoin_uncons(seq.skip(k), gap.skip(k));
    let rest = rjoin(seq.skip(k + 1), gap.skip(k + 1));
    let suffix = rjoin(seq.take(k), gap.take(k + 1));
    let parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().flatten_alt();
    assert(seq.skip(k)[0] == seq[k]);
    assert(gap.skip(k)[0] == gap[k]);
    assert(seq.skip(k).skip(1) == seq.skip(k + 1));
    assert(gap.skip(k).skip(1) == gap.skip(k + 1));
    assert(rjoin(seq.skip(k), gap.skip(k)) == rest + seq[k] + gap[k]);
    assert(gap.take(k + 1).last() == gap[k]);
    lemma_rjoin_split_at(seq.take(k), gap.take(k + 1), k);
    assert(seq.take(k).skip(k) == seq![]);
    assert(gap.take(k + 1).skip(k) == seq![gap[k]]);
    assert(rjoin(seq.take(k).skip(k), gap.take(k + 1).skip(k)) == gap[k]);
    assert_seqs_equal!(seq.take(k).take(k).map(|i: int, ss: Seq<char>| ss + gap.take(k + 1)[i])
        == seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]), i => {
        assert(gap.take(k + 1)[i] == gap[i]);
    });
    assert(suffix == gap[k] + parts);
    lemma_concat_associative(rest, seq[k], gap[k] + parts);
    lemma_concat_associative(rest + seq[k], gap[k], parts);
    assert(rjoin(seq, gap) == rest + seq[k] + suffix);
}

proof fn lemma_join_empty_gap(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
        gap.all(|ss: Seq<char>| ss.len() == 0),
    ensures
        join(seq, gap) == seq.flatten(),
    decreases
        seq.len(),
{
    let pred = |ss: Seq<char>| ss.len() == 0;
    if seq.len() == 0 {
        assert(join(seq, gap) == gap[0]);
        assert(pred(gap[0]));
        assert(join(seq, gap).len() == 0);
        assert(seq.flatten().len() == 0);
    } else {
        calc!{
            (==)
            join(seq, gap); { lemma_join_uncons(seq, gap) }
            gap[0] + seq[0] + join(seq.skip(1), gap.skip(1)); { assert(pred(gap[0])) }
            seq[0] + join(seq.skip(1), gap.skip(1)); { lemma_join_empty_gap(seq.skip(1), gap.skip(1)) }
            seq[0] + seq.skip(1).flatten(); {}
            seq.flatten();
        }
    }
}

proof fn lemma_str_matches_count(
    seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, pred: spec_fn(char) -> bool,
)
    requires
        gap.len() == seq.len() + 1,
        forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() ==> gap[i].all(|c: char| !pred(c)),
        forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> seq[i].len() == 1 && pred(seq[i][0]),
    ensures
        join(seq, gap).count(pred) == seq.len(),
    decreases
        seq.len(),
{
    if seq.len() == 0 {
        assert(gap.len() == 1);
        assert_seqs_equal!(join(seq, gap) == gap[0]);
        gap[0].lemma_all_neg_filter_empty(pred);
    } else {
        let rest_seq = seq.drop_first();
        let rest_gap = gap.drop_first();
        assert(rest_gap.len() == rest_seq.len() + 1);
        assert forall |i: int| #![trigger rest_gap[i]] 0 <= i < rest_gap.len()
            implies rest_gap[i].all(|c: char| !pred(c)) by {
            assert(rest_gap[i] == gap[i + 1]);
        }
        assert forall |i: int| #![trigger rest_seq[i]] 0 <= i < rest_seq.len()
            implies rest_seq[i].len() == 1 && pred(rest_seq[i][0]) by {
            assert(rest_seq[i] == seq[i + 1]);
        }
        lemma_str_matches_count(rest_seq, rest_gap, pred);

        let rest = join(rest_seq, rest_gap);
        let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
        let rest_parts = rest_gap.drop_first().map(|i: int, ss: Seq<char>| rest_seq[i] + ss);
        assert(parts.len() > 0);
        assert(parts.first() == seq[0] + gap[1]);
        assert_seqs_equal!(parts.drop_first() == rest_parts, i => {
            assert(gap.drop_first().drop_first()[i] == gap[i + 2]);
            assert(rest_gap.drop_first()[i] == gap[i + 2]);
            assert(rest_seq[i] == seq[i + 1]);
        });
        reveal_with_fuel(Seq::<_>::flatten, 3);
        assert(rest == gap[1] + rest_parts.flatten());
        lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
        assert(parts.flatten() == seq[0] + rest);
        assert(join(seq, gap) == gap[0] + parts.flatten());
        lemma_concat_associative(gap[0], seq[0], rest);
        assert(join(seq, gap) == gap[0] + seq[0] + rest);
        gap[0].lemma_all_neg_filter_empty(pred);
        assert(seq[0].filter(pred).len() == 1) by {
            reveal(Seq::filter);
            assert(seq[0].last() == seq[0][0]);
            assert(seq[0].drop_last().len() == 0);
        }
        Seq::<char>::filter_distributes_over_add(gap[0], seq[0], pred);
        Seq::<char>::filter_distributes_over_add(gap[0] + seq[0], rest, pred);
        assert(join(seq, gap).filter(pred).len() == rest.filter(pred).len() + 1);
    }
}

proof fn lemma_str_rmatches_count(
    seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, pred: spec_fn(char) -> bool,
)
    requires
        gap.len() == seq.len() + 1,
        forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() ==> gap[i].all(|c: char| !pred(c)),
        forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> seq[i].len() == 1 && pred(seq[i][0]),
    ensures
        rjoin(seq, gap).count(pred) == seq.len(),
    decreases
        seq.len(),
{
    if seq.len() == 0 {
        assert(gap.len() == 1);
        assert_seqs_equal!(rjoin(seq, gap) == gap[0]);
        gap[0].lemma_all_neg_filter_empty(pred);
    } else {
        let rest_seq = seq.drop_first();
        let rest_gap = gap.drop_first();
        assert(rest_gap.len() == rest_seq.len() + 1);
        assert forall |i: int| #![trigger rest_gap[i]] 0 <= i < rest_gap.len()
            implies rest_gap[i].all(|c: char| !pred(c)) by {
            assert(rest_gap[i] == gap[i + 1]);
        }
        assert forall |i: int| #![trigger rest_seq[i]] 0 <= i < rest_seq.len()
            implies rest_seq[i].len() == 1 && pred(rest_seq[i][0]) by {
            assert(rest_seq[i] == seq[i + 1]);
        }
        lemma_str_rmatches_count(rest_seq, rest_gap, pred);

        let rest = rjoin(rest_seq, rest_gap);
        let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
        let rest_parts = rest_gap.drop_first().map(|i: int, ss: Seq<char>| ss + rest_seq[i]);
        assert(parts.len() > 0);
        assert(parts.first() == gap[1] + seq[0]);
        assert_seqs_equal!(parts.drop_first() == rest_parts, i => {
            assert(gap.drop_first().drop_first()[i] == gap[i + 2]);
            assert(rest_gap.drop_first()[i] == gap[i + 2]);
            assert(rest_seq[i] == seq[i + 1]);
        });
        assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
        assert(parts.reverse().last() == parts.first());
        reveal_with_fuel(Seq::<_>::flatten_alt, 4);
        assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
        assert(rjoin(seq, gap) == parts.reverse().flatten_alt() + gap[0]);
        assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
        lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
        assert(parts.reverse().flatten_alt() == rest + seq[0]);
        lemma_concat_associative(rest, seq[0], gap[0]);
        assert(rjoin(seq, gap) == rest + seq[0] + gap[0]);
        gap[0].lemma_all_neg_filter_empty(pred);
        assert(seq[0].filter(pred).len() == 1) by {
            reveal(Seq::filter);
            assert(seq[0].last() == seq[0][0]);
            assert(seq[0].drop_last().len() == 0);
        }
        Seq::<char>::filter_distributes_over_add(rest, seq[0], pred);
        Seq::<char>::filter_distributes_over_add(rest + seq[0], gap[0], pred);
        assert(rjoin(seq, gap).filter(pred).len() == rest.filter(pred).len() + 1);
    }
}

}
