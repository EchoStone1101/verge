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
use vstd::arithmetic::div_mod::*;
use vstd::seq_lib::{
    lemma_flatten_concat, lemma_concat_associative,
};

use std::str::pattern::*;

verus! {

mod internal;
mod contains;
mod starts_with;
mod ends_with;
mod find;
mod rfind;
mod split;
mod split_inclusive;
mod rsplit;
mod split_terminator;
mod rsplit_terminator;
mod splitn;
mod rsplitn;
mod split_once;
mod rsplit_once;
mod matches;
mod rmatches;
mod match_indices;
mod rmatch_indices;
mod trim_matches;
mod trim_start_matches;
mod trim_end_matches;
mod strip_prefix;
mod strip_suffix;

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

// TODO: common lemmas concerning join and rjoin

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

// TODO: missing linking lemmas for APIs like str::split_whitespace

/// Proof that links the full spec to `str::contains` with a `char` pattern.
pub use contains::lemma_str_contains_char;

/// Proof that links the full spec to `str::contains` with a closure pattern.
pub use contains::lemma_str_contains_closure;

/// Proof that links the full spec to `str::contains` with a `&[char]` pattern.
pub use contains::lemma_str_contains_chars;

/// Proof that links the full spec to `str::contains` with a string pattern.
pub use contains::lemma_str_contains_string;

/// Proof that links the full spec to `str::starts_with` with a `char` pattern.
pub use starts_with::lemma_str_starts_with_char;

/// Proof that links the full spec to `str::starts_with` with a closure pattern.
pub use starts_with::lemma_str_starts_with_closure;

/// Proof that links the full spec to `str::starts_with` with a `&[char]` pattern.
pub use starts_with::lemma_str_starts_with_chars;

/// Proof that links the full spec to `str::starts_with` with a string pattern.
pub use starts_with::lemma_str_starts_with_string;

/// Proof that links the full spec to `str::ends_with` with a `char` pattern.
pub use ends_with::lemma_str_ends_with_char;

/// Proof that links the full spec to `str::ends_with` with a closure pattern.
pub use ends_with::lemma_str_ends_with_closure;

/// Proof that links the full spec to `str::ends_with` with a `&[char]` pattern.
pub use ends_with::lemma_str_ends_with_chars;

/// Proof that links the full spec to `str::ends_with` with a string pattern.
pub use ends_with::lemma_str_ends_with_string;

/// Proof that links the full spec to `str::find` with a `char` pattern.
pub use find::lemma_str_find_char;

/// Proof that links the full spec to `str::find` with a closure pattern.
pub use find::lemma_str_find_closure;

/// Proof that links the full spec to `str::find` with a `&[char]` pattern.
pub use find::lemma_str_find_chars;

/// Proof that links the full spec to `str::find` with a string pattern.
pub use find::lemma_str_find_string;

/// Proof that links the full spec to `str::rfind` with a `char` pattern.
pub use rfind::lemma_str_rfind_char;

/// Proof that links the full spec to `str::rfind` with a closure pattern.
pub use rfind::lemma_str_rfind_closure;

/// Proof that links the full spec to `str::rfind` with a `&[char]` pattern.
pub use rfind::lemma_str_rfind_chars;

/// Proof that links the full spec to `str::rfind` with a string pattern.
pub use rfind::lemma_str_rfind_string;

/// Proof that links the full spec to `str::split` with a `char` pattern.
pub use split::lemma_str_split_iter_char;

/// Proof that links the full spec to `str::split` with a closure pattern.
pub use split::lemma_str_split_iter_closure;

/// Proof that links the full spec to `str::split` with a `&[char]` pattern.
pub use split::lemma_str_split_iter_chars;

/// Proof that links the full spec to `str::split` with a string pattern.
pub use split::lemma_str_split_iter_string;

/// Proof that links the full spec to `str::split_inclusive` with a `char` pattern.
pub use split_inclusive::lemma_str_split_inclusive_iter_char;

/// Proof that links the full spec to `str::split_inclusive` with a closure pattern.
pub use split_inclusive::lemma_str_split_inclusive_iter_closure;

/// Proof that links the full spec to `str::split_inclusive` with a `&[char]` pattern.
pub use split_inclusive::lemma_str_split_inclusive_iter_chars;

/// Proof that links the full spec to `str::split_inclusive` with a string pattern.
pub use split_inclusive::lemma_str_split_inclusive_iter_string;

/// Proof that links the full spec to `str::rsplit` with a `char` pattern.
pub use rsplit::lemma_str_rsplit_iter_char;

/// Proof that links the full spec to `str::rsplit` with a closure pattern.
pub use rsplit::lemma_str_rsplit_iter_closure;

/// Proof that links the full spec to `str::rsplit` with a `&[char]` pattern.
pub use rsplit::lemma_str_rsplit_iter_chars;

/// Proof that links the full spec to `str::rsplit` with a string pattern.
pub use rsplit::lemma_str_rsplit_iter_string;

/// Proof that links the full spec to `str::split_terminator` with a `char` pattern.
pub use split_terminator::lemma_str_split_terminator_iter_char;

/// Proof that links the full spec to `str::split_terminator` with a closure pattern.
pub use split_terminator::lemma_str_split_terminator_iter_closure;

/// Proof that links the full spec to `str::split_terminator` with a `&[char]` pattern.
pub use split_terminator::lemma_str_split_terminator_iter_chars;

/// Proof that links the full spec to `str::split_terminator` with a string pattern.
pub use split_terminator::lemma_str_split_terminator_iter_string;

/// Proof that links the full spec to `str::rsplit_terminator` with a `char` pattern.
pub use rsplit_terminator::lemma_str_rsplit_terminator_iter_char;

/// Proof that links the full spec to `str::rsplit_terminator` with a closure pattern.
pub use rsplit_terminator::lemma_str_rsplit_terminator_iter_closure;

/// Proof that links the full spec to `str::rsplit_terminator` with a `&[char]` pattern.
pub use rsplit_terminator::lemma_str_rsplit_terminator_iter_chars;

/// Proof that links the full spec to `str::rsplit_terminator` with a string pattern.
pub use rsplit_terminator::lemma_str_rsplit_terminator_iter_string;

/// Proof that links the full spec to `str::splitn` with a `char` pattern.
pub use splitn::lemma_str_splitn_iter_char;

/// Proof that links the full spec to `str::splitn` with a closure pattern.
pub use splitn::lemma_str_splitn_iter_closure;

/// Proof that links the full spec to `str::splitn` with a `&[char]` pattern.
pub use splitn::lemma_str_splitn_iter_chars;

/// Proof that links the full spec to `str::splitn` with a string pattern.
pub use splitn::lemma_str_splitn_iter_string;

/// Proof that links the full spec to `str::rsplitn` with a `char` pattern.
pub use rsplitn::lemma_str_rsplitn_iter_char;

/// Proof that links the full spec to `str::rsplitn` with a closure pattern.
pub use rsplitn::lemma_str_rsplitn_iter_closure;

/// Proof that links the full spec to `str::rsplitn` with a `&[char]` pattern.
pub use rsplitn::lemma_str_rsplitn_iter_chars;

/// Proof that links the full spec to `str::rsplitn` with a string pattern.
pub use rsplitn::lemma_str_rsplitn_iter_string;

/// Proof that links the full spec to `str::split_once` with a `char` pattern.
pub use split_once::lemma_str_split_once_char;

/// Proof that links the full spec to `str::split_once` with a closure pattern.
pub use split_once::lemma_str_split_once_closure;

/// Proof that links the full spec to `str::split_once` with a `&[char]` pattern.
pub use split_once::lemma_str_split_once_chars;

/// Proof that links the full spec to `str::split_once` with a string pattern.
pub use split_once::lemma_str_split_once_string;

/// Proof that links the full spec to `str::rsplit_once` with a `char` pattern.
pub use rsplit_once::lemma_str_rsplit_once_char;

/// Proof that links the full spec to `str::rsplit_once` with a closure pattern.
pub use rsplit_once::lemma_str_rsplit_once_closure;

/// Proof that links the full spec to `str::rsplit_once` with a `&[char]` pattern.
pub use rsplit_once::lemma_str_rsplit_once_chars;

/// Proof that links the full spec to `str::rsplit_once` with a string pattern.
pub use rsplit_once::lemma_str_rsplit_once_string;

/// Proof that links the full spec to `str::matches` with a `char` pattern.
pub use matches::lemma_str_matches_iter_char;

/// Proof that links the full spec to `str::matches` with a closure pattern.
pub use matches::lemma_str_matches_iter_closure;

/// Proof that links the full spec to `str::matches` with a `&[char]` pattern.
pub use matches::lemma_str_matches_iter_chars;

/// Proof that links the full spec to `str::matches` with a string pattern.
pub use matches::lemma_str_matches_iter_string;

/// Proof that links the full spec to `str::rmatches` with a `char` pattern.
pub use rmatches::lemma_str_rmatches_iter_char;

/// Proof that links the full spec to `str::rmatches` with a closure pattern.
pub use rmatches::lemma_str_rmatches_iter_closure;

/// Proof that links the full spec to `str::rmatches` with a `&[char]` pattern.
pub use rmatches::lemma_str_rmatches_iter_chars;

/// Proof that links the full spec to `str::rmatches` with a string pattern.
pub use rmatches::lemma_str_rmatches_iter_string;

/// Proof that links the full spec to `str::match_indices` with a `char` pattern.
pub use match_indices::lemma_str_match_indices_iter_char;

/// Proof that links the full spec to `str::match_indices` with a closure pattern.
pub use match_indices::lemma_str_match_indices_iter_closure;

/// Proof that links the full spec to `str::match_indices` with a `&[char]` pattern.
pub use match_indices::lemma_str_match_indices_iter_chars;

/// Proof that links the full spec to `str::match_indices` with a string pattern.
pub use match_indices::lemma_str_match_indices_iter_string;

/// Proof that links the full spec to `str::rmatch_indices` with a `char` pattern.
pub use rmatch_indices::lemma_str_rmatch_indices_iter_char;

/// Proof that links the full spec to `str::rmatch_indices` with a closure pattern.
pub use rmatch_indices::lemma_str_rmatch_indices_iter_closure;

/// Proof that links the full spec to `str::rmatch_indices` with a `&[char]` pattern.
pub use rmatch_indices::lemma_str_rmatch_indices_iter_chars;

/// Proof that links the full spec to `str::rmatch_indices` with a string pattern.
pub use rmatch_indices::lemma_str_rmatch_indices_iter_string;

/// Proof that links the full spec to `str::trim_matches` with a `char` pattern.
pub use trim_matches::lemma_str_trim_matches_char;

/// Proof that links the full spec to `str::trim_matches` with a closure pattern.
pub use trim_matches::lemma_str_trim_matches_closure;

/// Proof that links the full spec to `str::trim_matches` with a `&[char]` pattern.
pub use trim_matches::lemma_str_trim_matches_chars;

/// Proof that links the full spec to `str::trim_start_matches` with a `char` pattern.
pub use trim_start_matches::lemma_str_trim_start_matches_char;

/// Proof that links the full spec to `str::trim_start_matches` with a closure pattern.
pub use trim_start_matches::lemma_str_trim_start_matches_closure;

/// Proof that links the full spec to `str::trim_start_matches` with a `&[char]` pattern.
pub use trim_start_matches::lemma_str_trim_start_matches_chars;

/// Proof that links the full spec to `str::trim_start_matches` with a string pattern.
pub use trim_start_matches::lemma_str_trim_start_matches_string;

/// Proof that links the full spec to `str::trim_end_matches` with a `char` pattern.
pub use trim_end_matches::lemma_str_trim_end_matches_char;

/// Proof that links the full spec to `str::trim_end_matches` with a closure pattern.
pub use trim_end_matches::lemma_str_trim_end_matches_closure;

/// Proof that links the full spec to `str::trim_end_matches` with a `&[char]` pattern.
pub use trim_end_matches::lemma_str_trim_end_matches_chars;

/// Proof that links the full spec to `str::trim_end_matches` with a string pattern.
pub use trim_end_matches::lemma_str_trim_end_matches_string;

/// Proof that links the full spec to `str::strip_prefix` with a `char` pattern.
pub use strip_prefix::lemma_str_strip_prefix_char;

/// Proof that links the full spec to `str::strip_prefix` with a closure pattern.
pub use strip_prefix::lemma_str_strip_prefix_closure;

/// Proof that links the full spec to `str::strip_prefix` with a `&[char]` pattern.
pub use strip_prefix::lemma_str_strip_prefix_chars;

/// Proof that links the full spec to `str::strip_prefix` with a string pattern.
pub use strip_prefix::lemma_str_strip_prefix_string;

/// Proof that links the full spec to `str::strip_suffix` with a `char` pattern.
pub use strip_suffix::lemma_str_strip_suffix_char;

/// Proof that links the full spec to `str::strip_suffix` with a closure pattern.
pub use strip_suffix::lemma_str_strip_suffix_closure;

/// Proof that links the full spec to `str::strip_suffix` with a `&[char]` pattern.
pub use strip_suffix::lemma_str_strip_suffix_chars;

/// Proof that links the full spec to `str::strip_suffix` with a string pattern.
pub use strip_suffix::lemma_str_strip_suffix_string;

// --- Broadcast groups by API ---

/// Broadcast group for all `str::contains` pattern linking lemmas.
pub broadcast group group_str_contains {
    lemma_str_contains_char,
    lemma_str_contains_closure,
    lemma_str_contains_chars,
    lemma_str_contains_string,
}

/// Broadcast group for all `str::starts_with` pattern linking lemmas.
pub broadcast group group_str_starts_with {
    lemma_str_starts_with_char,
    lemma_str_starts_with_closure,
    lemma_str_starts_with_chars,
    lemma_str_starts_with_string,
}

/// Broadcast group for all `str::ends_with` pattern linking lemmas.
pub broadcast group group_str_ends_with {
    lemma_str_ends_with_char,
    lemma_str_ends_with_closure,
    lemma_str_ends_with_chars,
    lemma_str_ends_with_string,
}

/// Broadcast group for all `str::find` pattern linking lemmas.
pub broadcast group group_str_find {
    lemma_str_find_char,
    lemma_str_find_closure,
    lemma_str_find_chars,
    lemma_str_find_string,
}

/// Broadcast group for all `str::rfind` pattern linking lemmas.
pub broadcast group group_str_rfind {
    lemma_str_rfind_char,
    lemma_str_rfind_closure,
    lemma_str_rfind_chars,
    lemma_str_rfind_string,
}

/// Broadcast group for all `str::split` pattern linking lemmas.
pub broadcast group group_str_split_iter {
    lemma_str_split_iter_char,
    lemma_str_split_iter_closure,
    lemma_str_split_iter_chars,
    lemma_str_split_iter_string,
}

/// Broadcast group for all `str::split_inclusive` pattern linking lemmas.
pub broadcast group group_str_split_inclusive_iter {
    lemma_str_split_inclusive_iter_char,
    lemma_str_split_inclusive_iter_closure,
    lemma_str_split_inclusive_iter_chars,
    lemma_str_split_inclusive_iter_string,
}

/// Broadcast group for all `str::rsplit` pattern linking lemmas.
pub broadcast group group_str_rsplit_iter {
    lemma_str_rsplit_iter_char,
    lemma_str_rsplit_iter_closure,
    lemma_str_rsplit_iter_chars,
    lemma_str_rsplit_iter_string,
}

/// Broadcast group for all `str::split_terminator` pattern linking lemmas.
pub broadcast group group_str_split_terminator_iter {
    lemma_str_split_terminator_iter_char,
    lemma_str_split_terminator_iter_closure,
    lemma_str_split_terminator_iter_chars,
    lemma_str_split_terminator_iter_string,
}

/// Broadcast group for all `str::rsplit_terminator` pattern linking lemmas.
pub broadcast group group_str_rsplit_terminator_iter {
    lemma_str_rsplit_terminator_iter_char,
    lemma_str_rsplit_terminator_iter_closure,
    lemma_str_rsplit_terminator_iter_chars,
    lemma_str_rsplit_terminator_iter_string,
}

/// Broadcast group for all `str::splitn` pattern linking lemmas.
pub broadcast group group_str_splitn_iter {
    lemma_str_splitn_iter_char,
    lemma_str_splitn_iter_closure,
    lemma_str_splitn_iter_chars,
    lemma_str_splitn_iter_string,
}

/// Broadcast group for all `str::rsplitn` pattern linking lemmas.
pub broadcast group group_str_rsplitn_iter {
    lemma_str_rsplitn_iter_char,
    lemma_str_rsplitn_iter_closure,
    lemma_str_rsplitn_iter_chars,
    lemma_str_rsplitn_iter_string,
}

/// Broadcast group for all `str::split_once` pattern linking lemmas.
pub broadcast group group_str_split_once {
    lemma_str_split_once_char,
    lemma_str_split_once_closure,
    lemma_str_split_once_chars,
    lemma_str_split_once_string,
}

/// Broadcast group for all `str::rsplit_once` pattern linking lemmas.
pub broadcast group group_str_rsplit_once {
    lemma_str_rsplit_once_char,
    lemma_str_rsplit_once_closure,
    lemma_str_rsplit_once_chars,
    lemma_str_rsplit_once_string,
}

/// Broadcast group for all `str::matches` pattern linking lemmas.
pub broadcast group group_str_matches_iter {
    lemma_str_matches_iter_char,
    lemma_str_matches_iter_closure,
    lemma_str_matches_iter_chars,
    lemma_str_matches_iter_string,
}

/// Broadcast group for all `str::rmatches` pattern linking lemmas.
pub broadcast group group_str_rmatches_iter {
    lemma_str_rmatches_iter_char,
    lemma_str_rmatches_iter_closure,
    lemma_str_rmatches_iter_chars,
    lemma_str_rmatches_iter_string,
}

/// Broadcast group for all `str::match_indices` pattern linking lemmas.
pub broadcast group group_str_match_indices_iter {
    lemma_str_match_indices_iter_char,
    lemma_str_match_indices_iter_closure,
    lemma_str_match_indices_iter_chars,
    lemma_str_match_indices_iter_string,
}

/// Broadcast group for all `str::rmatch_indices` pattern linking lemmas.
pub broadcast group group_str_rmatch_indices_iter {
    lemma_str_rmatch_indices_iter_char,
    lemma_str_rmatch_indices_iter_closure,
    lemma_str_rmatch_indices_iter_chars,
    lemma_str_rmatch_indices_iter_string,
}

/// Broadcast group for all `str::trim_matches` pattern linking lemmas.
pub broadcast group group_str_trim_matches {
    lemma_str_trim_matches_char,
    lemma_str_trim_matches_closure,
    lemma_str_trim_matches_chars,
}

/// Broadcast group for all `str::trim_start_matches` pattern linking lemmas.
pub broadcast group group_str_trim_start_matches {
    lemma_str_trim_start_matches_char,
    lemma_str_trim_start_matches_closure,
    lemma_str_trim_start_matches_chars,
    lemma_str_trim_start_matches_string,
}

/// Broadcast group for all `str::trim_end_matches` pattern linking lemmas.
pub broadcast group group_str_trim_end_matches {
    lemma_str_trim_end_matches_char,
    lemma_str_trim_end_matches_closure,
    lemma_str_trim_end_matches_chars,
    lemma_str_trim_end_matches_string,
}

/// Broadcast group for all `str::strip_prefix` pattern linking lemmas.
pub broadcast group group_str_strip_prefix {
    lemma_str_strip_prefix_char,
    lemma_str_strip_prefix_closure,
    lemma_str_strip_prefix_chars,
    lemma_str_strip_prefix_string,
}

/// Broadcast group for all `str::strip_suffix` pattern linking lemmas.
pub broadcast group group_str_strip_suffix {
    lemma_str_strip_suffix_char,
    lemma_str_strip_suffix_closure,
    lemma_str_strip_suffix_chars,
    lemma_str_strip_suffix_string,
}

}
