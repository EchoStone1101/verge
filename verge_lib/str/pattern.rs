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
    admit()
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
    admit()
}

/// Proof that links the full spec to `str::ends_with` with a `&[char]` pattern.
pub broadcast proof fn lemma_str_ends_with_chars<'b>(s: Seq<char>, chars: &'b [char], ret: bool)
    requires
        #[trigger] str_ends_with_post(s, chars, ret),
    ensures
        ret <==> s.len() > 0 && chars@.contains(s.last()),
{
    admit()
}

/// Proof that links the full spec to `str::ends_with` with a string pattern.
pub broadcast proof fn lemma_str_ends_with_string<'b>(s: Seq<char>, pat: &'b str, ret: bool)
    requires
        #[trigger] str_ends_with_post(s, pat, ret),
    ensures
        ret <==> pat@.is_suffix_of(s),
{
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
            <==> s == iter_seq.map_values(|ss: &'a str| ss@.push(ch)).flatten(),
        s.len() > 0 && s.last() != ch 
            <==> s == iter_seq.drop_last().map_values(|ss: &'a str| ss@.push(ch)).flatten() + iter_seq.last()@,
{
    admit()
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
                    <==> {
                        &&& delim.len() == iter_seq.len() 
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten()
                    }
            &&& s.len() > 0 && call_ensures(f, (s.last(),), false)
                    <==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten() + iter_seq.last()@
                    }
        },
{
    admit()
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
            &&& s.len() > 0 && chars@.contains(s.first())
                    <==> {
                        &&& delim.len() == iter_seq.len() 
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten()
                    }
            &&& s.len() > 0 && !chars@.contains(s.first())
                    <==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten() + iter_seq.last()@
                    }
        },
{
    admit()
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
    admit()
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
            <==> s == iter_seq.map_values(|ss: &'a str| ss@.push(ch)).reverse().flatten(),
        s.len() > 0 && s.last() != ch 
            <==> s == iter_seq.drop_first().map_values(|ss: &'a str| ss@.push(ch)).reverse().flatten() + iter_seq.first()@,
{
    admit()
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
                    <==> {
                        &&& delim.len() == iter_seq.len()
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten()
                    }
            &&& s.len() > 0 && call_ensures(f, (s.last(),), false)
                    <==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten() + iter_seq.first()@
                    }
        },
{
    admit()
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
            &&& s.len() > 0 && chars@.contains(s.first())
                    <==> {
                        &&& delim.len() == iter_seq.len()
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten()
                    }
            &&& s.len() > 0 && !chars@.contains(s.first())
                    <==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten() + iter_seq.first()@
                    }
        },
{
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
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
    admit()
}

}