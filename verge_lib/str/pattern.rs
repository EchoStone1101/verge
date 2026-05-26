//! Specifications and lemmas for string pattern related operations.
//!
//! ## Specification Methodology
//! To specify `str::split`, `str::contains`, and other methods that make use of 
//! the `std::str::Pattern` trait, Verge directly models the `Pattern` trait by
//! adding the core specs (`splitn` and `rsplitn`) as extension to the trait, 
//! which are used to derive the general post-condition specs (e.g., `str_contains_post`) 
//! regardless of the pattern type. Then, broadcast lemmas use the general 
//! specs as triggers to automatically introduce actual specs per pattern type 
//! (e.g., `lemma_str_contains_str` for `&str` patterns, `lemma_str_contains_char` 
//! for `char` patterns). This design minimizes both spec redundancy and user burden.

use super::*;
use crate::seq::*;
use std::str::{
    Split, SplitInclusive, SplitTerminator, SplitN, 
};
use std::str::pattern::{
    Pattern, Searcher, ReverseSearcher, DoubleEndedSearcher,
};

verus! {

/// Enables `std::str::pattern::Pattern`.
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(PatternSpec via PatternSpecImpl)]
pub trait ExPattern: Sized {
    type ExternalTraitSpecificationFor: Pattern;

    /// Post-conditions for forward string splitting using this pattern.
    /// 
    /// Semantically, this function specifies the uninterpreted spec function `spec_splitn`,
    /// where the splits are captured as `seq` and the delimiters are captured as `delim`.
    /// Other forward pattern-matching methods receive specs derived from this.
    spec fn splitn_post<'a>(self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>) -> bool
        recommends n > 0,
    ;

    /// Post-conditions for backward string splitting using this pattern.
    /// 
    /// Semantically, this function specifies the uninterpreted spec function `spec_rsplitn`, 
    /// where the splits are captured as `seq` and the delimiters are captured as `delim`.
    /// Other backward pattern-matching methods receive specs derived from this.
    spec fn rsplitn_post<'a>(self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>) -> bool
        recommends n > 0,
    ;
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

/// Forward joining `seq` and `delim`.
#[verifier::inline]
pub open spec fn join<'a>(seq: Seq<&'a str>, delim: Seq<&'a str>) -> Seq<char>
    recommends
        delim.len() + 1 == seq.len(),
{
    seq.first()@
    + seq
        .drop_first()
        .map(|i: int, ss: &'a str| delim[i]@ + ss@)
        .flatten()
}

/// Backward joining `seq` and `delim`.
#[verifier::inline]
pub open spec fn rjoin<'a>(seq: Seq<&'a str>, delim: Seq<&'a str>) -> Seq<char>
    recommends
        delim.len() + 1 == seq.len(),
{
    seq
        .drop_first()
        .map(|i: int, ss: &'a str| ss@ + delim[i]@)
        .reverse()
        .flatten()
    + seq.first()@
}

/// Post-conditions for splitting by the `char` pattern, aside from the joining.
#[verifier::inline]
pub open spec fn char_splits_post<'a>(
    s: &'a str, n: int, c: char, seq: Seq<&'a str>, delim: Seq<&'a str>,
) -> bool 
{
    // splits are never empty, and there are at most `n` of them
    &&& 0 < seq.len() <= n
    // splits (apart from the last) cannot contain the pattern
    &&& forall |i: int| 0 <= i < seq.len() - 1 ==> !(#[trigger] seq[i]@.contains(c))
    // last split (if not the n-th) cannot contain the pattern
    &&& seq.len() < n ==> !seq.last()@.contains(c)
    // delimiters have one item less than seq
    &&& delim.len() + 1 == seq.len()
    // delimiters match the pattern
    &&& forall |i: int| 0 <= i < delim.len() ==> #[trigger] (delim[i]@ =~= seq![c])
}

/// Post-conditions for splitting by the closure pattern, aside from the joining.
#[verifier::inline]
pub open spec fn closure_splits_post<'a, F>(
    s: &'a str, n: int, f: F, seq: Seq<&'a str>, delim: Seq<&'a str>,
) -> bool 
where F: FnMut(char) -> bool
{
    // splits are never empty, and there are at most `n` of them
    &&& 0 < seq.len() <= n
    // splits (apart from the last) cannot contain the pattern
    &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==> 
        seq[i]@.all(|c: char| call_ensures(f, (c,), false))
    // last split (if not the n-th) cannot contain the pattern
    &&& seq.len() < n ==> seq.last()@.all(|c: char| call_ensures(f, (c,), false))
    // delimiters have one item less than seq
    &&& delim.len() + 1 == seq.len()
    // delimiters match the pattern
    &&& forall |i: int| #![trigger delim[i]] 0 <= i < delim.len() ==> 
        delim[i]@.len() == 1 && call_ensures(f, (delim[i]@[0],), true)
}

/// Post-conditions for splitting by the char slice pattern, aside from the joining.
#[verifier::inline]
pub open spec fn chars_splits_post<'a>(
    s: &'a str, n: int, chars: Seq<char>, seq: Seq<&'a str>, delim: Seq<&'a str>,
) -> bool 
{
    // splits are never empty, and there are at most `n` of them
    &&& 0 < seq.len() <= n
    // splits (apart from the last) cannot contain the pattern
    &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==> 
        chars.all(|c: char| !seq[i]@.contains(c))
    // last split (if not the n-th) cannot contain the pattern
    &&& seq.len() < n ==> chars.all(|c: char| !seq.last()@.contains(c))
    // delimiters have one item less than seq
    &&& delim.len() + 1 == seq.len()
    // delimiters match the pattern
    &&& forall |i: int| #![trigger delim[i]] 0 <= i < delim.len() ==> 
        chars.any(|c: char| delim[i]@ == seq![c])
}

/// Post-conditions for forward splitting by the string pattern, aside from the joining.
#[verifier::inline]
pub open spec fn str_splits_post<'a>(
    s: &'a str, n: int, pat: Seq<char>, seq: Seq<&'a str>, delim: Seq<&'a str>,
) -> bool 
{
    // splits are never empty, and there are at most `n` splits
    &&& 0 < seq.len() <= n
    // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
    &&& forall |i: int| 0 <= i < seq.len() - 1 ==> 
        !(#[trigger] pat.is_prefix_of(seq[i]@ + pat) || #[trigger] pat.is_infix_of(seq[i]@ + pat))
    // last split (if not the n-th) cannot have `pat` as a substring
    &&& seq.len() < n ==> !(#[trigger] pat.is_subrange_of(seq.last()@))
    // delimiters have one item less than seq
    &&& delim.len() + 1 == seq.len()
    // delimiters match the pattern
    &&& forall |i: int| 0 <= i < delim.len() ==> #[trigger] (delim[i]@ =~= pat)
}

/// Post-conditions for backward splitting by the string pattern, aside from the joining.
#[verifier::inline]
pub open spec fn str_rsplits_post<'a>(
    s: &'a str, n: int, pat: Seq<char>, seq: Seq<&'a str>, delim: Seq<&'a str>,
) -> bool 
{
    // splits are never empty, and there are at most `n` splits
    &&& 0 < seq.len() <= n
    // `pat + split` (apart from the last) cannot have `pat` as a suffix or infix
    &&& forall |i: int| 0 <= i < seq.len() - 1 ==> 
        !(#[trigger] pat.is_suffix_of(pat + seq[i]@) || #[trigger] pat.is_infix_of(pat + seq[i]@))
    // last split (if not the n-th) cannot have `pat` as a substring
    &&& seq.len() < n ==> !(#[trigger] pat.is_subrange_of(seq.last()@))
    // delimiters have one item less than seq
    &&& delim.len() + 1 == seq.len()
    // delimiters match the pattern
    &&& forall |i: int| 0 <= i < delim.len() ==> #[trigger] (delim[i]@ =~= pat)
}

// ---------- Trigger specs ----------
// These exist as triggers for the per-type lemmas.

/// Encodes forward splitting `s` by general pattern `pat`, into up to `n` items, 
/// returning the splits and the matched delimiters.
pub uninterp spec fn spec_splitn<'a, P: Pattern>(s: &'a str, n: int, pat: P) -> (Seq<&'a str>, Seq<&'a str>)
    recommends n > 0,
;

/// Encodes backward splitting `s` by general pattern `pat`, into up to `n` items, 
/// returning the splits and the matched delimiters.
pub uninterp spec fn spec_rsplitn<'a, P: Pattern>(s: &'a str, n: int, pat: P) -> (Seq<&'a str>, Seq<&'a str>)
    recommends n > 0,
;

/// Encodes `str::contains` for general patterns.
pub closed spec fn str_contains_post<'a, P: Pattern>(s: &'a str, pat: P, ret: bool) -> bool {
    let (seq, delim) = spec_splitn(s, 2, pat);
    pat.splitn_post(s, 2, seq, delim) ==> {
        ret == (delim.len() > 0)
    }
}

/// Encodes `str::starts_with` for general patterns.
pub closed spec fn str_starts_with_post<'a, P: Pattern>(s: &'a str, pat: P, ret: bool) -> bool {
    let (seq, delim) = spec_splitn(s, 2, pat);
    pat.splitn_post(s, 2, seq, delim) ==> {
        ret == (delim.len() > 0 && seq.first()@.len() == 0)
    }
}

/// Encodes `str::ends_with` for general patterns.
pub closed spec fn str_ends_with_post<'a, P>(s: &'a str, pat: P, ret: bool) -> bool 
    where 
        P: Pattern,
        for<'b> <P as Pattern>::Searcher<'b>: ReverseSearcher<'b>,
{
    let (seq, delim) = spec_rsplitn(s, 2, pat);
    pat.rsplitn_post(s, 2, seq, delim) ==> {
        ret == (delim.len() > 0 && seq.first()@.len() == 0)
    }
}

/// Encodes `str::find` for general patterns.
pub closed spec fn str_find_post<'a, P: Pattern>(s: &'a str, pat: P, ret: Option<usize>) -> bool {
    let (seq, delim) = spec_splitn(s, 2, pat);
    pat.splitn_post(s, 2, seq, delim) ==> {
        &&& ret is None ==> delim.len() == 0
        &&& ret is Some ==> 
            delim.len() > 0 
            && ret->0 == seq.first()@.as_bytes().len()
    }
}

/// Encodes `str::rfind` for general patterns.
pub closed spec fn str_rfind_post<'a, P>(s: &'a str, pat: P, ret: Option<usize>) -> bool 
    where 
        P: Pattern,
        for<'b> <P as Pattern>::Searcher<'b>: ReverseSearcher<'b>,
{
    let (seq, delim) = spec_rsplitn(s, 2, pat);
    pat.rsplitn_post(s, 2, seq, delim) ==> {
        &&& ret is None ==> delim.len() == 0
        &&& ret is Some ==> 
            delim.len() > 0 
            && ret->0 == s@.as_bytes().len() - seq.first()@.as_bytes().len() - delim.first()@.as_bytes().len()
    }
}

// TODO: 
// add trait methods for xxx -> xxx_iter() (IteratorSpec encoding)
// e.g., char_indices_iter; split_iter; ...
// iter -> iterate 

// pub assume_specification<P> [ str::ends_with ] (s: &str, pat: P) -> (ret: bool)
//     where 
//         P: Pattern, 
//         for<'a> <P as Pattern>::Searcher<'a>: ReverseSearcher<'a>,
//     ensures
//         true,
// ;

// /// Encodes `str::split` for general patterns.
// pub closed spec fn str_find_post<'a, P: Pattern>(s: &'a str, pat: P, ret: Split<'a, P>) -> bool {
//     let (seq, delim) = spec_splitn(s, 2, pat);
//     pat.splitn_post(s, 2, seq, delim) ==> {
//         &&& ret is None ==> delim.len() == 0
//         &&& ret is Some ==> 
//             delim.len() > 0 
//             && ret->0 == seq.first()@.as_bytes().len()
//     }
// }


// pub proof fn lemma_str_contains_str<'a, 'b>(s: &'a str, pat: &'b str)
//     requires
//         str_contains(s, pat),
//     ensures
//         pat@.is_subrange_of(s@),
// {
//     admit()
// }


// ---------- Specs for `Pattern` ----------

// `char`

impl PatternSpecImpl for char {
    /// Forward splitting with the `char` pattern.
    open spec fn splitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        &&& char_splits_post(s, n, self, seq, delim)
        &&& s@ =~= join(seq, delim)
    }

    /// Backward splitting with the `char` pattern.
    open spec fn rsplitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        // `char` splitting works the same backwards
        &&& char_splits_post(s, n, self, seq, delim)
        &&& s@ =~= rjoin(seq, delim)
    }
}

// closure

impl<F> PatternSpecImpl for F 
    where F: FnMut(char) -> bool
{
    /// Forward splitting with the closure pattern.
    open spec fn splitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        &&& closure_splits_post(s, n, self, seq, delim)
        &&& s@ =~= join(seq, delim)
    }

    /// Backward splitting with the closure pattern.
    open spec fn rsplitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        // closure splitting works the same backwards
        &&& closure_splits_post(s, n, self, seq, delim)
        &&& s@ =~= rjoin(seq, delim)
    }
}

// `&[char]` / `&[char; N]` / `[char; N]`

impl<'b> PatternSpecImpl for &'b [char] {
    /// Forward splitting with the `&[char]` pattern.
    open spec fn splitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        &&& chars_splits_post(s, n, self@, seq, delim)
        &&& s@ =~= join(seq, delim)
    }

    /// Backward splitting with the `&[char]` pattern.
    open spec fn rsplitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        // `&[char]` splitting works the same backwards
        &&& chars_splits_post(s, n, self@, seq, delim)
        &&& s@ =~= rjoin(seq, delim)
    }
}

impl<'b, const N: usize> PatternSpecImpl for &'b [char; N] {
    /// Forward splitting with the `&[char; N]` pattern.
    open spec fn splitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        &&& chars_splits_post(s, n, self@, seq, delim)
        &&& s@ =~= join(seq, delim)
    }

    /// Backward splitting with the `&[char; N]` pattern.
    open spec fn rsplitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        // `&[char; N]` splitting works the same backwards
        &&& chars_splits_post(s, n, self@, seq, delim)
        &&& s@ =~= rjoin(seq, delim)
    }
}

impl<const N: usize> PatternSpecImpl for [char; N] {
    /// Forward splitting with the `[char; N]` pattern.
    open spec fn splitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        &&& chars_splits_post(s, n, self@, seq, delim)
        &&& s@ =~= join(seq, delim)
    }

    /// Backward splitting with the `[char; N]` pattern.
    open spec fn rsplitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        // `[char; N]` splitting works the same backwards
        &&& chars_splits_post(s, n, self@, seq, delim)
        &&& s@ =~= rjoin(seq, delim)
    }
}

// `&str` / `&String` / `&&str`

impl<'b> PatternSpecImpl for &'b str {
    /// Forward splitting with the `&str` pattern.
    open spec fn splitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        &&& str_splits_post(s, n, self@, seq, delim)
        &&& s@ =~= join(seq, delim)
    }

    /// Backward splitting with the `&str` pattern.
    open spec fn rsplitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        &&& str_rsplits_post(s, n, self@, seq, delim)
        &&& s@ =~= rjoin(seq, delim)
    }
}

impl<'b> PatternSpecImpl for &'b String {
    /// Forward splitting with the `&String` pattern.
    open spec fn splitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        &&& str_splits_post(s, n, self@, seq, delim)
        &&& s@ =~= join(seq, delim)
    }

    /// Backward splitting with the `&String` pattern.
    open spec fn rsplitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        &&& str_rsplits_post(s, n, self@, seq, delim)
        &&& s@ =~= rjoin(seq, delim)
    }
}

impl<'b, 'c> PatternSpecImpl for &'c &'b str {
    /// Forward splitting with the `&&str` pattern.
    open spec fn splitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        &&& str_splits_post(s, n, self@, seq, delim)
        &&& s@ =~= join(seq, delim)
    }

    /// Backward splitting with the `&&str` pattern.
    open spec fn rsplitn_post<'a>(
        self, s: &'a str, n: int, seq: Seq<&'a str>, delim: Seq<&'a str>,
    ) -> bool 
    {
        &&& str_rsplits_post(s, n, self@, seq, delim)
        &&& s@ =~= rjoin(seq, delim)
    }
}

}