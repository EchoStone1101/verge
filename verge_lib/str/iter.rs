//! Iterator methods and types for strings.

#![allow(unused_imports)]
use super::*;
use crate::iter::{IteratorView, impl_iterator_default, impl_iterator_verge};

use std::str::{
    CharIndices, SplitAsciiWhitespace, Lines,
};

verus! {

/// Enables `std::str::CharIndices` as an iterator.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCharIndices<'a>(CharIndices<'a>);

impl_iterator_default!(
    CharIndices['a] where Item = (usize, char)
    [ str::char_indices ] (s: &'a str) -> |seq| {
        seq == s@.map(|i: int, c: char| (s@.take(i).as_bytes().len() as usize, c))
    }
);

/// Enables `std::str::SplitAsciiWhitespace` as an iterator.
/// 
/// The iterator returned will return string slices that are sub-slices of the original string slice, 
/// separated by any amount of ASCII whitespace.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExSplitAsciiWhitespace<'a>(SplitAsciiWhitespace<'a>);

impl_iterator_default!(
    SplitAsciiWhitespace['a] where Item = &'a str
    [ str::split_ascii_whitespace ] (s: &'a str) -> |seq| {
        // splits cannot have whitespaces, and are not empty
        &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> {
            &&& seq[i]@.len() > 0
            &&& forall |j: int| #![trigger seq[i]@[j]] 0 <= j < seq[i]@.len() ==> 
                    !seq[i]@[j].is_ascii_whitespace()
        }
        &&& exists |ws: Seq<Seq<char>>| {
            // delimeters are all whitespaces
            &&& #[trigger] ws.len() == seq.len() + 1
            &&& forall |i: int| #![trigger ws[i]] 0 <= i < ws.len() ==> {
                &&& 1 <= i < ws.len() - 1 ==> ws[i].len() > 0
                &&& forall |j: int| #![trigger ws[i][j]] 0 <= j < ws[i].len() ==> 
                        ws[i][j].is_ascii_whitespace()
            }    
            // delimeters and splits make up the original string
            &&& s@ =~= seq.zip_with(ws.drop_first()).fold_left(
                ws.first(), |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1
            )
        }
    }
);

/// Enables `std::str::Lines` as an iterator.
///
/// Lines are split at line endings that are either newlines (`\n`) or sequences of a carriage return followed by a line feed (`\r\n`).
/// Line terminators are not included in the lines returned by the iterator.
/// Note that any carriage return (`\r`) not immediately followed by a line feed (`\n`) does not split a line. 
/// These carriage returns are thereby included in the produced lines.
/// The final line ending is optional. A string that ends with a final line ending will return the same lines as an otherwise identical 
/// string without a final line ending.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExLines<'a>(Lines<'a>);

impl_iterator_default!(
    Lines['a] where Item = &'a str
    [ str::lines ] (s: &'a str) -> |seq| {
        // lines cannot have `\n`
        &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> 
                forall |j: int| #![trigger seq[i]@[j]] 0 <= j < seq[i]@.len() ==> 
                    !(seq[i]@[j] == '\n')
        // the last line (if there is) must be empty (empty `s` map to *no* lines)
        &&& seq.len() > 0 ==> seq.last()@.len() > 0
        &&& exists |nls: Seq<Seq<char>>| {
            // delimeters are all `\n` or `\r\n`; the last can be empty
            &&& #[trigger] nls.len() == seq.len()
            &&& forall |i: int| #![trigger nls[i]] 0 <= i < nls.len() ==> {
                &&& nls[i] == seq!['\n'] || nls[i] == seq!['\r', '\n'] || (i == nls.len() - 1 && nls[i].len() == 0 )
                &&& nls[i] == seq!['\n'] ==> !seq!['\r'].is_suffix_of(seq[i]@)
            }
            // delimeters and lines make up the original string
            &&& s@ =~= seq.zip_with(nls).fold_left(
                Seq::<char>::empty(), |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1
            )
        }
    }
);

/// Enables `Split` as an iterator (wrapping is needed because we don't fully support the `Pattern` trait bound).
///
/// Returns an iterator over substrings of this string slice, separated by characters matched by a pattern.
/// If there are no matches the full string slice is returned as the only item in the iterator.
#[verifier::external]
pub struct Split<'a, 'pat>(std::str::Split<'a, &'pat str>);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExSplit<'a, 'pat>(Split<'a, 'pat>);

impl_iterator_verge!(
    Split ['a, 'pat] where Item = &'a str
    [ str_split via str::split ] (s: &'a str, pat: &'pat str) 
        requires(pat@.len() > 0) -> |seq| { 
        // splits are never empty
        &&& seq.len() > 0
        // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
        &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==> 
                forall |j: int| #![trigger (seq[i]@ + pat@).subrange(j, j + pat@.len())] 0 <= j < seq[i]@.len() ==> 
                    !((seq[i]@ + pat@).subrange(j, j + pat@.len()) =~= pat@)
        // last split cannot have `pat` as a substring
        &&& forall |j: int| #![trigger seq.last()@.subrange(j, j + pat@.len())] 0 <= j <= seq.last()@.len() - pat@.len() ==> 
                !(seq.last()@.subrange(j, j + pat@.len()) =~= pat@)
        // delimeters and splits make up the original string
        &&& s@ =~= seq.drop_first().fold_left(
            seq.first()@, |sum: Seq<char>, ss: &'a str| sum + pat@ + ss@
        )
    }
);

/// Enables `SplitInclusive` as an iterator (wrapping is needed because we don't fully support the `Pattern` trait bound).
///
/// Returns an iterator over substrings of this string slice, separated by characters matched by a pattern.
/// Unlike `Split`, `SplitInclusive` leaves the matched part as the terminator of the substring.
#[verifier::external]
pub struct SplitInclusive<'a, 'pat>(std::str::SplitInclusive<'a, &'pat str>);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExSplitInclusive<'a, 'pat>(SplitInclusive<'a, 'pat>);

impl_iterator_verge!(
    SplitInclusive ['a, 'pat] where Item = &'a str
    [ str_split_inclusive via str::split_inclusive ] (s: &'a str, pat: &'pat str)
        requires(pat@.len() > 0) -> |seq| {
        // splits cannot have `pat` as a prefix or infix
        &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> 
                forall |j: int| #![trigger seq[i]@.subrange(j, j + pat@.len())] 0 <= j < seq[i]@.len() - pat@.len() ==> 
                    !(seq[i]@.subrange(j, j + pat@.len()) =~= pat@)
        // splits (apart from the last) must have `pat` as a suffix
        &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==> 
                pat@.is_suffix_of(seq[i]@)
        // splits make up the original string
        &&& s@ =~= seq.fold_left(
            Seq::<char>::empty(), |sum: Seq<char>, ss: &'a str| sum + ss@
        )
    }
);

/// Enables `SplitTerminator` as an iterator (wrapping is needed because we don't fully support the `Pattern` trait bound).
///
/// Returns an iterator over substrings of the given string slice, separated by characters matched by a pattern.
/// Equivalent to `Split`, except that the trailing substring is skipped if empty.
#[verifier::external]
pub struct SplitTerminator<'a, 'pat>(std::str::SplitTerminator<'a, &'pat str>);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExSplitTerminator<'a, 'pat>(SplitTerminator<'a, 'pat>);

impl_iterator_verge!(
    SplitTerminator ['a, 'pat] where Item = &'a str
    [ str_split_terminator via str::split_terminator ] (s: &'a str, pat: &'pat str) 
        requires(pat@.len() > 0) -> |seq| {
        // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
        &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==> 
                forall |j: int| #![trigger (seq[i]@ + pat@).subrange(j, j + pat@.len())] 0 <= j < seq[i]@.len() ==> 
                    !((seq[i]@ + pat@).subrange(j, j + pat@.len()) =~= pat@)
        // the last returned split cannot have `pat` as a substring
        &&& seq.len() > 0 ==> {
            &&& forall |j: int| #![trigger seq.last()@.subrange(j, j + pat@.len())] 0 <= j <= seq.last()@.len() - pat@.len() ==> 
                    !(seq.last()@.subrange(j, j + pat@.len()) =~= pat@)
            // `split_terminator` either matches `split`, or drops one trailing empty split
            &&& (
                (
                    seq.last()@.len() > 0
                    && s@ =~= seq.drop_first().fold_left(
                        seq.first()@, |sum: Seq<char>, ss: &'a str| sum + pat@ + ss@
                    )
                )
                ||
                s@ =~= seq.drop_first().fold_left(
                    seq.first()@, |sum: Seq<char>, ss: &'a str| sum + pat@ + ss@
                ) + pat@
            )
        }
        // the empty input still yields no splits
        &&& seq.len() == 0 ==> s@.len() == 0
    }
);

/// Enables `SplitN` as an iterator (wrapping is needed because we don't fully support the `Pattern` trait bound).
///
/// Returns an iterator over substrings of the given string slice, separated by a pattern, restricted to returning at most `n` items.
/// If `n` substrings are returned, the last substring (the `n`th substring) will contain the remainder of the string.
#[verifier::external]
pub struct SplitN<'a, 'pat>(std::str::SplitN<'a, &'pat str>);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExSplitN<'a, 'pat>(SplitN<'a, 'pat>);

impl_iterator_verge!(
    SplitN ['a, 'pat] where Item = &'a str
    [ str_splitn via str::splitn ] (s: &'a str, n: usize, pat: &'pat str) 
        requires(n > 0 && pat@.len() > 0) -> |seq| { 
        // splits are never empty, and there are at most `n` splits
        &&& 0 < seq.len() <= n
        // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
        &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==> 
                forall |j: int| #![trigger (seq[i]@ + pat@).subrange(j, j + pat@.len())] 0 <= j < seq[i]@.len() ==>
                    !((seq[i]@ + pat@).subrange(j, j + pat@.len()) =~= pat@)
        // last split (if not the n-th) cannot have `pat` as a substring
        &&& seq.len() < n ==>
            forall |j: int| #![trigger seq.last()@.subrange(j, j + pat@.len())] 0 <= j <= seq.last()@.len() - pat@.len() ==> 
                !(seq.last()@.subrange(j, j + pat@.len()) =~= pat@)
        // delimeters and splits make up the original string
        &&& s@ =~= seq.drop_first().fold_left(
            seq.first()@, |sum: Seq<char>, ss: &'a str| sum + pat@ + ss@
        )
    }
);

/// Enables `str::split_once`.
#[verifier::external_body]
pub fn str_split_once<'a, 'pat>(s: &'a str, pat: &'pat str) -> (ret: Option<(&'a str, &'a str)>)
    requires
        pat@.len() > 0,
    ensures
        ({
            match ret {
                Some((head, tail)) => {
                    // `head + pat` cannot have `pat` as a prefix or infix
                    &&& forall |i: int| #![trigger head@.subrange(i, i + pat@.len())] 0 <= i < head@.len() ==> 
                            !((head@ + pat@).subrange(i, i + pat@.len()) =~= pat@)
                    // delimeter and splits make up the original string
                    &&& s@ =~= head@ + pat@ + tail@
                },
                None => {
                    forall |i: int| #![trigger s@.subrange(i, i + pat@.len())] 0 <= i <= s@.len() - pat@.len() ==> 
                        !(s@.subrange(i, i + pat@.len()) =~= pat@)
                },
            }
        }),
    no_unwind
{
    s.split_once(pat)
}

/// Enables `MatchIndices` as an iterator (wrapping is needed because we don't fully support the `Pattern` trait bound).
///
/// Returns an iterator over the disjoint matches of a pattern within this string slice as well as the index that the match starts at.
/// For matches of pat within self that overlap, only the indices corresponding to the first match are returned.
#[verifier::external]
pub struct MatchIndices<'a, 'pat>(std::str::MatchIndices<'a, &'pat str>);
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExMatchIndices<'a, 'pat>(MatchIndices<'a, 'pat>);

impl_iterator_verge!(
    MatchIndices ['a, 'pat] where Item = (usize, &'a str)
    [ str_match_indices via str::match_indices ] (s: &'a str, pat: &'pat str) 
        requires(pat@.len() > 0) -> |seq| { 
        let slen = s@.as_bytes().len() as int;
        let plen = pat@.as_bytes().len() as int;
        let indices = seq.map(|_i: int, p: (usize, &'a str)| p.0 as int);
        let ends = indices.map(|_i: int, idx: int| idx + plen);
        let mismatches = (seq![0int] + ends).zip_with(indices + seq![(s@.as_bytes().len() - plen + 1) as int]);
        // indices points to matches
        &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> {
            &&& indices[i] + plen <= slen
            &&& s@.as_bytes().subrange(indices[i], indices[i] + plen) =~= pat@.as_bytes()
            &&& seq[i].1@ =~= pat@
        }
        // matches are disjoint and ordered
        &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==> indices[i] + plen <= indices[i + 1]
        // mismatches cannot have matches
        &&& forall |i: int| #![trigger mismatches[i]] 0 <= i < mismatches.len() ==> 
                forall |j: int| #![trigger s@.as_bytes().subrange(j, j + plen)] mismatches[i].0 <= j < mismatches[i].1 ==> 
                    !(s@.as_bytes().subrange(j, j + plen) =~= pat@.as_bytes())
    }
);

mod tests {
    use super::*;

    proof fn lemma_fold_left_keeps_prefix<'a>(xs: Seq<&'a str>, init: Seq<char>, pat: Seq<char>, k: int)
        requires
            0 <= k <= init.len(),
        ensures
            xs.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + pat + ss@).subrange(0, k) =~=
                init.subrange(0, k),
        decreases xs.len(),
    {
        if xs.len() == 0 {
            assert(xs.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + pat + ss@) =~= init) by {
                reveal_with_fuel(Seq::<_>::fold_left, 2);
            }
        } else {
            xs.lemma_fold_left_split(init, |sum: Seq<char>, ss: &'a str| sum + pat + ss@, 1);
            assert(xs.subrange(0, 1).len() == 1);
            assert(xs.subrange(0, 1)[0] == xs[0]);
            assert(xs.subrange(0, 1).fold_left(
                init,
                |sum: Seq<char>, ss: &'a str| sum + pat + ss@
            ) =~= init + pat + xs[0]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }
            lemma_fold_left_keeps_prefix(
                xs.subrange(1, xs.len() as int),
                init + pat + xs[0]@,
                pat,
                k,
            );
            assert((init + pat + xs[0]@).subrange(0, k) =~= init.subrange(0, k));
        }
    }

    proof fn lemma_fold_left_len_ge_init<'a>(xs: Seq<&'a str>, init: Seq<char>, pat: Seq<char>)
        ensures
            xs.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + pat + ss@).len() >= init.len(),
        decreases xs.len(),
    {
        if xs.len() == 0 {
            assert(xs.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + pat + ss@) =~= init) by {
                reveal_with_fuel(Seq::<_>::fold_left, 2);
            }
        } else {
            xs.lemma_fold_left_split(init, |sum: Seq<char>, ss: &'a str| sum + pat + ss@, 1);
            assert(xs.subrange(0, 1).len() == 1);
            assert(xs.subrange(0, 1)[0] == xs[0]);
            assert(xs.subrange(0, 1).fold_left(
                init,
                |sum: Seq<char>, ss: &'a str| sum + pat + ss@
            ) =~= init + pat + xs[0]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }
            lemma_fold_left_len_ge_init(
                xs.subrange(1, xs.len() as int),
                init + pat + xs[0]@,
                pat,
            );
        }
    }

    proof fn lemma_concat_fold_left_keeps_prefix<'a>(xs: Seq<&'a str>, init: Seq<char>, k: int)
        requires
            0 <= k <= init.len(),
        ensures
            xs.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ss@).subrange(0, k) =~=
                init.subrange(0, k),
        decreases xs.len(),
    {
        if xs.len() == 0 {
            assert(xs.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ss@) =~= init) by {
                reveal_with_fuel(Seq::<_>::fold_left, 2);
            }
        } else {
            xs.lemma_fold_left_split(init, |sum: Seq<char>, ss: &'a str| sum + ss@, 1);
            assert(xs.subrange(0, 1).len() == 1);
            assert(xs.subrange(0, 1)[0] == xs[0]);
            assert(xs.subrange(0, 1).fold_left(
                init,
                |sum: Seq<char>, ss: &'a str| sum + ss@
            ) =~= init + xs[0]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }
            lemma_concat_fold_left_keeps_prefix(
                xs.subrange(1, xs.len() as int),
                init + xs[0]@,
                k,
            );
            assert((init + xs[0]@).subrange(0, k) =~= init.subrange(0, k));
        }
    }

    proof fn lemma_concat_fold_left_len_ge_init<'a>(xs: Seq<&'a str>, init: Seq<char>)
        ensures
            xs.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ss@).len() >= init.len(),
        decreases xs.len(),
    {
        if xs.len() == 0 {
            assert(xs.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ss@) =~= init) by {
                reveal_with_fuel(Seq::<_>::fold_left, 2);
            }
        } else {
            xs.lemma_fold_left_split(init, |sum: Seq<char>, ss: &'a str| sum + ss@, 1);
            assert(xs.subrange(0, 1).len() == 1);
            assert(xs.subrange(0, 1)[0] == xs[0]);
            assert(xs.subrange(0, 1).fold_left(
                init,
                |sum: Seq<char>, ss: &'a str| sum + ss@
            ) =~= init + xs[0]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }
            lemma_concat_fold_left_len_ge_init(
                xs.subrange(1, xs.len() as int),
                init + xs[0]@,
            );
        }
    }

    proof fn lemma_pair_fold_left_keeps_prefix<'a>(xs: Seq<(&'a str, Seq<char>)>, init: Seq<char>, k: int)
        requires
            0 <= k <= init.len(),
        ensures
            xs.fold_left(init, |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1).subrange(0, k) =~=
                init.subrange(0, k),
        decreases xs.len(),
    {
        if xs.len() == 0 {
            assert(xs.fold_left(init, |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1) =~= init) by {
                reveal_with_fuel(Seq::<_>::fold_left, 2);
            }
        } else {
            xs.lemma_fold_left_split(
                init,
                |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1,
                1,
            );
            assert(xs.subrange(0, 1).len() == 1);
            assert(xs.subrange(0, 1)[0] == xs[0]);
            assert(xs.subrange(0, 1).fold_left(
                init,
                |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1
            ) =~= init + xs[0].0@ + xs[0].1) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }
            lemma_pair_fold_left_keeps_prefix(
                xs.subrange(1, xs.len() as int),
                init + xs[0].0@ + xs[0].1,
                k,
            );
            assert((init + xs[0].0@ + xs[0].1).subrange(0, k) =~= init.subrange(0, k));
        }
    }

    proof fn lemma_pair_fold_left_len_ge_init<'a>(xs: Seq<(&'a str, Seq<char>)>, init: Seq<char>)
        ensures
            xs.fold_left(init, |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1).len() >= init.len(),
        decreases xs.len(),
    {
        if xs.len() == 0 {
            assert(xs.fold_left(init, |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1) =~= init) by {
                reveal_with_fuel(Seq::<_>::fold_left, 2);
            }
        } else {
            xs.lemma_fold_left_split(
                init,
                |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1,
                1,
            );
            assert(xs.subrange(0, 1).len() == 1);
            assert(xs.subrange(0, 1)[0] == xs[0]);
            assert(xs.subrange(0, 1).fold_left(
                init,
                |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1
            ) =~= init + xs[0].0@ + xs[0].1) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }
            lemma_pair_fold_left_len_ge_init(
                xs.subrange(1, xs.len() as int),
                init + xs[0].0@ + xs[0].1,
            );
        }
    }

    fn test_char_indices() {
        broadcast use crate::str::group_str_view;
        proof {
            reveal_strlit("ab");
        }

        let s = "ab";
        let mut it = s.char_indices();

        match it.next() {
            Some((i, c)) => {
                assert(i == 0usize);
                assert(c == 'a');
            }
            None => { assert(false); }
        }
        match it.next() {
            Some((i, c)) => {
                assert(i == 1usize);
                assert(c == 'b');
            }
            None => { assert(false); }
        }
        match it.next() {
            Some(_) => { assert(false); }
            None => { }
        }
    }

    fn test_lines() {
        broadcast use crate::str::group_str_view;
        proof {
            reveal_strlit("a\nb");
            reveal_strlit("a");
            reveal_strlit("b");
        }

        let s = "a\nb";
        assert(s@.len() == 3);
        assert(s@[0] == 'a');
        assert(s@[1] == '\n');
        assert(s@[2] == 'b');

        let mut it = s.lines();
        let ghost seq = it@.1;
        let ghost nls = choose |nls: Seq<Seq<char>>| {
            &&& #[trigger] nls.len() == seq.len()
            &&& forall |i: int| #![trigger nls[i]] 0 <= i < nls.len() ==> {
                &&& nls[i] == seq!['\n'] || nls[i] == seq!['\r', '\n'] || (i == nls.len() - 1 && nls[i].len() == 0 )
                &&& nls[i] == seq!['\n'] ==> !seq!['\r'].is_suffix_of(seq[i]@)
            }
            &&& s@ =~= seq.zip_with(nls).fold_left(
                Seq::<char>::empty(), |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
            )
        };
        let ghost pairs = seq.zip_with(nls);

        proof {
            assert(nls.len() == seq.len());
            assert(pairs.len() == seq.len());

            assert_by_contradiction!(seq.len() > 0, {
                assert(seq.len() == 0);
                assert(pairs.len() == 0);
                assert(pairs.fold_left(
                    Seq::<char>::empty(),
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ) =~= Seq::<char>::empty()) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 2);
                }
            });

            assert_by_contradiction!(seq.len() >= 2, {
                assert(seq.len() == 1);
                assert(nls.len() == 1);
                assert(pairs.len() == 1);
                assert(pairs[0] == (seq[0], nls[0]));
                assert(pairs.fold_left(
                    Seq::<char>::empty(),
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ) =~= seq[0]@ + nls[0]) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 3);
                }
                assert(s@ =~= seq[0]@ + nls[0]);

                if nls[0].len() == 0 {
                    assert(seq[0]@.len() == 3);
                    assert(seq[0]@[1] == s@[1]);
                } else if nls[0].len() == 1 {
                    assert(nls[0] == seq!['\n']);
                    assert(seq[0]@.len() == 2);
                    assert((seq[0]@ + nls[0])[1] == s@[1]);
                    assert((seq[0]@ + nls[0])[1] == seq[0]@[1]);
                    assert(seq[0]@[1] == '\n');
                } else {
                    assert(nls[0].len() == 2);
                    assert(nls[0] == seq!['\r', '\n']);
                    assert(seq[0]@.len() == 1);
                    assert((seq[0]@ + nls[0])[1] == s@[1]);
                    assert((seq[0]@ + nls[0])[1] == nls[0][0]);
                    assert(nls[0][0] == '\r');
                }
            });

            pairs.lemma_fold_left_split(
                Seq::<char>::empty(),
                |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1,
                1,
            );
            assert(pairs.subrange(0, 1).len() == 1);
            assert(pairs.subrange(0, 1)[0] == (seq[0], nls[0]));
            assert(pairs.subrange(0, 1).fold_left(
                Seq::<char>::empty(),
                |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
            ) =~= seq[0]@ + nls[0]) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }

            let ghost tail = pairs.subrange(1, pairs.len() as int);
            assert(tail.fold_left(
                seq[0]@ + nls[0],
                |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
            ) =~= s@);
            assert(nls[0] == seq!['\n'] || nls[0] == seq!['\r', '\n']);

            assert_by_contradiction!(seq[0]@.len() > 0, {
                assert(seq[0]@.len() == 0);
                lemma_pair_fold_left_keeps_prefix(tail, nls[0], 1);
                assert(s@.subrange(0, 1) =~=
                    tail.fold_left(nls[0], |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1).subrange(0, 1));
                assert(tail.fold_left(
                    nls[0],
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ).subrange(0, 1) =~= nls[0].subrange(0, 1));
                assert(s@.subrange(0, 1) =~= nls[0].subrange(0, 1));
                assert(s@.subrange(0, 1)[0] == s@[0]);
                assert(nls[0].subrange(0, 1)[0] == nls[0][0]);
                assert(nls[0][0] == '\n' || nls[0][0] == '\r');
            });

            assert_by_contradiction!(seq[0]@.len() <= 1, {
                assert(2 <= seq[0]@.len() + nls[0].len());
                lemma_pair_fold_left_keeps_prefix(tail, seq[0]@ + nls[0], 2);
                assert(s@.subrange(0, 2) =~=
                    tail.fold_left(seq[0]@ + nls[0], |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1).subrange(0, 2));
                assert(tail.fold_left(
                    seq[0]@ + nls[0],
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ).subrange(0, 2) =~= (seq[0]@ + nls[0]).subrange(0, 2));
                assert(s@.subrange(0, 2) =~= (seq[0]@ + nls[0]).subrange(0, 2));
                assert(s@.subrange(0, 2)[1] == s@[1]);
                assert((seq[0]@ + nls[0]).subrange(0, 2)[1] == (seq[0]@ + nls[0])[1]);
                assert((seq[0]@ + nls[0])[1] == seq[0]@[1]);
            });

            assert(seq[0]@.len() == 1);
            lemma_pair_fold_left_keeps_prefix(tail, seq[0]@ + nls[0], 1);
            assert(s@.subrange(0, 1) =~=
                tail.fold_left(seq[0]@ + nls[0], |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1).subrange(0, 1));
            assert(tail.fold_left(
                seq[0]@ + nls[0],
                |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
            ).subrange(0, 1) =~= (seq[0]@ + nls[0]).subrange(0, 1));
            assert(s@.subrange(0, 1) =~= (seq[0]@ + nls[0]).subrange(0, 1));
            assert((seq[0]@ + nls[0]).subrange(0, 1) =~= seq[0]@);
            assert(seq[0]@ =~= "a"@);
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[0]);
                assert(part@ =~= "a"@);
                assert(it@.0 == 1);
            }
            None => { assert(false); }
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[1]);
                assert(it@.0 == 2);
            }
            None => { assert(false); }
        }

        proof {
            assert_by_contradiction!(seq.len() == 2, {
                assert(seq.len() >= 3);
                pairs.lemma_fold_left_split(
                    Seq::<char>::empty(),
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1,
                    3,
                );
                assert(pairs.subrange(0, 3).len() == 3);
                assert(pairs.subrange(0, 3)[0] == (seq[0], nls[0]));
                assert(pairs.subrange(0, 3)[1] == (seq[1], nls[1]));
                assert(pairs.subrange(0, 3)[2] == (seq[2], nls[2]));
                assert(pairs.subrange(0, 3).fold_left(
                    Seq::<char>::empty(),
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ) =~= seq[0]@ + nls[0] + seq[1]@ + nls[1] + seq[2]@ + nls[2]) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 5);
                }
                let ghost init3 = seq[0]@ + nls[0] + seq[1]@ + nls[1] + seq[2]@ + nls[2];
                let ghost tail3 = pairs.subrange(3, pairs.len() as int);
                assert(tail3.fold_left(
                    init3,
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ) =~= pairs.fold_left(
                    Seq::<char>::empty(),
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ));
                assert(tail3.fold_left(
                    init3,
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ) =~= s@);
                assert(seq[0]@.len() == 1);
                assert(nls[0].len() > 0);
                assert(nls[1].len() > 0);
                assert(seq[2]@.len() + nls[2].len() > 0) by {
                    if seq.len() == 3 {
                        assert(seq[2] == seq.last());
                        assert(seq[2]@.len() > 0);
                    } else {
                        assert(2 < nls.len() - 1);
                        assert(nls[2] == seq!['\n'] || nls[2] == seq!['\r', '\n']);
                    }
                }
                assert(init3.len() ==
                    seq[0]@.len() + nls[0].len() + seq[1]@.len() + nls[1].len() + seq[2]@.len() + nls[2].len());
                assert(init3.len() > 3);
                lemma_pair_fold_left_len_ge_init(tail3, init3);
                assert(tail3.fold_left(
                    init3,
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ).len() >= init3.len());
                assert(s@.len() == 3);
            });
        }

        match it.next() {
            Some(_) => { assert(false); }
            None => {
                assert(it@.0 == seq.len());
                assert(it@.1 == seq);
                assert(seq.len() == 2);
            }
        }

        proof {
            assert(nls.len() == 2);
            assert(pairs.len() == 2);
            assert(seq.last() == seq[1]);
            assert(seq[1]@.len() > 0);
            assert(pairs.fold_left(
                Seq::<char>::empty(),
                |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
            ) =~= seq[0]@ + nls[0] + seq[1]@ + nls[1]) by {
                reveal_with_fuel(Seq::<_>::fold_left, 4);
            }
            assert(s@ =~= "a"@ + nls[0] + seq[1]@ + nls[1]);
            assert(nls[0] == seq!['\n'] || nls[0] == seq!['\r', '\n']);
            assert(nls[1] == seq!['\n'] || nls[1] == seq!['\r', '\n'] || nls[1].len() == 0);
            assert(nls[0].len() > 0);
            assert(seq[1]@.len() == 1);
            assert(nls[0].len() == 1);
            assert(nls[1].len() == 0);
            assert(nls[0] == seq!['\n']);
            assert(seq[1]@[0] == ("a"@ + nls[0] + seq[1]@ + nls[1])[2]);
            assert(("a"@ + nls[0] + seq[1]@ + nls[1])[2] == s@[2]);
            assert(seq[1]@[0] == 'b');
            assert(seq[1]@ =~= "b"@);
        }

        assert(seq[1]@ =~= "b"@);
    }

    fn test_split_ascii_whitespace() {
        broadcast use crate::str::group_str_view;
        proof {
            reveal_strlit(" a");
            reveal_strlit("a");
        }

        let s = " a";
        assert(s@.len() == 2);
        assert(s@[0] == ' ');
        assert(s@[1] == 'a');

        let mut it = s.split_ascii_whitespace();
        let ghost seq = it@.1;
        let ghost ws = choose |ws: Seq<Seq<char>>| {
            &&& #[trigger] ws.len() == seq.len() + 1
            &&& forall |i: int| #![trigger ws[i]] 0 <= i < ws.len() ==> {
                &&& 1 <= i < ws.len() - 1 ==> ws[i].len() > 0
                &&& forall |j: int| #![trigger ws[i][j]] 0 <= j < ws[i].len() ==>
                    ws[i][j].is_ascii_whitespace()
            }
            &&& s@ =~= seq.zip_with(ws.drop_first()).fold_left(
                ws.first(), |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
            )
        };
        let ghost pairs = seq.zip_with(ws.drop_first());

        proof {
            assert(ws.len() == seq.len() + 1);
            assert(pairs.len() == seq.len());

            assert_by_contradiction!(seq.len() > 0, {
                assert(seq.len() == 0);
                assert(ws.len() == 1);
                assert(pairs.len() == 0);
                assert(pairs.fold_left(
                    ws.first(),
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ) =~= ws.first()) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 2);
                }
                assert(s@ =~= ws[0]);
                assert(ws[0].len() == 2);
                assert(ws[0][1] == s@[1]);
                assert(ws[0][1].is_ascii_whitespace());
                assert('a' == s@[1]);
                assert(!'a'.is_ascii_whitespace());
            });

            assert_by_contradiction!(seq.len() == 1, {
                assert(seq.len() >= 2);
                assert(ws.len() >= 3);
                assert(seq[0]@.len() > 0);
                assert(seq[1]@.len() > 0);
                assert(ws[1].len() > 0);

                pairs.lemma_fold_left_split(
                    ws.first(),
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1,
                    2,
                );
                assert(pairs.subrange(0, 2).len() == 2);
                assert(pairs.subrange(0, 2)[0] == (seq[0], ws[1]));
                assert(pairs.subrange(0, 2)[1] == (seq[1], ws[2]));
                assert(pairs.subrange(0, 2).fold_left(
                    ws.first(),
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ) =~= ws[0] + seq[0]@ + ws[1] + seq[1]@ + ws[2]) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 4);
                }

                let ghost init2 = ws[0] + seq[0]@ + ws[1] + seq[1]@ + ws[2];
                let ghost tail2 = pairs.subrange(2, pairs.len() as int);
                assert(tail2.fold_left(
                    init2,
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ) =~= pairs.fold_left(
                    ws.first(),
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ));
                assert(tail2.fold_left(
                    init2,
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ) =~= s@);
                assert(init2.len() ==
                    ws[0].len() + seq[0]@.len() + ws[1].len() + seq[1]@.len() + ws[2].len());
                assert(init2.len() > 2);
                lemma_pair_fold_left_len_ge_init(tail2, init2);
                assert(tail2.fold_left(
                    init2,
                    |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
                ).len() >= init2.len());
                assert(s@.len() == 2);
            });

            assert(ws.len() == 2);
            assert(pairs.len() == 1);
            assert(pairs[0] == (seq[0], ws[1]));
            assert(pairs.fold_left(
                ws.first(),
                |sum: Seq<char>, p: (&str, Seq<char>)| sum + p.0@ + p.1
            ) =~= ws[0] + seq[0]@ + ws[1]) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }
            assert(s@ =~= ws[0] + seq[0]@ + ws[1]);

            assert_by_contradiction!(ws[0].len() > 0, {
                assert(ws[0].len() == 0);
                assert((ws[0] + seq[0]@ + ws[1])[0] == seq[0]@[0]);
                assert(s@[0] == seq[0]@[0]);
                assert(seq[0]@[0].is_ascii_whitespace());
            });
            assert(ws[0].len() > 0);

            assert_by_contradiction!(ws[0].len() <= 1, {
                assert(ws[0].len() > 1);
                assert(ws[0].len() + seq[0]@.len() + ws[1].len() > 2);
            });
            assert(ws[0].len() == 1);

            assert_by_contradiction!(seq[0]@.len() <= 1, {
                assert(seq[0]@.len() > 1);
                assert(ws[0].len() + seq[0]@.len() + ws[1].len() > 2);
            });
            assert(seq[0]@.len() == 1);

            assert_by_contradiction!(ws[1].len() == 0, {
                assert(ws[1].len() > 0);
                assert(ws[0].len() + seq[0]@.len() + ws[1].len() > 2);
            });
            assert(ws[1].len() == 0);

            assert((ws[0] + seq[0]@ + ws[1])[1] == seq[0]@[0]);
            assert(s@[1] == seq[0]@[0]);
            assert(seq[0]@[0] == 'a');
            assert(seq[0]@ =~= "a"@);
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[0]);
                assert(part@ =~= "a"@);
                assert(it@.0 == 1);
            }
            None => { assert(false); }
        }

        match it.next() {
            Some(_) => { assert(false); }
            None => {
                assert(it@.0 == seq.len());
                assert(it@.1 == seq);
                assert(seq.len() == 1);
            }
        }
    }

    fn test_split_inclusive() {
        broadcast use crate::str::group_str_view;
        proof {
            reveal_strlit("a,b");
            reveal_strlit(",");
            reveal_strlit("a,");
            reveal_strlit("b");
        }

        let s = "a,b";
        assert(s@.len() == 3);
        assert(","@.len() == 1);
        assert(s@[0] == 'a');
        assert(s@[1] == ',');
        assert(s@[2] == 'b');
        assert("a,b"@.subrange(1, 2) =~= ","@) by {
            assert("a,b"@[1] == ',');
            assert(","@[0] == ',');
        }

        let mut it = str_split_inclusive("a,b", ",");
        let ghost seq = it@.1;

        proof {
            assert_by_contradiction!(seq.len() > 0, {
                assert(seq.len() == 0);
                assert(seq.fold_left(
                    Seq::<char>::empty(),
                    |sum: Seq<char>, ss: &str| sum + ss@
                ) =~= Seq::<char>::empty()) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 2);
                }
            });

            assert_by_contradiction!(seq.len() >= 2, {
                assert(seq.len() == 1);
                assert(seq.fold_left(
                    Seq::<char>::empty(),
                    |sum: Seq<char>, ss: &str| sum + ss@
                ) =~= seq[0]@) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 3);
                }
                assert(s@ =~= seq[0]@);
                assert(seq[0]@.subrange(1, 1 + ","@.len() as int) =~= ","@);
                assert(!(seq[0]@.subrange(1, 1 + ","@.len() as int) =~= ","@)) by {
                    assert(0 <= 1 < seq[0]@.len() - ","@.len());
                }
            });

            seq.lemma_fold_left_split(
                Seq::<char>::empty(),
                |sum: Seq<char>, ss: &str| sum + ss@,
                1,
            );
            assert(seq.subrange(0, 1).len() == 1);
            assert(seq.subrange(0, 1)[0] == seq[0]);
            assert(seq.subrange(0, 1).fold_left(
                Seq::<char>::empty(),
                |sum: Seq<char>, ss: &str| sum + ss@
            ) =~= seq[0]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }

            let ghost tail = seq.subrange(1, seq.len() as int);
            assert(tail.fold_left(
                seq[0]@,
                |sum: Seq<char>, ss: &str| sum + ss@
            ) =~= seq.fold_left(
                Seq::<char>::empty(),
                |sum: Seq<char>, ss: &str| sum + ss@
            ));
            assert(tail.fold_left(
                seq[0]@,
                |sum: Seq<char>, ss: &str| sum + ss@
            ) =~= s@);
            assert(","@.is_suffix_of(seq[0]@));

            assert_by_contradiction!(seq[0]@.len() > 1, {
                assert(seq[0]@.len() <= 1);
                lemma_concat_fold_left_keeps_prefix(tail, seq[0]@, 1);
                assert("a,b"@.subrange(0, 1) =~=
                    tail.fold_left(seq[0]@, |sum: Seq<char>, ss: &str| sum + ss@).subrange(0, 1));
                assert(tail.fold_left(
                    seq[0]@,
                    |sum: Seq<char>, ss: &str| sum + ss@
                ).subrange(0, 1) =~= seq[0]@.subrange(0, 1));
                assert("a,b"@.subrange(0, 1) =~= seq[0]@.subrange(0, 1));
                assert("a,b"@.subrange(0, 1)[0] == "a,b"@[0]);
                assert(seq[0]@.subrange(0, 1)[0] == seq[0]@[0]);
                assert(seq[0]@[0] == ',');
            });

            assert_by_contradiction!(seq[0]@.len() <= 2, {
                assert(seq[0]@.len() > 2);
                lemma_concat_fold_left_keeps_prefix(tail, seq[0]@, 2);
                assert("a,b"@.subrange(0, 2) =~=
                    tail.fold_left(seq[0]@, |sum: Seq<char>, ss: &str| sum + ss@).subrange(0, 2));
                assert(tail.fold_left(
                    seq[0]@,
                    |sum: Seq<char>, ss: &str| sum + ss@
                ).subrange(0, 2) =~= seq[0]@.subrange(0, 2));
                assert("a,b"@.subrange(0, 2) =~= seq[0]@.subrange(0, 2));
                assert("a,b"@.subrange(0, 2)[1] == "a,b"@[1]);
                assert(seq[0]@.subrange(0, 2)[1] == seq[0]@[1]);
                assert(seq[0]@.subrange(1, 1 + ","@.len() as int) =~= ","@) by {
                    assert(seq[0]@[1] == ',');
                    assert(","@[0] == ',');
                }
                assert(!(seq[0]@.subrange(1, 1 + ","@.len() as int) =~= ","@)) by {
                    assert(0 <= 1 < seq[0]@.len() - ","@.len());
                }
            });

            assert(seq[0]@.len() == 2);
            lemma_concat_fold_left_keeps_prefix(tail, seq[0]@, 2);
            assert("a,b"@.subrange(0, 2) =~=
                tail.fold_left(seq[0]@, |sum: Seq<char>, ss: &str| sum + ss@).subrange(0, 2));
            assert(tail.fold_left(
                seq[0]@,
                |sum: Seq<char>, ss: &str| sum + ss@
            ).subrange(0, 2) =~= seq[0]@.subrange(0, 2));
            assert("a,b"@.subrange(0, 2) =~= seq[0]@.subrange(0, 2));
            assert(seq[0]@ =~= "a,"@);

            assert_by_contradiction!(seq.len() == 2, {
                assert(seq.len() >= 3);

                seq.lemma_fold_left_split(
                    Seq::<char>::empty(),
                    |sum: Seq<char>, ss: &str| sum + ss@,
                    2,
                );
                assert(seq.subrange(0, 2).len() == 2);
                assert(seq.subrange(0, 2)[0] == seq[0]);
                assert(seq.subrange(0, 2)[1] == seq[1]);
                assert(seq.subrange(0, 2).fold_left(
                    Seq::<char>::empty(),
                    |sum: Seq<char>, ss: &str| sum + ss@
                ) =~= seq[0]@ + seq[1]@) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 4);
                }

                let ghost tail2 = seq.subrange(2, seq.len() as int);
                let ghost init2 = seq[0]@ + seq[1]@;
                assert(tail2.fold_left(
                    init2,
                    |sum: Seq<char>, ss: &str| sum + ss@
                ) =~= seq.fold_left(
                    Seq::<char>::empty(),
                    |sum: Seq<char>, ss: &str| sum + ss@
                ));
                assert(tail2.fold_left(
                    init2,
                    |sum: Seq<char>, ss: &str| sum + ss@
                ) =~= s@);
                assert(","@.is_suffix_of(seq[1]@));

                assert_by_contradiction!(seq[1]@.len() > 1, {
                    assert(seq[1]@.len() <= 1);
                    lemma_concat_fold_left_keeps_prefix(tail2, init2, 3);
                    assert("a,b"@.subrange(0, 3) =~=
                        tail2.fold_left(init2, |sum: Seq<char>, ss: &str| sum + ss@).subrange(0, 3));
                    assert(tail2.fold_left(
                        init2,
                        |sum: Seq<char>, ss: &str| sum + ss@
                    ).subrange(0, 3) =~= init2.subrange(0, 3));
                    assert("a,b"@.subrange(0, 3) =~= init2.subrange(0, 3));
                    assert("a,b"@.subrange(0, 3)[2] == "a,b"@[2]);
                    assert(init2.subrange(0, 3)[2] == init2[2]);
                    assert(init2[2] == ',');
                });

                assert(init2.len() == seq[0]@.len() + seq[1]@.len());
                assert(seq[0]@.len() == 2);
                assert(init2.len() > 3);
                lemma_concat_fold_left_len_ge_init(tail2, init2);
                assert(tail2.fold_left(
                    init2,
                    |sum: Seq<char>, ss: &str| sum + ss@
                ).len() >= init2.len());
                assert("a,b"@.len() == 3);
            });

            assert(seq.len() == 2);
            assert(seq.fold_left(
                Seq::<char>::empty(),
                |sum: Seq<char>, ss: &str| sum + ss@
            ) =~= seq[0]@ + seq[1]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 4);
            }
            assert("a,b"@ =~= seq[0]@ + seq[1]@);
            assert(seq[1]@ =~= "b"@) by {
                assert("a,b"@.subrange(2, 3) =~= "b"@);
            }
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[0]);
                assert(part@ =~= "a,"@);
                assert(it@.0 == 1);
            }
            None => { assert(false); }
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[1]);
                assert(part@ =~= "b"@);
                assert(it@.0 == 2);
            }
            None => { assert(false); }
        }

        match it.next() {
            Some(_) => { assert(false); }
            None => {
                assert(it@.0 == seq.len());
                assert(it@.1 == seq);
                assert(seq.len() == 2);
            }
        }
    }

    fn test_match_indices() {
        broadcast use crate::str::group_str_view;
        proof {
            reveal_strlit("ababa");
            reveal_strlit("aba");
        }

        let s = "ababa";
        let mut it = str_match_indices(s, "aba");
        let ghost seq = it@.1;
        let ghost plen = "aba"@.as_bytes().len() as int;
        let ghost indices = seq.map(|_i: int, p: (usize, &str)| p.0 as int);
        let ghost ends = indices.map(|_i: int, idx: int| idx + plen);
        let ghost mismatches =
            (seq![0int] + ends).zip_with(indices + seq![(s@.as_bytes().len() - plen + 1) as int]);

        assert("ababa"@.as_bytes().len() == 5);
        assert("aba"@.as_bytes().len() == 3);
        assert(s@.as_bytes().subrange(0, 0 + plen) =~= "aba"@.as_bytes());
        assert(s@.as_bytes().subrange(2, 2 + plen) =~= "aba"@.as_bytes());

        proof {
            assert_by_contradiction!(seq.len() > 0, {
                assert(seq.len() == 0);
                assert(indices.len() == 0);
                assert(ends.len() == 0);
                assert((seq![0int] + ends).len() == 1);
                assert((indices + seq![(s@.as_bytes().len() - plen + 1) as int]).len() == 1);
                assert(mismatches.len() == 1);
                assert((seq![0int] + ends)[0] == 0);
                assert((indices + seq![(s@.as_bytes().len() - plen + 1) as int])[0] == 3);
                assert(mismatches[0].0 == 0);
                assert(mismatches[0].1 == 3);
                assert(!(s@.as_bytes().subrange(0, 0 + plen) =~= "aba"@.as_bytes()));
            });

            assert((seq![0int] + ends)[0] == 0);
            assert((indices + seq![(s@.as_bytes().len() - plen + 1) as int])[0] == indices[0]);
            assert(mismatches[0].0 == 0);
            assert(mismatches[0].1 == indices[0]);
            assert_by_contradiction!(indices[0] == 0, {
                assert(0 < indices[0]);
                assert(mismatches[0].0 <= 0 < mismatches[0].1);
                assert(!(s@.as_bytes().subrange(0, 0 + plen) =~= "aba"@.as_bytes()));
            });
            assert(seq[0].0 == 0usize);
            assert(seq[0].1@ =~= "aba"@);

            assert_by_contradiction!(seq.len() == 1, {
                assert(seq.len() >= 2);
                assert(indices[0] + plen <= indices[1]);
                assert(indices[0] == 0);
                assert(3 <= indices[1]);
                assert(indices[1] + plen <= s@.as_bytes().len());
                assert(indices[1] <= 2);
            });
        }

        match it.next() {
            Some((idx, part)) => {
                assert((idx, part) == seq[0]);
                assert(idx == 0usize);
                assert(part@ =~= "aba"@);
                assert(it@.0 == 1);
            }
            None => { assert(false); }
        }

        match it.next() {
            Some(_) => { assert(false); }
            None => {
                assert(it@.0 == seq.len());
                assert(it@.1 == seq);
                assert(seq.len() == 1);
            }
        }
    }

    fn test_split_once() {
        broadcast use crate::str::group_str_view;
        proof {
            reveal_strlit("aa,b,c");
            reveal_strlit(",");
            reveal_strlit(".");
            reveal_strlit("aa");
            reveal_strlit("b,c");
        }

        let s = "aa,b,c";
        let result = str_split_once(s, ",");
        assert(2 + ","@.len() as int == 3);
        assert(s@.subrange(2, 3) =~= ","@) by {
            assert(s@[2] == ',');
            assert(","@[0] == ',');
        }
        assert(result.is_some());

        match result {
            Some((head, tail)) => {
                assert(s@ =~= head@ + ","@ + tail@);
                assert(head@ =~= "aa"@) by {
                    assert_by_contradiction!(head@.len() <= 2, {
                        assert(head@.subrange(2, 3) =~= s@.subrange(2, 3));
                    });
                    assert_by_contradiction!(head@.len() > 1, {
                        let i = head@.len() as int;
                        assert(s@[i] != ',') by { assert(0 <= i <= 1); };
                    });
                    assert(head@.len() == 2);
                    assert(s@.subrange(0, 2) =~= head@.subrange(0, 2));
                }
                assert(tail@ =~= "b,c"@) by {
                    assert(s@.subrange(3, 6) =~= "b,c"@);
                }
            }
            None => { assert(false); }
        }

        let none = str_split_once(s, ".");
        assert(forall |i: int| 0 <= i < s@.len() ==> #[trigger] s@[i] != '.');

        proof {
            assert_by_contradiction!(none.is_none(), {
                assert(none.is_some());
                match none {
                    Some((h, t)) => {
                        let i = h@.len() as int;
                        assert(s@ =~= h@ + "."@ + t@);
                        assert(s@[i] == '.');
                    }
                    None => { assert(false) }
                }
            });
        }

        assert(none.is_none());
    }

    fn test_split() {
        broadcast use crate::str::group_str_view;
        proof {
            reveal_strlit("aa,b");
            reveal_strlit(",");
            reveal_strlit("aa");
            reveal_strlit("aa,,");
            reveal_strlit("b");
        }

        assert("aa,b"@.len() == 4);
        assert(","@.len() == 1);
        assert(2 + ","@.len() == 3);
        assert("aa,b"@.subrange(2, 3) =~= ","@) by {
            assert("aa,b"@[2] == ',');
            assert(","@[0] == ',');
        }

        let mut it = str_split("aa,b", ",");
        let ghost seq = it@.1;

        proof {
            assert_by_contradiction!(seq.len() >= 2, {
                assert(seq.len() == 1);
                assert(seq.last()@.subrange(2, 3) =~= ","@);
            });

            assert(seq.drop_first().subrange(0, 1).fold_left(
                seq.first()@,
                |sum: Seq<char>, ss: &str| sum + ","@ + ss@
            ) =~= seq[0]@ + ","@ + seq[1]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }

            let ghost tail = seq.drop_first().subrange(1, seq.drop_first().len() as int);
            let ghost init = seq[0]@ + ","@ + seq[1]@;

            assert_by_contradiction!(seq[0]@.len() <= 2, {
                lemma_fold_left_keeps_prefix(tail, init, ","@, 3);
                assert(init.subrange(0, 3)[2] == init[2]);
                assert(init.subrange(2, 3) =~= ","@) by {
                    assert(init[2] == ',');
                    assert(","@[0] == ',');
                }
                assert(init.subrange(2, 3) =~= (seq[0]@ + ","@).subrange(2, 3));
                assert(!((seq[0]@ + ","@).subrange(2, 3) =~= ","@)) by {
                    assert(seq[0]@.len() > 2);
                }
            });

            assert_by_contradiction!(seq[0]@.len() > 1, {
                let i = seq[0]@.len() as int;
                lemma_fold_left_keeps_prefix(tail, init, ","@, i + 1);
                assert(init.subrange(0, i + 1)[i] == init[i]);
                assert(init[i] == "aa,b"@[i]);
                assert("aa,b"@[i] != ',') by {
                    assert(0 <= i <= 1);
                }
            });
            assert(seq[0]@.len() == 2);

            lemma_fold_left_keeps_prefix(tail, init, ","@, 2);
            assert(init.subrange(0, 2) =~= seq[0]@);
            assert(seq[0]@ =~= "aa"@);

            assert_by_contradiction!(seq[1]@.len() > 0, {
                assert(tail.subrange(0, 1).fold_left(
                    init,
                    |sum: Seq<char>, ss: &str| sum + ","@ + ss@
                ) =~= init + ","@ + tail[0]@) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 3);
                }
                let ghost init = init + ","@ + tail[0]@;
                let ghost tail = tail.subrange(1, tail.len() as int);
                lemma_fold_left_keeps_prefix(tail, init, ","@, 4);
                assert("aa,b"@.subrange(0, 4)[3] == "aa,,"@[3]);
            });

            lemma_fold_left_keeps_prefix(tail, init, ","@, 4);
            assert("aa,b"@.subrange(0, 4) =~=
                tail.fold_left(init, |sum: Seq<char>, ss: &str| sum + ","@ + ss@).subrange(0, 4));
            assert(tail.fold_left(
                init,
                |sum: Seq<char>, ss: &str| sum + ","@ + ss@
            ).subrange(0, 4) =~= init.subrange(0, 4));
            assert(init.subrange(0, 4) =~= "aa,b"@.subrange(0, 4));
            assert(init.subrange(0, 4)[3] == init[3]);
            assert(init[3] == seq[1]@[0]);
            assert(seq[1]@[0] == 'b');
            assert(seq[1]@.subrange(0, 1) =~= "b"@);

            assert_by_contradiction!(seq[1]@.len() <= 1, {
                lemma_fold_left_len_ge_init(tail, init, ","@);
            });

            assert_by_contradiction!(seq.len() == 2, {
                seq.drop_first().lemma_fold_left_split(
                    seq.first()@,
                    |sum: Seq<char>, ss: &str| sum + ","@ + ss@,
                    2,
                );
                assert(seq.drop_first().subrange(0, 2).fold_left(
                    seq.first()@,
                    |sum: Seq<char>, ss: &str| sum + ","@ + ss@
                ) =~= seq[0]@ + ","@ + seq[1]@ + ","@ + seq[2]@) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 4);
                }
                let ghost init2 = seq[0]@ + ","@ + seq[1]@ + ","@ + seq[2]@;
                let ghost tail2 = seq.drop_first().subrange(2, seq.drop_first().len() as int);
                lemma_fold_left_len_ge_init(tail2, init2, ","@);
            });
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[0]);
                assert(part@ =~= "aa"@);
                assert(it@.0 == 1);
            }
            None => { assert(false); }
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[1]);
                assert(part@ =~= "b"@);
                assert(it@.0 == 2);
            }
            None => { assert(false); }
        }

        match it.next() {
            Some(_) => { assert(false); }
            None => {
                assert(it@.0 == seq.len());
                assert(it@.1 == seq);
                assert(seq.len() == 2);
            }
        }
    }

    fn test_splitn() {
        broadcast use crate::str::group_str_view;
        proof {
            reveal_strlit("a,b,c");
            reveal_strlit(",");
            reveal_strlit("a");
            reveal_strlit("b,c");
        }

        assert("a,b,c"@.len() == 5);
        assert(","@.len() == 1);
        assert(1 + ","@.len() == 2);
        assert("a,b,c"@.subrange(1, 2) =~= ","@) by {
            assert("a,b,c"@[1] == ',');
            assert(","@[0] == ',');
        }

        let mut it = str_splitn("a,b,c", 2usize, ",");
        let ghost seq = it@.1;

        proof {
            assert_by_contradiction!(seq.len() == 2, {   
                assert(seq.last()@ =~= "a,b,c"@);
                assert(seq.last()@.subrange(1, 2) =~= ","@);
                assert(!(seq.last()@.subrange(1, 2) =~= ","@)) by { assert(seq.len() < 2); }
            });

            assert(seq.drop_first().fold_left(
                seq.first()@, |sum: Seq<char>, ss: &str| sum + ","@ + ss@
            ) =~= seq.first()@ + ","@ + seq[1]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }
            assert("a,b,c"@ =~= seq[0]@ + ","@ + seq[1]@);

            assert(seq[0]@ =~= "a"@) by {
                assert_by_contradiction!(seq[0]@.len() <= 1, {
                    assert((seq[0]@ + ","@).subrange(1, 2) =~= "a,b,c"@.subrange(1, 2));
                });
                assert_by_contradiction!(seq[0]@.len() > 0, {
                    assert((seq[0]@ + ","@)[0] == ',');
                    assert("a,b,c"@[0] == 'a');
                });
                assert(seq[0]@.len() == 1);
                assert(seq[0]@[0] == "a,b,c"@[0]);
                assert(seq[0]@[0] == 'a');
            }

            assert(seq[1]@ =~= "b,c"@) by {
                assert("a,b,c"@.subrange(2, 5) =~= "b,c"@);
            }
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[0]);
                assert(part@ =~= "a"@);
                assert(it@.0 == 1);
            }
            None => { assert(false); }
        }
        match it.next() {
            Some(part) => {
                assert(part == seq[1]);
                assert(part@ =~= "b,c"@);
                assert(it@.0 == 2);
            }
            None => { assert(false); }
        }
        match it.next() {
            Some(_) => { assert(false); }
            None => {
                assert(it@.0 == seq.len());
                assert(it@.1 == seq);
            }
        }
    }

    proof fn lemma_split_terminator_singleton_when_joined_is_a<'a>(
        seq: Seq<&'a str>,
        joined: Seq<char>,
    )
        requires
            seq.len() > 0,
            joined =~= seq.drop_first().fold_left(
                seq.first()@,
                |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
            ),
            joined.len() == 1,
            joined[0] == 'a',
        ensures
            seq.len() == 1,
            seq[0]@ =~= "a"@,
    {
        reveal_strlit("a");
        reveal_strlit(",");

        assert_by_contradiction!(seq[0]@.len() > 0, {
            assert(seq[0]@.len() == 0);
            if seq.len() == 1 {
                assert(seq[0] == seq.first());
                assert(seq[0] == seq.last());
                assert(seq.drop_first().len() == 0);
                assert(joined =~= seq[0]@) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 2);
                }
                assert(joined.len() == 0);
            } else {
                assert(seq.len() >= 2);
                seq.drop_first().lemma_fold_left_split(
                    seq.first()@,
                    |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@,
                    1,
                );
                assert(seq.drop_first().subrange(0, 1).fold_left(
                    seq.first()@,
                    |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
                ) =~= seq[0]@ + ","@ + seq[1]@) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 3);
                }
                let ghost tail = seq.drop_first().subrange(1, seq.drop_first().len() as int);
                assert(tail.fold_left(
                    seq[0]@ + ","@ + seq[1]@,
                    |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
                ) =~= joined);
                lemma_fold_left_keeps_prefix(tail, seq[0]@ + ","@ + seq[1]@, ","@, 1);
                assert(joined.subrange(0, 1) =~= (seq[0]@ + ","@ + seq[1]@).subrange(0, 1));
                assert((seq[0]@ + ","@ + seq[1]@).subrange(0, 1)[0] == (seq[0]@ + ","@ + seq[1]@)[0]);
                assert((seq[0]@ + ","@ + seq[1]@)[0] == ',');
                assert(joined[0] == ',');
                assert(false);
            }
        });

        assert_by_contradiction!(seq[0]@.len() <= 1, {
            assert(seq[0]@.len() > 1);
            if seq.len() == 1 {
                assert(seq[0] == seq.first());
                assert(seq[0] == seq.last());
                assert(seq.drop_first().len() == 0);
                assert(joined =~= seq[0]@) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 2);
                }
                assert(joined.len() == seq[0]@.len());
                assert(false);
            } else {
                assert(seq.len() >= 2);
                seq.drop_first().lemma_fold_left_split(
                    seq.first()@,
                    |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@,
                    1,
                );
                assert(seq.drop_first().subrange(0, 1).fold_left(
                    seq.first()@,
                    |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
                ) =~= seq[0]@ + ","@ + seq[1]@) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 3);
                }
                let ghost tail = seq.drop_first().subrange(1, seq.drop_first().len() as int);
                let ghost init = seq[0]@ + ","@ + seq[1]@;
                assert(tail.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@) =~= joined);
                lemma_fold_left_len_ge_init(tail, init, ","@);
                assert(joined.len() >= init.len());
                assert(init.len() == seq[0]@.len() + ","@.len() + seq[1]@.len());
                assert(","@.len() == 1);
                assert(init.len() > 1);
                assert(false);
            }
        });

        assert(seq[0]@.len() == 1);
        if seq.len() == 1 {
            assert(seq[0] == seq.first());
            assert(seq[0] == seq.last());
            assert(seq.drop_first().len() == 0);
            assert(joined =~= seq[0]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 2);
            }
            assert(seq[0]@[0] == joined[0]);
        } else {
            assert(seq.len() >= 2);
            seq.drop_first().lemma_fold_left_split(
                seq.first()@,
                |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@,
                1,
            );
            assert(seq.drop_first().subrange(0, 1).fold_left(
                seq.first()@,
                |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
            ) =~= seq[0]@ + ","@ + seq[1]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }
            let ghost tail = seq.drop_first().subrange(1, seq.drop_first().len() as int);
            assert(tail.fold_left(
                seq[0]@ + ","@ + seq[1]@,
                |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
            ) =~= joined);
            lemma_fold_left_keeps_prefix(tail, seq[0]@ + ","@ + seq[1]@, ","@, 1);
            assert(joined.subrange(0, 1) =~= (seq[0]@ + ","@ + seq[1]@).subrange(0, 1));
            assert((seq[0]@ + ","@ + seq[1]@).subrange(0, 1)[0] ==
                (seq[0]@ + ","@ + seq[1]@)[0]);
            assert(seq[0]@.subrange(0, 1)[0] == seq[0]@[0]);
            assert((seq[0]@ + ","@ + seq[1]@)[0] == seq[0]@[0]);
        }
        assert(seq[0]@[0] == 'a');
        assert(seq[0]@ =~= "a"@);

        assert_by_contradiction!(seq.len() == 1, {
            assert(seq.len() >= 2);
            seq.drop_first().lemma_fold_left_split(
                seq.first()@,
                |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@,
                1,
            );
            assert(seq.drop_first().subrange(0, 1).fold_left(
                seq.first()@,
                |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
            ) =~= seq[0]@ + ","@ + seq[1]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }
            let ghost tail = seq.drop_first().subrange(1, seq.drop_first().len() as int);
            let ghost init = seq[0]@ + ","@ + seq[1]@;
            assert(tail.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@) =~= joined);
            lemma_fold_left_len_ge_init(tail, init, ","@);
            assert(joined.len() >= init.len());
            assert(init.len() == seq[0]@.len() + ","@.len() + seq[1]@.len());
            assert(seq[0]@.len() == 1);
            assert(","@.len() == 1);
            assert(init.len() >= 2);
            assert(false);
        });
    }

    proof fn lemma_split_terminator_a_comma_comma<'a>(seq: Seq<&'a str>)
        requires
            seq.len() > 0,
            forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==>
                forall |j: int| #![trigger (seq[i]@ + ","@).subrange(j, j + ","@.len())]
                    0 <= j < seq[i]@.len() ==>
                    !((seq[i]@ + ","@).subrange(j, j + ","@.len()) =~= ","@),
            forall |j: int| #![trigger seq.last()@.subrange(j, j + ","@.len())]
                0 <= j <= seq.last()@.len() - ","@.len() ==>
                !(seq.last()@.subrange(j, j + ","@.len()) =~= ","@),
            (
                (
                    seq.last()@.len() > 0
                    && "a,,"@ =~= seq.drop_first().fold_left(
                        seq.first()@,
                        |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
                    )
                )
                ||
                "a,,"@ =~= seq.drop_first().fold_left(
                    seq.first()@,
                    |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
                ) + ","@
            ),
        ensures
            seq.len() == 2,
            seq[0]@ =~= "a"@,
            seq[1]@ =~= ""@,
    {
        reveal_strlit("a,,");
        reveal_strlit("a,");
        reveal_strlit("a");
        reveal_strlit(",");
        reveal_strlit("");

        let ghost joined = seq.drop_first().fold_left(
            seq.first()@,
            |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
        );

        assert_by_contradiction!(seq.last()@.len() == 0 || !("a,,"@ =~= joined), {
            if seq.len() == 1 {
                assert(joined =~= seq[0]@) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 2);
                }
                assert(seq.last()@.len() == joined.len());
                assert(joined.len() == "a,,"@.len());
                assert(seq.last()@.subrange(1, 2) =~= ","@) by {
                    assert(seq.last()@[1] == joined[1]);
                }
                assert(0 <= 1 <= seq.last()@.len() - ","@.len());
                assert(!(seq.last()@.subrange(1, 2) =~= ","@));
                assert(false);
            } else {
                assert(seq.len() >= 2);
                seq.drop_first().lemma_fold_left_split(
                    seq.first()@,
                    |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@,
                    1,
                );
                assert(seq.drop_first().subrange(0, 1).fold_left(
                    seq.first()@,
                    |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
                ) =~= seq[0]@ + ","@ + seq[1]@) by {
                    reveal_with_fuel(Seq::<_>::fold_left, 3);
                }
                let ghost tail = seq.drop_first().subrange(1, seq.drop_first().len() as int);
                let ghost init = seq[0]@ + ","@ + seq[1]@;
                assert(tail.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@) =~= joined);
                assert_by_contradiction!(seq[0]@.len() > 0, {
                    assert(seq[0]@.len() == 0);
                    lemma_fold_left_keeps_prefix(tail, init, ","@, 1);
                    assert(init.subrange(0, 1)[0] == init[0]);
                    assert(init[0] == ',') by { assert(seq[0]@.len() == 0); };
                    assert(joined[0] == 'a');
                    assert(false);
                });
                assert_by_contradiction!(seq[0]@.len() <= 1, {
                    assert(seq[0]@.len() > 1);
                    lemma_fold_left_keeps_prefix(tail, init, ","@, 2);
                    assert(joined.subrange(0, 2) =~= init.subrange(0, 2));
                    assert(init.subrange(1, 2) =~= (seq[0]@ + ","@).subrange(1, 2));
                    assert(init.subrange(1, 2) =~= ","@) by {
                        assert(init.subrange(0, 2)[1] == joined.subrange(0, 2)[1]);
                        assert(joined.subrange(0, 2)[1] == joined[1]);
                        assert(joined[1] == ',');
                        assert(","@[0] == ',');
                    }
                    assert(forall |j: int| #![trigger (seq[0]@ + ","@).subrange(j, j + ","@.len())]
                        0 <= j < seq[0]@.len() ==> !((seq[0]@ + ","@).subrange(j, j + ","@.len()) =~= ","@)
                    );
                    assert(false);
                });
                assert(seq[0]@.len() == 1);
                lemma_fold_left_len_ge_init(tail, init, ","@);
                assert(joined.len() >= init.len());
                assert(init.len() == seq[0]@.len() + ","@.len() + seq[1]@.len());
                assert(seq[1]@.len() <= 1);
                if tail.len() == 0 {
                    assert(seq.len() == 2);
                    assert(seq.last()@[0] == joined[2]);
                    assert(joined[2] == "a,,"@[2]);
                    assert(seq.last()@[0] == ',');
                    assert(seq.last()@.subrange(0, 1) =~= ","@);
                    assert(false);
                } else {
                    assert(tail.subrange(0, 1).fold_left(
                        init,
                        |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
                    ) =~= init + ","@ + tail[0]@) by {
                        reveal_with_fuel(Seq::<_>::fold_left, 3);
                    }
                    if seq[1]@.len() == 1 {
                        assert(init.len() == 3);
                        assert((init + ","@ + tail[0]@).len() > init.len());
                        lemma_fold_left_len_ge_init(
                            tail.drop_first(),
                            init + ","@ + tail[0]@,
                            ","@,
                        );
                        assert(tail.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@).len()
                            >= (init + ","@ + tail[0]@).len());
                        assert(tail.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@).len() > 3);
                        assert(false);
                    } else {
                        assert(seq[1]@.len() == 0);
                        assert(init.len() == 2);
                        assert_by_contradiction!(tail.len() == 1, {
                            assert(tail.len() > 1);
                            let ghost tail2 = tail.drop_first();
                            assert(tail2.subrange(0, 1).fold_left(
                                init + ","@ + tail[0]@,
                                |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
                            ) =~= init + ","@ + tail[0]@ + ","@ + tail2[0]@) by {
                                reveal_with_fuel(Seq::<_>::fold_left, 3);
                            }
                            lemma_fold_left_len_ge_init(
                                tail2.drop_first(),
                                init + ","@ + tail[0]@ + ","@ + tail2[0]@,
                                ","@,
                            );
                            assert(tail.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@).len()
                                >= (init + ","@ + tail[0]@ + ","@ + tail2[0]@).len());
                            assert((init + ","@ + tail[0]@ + ","@ + tail2[0]@).len() > 3);
                            assert(false);
                        });
                        assert(tail[0] == seq.last());
                        assert((init + ","@ + tail[0]@).len() == joined.len());
                        assert(tail[0]@.len() == 0);
                        assert(seq.last()@.len() > 0);
                        assert(false);
                    }
                }
            }
        });

        assert_by_contradiction!("a,,"@ =~= joined + ","@, {
            assert(!("a,,"@ =~= joined + ","@));
            assert(!(seq.last()@.len() > 0 && "a,,"@ =~= joined));
            assert(!((seq.last()@.len() > 0 && "a,,"@ =~= joined) || "a,,"@ =~= joined + ","@));
        });

        assert("a,,"@.len() == (joined + ","@).len());
        assert((joined + ","@).len() == joined.len() + ","@.len());
        assert("a,,"@.len() == 3);
        assert(","@.len() == 1);
        assert(joined.len() == 2);
        assert(joined[0] == 'a') by {
            assert((joined + ","@)[0] == joined[0]);
            assert("a,,"@[0] == (joined + ","@)[0]);
        }
        assert(joined[1] == ',') by {
            assert((joined + ","@)[1] == joined[1]);
            assert("a,,"@[1] == (joined + ","@)[1]);
        }
        assert(joined.subrange(0, 2) =~= "a,"@) by {
            assert(joined.subrange(0, 2)[0] == joined[0]);
            assert(joined.subrange(0, 2)[1] == joined[1]);
            assert("a,"@[0] == 'a');
            assert("a,"@[1] == ',');
        }

        assert_by_contradiction!(seq.len() >= 2, {
            assert(seq.len() == 1);
            assert(seq[0] == seq.first());
            assert(seq[0] == seq.last());
            assert(seq.drop_first().len() == 0);
            assert(joined =~= seq[0]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 2);
            }
            assert(seq.last()@.len() == joined.len());
            assert(joined.len() == 2);
            assert(seq.last()@.subrange(1, 2) =~= ","@) by {
                assert(seq.last()@[1] == joined[1]);
                assert(joined.subrange(0, 2) =~= "a,"@);
                assert("a,"@[1] == ',');
                assert(","@[0] == ',');
            }
            assert(forall |j: int| #![trigger seq.last()@.subrange(j, j + ","@.len())]
                0 <= j <= seq.last()@.len() - ","@.len() ==> !(seq.last()@.subrange(j, j + ","@.len()) =~= ","@)
            ) by {}
            assert(!(seq.last()@.subrange(1, 2) =~= ","@)) by {
                assert(0 <= 1 <= seq.last()@.len() - ","@.len());
            }
            assert(false);
        });

        seq.drop_first().lemma_fold_left_split(
            seq.first()@,
            |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@,
            1,
        );
        assert(seq.drop_first().subrange(0, 1).fold_left(
            seq.first()@,
            |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
        ) =~= seq[0]@ + ","@ + seq[1]@) by {
            reveal_with_fuel(Seq::<_>::fold_left, 3);
        }

        let ghost tail = seq.drop_first().subrange(1, seq.drop_first().len() as int);
        let ghost init = seq[0]@ + ","@ + seq[1]@;
        assert(tail.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@) =~= joined);

        assert_by_contradiction!(seq[0]@.len() > 0, {
            assert(seq[0]@.len() == 0);
            lemma_fold_left_keeps_prefix(tail, init, ","@, 1);
            assert(joined.subrange(0, 1) =~= init.subrange(0, 1));
            assert("a,"@.subrange(0, 1) =~= joined.subrange(0, 1));
            assert(init.subrange(0, 1)[0] == init[0]);
            assert(init[0] == ',');
            assert(false);
        });

        assert_by_contradiction!(seq[0]@.len() <= 1, {
            assert(seq[0]@.len() > 1);
            lemma_fold_left_keeps_prefix(tail, init, ","@, 2);
            assert(joined.subrange(0, 2) =~= init.subrange(0, 2));
            assert("a,"@.subrange(0, 2) =~= joined.subrange(0, 2));
            assert(init.subrange(1, 2) =~= (seq[0]@ + ","@).subrange(1, 2));
            assert(init.subrange(1, 2) =~= ","@) by {
                assert(init.subrange(0, 2)[1] == init.subrange(0, 2)[1]);
                assert(init.subrange(0, 2)[1] == "a,"@.subrange(0, 2)[1]);
                assert("a,"@.subrange(0, 2)[1] == "a,"@[1]);
                assert(init.subrange(1, 2)[0] == init[1]);
                assert(init[1] == ',');
                assert(","@[0] == ',');
            }
            assert(!((seq[0]@ + ","@).subrange(1, 2) =~= ","@)) by {
                assert(0 <= 1 < seq[0]@.len());
            }
            assert(false);
        });

        assert(seq[0]@.len() == 1);
        lemma_fold_left_keeps_prefix(tail, init, ","@, 1);
        assert(joined.subrange(0, 1) =~= init.subrange(0, 1));
        assert("a,"@.subrange(0, 1) =~= joined.subrange(0, 1));
        assert(init.subrange(0, 1) =~= seq[0]@.subrange(0, 1)) by {
            assert(init.subrange(0, 1)[0] == init[0]);
            assert(init[0] == seq[0]@[0]);
            assert(seq[0]@.subrange(0, 1)[0] == seq[0]@[0]);
        }
        assert(seq[0]@[0] == 'a') by {
            assert("a,"@.subrange(0, 1)[0] == "a,"@[0]);
            assert(joined.subrange(0, 1)[0] == joined[0]);
            assert(seq[0]@.subrange(0, 1)[0] == seq[0]@[0]);
        }
        assert(seq[0]@ =~= "a"@);

        lemma_fold_left_len_ge_init(tail, init, ","@);
        assert(joined.len() >= init.len());
        assert(init.len() == seq[0]@.len() + ","@.len() + seq[1]@.len());
        assert(seq[1]@.len() == 0);

        if tail.len() == 0 {
            assert(seq.len() == 2);
        } else {
            assert(tail.subrange(0, 1).fold_left(
                init,
                |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@
            ) =~= init + ","@ + tail[0]@) by {
                reveal_with_fuel(Seq::<_>::fold_left, 3);
            }
            let ghost tail2 = tail.subrange(1, tail.len() as int);
            lemma_fold_left_len_ge_init(
                tail2,
                init + ","@ + tail[0]@,
                ","@,
            );
            assert(tail.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@).len()
                >= (init + ","@ + tail[0]@).len());
            assert((init + ","@ + tail[0]@).len() > init.len());
            assert(tail.fold_left(init, |sum: Seq<char>, ss: &'a str| sum + ","@ + ss@).len() > 2);
            assert(joined.len() > 2);
            assert(false);
        }

        assert(seq.len() == 2);
        assert(seq[1] == seq.last());
        assert(seq[1]@.len() == 0);
        assert(seq[1]@ =~= ""@);
    }

    fn test_split_terminator() {
        broadcast use crate::str::group_str_view;
        proof {
            reveal_strlit("a");
            reveal_strlit("a,");
            reveal_strlit("a,,");
            reveal_strlit(",");
            reveal_strlit("");
        }

        assert("a"@.len() == 1);
        assert(","@.len() == 1);

        let mut it = str_split_terminator("a", ",");
        let ghost seq = it@.1;

        proof {
            assert_by_contradiction!(seq.len() > 0, {
                assert(seq.len() == 0);
                assert("a"@.len() == 0);
            });

            let ghost joined = seq.drop_first().fold_left(
                seq.first()@,
                |sum: Seq<char>, ss: &str| sum + ","@ + ss@
            );

            assert_by_contradiction!(!("a"@ =~= joined + ","@), {
                assert("a"@ =~= joined + ","@);
                assert("a"@.len() == (joined + ","@).len());
                assert((joined + ","@).len() == joined.len() + ","@.len());
                assert(joined.len() == 0);
                assert((joined + ","@)[0] == ","@[0]) by {
                    assert(joined.len() == 0);
                }
                assert("a"@[0] == (joined + ","@)[0]);
                assert(","@[0] == ',');
            });
            assert(joined.len() == 1);
            assert(joined[0] == 'a') by {
                assert("a"@[0] == joined[0]);
            }
            lemma_split_terminator_singleton_when_joined_is_a(seq, joined);
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[0]);
                assert(part@ =~= "a"@);
                assert(it@.0 == 1);
            }
            None => { assert(false); }
        }

        match it.next() {
            Some(_) => { assert(false); }
            None => {
                assert(it@.0 == seq.len());
                assert(it@.1 == seq);
                assert(seq.len() == 1);
            }
        }

        assert("a,"@.len() == 2);
        assert("a,"@.subrange(1, 2) =~= ","@) by {
            assert("a,"@[1] == ',');
            assert(","@[0] == ',');
        }

        let mut it = str_split_terminator("a,", ",");
        let ghost seq = it@.1;

        proof {
            assert_by_contradiction!(seq.len() > 0, {
                assert(seq.len() == 0);
                assert("a,"@.len() == 0);
            });

            let ghost joined = seq.drop_first().fold_left(
                seq.first()@,
                |sum: Seq<char>, ss: &str| sum + ","@ + ss@
            );

            assert_by_contradiction!(seq.last()@.len() == 0 || !("a,"@ =~= joined), {
                if seq.len() == 1 {
                    assert(joined =~= seq[0]@) by {
                        reveal_with_fuel(Seq::<_>::fold_left, 2);
                    }
                    assert(seq.last()@.len() == joined.len());
                    assert(joined.len() == "a,"@.len());
                    assert("a,"@.subrange(1, 1 + ","@.len() as int) =~= ","@) by {
                        assert(seq.last()@[1] == joined[1]);
                    }
                    assert(forall |j: int| #![trigger seq.last()@.subrange(j, j + ","@.len())]
                        0 <= j <= seq.last()@.len() - ","@.len() ==> !(seq.last()@.subrange(j, j + ","@.len()) =~= ","@)
                    );
                } else {
                    assert(seq.drop_first().subrange(0, 1).fold_left(
                        seq.first()@,
                        |sum: Seq<char>, ss: &str| sum + ","@ + ss@
                    ) =~= seq[0]@ + ","@ + seq[1]@) by {
                        reveal_with_fuel(Seq::<_>::fold_left, 3);
                    }
                    let ghost tail = seq.drop_first().subrange(1, seq.drop_first().len() as int);
                    let ghost init = seq[0]@ + ","@ + seq[1]@;
                    assert_by_contradiction!(seq[0]@.len() > 0, {
                        lemma_fold_left_keeps_prefix(tail, init, ","@, 1);
                        assert(init.subrange(0, 1)[0] == init[0]);
                        assert(init[0] == ',') by { assert(seq[0]@.len() == 0); };
                        assert(joined[0] == 'a');
                    });
                    assert_by_contradiction!(seq[0]@.len() <= 1, {
                        lemma_fold_left_keeps_prefix(tail, init, ","@, 2);
                        assert(init.subrange(1, 2) =~= (seq[0]@ + ","@).subrange(1, 2));
                        assert((seq[0]@ + ","@)[1] != ',') by { assert(seq[0]@.len() > 1); };
                        assert(joined[1] == ',');
                    });
                    assert(seq[0]@.len() == 1);
                    lemma_fold_left_len_ge_init(tail, init, ","@);
                    assert(init.len() == 2) by { assert(init.len() <= joined.len()); };
                    assert(init.len() == joined.len());
                    if tail.len() == 0 {
                        assert(seq.len() == 2);
                        assert(seq.last()@.len() == 0);
                    } else {
                        assert(tail.subrange(0, 1).fold_left(
                            init,
                            |sum: Seq<char>, ss: &str| sum + ","@ + ss@
                        ) =~= init + ","@ + tail[0]@) by {
                            reveal_with_fuel(Seq::<_>::fold_left, 3);
                        }
                        assert((init + ","@ + tail[0]@).len() > init.len());
                        lemma_fold_left_len_ge_init(tail.drop_first(), init + ","@ + tail[0]@, ","@);
                    }
                }
            });

            assert("a,"@ =~= joined + ","@);
            assert(joined[0] == 'a') by { assert("a,"@[0] == joined[0]); };
            lemma_split_terminator_singleton_when_joined_is_a(seq, joined);
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[0]);
                assert(part@ =~= "a"@);
                assert(it@.0 == 1);
            }
            None => { assert(false); }
        }

        match it.next() {
            Some(_) => { assert(false); }
            None => {
                assert(it@.0 == seq.len());
                assert(it@.1 == seq);
                assert(seq.len() == 1);
            }
        }

        assert("a,,"@.len() == 3);
        assert("a,,"@.subrange(1, 2) =~= ","@) by {
            assert("a,,"@[1] == ',');
            assert(","@[0] == ',');
        }
        assert("a,,"@.subrange(2, 3) =~= ","@) by {
            assert("a,,"@[2] == ',');
            assert(","@[0] == ',');
        }

        let mut it = str_split_terminator("a,,", ",");
        let ghost seq = it@.1;

        proof {
            lemma_split_terminator_a_comma_comma(seq);
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[0]);
                assert(part@ =~= "a"@);
                assert(it@.0 == 1);
            }
            None => { assert(false); }
        }

        match it.next() {
            Some(part) => {
                assert(part == seq[1]);
                assert(part@ =~= ""@);
                assert(it@.0 == 2);
            }
            None => { assert(false); }
        }

        match it.next() {
            Some(_) => { assert(false); }
            None => {
                assert(it@.0 == seq.len());
                assert(it@.1 == seq);
                assert(seq.len() == 2);
            }
        }
    }
}

} // verus!