//! Iterator methods and types for strings.

#![allow(unused_imports)]
use super::*;
use crate::iter::*;
use vstd::std_specs::iter::*;

use std::str::{
    CharIndices, SplitAsciiWhitespace, Lines, Split,
    pattern::Pattern,
};

verus! {

/// Specifies the iterator `VergeCharIndices` which wraps `CharIndices`, 
/// contructed via `str::char_indices_iter()`.
impl_iterator!(
    CharIndices['a] as VergeCharIndices['_] :: Item = (usize, char)
    [ [str as View<V=Seq<char>>] :: char_indices_iter via char_indices ] 
    (&self,) -> |seq| {
        seq == self@.map(|i: int, c: char| (self@.take(i).as_bytes().len() as usize, c))
    } 
);
impl<'a> core::iter::Iterator for VergeCharIndices<'a> {
    type Item = <Self as VergeIteratorSpec>::Item;
    #[verifier::external_body]
    fn next(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
        { self.0.next() }
}

/// Specifies the iterator `VergeCharIndices` as a double-ended iterator.
impl_double_ended_iterator!(
    CharIndices as VergeCharIndices ['a] :: Item = (usize, char)
);
impl<'a> core::iter::DoubleEndedIterator for VergeCharIndices<'a> {
    #[verifier::external_body]
    fn next_back(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
        { self.0.next_back() }
}

// TODO: derive from pattern
/// Specifies the iterator `VergeSplitAsciiWhitespace` which wraps `SplitAsciiWhitespace`, 
/// contructed via `str::split_ascii_whitespace_iter()`.
impl_iterator!(
    SplitAsciiWhitespace['a] as VergeSplitAsciiWhitespace['_] :: Item = &'a str
    [ [str as View<V=Seq<char>>] :: split_ascii_whitespace_iter via split_ascii_whitespace ] 
    (&self,) -> |seq| {
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
            &&& self@ =~= seq.zip_with(ws.drop_first()).fold_left(
                ws.first(), |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1
            )
        }
    }
);
impl<'a> core::iter::Iterator for VergeSplitAsciiWhitespace<'a> {
    type Item = <Self as VergeIteratorSpec>::Item;
    #[verifier::external_body]
    fn next(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
        { self.0.next() }
}

/// Specifies the iterator `VergeSplitAsciiWhitespace` as a double-ended iterator.
impl_double_ended_iterator!(
    SplitAsciiWhitespace as VergeSplitAsciiWhitespace ['a] :: Item = &'a str
);
impl<'a> core::iter::DoubleEndedIterator for VergeSplitAsciiWhitespace<'a> {
    #[verifier::external_body]
    fn next_back(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
        { self.0.next_back() }
}

/// Specifies the iterator `VergeLines` which wraps `Lines`, 
/// contructed via `str::lines_iter()`.
impl_iterator!(
    Lines['a] as VergeLines['_] :: Item = &'a str
    [ [str as View<V=Seq<char>>] :: lines_iter via lines ] 
    (&self,) -> |seq| {
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
            &&& self@ =~= seq.zip_with(nls).fold_left(
                Seq::<char>::empty(), |sum: Seq<char>, p: (&'a str, Seq<char>)| sum + p.0@ + p.1
            )
        }
    }
);
impl<'a> core::iter::Iterator for VergeLines<'a> {
    type Item = <Self as VergeIteratorSpec>::Item;
    #[verifier::external_body]
    fn next(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
        { self.0.next() }
}

/// Specifies the iterator `VergeLines` as a double-ended iterator.
impl_double_ended_iterator!(
    Lines as VergeLines ['a] :: Item = &'a str
);
impl<'a> core::iter::DoubleEndedIterator for VergeLines<'a> {
    #[verifier::external_body]
    fn next_back(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
        { self.0.next_back() }
}

/// Specifies the iterator `VergeSplit` which wraps `Split`, 
/// contructed via `str::split_iter()`. 
impl_iterator!(
    #[verifier::reject_recursive_types(P)]
    Split['a, P] as VergeSplit['_, P] :: Item = &'a str
    [ [str as View<V=Seq<char>>] :: split_iter via split
        where P: Pattern,
    ] (&self, pat: P) -> |seq| {
        true // TODO
    }
);
impl<'a, P> core::iter::Iterator for VergeSplit<'a, P> 
    where P: Pattern,
{
    type Item = <Self as VergeIteratorSpec>::Item;
    #[verifier::external_body]
    fn next(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
        { self.0.next() }
}

// impl_iterator_verge!(
//     Split ['a, 'pat] where Item = &'a str
//     [ str_split via str::split ] (s: &'a str, pat: &'pat str) 
//         requires(pat@.len() > 0) -> |seq| { 
//         // splits are never empty
//         &&& seq.len() > 0
//         // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
//         &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==> 
//                 forall |j: int| #![trigger seq[i]@.subrange(j, j + pat@.len())] 0 <= j < seq[i]@.len() ==> 
//                     !((seq[i]@ + pat@).subrange(j, j + pat@.len()) =~= pat@)
//         // last split cannot have `pat` as a substring
//         &&& forall |j: int| #![trigger seq.last()@.subrange(j, j + pat@.len())] 0 <= j <= seq.last()@.len() - pat@.len() ==> 
//                 !(seq.last()@.subrange(j, j + pat@.len()) =~= pat@)
//         // delimeters and splits make up the original string
//         &&& s@ =~= seq.drop_first().fold_left(
//             seq.first()@, |sum: Seq<char>, ss: &'a str| sum + pat@ + ss@
//         )
//     }
// );

// /// Enables `SplitInclusive` as an iterator (wrapping is needed because we don't fully support the `Pattern` trait bound).
// ///
// /// Returns an iterator over substrings of this string slice, separated by characters matched by a pattern.
// /// Unlike `Split`, `SplitInclusive` leaves the matched part as the terminator of the substring.
// #[verifier::external]
// pub struct SplitInclusive<'a, 'pat>(std::str::SplitInclusive<'a, &'pat str>);
// #[verifier::external_type_specification]
// #[verifier::external_body]
// pub struct ExSplitInclusive<'a, 'pat>(SplitInclusive<'a, 'pat>);

// impl_iterator_verge!(
//     SplitInclusive ['a, 'pat] where Item = &'a str
//     [ str_split_inclusive via str::split_inclusive ] (s: &'a str, pat: &'pat str)
//         requires(pat@.len() > 0) -> |seq| {
//         // splits cannot have `pat` as a prefix or infix
//         &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> 
//                 forall |j: int| #![trigger seq[i]@.subrange(j, j + pat@.len())] 0 <= j < seq[i]@.len() - pat@.len() ==> 
//                     !(seq[i]@.subrange(j, j + pat@.len()) =~= pat@)
//         // splits (apart from the last) must have `pat` as a suffix
//         &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==> 
//                 pat@.is_suffix_of(seq[i]@)
//         // splits make up the original string
//         &&& s@ =~= seq.fold_left(
//             Seq::<char>::empty(), |sum: Seq<char>, ss: &'a str| sum + ss@
//         )
//     }
// );

// /// Enables `SplitTerminator` as an iterator (wrapping is needed because we don't fully support the `Pattern` trait bound).
// ///
// /// Returns an iterator over substrings of the given string slice, separated by characters matched by a pattern.
// /// Equivalent to `Split`, except that the trailing substring is skipped if empty.
// #[verifier::external]
// pub struct SplitTerminator<'a, 'pat>(std::str::SplitTerminator<'a, &'pat str>);
// #[verifier::external_type_specification]
// #[verifier::external_body]
// pub struct ExSplitTerminator<'a, 'pat>(SplitTerminator<'a, 'pat>);

// impl_iterator_verge!(
//     SplitTerminator ['a, 'pat] where Item = &'a str
//     [ str_split_terminator via str::split_terminator ] (s: &'a str, pat: &'pat str) 
//         requires(pat@.len() > 0) -> |seq| {
//         // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
//         &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==> 
//                 forall |j: int| #![trigger seq[i]@.subrange(j, j + pat@.len())] 0 <= j < seq[i]@.len() ==> 
//                     !((seq[i]@ + pat@).subrange(j, j + pat@.len()) =~= pat@)
//         // last split (if existent) is not empty, and cannot have `pat` as a substring
//         &&& seq.len() > 0 ==> {
//             &&& seq.last()@.len() > 0
//             &&& forall |j: int| #![trigger seq.last()@.subrange(j, j + pat@.len())] 0 <= j <= seq.last()@.len() - pat@.len() ==> 
//                     !(seq.last()@.subrange(j, j + pat@.len()) =~= pat@)
//         }
//         // delimeters and splits make up the original string
//         &&& seq.len() == 0 ==> s@.len() == 0
//         &&& seq.len() > 0 ==> s@ =~= seq.drop_first().fold_left(
//                 seq.first()@, |sum: Seq<char>, ss: &'a str| sum + pat@ + ss@)
//     }
// );

// /// Enables `SplitN` as an iterator (wrapping is needed because we don't fully support the `Pattern` trait bound).
// ///
// /// Returns an iterator over substrings of the given string slice, separated by a pattern, restricted to returning at most `n` items.
// /// If `n` substrings are returned, the last substring (the `n`th substring) will contain the remainder of the string.
// #[verifier::external]
// pub struct SplitN<'a, 'pat>(std::str::SplitN<'a, &'pat str>);
// #[verifier::external_type_specification]
// #[verifier::external_body]
// pub struct ExSplitN<'a, 'pat>(SplitN<'a, 'pat>);

// impl_iterator_verge!(
//     SplitN ['a, 'pat] where Item = &'a str
//     [ str_splitn via str::splitn ] (s: &'a str, n: usize, pat: &'pat str) 
//         requires(n > 0 && pat@.len() > 0) -> |seq| { 
//         // splits are never empty, and there are at most `n` splits
//         &&& 0 < seq.len() <= n
//         // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
//         &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() - 1 ==> 
//                 forall |j: int| #![trigger (seq[i]@ + pat@).subrange(j, j + pat@.len())] 0 <= j < seq[i]@.len() ==>
//                     !((seq[i]@ + pat@).subrange(j, j + pat@.len()) =~= pat@)
//         // last split (if not the n-th) cannot have `pat` as a substring
//         &&& seq.len() < n ==>
//             forall |j: int| #![trigger seq.last()@.subrange(j, j + pat@.len())] 0 <= j <= seq.last()@.len() - pat@.len() ==> 
//                 !(seq.last()@.subrange(j, j + pat@.len()) =~= pat@)
//         // delimeters and splits make up the original string
//         &&& s@ =~= seq.drop_first().fold_left(
//             seq.first()@, |sum: Seq<char>, ss: &'a str| sum + pat@ + ss@
//         )
//     }
// );

// /// Enables `str::split_once`.
// #[verifier::external_body]
// pub fn str_split_once<'a, 'pat>(s: &'a str, pat: &'pat str) -> (ret: Option<(&'a str, &'a str)>)
//     requires
//         pat@.len() > 0,
//     ensures
//         ({
//             match ret {
//                 Some((head, tail)) => {
//                     // `head + pat` cannot have `pat` as a prefix or infix
//                     &&& forall |i: int| #![trigger head@.subrange(i, i + pat@.len())] 0 <= i < head@.len() ==> 
//                             !((head@ + pat@).subrange(i, i + pat@.len()) =~= pat@)
//                     // delimeter and splits make up the original string
//                     &&& s@ =~= head@ + pat@ + tail@
//                 },
//                 None => {
//                     forall |i: int| #![trigger s@.subrange(i, i + pat@.len())] 0 <= i <= s@.len() - pat@.len() ==> 
//                         !(s@.subrange(i, i + pat@.len()) =~= pat@)
//                 },
//             }
//         }),
//     no_unwind
// {
//     s.split_once(pat)
// }

// /// Enables `MatchIndices` as an iterator (wrapping is needed because we don't fully support the `Pattern` trait bound).
// ///
// /// Returns an iterator over the disjoint matches of a pattern within this string slice as well as the index that the match starts at.
// /// For matches of pat within self that overlap, only the indices corresponding to the first match are returned.
// #[verifier::external]
// pub struct MatchIndices<'a, 'pat>(std::str::MatchIndices<'a, &'pat str>);
// #[verifier::external_type_specification]
// #[verifier::external_body]
// pub struct ExMatchIndices<'a, 'pat>(MatchIndices<'a, 'pat>);

// impl_iterator_verge!(
//     MatchIndices ['a, 'pat] where Item = (usize, &'a str)
//     [ str_match_indices via str::match_indices ] (s: &'a str, pat: &'pat str) 
//         requires(pat@.len() > 0) -> |seq| { 
//         let slen = s@.as_bytes().len() as int;
//         let plen = pat@.as_bytes().len() as int;
//         let indices = seq.map(|_i: int, p: (usize, &'a str)| p.0 as int);
//         let mismatches = (seq![0int] + indices).zip_with(indices + seq![(s@.as_bytes().len() - plen + 1) as int]);
//         // indices points to matches
//         &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> {
//             &&& indices[i] + plen <= slen
//             &&& s@.as_bytes().subrange(indices[i], indices[i] + plen) =~= pat@.as_bytes()
//         }
//         // mismatches cannot have matches
//         &&& forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> 
//                 forall |j: int| #![trigger s@.as_bytes()[j]] mismatches[i].0 <= j < mismatches[i].1 ==> 
//                     !(s@.as_bytes().subrange(j, j + plen) =~= pat@.as_bytes())
//     }
// );

mod tests {
    use super::*;

    fn test_char_indices() {
        broadcast use crate::str::group_str_view;
        proof { reveal_strlit("ab"); }

        let s = "ab";
        for (i, c) in iter: s.char_indices_iter()
            invariant
                iter.seq() == seq![(0usize, 'a'), (1usize, 'b')],
        {
            assert(c.is_ascii());
        }
        for (i, c) in iter: s.char_indices_iter().rev()
            invariant
                iter.seq() == seq![(1usize, 'b'), (0usize, 'a')],
        {
            assert(c.is_ascii());
        }
    }

    // fn test_split_once() {
    //     broadcast use crate::str::group_str_view;
    //     proof {
    //         reveal_strlit("aa,b,c");
    //         reveal_strlit(",");
    //         reveal_strlit(".");
    //         reveal_strlit("aa");
    //         reveal_strlit("b,c");
    //     }

    //     let s = "aa,b,c";
    //     let result = str_split_once(s, ",");
    //     assert(2 + ","@.len() as int == 3);
    //     assert(s@.subrange(2, 3) =~= ","@) by {
    //         assert(s@[2] == ',');
    //         assert(","@[0] == ',');
    //     }
    //     assert(result.is_some());

    //     match result {
    //         Some((head, tail)) => {
    //             assert(s@ =~= head@ + ","@ + tail@);
    //             assert(head@ =~= "aa"@) by {
    //                 assert_by_contradiction!(head@.len() <= 2, {
    //                     assert(head@.subrange(2, 3) =~= s@.subrange(2, 3));
    //                 });
    //                 assert_by_contradiction!(head@.len() > 1, {
    //                     let i = head@.len() as int;
    //                     assert(s@[i] != ',') by { assert(0 <= i <= 1); };
    //                 });
    //                 assert(head@.len() == 2);
    //                 assert(s@.subrange(0, 2) =~= head@.subrange(0, 2));
    //             }
    //             assert(tail@ =~= "b,c"@) by {
    //                 assert(s@.subrange(3, 6) =~= "b,c"@);
    //             }
    //         }
    //         None => { assert(false); }
    //     }

    //     let none = str_split_once(s, ".");
    //     assert(forall |i: int| 0 <= i < s@.len() ==> #[trigger] s@[i] != '.');

    //     proof {
    //         assert_by_contradiction!(none.is_none(), {
    //             assert(none.is_some());
    //             match none {
    //                 Some((h, t)) => {
    //                     let i = h@.len() as int;
    //                     assert(s@ =~= h@ + "."@ + t@);
    //                     assert(s@[i] == '.');
    //                 }
    //                 None => { assert(false) }
    //             }
    //         });
    //     }

    //     assert(none.is_none());
    // }

    // fn test_splitn() {
    //     broadcast use crate::str::group_str_view;
    //     proof {
    //         reveal_strlit("a,b,c");
    //         reveal_strlit(",");
    //         reveal_strlit("a");
    //         reveal_strlit("b,c");
    //     }

    //     assert("a,b,c"@.len() == 5);
    //     assert(","@.len() == 1);
    //     assert(1 + ","@.len() == 2);
    //     assert("a,b,c"@.subrange(1, 2) =~= ","@) by {
    //         assert("a,b,c"@[1] == ',');
    //         assert(","@[0] == ',');
    //     }

    //     let mut it = str_splitn("a,b,c", 2usize, ",");
    //     let ghost seq = it.seq();

    //     proof {
    //         assert_by_contradiction!(seq.len() == 2, {   
    //             assert(seq.last()@ =~= "a,b,c"@);
    //             assert(seq.last()@.subrange(1, 2) =~= ","@);
    //             assert(!(seq.last()@.subrange(1, 2) =~= ","@)) by { assert(seq.len() < 2); }
    //         });

    //         assert(seq.drop_first().fold_left(
    //             seq.first()@, |sum: Seq<char>, ss: &str| sum + ","@ + ss@
    //         ) =~= seq.first()@ + ","@ + seq[1]@) by {
    //             reveal_with_fuel(Seq::<_>::fold_left, 3);
    //         }
    //         assert("a,b,c"@ =~= seq[0]@ + ","@ + seq[1]@);

    //         assert(seq[0]@ =~= "a"@) by {
    //             assert_by_contradiction!(seq[0]@.len() <= 1, {
    //                 assert((seq[0]@ + ","@).subrange(1, 2) =~= "a,b,c"@.subrange(1, 2));
    //             });
    //             assert_by_contradiction!(seq[0]@.len() > 0, {
    //                 assert((seq[0]@ + ","@)[0] == ',');
    //                 assert("a,b,c"@[0] == 'a');
    //             });
    //             assert(seq[0]@.len() == 1);
    //             assert(seq[0]@[0] == "a,b,c"@[0]);
    //             assert(seq[0]@[0] == 'a');
    //         }

    //         assert(seq[1]@ =~= "b,c"@) by {
    //             assert("a,b,c"@.subrange(2, 5) =~= "b,c"@);
    //         }
    //     }

    //     match it.next() {
    //         Some(part) => {
    //             assert(part == seq[0]);
    //             assert(part@ =~= "a"@);
    //             assert(it.idx() == 1);
    //         }
    //         None => { assert(false); }
    //     }
    //     match it.next() {
    //         Some(part) => {
    //             assert(part == seq[1]);
    //             assert(part@ =~= "b,c"@);
    //             assert(it.idx() == 2);
    //         }
    //         None => { assert(false); }
    //     }
    //     match it.next() {
    //         Some(_) => { assert(false); }
    //         None => {
    //             assert(it.idx() == seq.len());
    //             assert(it.seq() == seq);
    //         }
    //     }
    // }
}

} // verus!