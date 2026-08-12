//! Monomorphic specifications for string pattern operations.
//!
//! Rust's `str` pattern APIs are generic over the unstable `Pattern` trait.
//! Verge exposes a concrete extension-trait surface instead: every supported
//! pattern kind has its own method suffix (`_ch`, `_chars`, `_fn`, or `_str`),
//! and each method carries a monomorphic specification respectively.

use super::*;
use crate::{is_deterministic, is_total, VergeView};
use vstd::prelude::*;
use vstd::utf8::{decode_utf8, is_char_boundary};

verus! {

/// Joins alternating result pieces and separators.
#[verifier::inline]
pub open spec fn join(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>) -> Seq<char>
    recommends seq.len() + 1 == gap.len(),
{
    gap.first()
        + gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss).flatten()
}

/// Joins alternating result pieces and separators from the right.
#[verifier::inline]
pub open spec fn rjoin(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>) -> Seq<char>
    recommends seq.len() + 1 == gap.len(),
{
    gap.last()
        + gap.drop_last().map(|i: int, ss: Seq<char>| ss + seq[i]).reverse().flatten()
}


pub trait StrPatternFns: View<V = Seq<char>> {
    fn contains_ch(&self, ch: char) -> (ret: bool)
        ensures
            ret == exists |i: int| 0 <= i < self@.len() && self@[i] == ch;
    fn contains_chars<'a>(&self, chars: &'a [char]) -> (ret: bool)
        ensures
            ret == exists |i: int| 0 <= i < self@.len() && #[trigger] chars@.contains(self@[i]);
    fn contains_fn<F>(&self, f: F) -> (ret: bool)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            ret == exists |i: int| 0 <= i < self@.len() && #[trigger] call_ensures(f, (self@[i],), true);
    fn contains_str<'a>(&self, pat: &'a str) -> (ret: bool)
        ensures
            ret == pat@.is_subrange_of(self@);

    fn starts_with_ch(&self, ch: char) -> (ret: bool)
        ensures
            ret == (self@.len() > 0 && self@.first() == ch);
    fn starts_with_chars<'a>(&self, chars: &'a [char]) -> (ret: bool)
        ensures
            ret == (self@.len() > 0 && #[trigger] chars@.contains(self@.first()));
    fn starts_with_fn<F>(&self, f: F) -> (ret: bool)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            ret == (self@.len() > 0 && #[trigger] call_ensures(f, (self@.first(),), true));
    fn starts_with_str<'a>(&self, pat: &'a str) -> (ret: bool)
        ensures
            ret == pat@.is_prefix_of(self@);

    fn ends_with_ch(&self, ch: char) -> (ret: bool)
        ensures
            ret == (self@.len() > 0 && self@.last() == ch);
    fn ends_with_chars<'a>(&self, chars: &'a [char]) -> (ret: bool)
        ensures
            ret == (self@.len() > 0 && #[trigger] chars@.contains(self@.last()));
    fn ends_with_fn<F>(&self, f: F) -> (ret: bool)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            ret == (self@.len() > 0 && #[trigger] call_ensures(f, (self@.last(),), true));
    fn ends_with_str<'a>(&self, pat: &'a str) -> (ret: bool)
        ensures
            ret == pat@.is_suffix_of(self@);

    fn find_ch(&self, ch: char) -> (ret: Option<usize>)
        ensures
            match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> self@[i] != ch,
        Some(k) => {
            let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
            &&& is_char_boundary(self@.as_bytes(), k as int)
            &&& i < self@.len()
            &&& self@[i] == ch
            &&& forall |j: int| 0 <= j < i ==> self@[j] != ch
        },
    };
    fn find_chars<'a>(&self, chars: &'a [char]) -> (ret: Option<usize>)
        ensures
            match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] chars@.contains(self@[i]),
        Some(k) => {
            let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
            &&& is_char_boundary(self@.as_bytes(), k as int)
            &&& i < self@.len()
            &&& chars@.contains(self@[i])
            &&& forall |j: int| 0 <= j < i ==> !#[trigger] chars@.contains(self@[j])
        },
    };
    fn find_fn<F>(&self, f: F) -> (ret: Option<usize>)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] call_ensures(f, (self@[i],), true),
        Some(k) => {
            let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
            &&& is_char_boundary(self@.as_bytes(), k as int)
            &&& i < self@.len()
            &&& call_ensures(f, (self@[i],), true)
            &&& forall |j: int| 0 <= j < i ==> !#[trigger] call_ensures(f, (self@[j],), true)
        },
    };
    fn find_str<'a>(&self, pat: &'a str) -> (ret: Option<usize>)
        ensures
            match ret {
        None => !pat@.is_subrange_of(self@),
        Some(k) => {
            let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
            &&& is_char_boundary(self@.as_bytes(), k as int)
            &&& i + pat@.len() <= self@.len()
            &&& pat@ == self@.subrange(i, i + pat@.len())
            &&& forall |j: int| 0 <= j < i ==> pat@ != #[trigger] self@.subrange(j, j + pat@.len())
        },
    };

    fn rfind_ch(&self, ch: char) -> (ret: Option<usize>)
        ensures
            match ret {
                None => forall |i: int| 0 <= i < self@.len() ==> self@[i] != ch,
                Some(k) => {
                    let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(self@.as_bytes(), k as int)
                    &&& i < self@.len()
                    &&& self@[i] == ch
                    &&& forall |j: int| i < j < self@.len() ==> self@[j] != ch
                },
            };
    fn rfind_chars<'a>(&self, chars: &'a [char]) -> (ret: Option<usize>)
        ensures
            match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] chars@.contains(self@[i]),
        Some(k) => {
            let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
            &&& is_char_boundary(self@.as_bytes(), k as int)
            &&& i < self@.len()
            &&& chars@.contains(self@[i])
            &&& forall |j: int| i < j < self@.len() ==> !#[trigger] chars@.contains(self@[j])
        },
    };
    fn rfind_fn<F>(&self, f: F) -> (ret: Option<usize>)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] call_ensures(f, (self@[i],), true),
        Some(k) => {
            let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
            &&& is_char_boundary(self@.as_bytes(), k as int)
            &&& i < self@.len()
            &&& call_ensures(f, (self@[i],), true)
            &&& forall |j: int| i < j < self@.len() ==> !#[trigger] call_ensures(f, (self@[j],), true)
        },
    };
    fn rfind_str<'a>(&self, pat: &'a str) -> (ret: Option<usize>)
        ensures
            match ret {
        None => !pat@.is_subrange_of(self@),
        Some(k) => {
            let i = decode_utf8(self@.as_bytes().take(k as int)).len() as int;
            &&& is_char_boundary(self@.as_bytes(), k as int)
            &&& i + pat@.len() <= self@.len()
            &&& pat@ == self@.subrange(i, i + pat@.len())
            &&& forall |j: int| i < j <= self@.len() - pat@.len()
                ==> pat@ != #[trigger] self@.subrange(j, j + pat@.len())
        },
    };

    fn split_once_ch<'a>(&'a self, ch: char) -> (ret: Option<(&'a str, &'a str)>)
        ensures
            match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> self@[i] != ch,
        Some((head, tail)) => {
            &&& self@ =~= head@ + seq![ch] + tail@
            &&& forall |i: int| 0 <= i < head@.len() ==> self@[i] != ch
        },
    };
    fn split_once_chars<'a, 'b>(&'a self, chars: &'b [char]) -> (ret: Option<(&'a str, &'a str)>)
        ensures
            match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] chars@.contains(self@[i]),
        Some((head, tail)) => {
            let i = head@.len() as int;
            &&& i < self@.len()
            &&& self@ =~= head@ + seq![self@[i]] + tail@
            &&& chars@.contains(self@[i])
            &&& forall |j: int| 0 <= j < i ==> !#[trigger] chars@.contains(self@[j])
        },
    };
    fn split_once_fn<'a, F>(&'a self, f: F) -> (ret: Option<(&'a str, &'a str)>)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] call_ensures(f, (self@[i],), true),
        Some((head, tail)) => {
            let i = head@.len() as int;
            &&& i < self@.len()
            &&& self@ =~= head@ + seq![self@[i]] + tail@
            &&& call_ensures(f, (self@[i],), true)
            &&& forall |j: int| 0 <= j < i ==> !#[trigger] call_ensures(f, (self@[j],), true)
        },
    };
    fn split_once_str<'a, 'b>(&'a self, pat: &'b str) -> (ret: Option<(&'a str, &'a str)>)
        ensures
            match ret {
        None => !pat@.is_subrange_of(self@),
        Some((head, tail)) => {
            &&& pat@.len() == 0 ==> (head@.len() == 0 && tail@ =~= self@)
            &&& pat@.len() > 0 ==> {
                let i = head@.len() as int;
                &&& i + pat@.len() <= self@.len()
                &&& self@ =~= head@ + pat@ + tail@
                &&& forall |j: int| 0 <= j < i ==> pat@ != #[trigger] self@.subrange(j, j + pat@.len())
            }
        },
    };

    fn rsplit_once_ch<'a>(&'a self, ch: char) -> (ret: Option<(&'a str, &'a str)>)
        ensures
            match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> self@[i] != ch,
        Some((head, tail)) => {
            &&& self@ =~= head@ + seq![ch] + tail@
            &&& forall |i: int| head@.len() + 1 <= i < self@.len() ==> self@[i] != ch
        },
    };
    fn rsplit_once_chars<'a, 'b>(&'a self, chars: &'b [char]) -> (ret: Option<(&'a str, &'a str)>)
        ensures
            match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] chars@.contains(self@[i]),
        Some((head, tail)) => {
            let i = head@.len() as int;
            &&& i < self@.len()
            &&& self@ =~= head@ + seq![self@[i]] + tail@
            &&& chars@.contains(self@[i])
            &&& forall |j: int| i < j < self@.len() ==> !#[trigger] chars@.contains(self@[j])
        },
    };
    fn rsplit_once_fn<'a, F>(&'a self, f: F) -> (ret: Option<(&'a str, &'a str)>)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            match ret {
        None => forall |i: int| 0 <= i < self@.len() ==> !#[trigger] call_ensures(f, (self@[i],), true),
        Some((head, tail)) => {
            let i = head@.len() as int;
            &&& i < self@.len()
            &&& self@ =~= head@ + seq![self@[i]] + tail@
            &&& call_ensures(f, (self@[i],), true)
            &&& forall |j: int| i < j < self@.len() ==> !#[trigger] call_ensures(f, (self@[j],), true)
        },
    };
    fn rsplit_once_str<'a, 'b>(&'a self, pat: &'b str) -> (ret: Option<(&'a str, &'a str)>)
        ensures
            match ret {
        None => !pat@.is_subrange_of(self@),
        Some((head, tail)) => {
            &&& pat@.len() == 0 ==> (head@ =~= self@ && tail@.len() == 0)
            &&& pat@.len() > 0 ==> {
                let i = head@.len() as int;
                &&& i + pat@.len() <= self@.len()
                &&& self@ =~= head@ + pat@ + tail@
                &&& forall |j: int| i < j <= self@.len() - pat@.len()
                    ==> pat@ != #[trigger] self@.subrange(j, j + pat@.len())
            }
        },
    };

    fn trim_matches_ch(&self, ch: char) -> (ret: &str)
        ensures
            ret@ == self@.skip_while(|c: char| c == ch).rskip_while(|c: char| c == ch);
    fn trim_matches_chars<'a>(&self, chars: &'a [char]) -> (ret: &str)
        ensures
            ret@ == self@.skip_while(|c: char| chars@.contains(c)).rskip_while(|c: char| chars@.contains(c));
    fn trim_matches_fn<F>(&self, f: F) -> (ret: &str)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            ret@ == self@.skip_while(|c: char| call_ensures(f, (c,), true))
        .rskip_while(|c: char| call_ensures(f, (c,), true));
    fn trim_matches_str<'a>(&self, pat: &'a str) -> (ret: &str)
        ensures
            (pat@.len() == 0 && ret@ == self@) || (pat@.len() > 0 && ret@.is_subrange_of(self@)
        && (ret@.len() == 0 || (!pat@.is_prefix_of(ret@) && !pat@.is_suffix_of(ret@))));

    fn trim_start_matches_ch(&self, ch: char) -> (ret: &str)
        ensures
            ret@ == self@.skip_while(|c: char| c == ch);
    fn trim_start_matches_chars<'a>(&self, chars: &'a [char]) -> (ret: &str)
        ensures
            ret@ == self@.skip_while(|c: char| chars@.contains(c));
    fn trim_start_matches_fn<F>(&self, f: F) -> (ret: &str)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            ret@ == self@.skip_while(|c: char| call_ensures(f, (c,), true));
    fn trim_start_matches_str<'a>(&self, pat: &'a str) -> (ret: &str)
        ensures
            (pat@.len() == 0 && ret@ == self@) || (pat@.len() > 0 && ret@.is_suffix_of(self@)
        && (ret@.len() == 0 || !pat@.is_prefix_of(ret@)));

    fn trim_end_matches_ch(&self, ch: char) -> (ret: &str)
        ensures
            ret@ == self@.rskip_while(|c: char| c == ch);
    fn trim_end_matches_chars<'a>(&self, chars: &'a [char]) -> (ret: &str)
        ensures
            ret@ == self@.rskip_while(|c: char| chars@.contains(c));
    fn trim_end_matches_fn<F>(&self, f: F) -> (ret: &str)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            ret@ == self@.rskip_while(|c: char| call_ensures(f, (c,), true));
    fn trim_end_matches_str<'a>(&self, pat: &'a str) -> (ret: &str)
        ensures
            (pat@.len() == 0 && ret@ == self@) || (pat@.len() > 0 && ret@.is_prefix_of(self@)
        && (ret@.len() == 0 || !pat@.is_suffix_of(ret@)));

    fn strip_prefix_ch<'a>(&'a self, ch: char) -> (ret: Option<&'a str>)
        ensures
            match ret {
        Some(rest) => self@ =~= seq![ch] + rest@,
        None => self@.len() == 0 || self@.first() != ch,
    };
    fn strip_prefix_chars<'a, 'b>(&'a self, chars: &'b [char]) -> (ret: Option<&'a str>)
        ensures
            match ret {
        Some(rest) => self@.len() > 0 && chars@.contains(self@.first()) && self@ =~= seq![self@.first()] + rest@,
        None => self@.len() == 0 || !chars@.contains(self@.first()),
    };
    fn strip_prefix_fn<'a, F>(&'a self, f: F) -> (ret: Option<&'a str>)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            match ret {
        Some(rest) => self@.len() > 0 && call_ensures(f, (self@.first(),), true)
            && self@ =~= seq![self@.first()] + rest@,
        None => self@.len() == 0 || !call_ensures(f, (self@.first(),), true),
    };
    fn strip_prefix_str<'a, 'b>(&'a self, pat: &'b str) -> (ret: Option<&'a str>)
        ensures
            match ret {
        Some(rest) => self@ =~= pat@ + rest@,
        None => !pat@.is_prefix_of(self@),
    };

    fn strip_suffix_ch<'a>(&'a self, ch: char) -> (ret: Option<&'a str>)
        ensures
            match ret {
        Some(rest) => self@ =~= rest@ + seq![ch],
        None => self@.len() == 0 || self@.last() != ch,
    };
    fn strip_suffix_chars<'a, 'b>(&'a self, chars: &'b [char]) -> (ret: Option<&'a str>)
        ensures
            match ret {
        Some(rest) => self@.len() > 0 && chars@.contains(self@.last()) && self@ =~= rest@ + seq![self@.last()],
        None => self@.len() == 0 || !chars@.contains(self@.last()),
    };
    fn strip_suffix_fn<'a, F>(&'a self, f: F) -> (ret: Option<&'a str>)
        where F: FnMut(char) -> bool,
        requires is_deterministic(f) && is_total(f),
        ensures
            match ret {
        Some(rest) => self@.len() > 0 && call_ensures(f, (self@.last(),), true)
            && self@ =~= rest@ + seq![self@.last()],
        None => self@.len() == 0 || !call_ensures(f, (self@.last(),), true),
    };
    fn strip_suffix_str<'a, 'b>(&'a self, pat: &'b str) -> (ret: Option<&'a str>)
        ensures
            match ret {
        Some(rest) => self@ =~= rest@ + pat@,
        None => !pat@.is_suffix_of(self@),
    };
}

impl StrPatternFns for str {
    #[verifier::external_body]
    fn contains_ch(&self, ch: char) -> bool { self.contains(ch) }
    #[verifier::external_body]
    fn contains_chars<'a>(&self, chars: &'a [char]) -> bool { self.contains(chars) }
    #[verifier::external_body]
    fn contains_fn<F>(&self, f: F) -> bool where F: FnMut(char) -> bool { self.contains(f) }
    #[verifier::external_body]
    fn contains_str<'a>(&self, pat: &'a str) -> bool { self.contains(pat) }

    #[verifier::external_body]
    fn starts_with_ch(&self, ch: char) -> bool { self.starts_with(ch) }
    #[verifier::external_body]
    fn starts_with_chars<'a>(&self, chars: &'a [char]) -> bool { self.starts_with(chars) }
    #[verifier::external_body]
    fn starts_with_fn<F>(&self, f: F) -> bool where F: FnMut(char) -> bool { self.starts_with(f) }
    #[verifier::external_body]
    fn starts_with_str<'a>(&self, pat: &'a str) -> bool { self.starts_with(pat) }

    #[verifier::external_body]
    fn ends_with_ch(&self, ch: char) -> bool { self.ends_with(ch) }
    #[verifier::external_body]
    fn ends_with_chars<'a>(&self, chars: &'a [char]) -> bool { self.ends_with(chars) }
    #[verifier::external_body]
    fn ends_with_fn<F>(&self, f: F) -> bool where F: FnMut(char) -> bool { self.ends_with(f) }
    #[verifier::external_body]
    fn ends_with_str<'a>(&self, pat: &'a str) -> bool { self.ends_with(pat) }

    #[verifier::external_body]
    fn find_ch(&self, ch: char) -> Option<usize> { self.find(ch) }
    #[verifier::external_body]
    fn find_chars<'a>(&self, chars: &'a [char]) -> Option<usize> { self.find(chars) }
    #[verifier::external_body]
    fn find_fn<F>(&self, f: F) -> Option<usize> where F: FnMut(char) -> bool { self.find(f) }
    #[verifier::external_body]
    fn find_str<'a>(&self, pat: &'a str) -> Option<usize> { self.find(pat) }

    #[verifier::external_body]
    fn rfind_ch(&self, ch: char) -> Option<usize> { self.rfind(ch) }
    #[verifier::external_body]
    fn rfind_chars<'a>(&self, chars: &'a [char]) -> Option<usize> { self.rfind(chars) }
    #[verifier::external_body]
    fn rfind_fn<F>(&self, f: F) -> Option<usize> where F: FnMut(char) -> bool { self.rfind(f) }
    #[verifier::external_body]
    fn rfind_str<'a>(&self, pat: &'a str) -> Option<usize> { self.rfind(pat) }

    #[verifier::external_body]
    fn split_once_ch<'a>(&'a self, ch: char) -> Option<(&'a str, &'a str)> { self.split_once(ch) }
    #[verifier::external_body]
    fn split_once_chars<'a, 'b>(&'a self, chars: &'b [char]) -> Option<(&'a str, &'a str)> { self.split_once(chars) }
    #[verifier::external_body]
    fn split_once_fn<'a, F>(&'a self, f: F) -> Option<(&'a str, &'a str)> where F: FnMut(char) -> bool { self.split_once(f) }
    #[verifier::external_body]
    fn split_once_str<'a, 'b>(&'a self, pat: &'b str) -> Option<(&'a str, &'a str)> { self.split_once(pat) }

    #[verifier::external_body]
    fn rsplit_once_ch<'a>(&'a self, ch: char) -> Option<(&'a str, &'a str)> { self.rsplit_once(ch) }
    #[verifier::external_body]
    fn rsplit_once_chars<'a, 'b>(&'a self, chars: &'b [char]) -> Option<(&'a str, &'a str)> { self.rsplit_once(chars) }
    #[verifier::external_body]
    fn rsplit_once_fn<'a, F>(&'a self, f: F) -> Option<(&'a str, &'a str)> where F: FnMut(char) -> bool { self.rsplit_once(f) }
    #[verifier::external_body]
    fn rsplit_once_str<'a, 'b>(&'a self, pat: &'b str) -> Option<(&'a str, &'a str)> { self.rsplit_once(pat) }

    #[verifier::external_body]
    fn trim_matches_ch(&self, ch: char) -> &str { self.trim_matches(ch) }
    #[verifier::external_body]
    fn trim_matches_chars<'a>(&self, chars: &'a [char]) -> &str { self.trim_matches(chars) }
    #[verifier::external_body]
    fn trim_matches_fn<F>(&self, f: F) -> &str where F: FnMut(char) -> bool { self.trim_matches(f) }
    #[verifier::external_body]
    fn trim_matches_str<'a>(&self, pat: &'a str) -> &str { self.trim_matches(|ch| pat@.contains(ch)) }

    #[verifier::external_body]
    fn trim_start_matches_ch(&self, ch: char) -> &str { self.trim_start_matches(ch) }
    #[verifier::external_body]
    fn trim_start_matches_chars<'a>(&self, chars: &'a [char]) -> &str { self.trim_start_matches(chars) }
    #[verifier::external_body]
    fn trim_start_matches_fn<F>(&self, f: F) -> &str where F: FnMut(char) -> bool { self.trim_start_matches(f) }
    #[verifier::external_body]
    fn trim_start_matches_str<'a>(&self, pat: &'a str) -> &str { self.trim_start_matches(pat) }

    #[verifier::external_body]
    fn trim_end_matches_ch(&self, ch: char) -> &str { self.trim_end_matches(ch) }
    #[verifier::external_body]
    fn trim_end_matches_chars<'a>(&self, chars: &'a [char]) -> &str { self.trim_end_matches(chars) }
    #[verifier::external_body]
    fn trim_end_matches_fn<F>(&self, f: F) -> &str where F: FnMut(char) -> bool { self.trim_end_matches(f) }
    #[verifier::external_body]
    fn trim_end_matches_str<'a>(&self, pat: &'a str) -> &str { self.trim_end_matches(pat) }

    #[verifier::external_body]
    fn strip_prefix_ch<'a>(&'a self, ch: char) -> Option<&'a str> { self.strip_prefix(ch) }
    #[verifier::external_body]
    fn strip_prefix_chars<'a, 'b>(&'a self, chars: &'b [char]) -> Option<&'a str> { self.strip_prefix(chars) }
    #[verifier::external_body]
    fn strip_prefix_fn<'a, F>(&'a self, f: F) -> Option<&'a str> where F: FnMut(char) -> bool { self.strip_prefix(f) }
    #[verifier::external_body]
    fn strip_prefix_str<'a, 'b>(&'a self, pat: &'b str) -> Option<&'a str> { self.strip_prefix(pat) }

    #[verifier::external_body]
    fn strip_suffix_ch<'a>(&'a self, ch: char) -> Option<&'a str> { self.strip_suffix(ch) }
    #[verifier::external_body]
    fn strip_suffix_chars<'a, 'b>(&'a self, chars: &'b [char]) -> Option<&'a str> { self.strip_suffix(chars) }
    #[verifier::external_body]
    fn strip_suffix_fn<'a, F>(&'a self, f: F) -> Option<&'a str> where F: FnMut(char) -> bool { self.strip_suffix(f) }
    #[verifier::external_body]
    fn strip_suffix_str<'a, 'b>(&'a self, pat: &'b str) -> Option<&'a str> { self.strip_suffix(pat) }
}


} // verus!
