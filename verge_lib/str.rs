//! Specifications and lemmas for strings, extending `vstd`'s support.
//!
//! ### Bytes or Chars
//! There are two typical ways to view a Rust string (`&str` or `String`): as bytes (`u8`), or as `char`s.
//! Each string is in fact stored as a raw `&[u8]`, so the byte representation is more true to the 
//! memory layout. 
//! However, Rust strings are by construction valid UTF-8, and not all byte sequences satisfy this. 
//! Given that this invariant is rooted in Rust by the type safety of `char` and `str`, Verus
//! views strings as `Seq<char>`, and this module follows that paradigm. 
//!
//! Conversion between the byte- and char-views is done via `vstd::utf8` methods, particularly
//! `encode_utf8()` (`Seq<char>` to `Seq<u8>`) and `decode_utf8()` (`Seq<u8>` to `Seq<char>`). 
//! However, directly using these as `open` specs can slow verification; hence they are wrapped 
//! in `as_bytes()` and `as_str()` with `#[verifier::opaque]`. Use lemmas provided by Verge for 
//! lightweight common-case reasoning, or `reveal` and use `vstd::utf8` if needed.
//!
//! ### `Deref` Methods
//! In native Rust, `String` inherits all `&self` methods from `str` because it implements `Deref<Target=str>`.
//! However, `Deref` coercion may not be automatically done in Verus, so an explicit `as_str()` is 
//! sometimes needed to call these methods (e.g., `s.as_str().is_char_boundary()`).

#![allow(unused)]
use vstd::prelude::*;
use vstd::math::{min, max};
use vstd::assert_by_contradiction;
use vstd::utf8::*;
use vstd::slice::*;
use vstd::std_specs::core::{IndexSpec, IndexSpecImpl};
use vstd::std_specs::iter::FromIteratorSpec; 
use crate::seq::*;
use crate::error::ErrorSpec;

use std::str::{
    Utf8Error, pattern::{Pattern, Searcher, ReverseSearcher, DoubleEndedSearcher},
};
use std::slice::SliceIndex;
use std::ops::{Range, Index, IndexMut};
use std::rc::Rc;

verus! {

pub mod chars;
pub mod fmt;
pub mod ord;
pub mod iter;
pub mod string;
pub mod parse;
pub mod pattern;

pub use chars::*;
pub use fmt::*;
pub use ord::*;
pub use iter::*;
pub use string::*;
pub use parse::*;
pub use pattern::*;

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExUtf8Error(Utf8Error);

/// This trait allows viewing a type as a string (sequence of `char`s).
pub trait StrView {

    /// Casts `self` as a `char` sequence.
    spec fn as_str(self) -> Seq<char>
        recommends self.is_utf8(),
    ;

    /// Predicate for asserting `self` can be viewed as a valid UTF-8 string.
    spec fn is_utf8(self) -> bool;

    /// Predicate for asserting `self` can be viewed as a valid ASCII string.
    spec fn is_ascii(self) -> bool;
}

impl StrView for Seq<u8> {

    open spec fn as_str(self) -> Seq<char> 
        { decode_utf8(self) }

    open spec fn is_utf8(self) -> bool
        { valid_utf8(self) }

    open spec fn is_ascii(self) -> bool {
        forall |i: int| #![auto] 0 <= i < self.len() ==> self[i] <= 0x7f
    }
}

/// This trait allows viewing a type as a byte sequence.
pub trait BytesView {
    /// Casts `self` as a `u8` sequence.
    spec fn as_bytes(self) -> Seq<u8>;

    /// Predicate for asserting `self` can be viewed as a valid sequence of ASCII bytes.
    spec fn is_ascii(self) -> bool;
}

impl BytesView for Seq<char> {

    open spec fn as_bytes(self) -> Seq<u8> 
        { encode_utf8(self) }

    open spec fn is_ascii(self) -> bool {
        forall |i: int| 0 <= i < self.len() ==> 0 <= #[trigger] self[i] <= 0x7f
    }
}

/// Full string lemmas.
#[verifier::broadcast_use_by_default_when_this_crate_is_imported]
pub broadcast group group_str_axioms {
    group_str_view,
    group_str_traits,
    group_str_ordering,
}

/// Lightweight lemmas for string views.
/// 
/// Note that by default, `as_bytes()` and `as_str()` are fully specified for ASCII strings only 
/// (in which case the specs are verification-friendly). For non-ASCII UTF-8 strings, `vstd::utf8` 
/// can be used, but the full UTF8 spec might be expensive to reason about.
pub broadcast group group_str_view {
    lemma_subrange_self,
    lemma_str_lower_lift,
    lemma_bytes_lift_lower,
    lemma_bytes_concat_lift,
    lemma_str_concat_lower,
    lemma_str_is_utf8,
    lemma_ascii_is_utf8,
    lemma_ascii_bytes_as_str,
    lemma_ascii_str_as_bytes,
    lemma_char_boundary_iff_utf8,
}

/// Linking lemmas for string trait methods.
pub broadcast group group_str_traits {
    lemma_str_range_index_requires,
    lemma_str_range_index_ensures,
    lemma_str_range_index_mut_ensures,
    lemma_boxed_str_from_iter_char,
    lemma_boxed_str_from_iter_ref_char,
    lemma_boxed_str_from_iter_str,
}

pub broadcast proof fn lemma_subrange_self<T>(s: Seq<T>)
    ensures (#[trigger] s.subrange(0, s.len() as int)) =~= s {}

/// Proof that lowering a string as bytes then lifting back is no-op.
pub broadcast proof fn lemma_str_lower_lift(s: Seq<char>)
    ensures #[trigger] s.as_bytes().as_str() =~= s,
{
    encode_utf8_decode_utf8(s);
}

/// Proof that lifting a UTF-8 byte sequence then lowering is no-op.
pub broadcast proof fn lemma_bytes_lift_lower(bytes: Seq<u8>)
    requires
        bytes.is_utf8(),
    ensures 
        #[trigger] bytes.as_str().as_bytes() =~= bytes,
{
    decode_utf8_encode_utf8(bytes);
}

/// Proof that concatenation of UTF-8 byte sequences can be lifted as concatenation of strings.
pub broadcast proof fn lemma_bytes_concat_lift(b1: Seq<u8>, b2: Seq<u8>)
    requires
        b1.is_utf8() && b2.is_utf8(),
    ensures
        #![trigger b1 + b2]
        (b1 + b2).is_utf8(),
        (b1 + b2).as_str() =~= b1.as_str() + b2.as_str(),
{
    assert((b1 + b2).is_utf8()) by { valid_utf8_concat(b1, b2) };
    assert(is_char_boundary(b1 + b2, b1.len() as int)) by {
        if b2.len() == 0 {
            assert(b1 + b2 == b1);
            is_char_boundary_start_end_of_seq(b1);
        }
        else {
            assert((b1 + b2)[b1.len() as int] == b2[0]);
            is_char_boundary_iff_is_leading_byte(b1 + b2, b1.len() as int);
        }
    };
    assert(b1 == (b1 + b2).subrange(0, b1.len() as int));
    assert(b2 == (b1 + b2).subrange(b1.len() as int, (b1 + b2).len() as int));
    decode_utf8_split(b1 + b2, b1.len() as int);
}

/// Proof that concatenation of strings can be lowered as concatenation of UTF-8 byte sequences.
pub broadcast proof fn lemma_str_concat_lower(s1: Seq<char>, s2: Seq<char>)
    ensures
        #[trigger] (s1 + s2).as_bytes() =~= s1.as_bytes() + s2.as_bytes(),
    decreases
        s1.len(),
{
    if s1.len() == 0 {
        assert(s1 + s2 == s2);
    } else {
        assert((s1 + s2).drop_first() =~= s1.drop_first() + s2);
        assert((s1 + s2)[0] =~= s1[0]);
        assert((s1 + s2).as_bytes() == encode_scalar((s1 + s2)[0] as u32) + (s1.drop_first() + s2).as_bytes());
        lemma_str_concat_lower(s1.drop_first(), s2);
    }
}

/// Proof that any string can be viewed as a valid UTF-8 byte sequence.
pub broadcast proof fn lemma_str_is_utf8(s: Seq<char>)
    ensures (#[trigger] s.as_bytes()).is_utf8(),
{
    encode_utf8_valid_utf8(s);
}

/// Proof that any valid ASCII byte sequence is also UTF-8.
pub broadcast proof fn lemma_ascii_is_utf8(bytes: Seq<u8>)
    requires
        bytes.is_ascii(),
    ensures
        #[trigger] bytes.is_utf8(),
    decreases
        bytes.len(),
{
    if bytes.len() == 0 {}
    else {
        assert(valid_first_scalar(bytes));
        assert(length_of_first_scalar(bytes) == 1);
        lemma_ascii_is_utf8(pop_first_scalar(bytes));
    }
}

/// Proof that conversion of ASCII bytes into strings is fully specified.
pub broadcast proof fn lemma_ascii_bytes_as_str(bytes: Seq<u8>)
    requires
        bytes.is_ascii(),
    ensures 
        (#[trigger] bytes.as_str()) =~= Seq::new(bytes.len(), |i: int| bytes[i] as char),
    decreases
        bytes.len(),
{
    if bytes.len() == 0 {}
    else {
        assert(valid_first_scalar(bytes));
        assert(length_of_first_scalar(bytes) == 1);
        assert(pop_first_scalar(bytes) == bytes.drop_first());
        lemma_ascii_is_utf8(bytes.drop_first());
        let b = bytes[0]; assert(b & 0x7f == b) by(bit_vector) requires b <= 0x7f;
        lemma_ascii_bytes_as_str(pop_first_scalar(bytes));
    }
}

/// Proof that conversion of ASCII strings into bytes is fully specified.
pub broadcast proof fn lemma_ascii_str_as_bytes(s: Seq<char>)
    requires
        s.is_ascii(),
    ensures 
        (#[trigger] s.as_bytes()) =~= Seq::new(s.len(), |i: int| s[i] as u8),
{
    is_ascii_chars_encode_utf8(s);
}

/// Proof that `index` is at char boundary in `bytes` iff the splits are UTF-8 byte sequences.
pub broadcast proof fn lemma_char_boundary_iff_utf8(bytes: Seq<u8>, index: int)
    requires
        bytes.is_utf8(),
        0 <= index <= bytes.len(),
    ensures 
        #![trigger is_char_boundary(bytes, index)] 
        is_char_boundary(bytes, index) <==> bytes.take(index).is_utf8(),
        is_char_boundary(bytes, index) <==> bytes.skip(index).is_utf8(),
{
    if is_char_boundary(bytes, index) {
        valid_utf8_split(bytes, index);
        assert(bytes.take(index).is_utf8());
        assert(bytes.skip(index).is_utf8());
    } 
    if bytes.take(index).is_utf8() {
        assert_by_contradiction!(bytes.skip(index).is_utf8(), {
            partial_valid_partial_invalid_utf8(bytes, index);
        });
    }
    if bytes.skip(index).is_utf8() {
        if index < bytes.len() {
            is_char_boundary_iff_is_leading_byte(bytes, index);
        } else {
            is_char_boundary_start_end_of_seq(bytes);
        }
    }
}

/// Enable `std::str::from_utf8`.
pub assume_specification [ str::from_utf8 ] (v: &[u8]) -> (ret: Result<&str, Utf8Error>)
    ensures 
        ({
            match ret {
                Ok(s) => v@.is_utf8() && s@.as_bytes() =~= v@,
                Err(e) => {
                    &&& !v@.is_utf8() 
                    &&& e.is_str_utf8_error()
                },
            }
        }),
    no_unwind
;

/// Enable `str::floor_char_boundary`.
pub assume_specification [ str::floor_char_boundary ] (s: &str, index: usize) -> (ret: usize)
    ensures
        ret <= s@.as_bytes().len() && ret <= index,
        is_char_boundary(s@.as_bytes(), ret as int),
        !exists|i: int| ret < i <= index && #[trigger] is_char_boundary(s@.as_bytes(), i),
    no_unwind
;

/// Enable `str::ceil_char_boundary`.
pub assume_specification [ str::ceil_char_boundary ] (s: &str, index: usize) -> (ret: usize)
    ensures
        ret <= s@.as_bytes().len() && ret >= min(index as int, s@.as_bytes().len() as int),
        s@.as_bytes().take(ret as int).is_utf8(),
        !exists|i: int| index <= i < ret && #[trigger] is_char_boundary(s@.as_bytes(), i),
    no_unwind
;

// -- `Index` and the `get` variants; not that `IndexMut` is currently *not* supported.

// TODO: we can now actually support indexes other than `Range<usize>`;
// consider move these into a first-class `index.rs`

pub open spec fn str_range_index_requires(s: &str, start: int, end: int) -> bool {
    &&& 0 <= start <= end <= s@.as_bytes().len()
    &&& is_char_boundary(s@.as_bytes(), start)
    &&& is_char_boundary(s@.as_bytes(), end)
}

pub open spec fn str_range_index_ensures<'a>(
    s: &'a str, start: int, end: int, r: &'a str,
) -> bool 
    recommends 
        str_range_index_requires(s, start, end),
{ 
    r@.as_bytes() == s@.as_bytes().subrange(start, end)
}

#[verifier::prophetic]
pub open spec fn str_range_index_mut_ensures<'a>(
    s: &'a mut str, start: int, end: int, r: &'a mut str,
) -> bool 
    recommends 
        str_range_index_requires(s, start, end),
{ 
    &&& r@.as_bytes() == s@.as_bytes().subrange(start, end)
    &&& final(s)@.as_bytes() == 
            s@.as_bytes().take(start)
            + final(r)@.as_bytes()
            + s@.as_bytes().skip(end)
}

pub uninterp spec fn str_index_ensures<'a, I>(s: &'a str, i: I, r: &'a <I as SliceIndex<str>>::Output) -> bool
    where I: SliceIndex<str>;
pub uninterp spec fn str_index_mut_ensures<'a, I>(s: &'a mut str, i: I, r: &'a mut <I as SliceIndex<str>>::Output) -> bool
    where I: SliceIndex<str>;

// XXX: these proofs are workarounds because Verge cannot implement `SliceIndexSpec` and `IndexSpec`

/// Proof that links `str_range_index_requires` with `IndexSpec::index_req`.
#[verifier::external_body]
pub broadcast axiom fn lemma_str_range_index_requires(s: &str, i: Range<usize>)
    ensures
        (#[trigger] s.index_req(&i)) 
            <==> str_range_index_requires(s, i.start as int, i.end as int)
;

/// Proof that links `str_range_index_ensures` spec with `str_index_ensures`.
#[verifier::external_body]
pub broadcast axiom fn lemma_str_range_index_ensures<'a>(s: &'a str, i: Range<usize>, r: &'a str)
    ensures
        (#[trigger] str_index_ensures(s, i, r)) 
            <==> str_range_index_ensures(s, i.start as int, i.end as int, r)
;

/// Proof that links `str_range_index_mut_ensures` spec with `str_index_mut_ensures`.
#[verifier::external_body]
pub broadcast axiom fn lemma_str_range_index_mut_ensures<'a>(s: &'a mut str, i: Range<usize>, r: &'a mut str)
    ensures
        (#[trigger] str_index_mut_ensures(s, i, r)) 
            <==> str_range_index_mut_ensures(s, i.start as int, i.end as int, r)
;

// actual specs

/// Enable `<str as Index<I>>::index`. 
/// 
/// The `requires` clause is implicit here (from the `IndexSpec` trait).
pub assume_specification<I: SliceIndex<str>>[ <str as Index<I>>::index ] (
    s: &str, i: I
) -> (ret: &<I as SliceIndex<str>>::Output)
    ensures
        str_index_ensures(s, i, ret),
;

/// Enable `str::get`. 
pub assume_specification<I: SliceIndex<str>>[ str::get ] (
    s: &str, i: I,
) -> (ret: Option<&<I as SliceIndex<str>>::Output>)
    ensures
        ({
            match ret {
                Some(o) => s.index_req(&i) && str_index_ensures(s, i, o),
                None => !s.index_req(&i),
            }
        }),
;

/// Enable `str::get_unchecked`; note that this is no longer unsafe.
pub assume_specification<I: SliceIndex<str>>[ str::get_unchecked ] (
    s: &str, i: I,
) -> (ret: &<I as SliceIndex<str>>::Output)
    requires
        s.index_req(&i),
    ensures
        str_index_ensures(s, i, ret),
;

/// Enable `str::get_mut`. 
pub assume_specification<I: SliceIndex<str>>[ str::get_mut ] (
    s: &mut str, i: I,
) -> (ret: Option<&mut <I as SliceIndex<str>>::Output>)
    ensures
        ({
            match ret {
                Some(o) => old(s).index_req(&i) && str_index_mut_ensures(s, i, o),
                None => !old(s).index_req(&i) && final(s)@ == old(s)@
            }
        }),
;

/// Enable `str::get_unchecked_mut`; note that this is no longer unsafe. 
pub assume_specification<I: SliceIndex<str>>[ str::get_unchecked_mut ] (
    s: &mut str, i: I,
) -> (ret: &mut <I as SliceIndex<str>>::Output)
    requires
        s.index_req(&i),
    ensures
        str_index_mut_ensures(s, i, ret),
;

// -- end of `Index`

/// Enable `str::split_at_mut`.
pub assume_specification[ str::split_at_mut ](s: &mut str, mid: usize) -> (ret: (&mut str, &mut str))
    requires
        is_char_boundary(s@.as_bytes(), mid as int),
    ensures
        ret.0@.as_bytes() =~= old(s)@.as_bytes().take(mid as int),
        ret.1@.as_bytes() =~= old(s)@.as_bytes().skip(mid as int),
        final(s)@.as_bytes() == final(ret.0)@.as_bytes() + final(ret.1)@.as_bytes(),
    no_unwind
;

/// Enable `str::split_at_checked`.
pub assume_specification[ str::split_at_checked ](s: &str, mid: usize) -> (ret: Option<(&str, &str)>)
    ensures
        ({
            match ret {
                Some((head, tail)) => {
                    &&& 0 <= mid <= s@.as_bytes().len()
                    &&& is_char_boundary(s@.as_bytes(), mid as int)
                    &&& head@.as_bytes() =~= s@.as_bytes().take(mid as int)
                    &&& tail@.as_bytes() =~= s@.as_bytes().skip(mid as int)
                },
                None => mid > s@.as_bytes().len() || !is_char_boundary(s@.as_bytes(), mid as int),
            }
        }),
    no_unwind
;

/// Enable `str::split_at_mut_checked`.
pub assume_specification[ str::split_at_mut_checked ](s: &mut str, mid: usize) -> (ret: Option<(&mut str, &mut str)>)
    ensures
        ({
            match ret {
                Some((head, tail)) => {
                    &&& 0 <= mid <= old(s)@.as_bytes().len()
                    &&& is_char_boundary(old(s)@.as_bytes(), mid as int)
                    &&& head@.as_bytes() =~= old(s)@.as_bytes().take(mid as int)
                    &&& tail@.as_bytes() =~= old(s)@.as_bytes().skip(mid as int)
                    &&& final(s)@.as_bytes() == final(head)@.as_bytes() + final(tail)@.as_bytes()
                },
                None => {
                    &&& mid > old(s)@.as_bytes().len() || !is_char_boundary(old(s)@.as_bytes(), mid as int)
                    &&& final(s)@ == old(s)@
                },
            }
        }),
    no_unwind
;

/// Enable `str::contains`.
pub assume_specification<P: Pattern>[ str::contains ](s: &str, pat: P) -> (ret: bool)
    ensures
        str_contains_post(s@, pat, ret),
;

/// Enable `str::starts_with`.
pub assume_specification<P: Pattern>[ str::starts_with ](s: &str, pat: P) -> (ret: bool)
    ensures
        str_starts_with_post(s@, pat, ret),
;

/// Enable `str::ends_with`.
pub assume_specification<P>[ str::ends_with ](s: &str, pat: P) -> (ret: bool)
    where 
        P: Pattern,
        for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ensures
        str_ends_with_post(s@, pat, ret),
;

/// Enable `str::find`.
pub assume_specification<P: Pattern>[ str::find ](s: &str, pat: P) -> (ret: Option<usize>)
    ensures
        str_find_post(s@, pat, ret),
;

/// Enable `str::rfind`.
pub assume_specification<P>[ str::rfind ](s: &str, pat: P) -> (ret: Option<usize>)
    where 
        P: Pattern,
        for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ensures
        str_rfind_post(s@, pat, ret),
;

/// Enable `str::split_once`.
pub assume_specification<P: Pattern>[ str::split_once ](s: &str, delimiter: P) -> (ret: Option<(&str, &str)>)
    ensures
        str_split_once_post(s@, delimiter, ret),
;

/// Enable `str::rsplit_once`.
pub assume_specification<P>[ str::rsplit_once ](s: &str, delimiter: P) -> (ret: Option<(&str, &str)>)
    where 
        P: Pattern,
        for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ensures
        str_rsplit_once_post(s@, delimiter, ret),
;

/// Enables `str::trim`.
pub assume_specification[ str::trim ](s: &str) -> (ret: &str)
    ensures
        ret@.is_subrange_of(s@),
        ret@.len() > 0 ==> 
            !ret@.first().is_whitespace() && !ret@.last().is_whitespace(),
;

/// Enables `str::trim_start`.
pub assume_specification[ str::trim_start ](s: &str) -> (ret: &str)
    ensures
        ret@.is_suffix_of(s@),
        ret@.len() > 0 ==> !ret@.first().is_whitespace(),
;

/// Enables `str::trim_end`.
pub assume_specification[ str::trim_end ](s: &str) -> (ret: &str)
    ensures
        ret@.is_prefix_of(s@),
        ret@.len() > 0 ==> !ret@.last().is_whitespace(),
;

/// Enables `str::trim_matches`.
pub assume_specification<P>[ str::trim_matches ](s: &str, pat: P) -> (ret: &str)
    where 
        P: Pattern,
        for<'x> <P as Pattern>::Searcher<'x>: DoubleEndedSearcher<'x>,
    ensures
        str_trim_matches_post(s@, pat, ret@),
;

/// Enables `str::trim_start_matches`.
pub assume_specification<P: Pattern>[ str::trim_start_matches ](s: &str, pat: P) -> (ret: &str)
    ensures
        str_trim_start_matches_post(s@, pat, ret@),
;

/// Enables `str::trim_end_matches`.
pub assume_specification<P>[ str::trim_end_matches ](s: &str, pat: P) -> (ret: &str)
    where 
        P: Pattern,
        for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ensures
        str_trim_end_matches_post(s@, pat, ret@),
;

/// Enables `str::strip_prefix`.
pub assume_specification<P: Pattern>[ str::strip_prefix ](s: &str, pat: P) -> (ret: Option<&str>)
    ensures
        str_strip_prefix_post(s@, pat, ret),
;

/// Enables `str::strip_suffix`.
pub assume_specification<P>[ str::strip_suffix ](s: &str, pat: P) -> (ret: Option<&str>)
    where 
        P: Pattern,
        for<'x> <P as Pattern>::Searcher<'x>: ReverseSearcher<'x>,
    ensures
        str_strip_suffix_post(s@, pat, ret),
;

/// Enable `str::to_ascii_lowercase`.
pub assume_specification [ str::to_ascii_lowercase ] (s: &str) -> (ret: String)
    ensures
        ret@ =~= Seq::<char>::new(
            s@.len(), |i: int| s@[i].to_ascii_lowercase()),
;

/// Enable `str::to_ascii_uppercase`.
pub assume_specification [ str::to_ascii_uppercase ] (s: &str) -> (ret: String)
    ensures
        ret@ =~= Seq::<char>::new(
            s@.len(), |i: int|  s@[i].to_ascii_uppercase())
;

/// Enable `str::make_ascii_lowercase`.
pub assume_specification [ str::make_ascii_lowercase ] (s: &mut str)
    ensures
        final(s)@ =~= Seq::<char>::new(
            old(s)@.len(), |i: int| old(s)@[i].to_ascii_lowercase()),
    no_unwind
;

/// Enable `str::make_ascii_uppercase`.
pub assume_specification [ str::make_ascii_uppercase ] (s: &mut str)
    ensures
        final(s)@ =~= Seq::<char>::new(
            old(s)@.len(), |i: int| old(s)@[i].to_ascii_uppercase()),
    no_unwind
;

/// Enable `str::trim_ascii_start`.
pub assume_specification [ str::trim_ascii_start ] (s: &str) -> (ret: &str)
    ensures
        ret@.is_suffix_of(s@),
        forall |i: int| 0 <= i < s@.len() - ret@.len() ==> #[trigger] s@[i].is_ascii_whitespace(),
        ret@.len() > 0 ==> !ret@.first().is_ascii_whitespace(),
    no_unwind
;

/// Enable `str::trim_ascii_end`.
pub assume_specification [ str::trim_ascii_end ] (s: &str) -> (ret: &str)
    ensures
        ret@.is_prefix_of(s@),
        forall |i: int| ret@.len() <= i < s@.len() ==> #[trigger] s@[i].is_ascii_whitespace(),
        ret@.len() > 0 ==> !ret@.last().is_ascii_whitespace(),
    no_unwind
;

/// Enable `str::trim_ascii`.
pub assume_specification [ str::trim_ascii ] (s: &str) -> (ret: &str)
    ensures
        exists |start: int| {
            &&& 0 <= start <= s@.len() - ret@.len()
            &&& #[trigger] s@.subrange(start, start + ret@.len()) =~= ret@
            &&& forall |i: int| 0 <= i < start ==> #[trigger] s@[i].is_ascii_whitespace()
            &&& forall |i: int| start + ret@.len() <= i < s@.len() ==> #[trigger] s@[i].is_ascii_whitespace()
        },
        ret@.len() > 0 ==> !ret@.first().is_ascii_whitespace() && !ret@.last().is_ascii_whitespace(),
    no_unwind
;

/// Enable `str::replace`.
pub assume_specification<P: Pattern> [ str::replace ] (s: &str, from: P, to: &str) -> (ret: String)
    ensures 
        str_replace_post(s@, from, to@, ret@),
;

/// Enable `str::replacen`.
pub assume_specification<P: Pattern> [ str::replacen ] (s: &str, from: P, to: &str, count: usize) -> (ret: String)
    ensures 
        str_replacen_post(s@, from, to@, count as nat, ret@),
;

/// Enable `str::repeat`.
pub assume_specification [ str::repeat ] (s: &str, n: usize) -> (ret: String)
    requires
        s@.as_bytes().len() * n <= usize::MAX,
    ensures 
        ret@ == Seq::new(n as nat, |i: int| s@).flatten(),
;

/// Enable `Box<str>::into_boxed_bytes`.
pub assume_specification [ str::into_boxed_bytes ] (s: Box<str>) -> (ret: Box<[u8]>)
    ensures 
        ret@ == s@.as_bytes(),
    no_unwind
;

/// Enable `Box<str>::into_string`.
pub assume_specification [ str::into_string ] (s: Box<str>) -> (ret: String)
    ensures 
        ret@ == s@,
    no_unwind
;

/// Additional methods on `str`. 
pub trait StrAdditionalFns {
    fn from_utf8_verified(v: &[u8]) -> &Self
        requires 
            v@.is_utf8(),
        no_unwind;
    fn from_utf8_verified_mut(v: &mut [u8]) -> &mut Self
        requires 
            v@.is_utf8(),
        no_unwind;
}

impl StrAdditionalFns for str {
    /// Enable `str::from_utf8_verified` which wraps `str::from_utf8_unchecked`; note that 
    /// this is no longer `unsafe`.
    #[verifier::external_body]
    fn from_utf8_verified(v: &[u8]) -> (ret: &Self) 
        ensures
            ret@.as_bytes() =~= v@,
    {
        unsafe { str::from_utf8_unchecked(v) }
    }

    /// Enable `str::from_utf8_verified_mut` which wraps `str::from_utf8_unchecked_mut`; note that 
    /// this is no longer `unsafe`.
    #[verifier::external_body]
    fn from_utf8_verified_mut(v: &mut [u8]) -> (ret: &mut Self)
        ensures
            final(ret)@.as_bytes() =~= final(v)@,
    {
        unsafe { str::from_utf8_unchecked_mut(v) }
    }
}

// conversion traits

/// Enable `<str as AsRef<[u8]>>::as_ref`.
pub assume_specification [ <str as AsRef<[u8]>>::as_ref ] (s: &str) -> (ret: &[u8])
    ensures 
        ret@ == s@.as_bytes(),
    no_unwind
;

/// Enable `<str as AsRef<str>>::as_ref`.
pub assume_specification [ <str as AsRef<str>>::as_ref ] (s: &str) -> (ret: &str)
    ensures 
        ret@ == s@,
    no_unwind
;

/// Enable `<String as AsMut<str>>::as_mut`.
pub assume_specification [ <String as AsMut<str>>::as_mut ] (s: &mut String) -> (ret: &mut str)
    ensures 
        ret@ == old(s)@,
        final(ret)@ == final(s)@,
    no_unwind
;

/// Enable `<str as AsMut<str>>::as_mut`.
pub assume_specification [ <str as AsMut<str>>::as_mut ] (s: &mut str) -> (ret: &mut str)
    ensures 
        ret@ == old(s)@,
        final(ret)@ == final(s)@,
    no_unwind
;

/// Enable `<Rc<str> as From<&str>>::from`.
pub assume_specification<'_0> [ <Rc<str> as From<&str>>::from ] (s: &str) -> (ret: Rc<str>)
    ensures 
        ret@ == s@,
;

/// Enable `<String as From<&str>>::from`.
pub assume_specification<'_0> [ <String as From<&str>>::from ] (s: &str) -> (ret: String)
    ensures 
        ret@ == s@,
;

/// Enable `<Vec<u8> as From<&str>>::from`.
pub assume_specification<'_0> [ <Vec<u8> as From<&str>>::from ] (s: &str) -> (ret: Vec<u8>)
    ensures 
        ret@ == s@.as_bytes(),
;

/// Enable `<Box<str> as From<String>>::from`.
pub assume_specification [ <Box<str> as From<String>>::from ] (s: String) -> (ret: Box<str>)
    ensures 
        ret@ == s@,
;

/// Enable `<Box<str> as FromIterator<char>>::from_iter`. 
///
/// The post-condition is implicit here (`FromIteratorSpec::from_iter_ensures`).
pub assume_specification<T> [ <Box<str> as FromIterator<char>>::from_iter ] (iter: T) -> (ret: Box<str>)
    where
        T: IntoIterator<Item = char>, 
;
// Proof that links `from_iter_ensures` with the actual spec.
pub broadcast axiom fn lemma_boxed_str_from_iter_char(iter: Seq<char>, s: Box<str>)
    requires
        #[trigger] <Box<str> as FromIteratorSpec<char>>::from_iter_ensures(iter, s),
    ensures
        s@ == iter,
;

/// Enable `<Box<str> as FromIterator<&'a char>>::from_iter`. 
///
/// The post-condition is implicit here (`FromIteratorSpec::from_iter_ensures`).
pub assume_specification<'a, T> [ <Box<str> as FromIterator<&'a char>>::from_iter ] (iter: T) -> (ret: Box<str>)
    where
        T: IntoIterator<Item = &'a char>, 
;
// Proof that links `from_iter_ensures` with the actual spec.
pub broadcast axiom fn lemma_boxed_str_from_iter_ref_char<'a>(iter: Seq<&'a char>, s: Box<str>)
    requires
        #[trigger] <Box<str> as FromIteratorSpec<&'a char>>::from_iter_ensures(iter, s),
    ensures
        s@ == iter.unref(),
;

/// Enable `<Box<str> as FromIterator<&'a str>>::from_iter`. 
///
/// The post-condition is implicit here (`FromIteratorSpec::from_iter_ensures`).
pub assume_specification<'a, T> [ <Box<str> as FromIterator<&'a str>>::from_iter ] (iter: T) -> (ret: Box<str>)
    where
        T: IntoIterator<Item = &'a str>, 
;
// Proof that links `from_iter_ensures` with the actual spec.
pub broadcast axiom fn lemma_boxed_str_from_iter_str<'a>(iter: Seq<&'a str>, s: Box<str>)
    requires
        #[trigger] <Box<str> as FromIteratorSpec<&'a str>>::from_iter_ensures(iter, s),
    ensures
        s@ == iter.deep_view().flatten(),
;

mod tests {
    use super::*;

    fn test_empty() {
        broadcast use group_str_axioms;
        let s = String::new();
        assert(s@.as_bytes().is_utf8());
        assert(Seq::<u8>::empty().is_utf8());
    }

    fn test_string_literal() -> (ret: String) 
        ensures ret@ =~= "abcd"@,
    {
        broadcast use group_str_axioms;
        proof { 
            reveal_strlit("abd");
            reveal_strlit("c");
            reveal_strlit("abcd");
        }

        let mut s = String::from_str("abd");
        s.insert_str(2, "c");
        s
    }

    fn test_string_truncate(s: &mut String) 
        requires 
            old(s).is_ascii(),
            old(s)@.len() > 1024,
    {
        broadcast use group_str_axioms;
        s.truncate(512);
    }

    fn test_utf8(s: &mut String) {
        broadcast use group_str_axioms;

        s.insert_str(0, "头");
        s.insert_str(s.len(), "尾");
        assert(s@ == "头"@ + old(s)@ + "尾"@);

        let ghost hlen = "头"@.as_bytes().len();
        let ghost tlen = "尾"@.as_bytes().len();
        let ghost len = s@.as_bytes().len();
        assert(s@.as_bytes().subrange(hlen as int, (len - tlen) as int) == old(s)@.as_bytes());
    }

    fn test_trim_ascii() {
        broadcast use group_str_axioms;

        proof { 
            reveal_strlit("  abc  ");
            reveal_strlit("  abc");
            reveal_strlit("abc  ");
            reveal_strlit("abc");
        }

        let s = "  abc  ";
        let x = "abc  ";
        let y = "  abc";
        let z = "abc";
        let trim_start = s.trim_ascii_start();
        let trim_end = s.trim_ascii_end();
        assert(trim_start@ =~= x@) by {
            let ghost start = s@.len() - trim_start@.len();
            assert(trim_start@ =~= s@.skip(start));
            assert_by_contradiction!(start <= 2, {
                assert(start > 2);
                // assert(s@[2] == 'a');
                assert(s@[2].is_ascii_whitespace());
            });
            assert_by_contradiction!(start >= 2, {
                assert(start < 2);
                assert(s@[start].is_ascii_whitespace());
            });
            assert(start == 2);
            assert(trim_start@ =~= s@.skip(2));
            assert(x@ =~= s@.skip(2));
        }
        assert(trim_end@ =~= y@) by {
            let ghost end = trim_end@.len();
            assert_by_contradiction!(end >= 5, {
                // assert(s@[4] == 'c');
                assert(s@[4].is_ascii_whitespace());
            });
            assert_by_contradiction!(end <= 5, {
                assert(end > 5);
                assert(s@[end as int].is_ascii_whitespace());
            });
            assert(end == 5);
            assert(trim_end@ =~= s@.take(5));
            assert(y@ =~= s@.take(5));
        }
        let s1 = s.trim_ascii_start().trim_ascii_end();
        let s2 = s.trim_ascii_end().trim_ascii_start();
        let s3 = s.trim_ascii();
        assert(s1@ =~= z@) by {
            let ghost end = s1@.len();
            assert(s1@ =~= trim_start@.take(end as int));
            assert_by_contradiction!(end >= 3, {
                assert(end < 3);
                assert(trim_start@[2].is_ascii_whitespace());
            });
            assert_by_contradiction!(end <= 3, {
                assert(end > 3);
                assert(s1@[end - 1] == trim_start@[end - 1]);
                assert(trim_start@[end - 1].is_ascii_whitespace());
            });
            assert(end == 3);
            assert(s1@ =~= trim_start@.take(3));
            assert(z@ =~= trim_start@.take(3));
        }
        assert(s2@ =~= z@) by {
            let ghost start = trim_end@.len() - s2@.len();
            assert(s2@ =~= trim_end@.skip(start));
            assert_by_contradiction!(start <= 2, {
                assert(start > 2);
                assert(trim_end@[2].is_ascii_whitespace());
            });
            assert_by_contradiction!(start >= 2, {
                assert(start < 2);
                assert(trim_end@[start].is_ascii_whitespace());
            });
            assert(start == 2);
            assert(s2@ =~= trim_end@.skip(2));
            assert(z@ =~= trim_end@.skip(2));
        }
        assert(s1@ =~= s3@);
        assert(s1@ =~= s2@);
        assert(s2@ =~= s3@);
    }

    fn test_trim_ascii_order_independent(s: &str) {
        broadcast use group_str_axioms;

        let trim_start = s.trim_ascii_start();
        let trim_end = s.trim_ascii_end();
        let s1 = trim_start.trim_ascii_end();
        let s2 = trim_end.trim_ascii_start();
        let s3 = s.trim_ascii();
        assert(s1@ =~= s3@);

        let ghost start1 = s@.len() - trim_start@.len();
        let ghost end1 = start1 + s1@.len();
        let ghost start2 = trim_end@.len() - s2@.len();
        let ghost end2 = trim_end@.len() as int;

        assert(s1@ =~= s@.subrange(start1, end1));
        assert(s2@ =~= s@.subrange(start2, end2));


        proof {
            if s1@.len() == 0 {
                assert(forall |i: int| 0 <= i < s@.len() ==> #[trigger] s@[i].is_ascii_whitespace());
                assert(s2@.len() == 0);
            } else {
                assert(exists |i: int| 0 <= i < s@.len() && #[trigger] s@[i].is_ascii_whitespace() == false);
                assert(s2@.len() > 0);

                assert_by_contradiction!(start1 == start2, {
                    if start1 < start2 {
                        //   s        = [ ... | s[start1] ...  | s[start2] ... ]
                        //                    ^                ^
                        //                  start1           start2
                        //   s1       =       [ s[start1] ... ]
                        //   trim_end = [ s[0] ... ... ... ... ... ... ... ... s[end2 - 1] ]
                        //   s2       =                        [ s[start2] ... s[end2 - 1] ]
                        //
                        // Since start1 < start2, the char at `s[start1]` is still in the
                        // prefix removed by `trim_end.trim_ascii_start()`, so it must be
                        // ASCII whitespace. But the same char is also the first char of
                        // `s1`, and a nonempty `trim_ascii_start()` result cannot start
                        // with ASCII whitespace. Contradiction.
                        assert(trim_end@[start1] == s@[start1]);
                        assert(trim_end@[start1].is_ascii_whitespace()) by { assert(start1 < start2); };
                        assert(s1@.first() == s@[start1]);
                        assert(!s1@.first().is_ascii_whitespace());
                    } else {
                        assert(s@[start2].is_ascii_whitespace()) by { assert(start2 < start1); };
                        assert(s2@.first() == s@[start2]);
                        assert(!s2@.first().is_ascii_whitespace());
                    }
                });

                assert_by_contradiction!(end1 == end2, {
                    if end1 < end2 {
                        let j = end2 - 1 - start1;
                        assert(trim_start@[j] == s@[end2 - 1]);
                        assert(trim_start@[j].is_ascii_whitespace()) by { assert(end1 < end2); };
                        assert(s2@.last() == s@[end2 - 1]);
                        assert(!s2@.last().is_ascii_whitespace());
                    } else {
                        assert(s@[end1 - 1].is_ascii_whitespace()) by { assert(end1 > end2); };
                        assert(s1@.last() == s@[end1 - 1]);
                        assert(!s1@.last().is_ascii_whitespace());
                    }
                });
            }
        }
        assert(s1@ =~= s2@);
    }

    fn test_case_sensitive() {
        broadcast use group_str_axioms;
        proof { 
            reveal_strlit("ABC");
            reveal_strlit("AbC");
            reveal_strlit("abc");
        }

        let upper = "ABC";
        let lower = "abc";
        let s = "AbC";
        let mut s1 = s.to_ascii_uppercase();
        let mut s2 = s.to_ascii_lowercase();
        assert(s1@ == upper@);
        assert(s2@ == lower@);
    }

    fn test_from_utf8() {
        broadcast use group_str_axioms;
        let good = vec![65u8, 66u8, 67u8];
        let bad = vec![0xffu8];
        assert(good@.is_utf8());

        let ok = str::from_utf8(good.as_slice());
        let err = str::from_utf8(bad.as_slice());

        assert(ok.is_ok());
        match err {
            Ok(_) => assert(bad@.is_utf8()),
            Err(_) => assert(!bad@.is_utf8()),
        }
    }

    fn test_from_utf8_verified() {
        broadcast use group_str_axioms;
        let bytes = vec![97u8, 98u8, 99u8];
        assert(bytes@.is_utf8());
        let s = str::from_utf8_verified(bytes.as_slice());
        assert(s@ =~= bytes@.as_str());
    }

    fn test_str_get(s: &mut str) 
        requires
            s@.is_ascii(),
            s@.len() > 10,
    {
        broadcast use group_str_axioms;
        let s1 = s.get(0..2);
        assert(s1 is Some);
        let s2 = &s[3..4];
        let s3 = s.get_mut(5..6);
        assert(s3 is Some);
    }

    fn test_collect() {
        broadcast use group_str_axioms;
        let array = &['a', 'b', 'c'];
        let s = array.into_iter().collect::<Box<str>>();

        assert(s@.len() == 3);
    }

    // fn test_str_slice_contains_and_not_found() {
    //     broadcast use group_str_axioms;
    //     proof {
    //         reveal_strlit("abca");
    //         reveal_strlit("bca");
    //         reveal_strlit("zzz");
    //         reveal_strlit("abc");
    //     }

    //     let s = "abca";
    //     let contains_bca = s.contains_str("bca");
    //     let contains_zzz = s.contains_str("zzz");
    //     let find_zzz = s.find_str("zzz");
    //     let rfind_zzz = s.rfind_str("zzz");

    //     assert(exists|i: int|
    //         0 <= i <= s@.len() - "bca"@.len()
    //         && #[trigger] s@.subrange(i, i + "bca"@.len()) =~= "bca"@
    //     ) by {
    //         assert(s@.subrange(1, 1 + "bca"@.len() as int) =~= "bca"@);
    //     }
    //     assert(contains_bca);

    //     assert(s@.len() == 4 && s@.as_bytes().len() == 4);
    //     assert("zzz"@.len() == 3 && "zzz"@.as_bytes().len() == 3);
        
    //     assert(s@.subrange(0, 0 + "zzz"@.len() as int) =~= "abc"@);
    //     assert(s@.subrange(1, 1 + "zzz"@.len() as int) =~= "bca"@);
    //     assert(!("abc"@ =~= "zzz"@) && !("bca"@ =~= "zzz"@)) by {
    //         assert("abc"@[0] == 'a');
    //         assert("bca"@[0] == 'b');
    //         assert("zzz"@[0] == 'z');
    //     }

    //     proof {
    //         assert_by_contradiction!(!(exists|i: int|
    //             0 <= i <= s@.len() - "zzz"@.len()
    //             && #[trigger] s@.subrange(i, i + "zzz"@.len()) =~= "zzz"@
    //         ), {
    //             let i = choose|i: int|
    //                 0 <= i <= s@.len() - "zzz"@.len()
    //                 && #[trigger] s@.subrange(i, i + "zzz"@.len()) =~= "zzz"@;
    //             assert(0 <= i <= 1);
    //             let subrange = s@.subrange(i, i + "zzz"@.len());
    //             // assert(s@.subrange(i, i + "zzz"@.len()) =~= "zzz"@);
    //             assert(subrange =~= "abc"@ || subrange =~= "bca"@);
    //         });
    //     }

    //     assert(s@.as_bytes().subrange(0, 0 + "zzz"@.as_bytes().len() as int) =~= "abc"@.as_bytes());
    //     assert(s@.as_bytes().subrange(1, 1 + "zzz"@.as_bytes().len() as int) =~= "bca"@.as_bytes());
    //     assert(!("abc"@.as_bytes() =~= "zzz"@.as_bytes()) && !("bca"@.as_bytes() =~= "zzz"@.as_bytes())) by {
    //         assert("abc"@.as_bytes()[0] == 'a' as u8);
    //         assert("bca"@.as_bytes()[0] == 'b' as u8);
    //         assert("zzz"@.as_bytes()[0] == 'z' as u8);
    //     }

    //     proof {
    //         assert_by_contradiction!(!(exists|i: int|
    //             0 <= i <= s@.as_bytes().len() - "zzz"@.as_bytes().len()
    //             && #[trigger] s@.as_bytes().subrange(i, i + "zzz"@.as_bytes().len()) =~= "zzz"@.as_bytes()
    //         ), {
    //             let i = choose|i: int|
    //                 0 <= i <= s@.as_bytes().len() - "zzz"@.as_bytes().len()
    //                 && #[trigger] s@.as_bytes().subrange(i, i + "zzz"@.as_bytes().len()) =~= "zzz"@.as_bytes();
    //             assert(0 <= i <= 1);
    //             let subrange = s@.as_bytes().subrange(i, i + "zzz"@.as_bytes().len());
    //             // assert(s@.as_bytes().subrange(i, i + "zzz"@.as_bytes().len()) =~= "zzz"@.as_bytes());
    //             assert(subrange =~= "abc"@.as_bytes() || subrange =~= "bca"@.as_bytes());
    //         });
    //     }

    //     assert(!contains_zzz);
    //     assert(rfind_zzz.is_none() && find_zzz.is_none());
    // }

    // fn test_str_slice_find_rfind() {
    //     broadcast use group_str_axioms;
    //     proof {
    //         reveal_strlit("aba");
    //         reveal_strlit("a");
    //     }

    //     let s = "aba";
    //     let found = s.find_str("a");
    //     let rfound = s.rfind_str("a");
    //     assert(found == Some(0usize)) by {
    //         match found {
    //             Some(idx) => {
    //                 let i = idx as int;
    //                 assert(0 <= i <= s@.as_bytes().len() - "a"@.as_bytes().len());
    //                 assert(s@.as_bytes().subrange(i, i + "a"@.as_bytes().len()) =~= "a"@.as_bytes());
    //                 assert_by_contradiction!(i <= 0, {
    //                     assert(s@.as_bytes().subrange(0, 0 + "a"@.as_bytes().len() as int) =~= "a"@.as_bytes());
    //                 })
    //             }
    //             None => {}
    //         }
    //     }
    //     assert(rfound == Some(2usize)) by {
    //         match rfound {
    //             Some(idx) => {
    //                 let i = idx as int;
    //                 assert(0 <= i <= s@.as_bytes().len() - "a"@.as_bytes().len());
    //                 assert(s@.as_bytes().subrange(i, i + "a"@.as_bytes().len()) =~= "a"@.as_bytes());
    //                 assert_by_contradiction!(!(i < 2), {
    //                     assert(s@.as_bytes().subrange(2, 2 + "a"@.as_bytes().len() as int) =~= "a"@.as_bytes());
    //                 })
    //             }
    //             None => {}
    //         }
    //     }
    // }

    // fn test_str_slice_starts_with() {
    //     broadcast use group_str_axioms;
    //     proof {
    //         reveal_strlit("abcabc");
    //         reveal_strlit("abc");
    //         reveal_strlit("bca");
    //     }

    //     let s = "abcabc";
    //     let starts_with_abc = s.starts_with_str("abc");
    //     let starts_with_bca = s.starts_with_str("bca");

    //     assert(starts_with_abc == "abc"@.is_prefix_of(s@));
    //     assert(starts_with_bca == "bca"@.is_prefix_of(s@));
    //     assert(starts_with_abc);
    //     assert(!"bca"@.is_prefix_of(s@)) by {
    //         assert("bca"@[0] == 'b');
    //         assert(s@[0] == 'a');
    //     }
    //     assert(!starts_with_bca);
    // }

    // fn test_str_slice_ends_with() {
    //     broadcast use group_str_axioms;
    //     proof {
    //         reveal_strlit("abcabc");
    //         reveal_strlit("abc");
    //         reveal_strlit("bca");
    //     }

    //     let s = "abcabc";
    //     let ends_with_abc = s.ends_with_str("abc");
    //     let ends_with_bca = s.ends_with_str("bca");

    //     assert(ends_with_abc);
    //     assert(!"bca"@.is_suffix_of(s@)) by {
    //         assert("bca"@.last() == 'a');
    //         assert(s@.last() == 'c');
    //     }
    //     assert(!ends_with_bca);
    // }
}

    
} // verus!