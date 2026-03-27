//! Specifications and lemmas for strings, extending `vstd`'s support.
//!
//! ### Bytes or Chars
//! There are two typical ways to view a Rust string (`&str` or `String`): as bytes (`u8`), or as `char`s.
//! Each string is in fact stored as a raw `&[u8]`, so the byte representation is more true to the 
//! memory layout. 
//! However, Rust strings are by construction valid UTF-8, and not all byte sequences satisfy this. 
//! Given that this invariant is rooted in Rust by the type safety of `char` and `str`, Verus
//! views strings as `Seq<char>`, and this module follows that paradigm. Generally, any added 
//! specification for string operations should be based on the `char` level.
//!
//! Conversion between the byte- and char-views is done via `vstd::utf8` methods, particularly
//! `encode_utf8()` (`Seq<char>` to `Seq<u8>`) and `decode_utf8()` (`Seq<u8>` to `Seq<char>`). 
//! However, directly using these as `open` specs can slow verification; hence they are wrapped 
//! in `as_bytes()` and `as_str()` with `#[verifier::opaque]`. Use lemmas provided by Verge for 
//! lightweight common-case reasoning, or `reveal` and use `vstd::utf8` if needed.
//!
//! ### `Deref` Methods
//! In native Rust, `String` inherits all `&self` methods from `str` because it implements `Deref<Target=str>`.
//! However, `Deref` coercion is not automatically done in Verus, so an explicit `as_str()` is needed 
//! to call these methods (e.g., `s.as_str().is_char_boundary()`).
//!
//! Note that some methods exists natively for both types, such as `str::len()` and `String::len()`; 
//! in this case they are covered by `assume_specification`.
//!
//! ### Mid-String Mutation
//! Because of the UTF-8 nature of Rust strings, mid-string mutation (e.g., updating a character in the middle of 
//! a string) is already awkward. In Verge, such APIs are generally not exposed on purpose.
//! This essentially forces strings to be grow-only containers, which is the typical use case anyway.
#![allow(unused)]
use vstd::prelude::*;
use vstd::math::min;
use vstd::assert_by_contradiction;
use vstd::utf8::*;
use crate::error::ErrorSpec;

pub use std::str::{
    Utf8Error,
};

verus! {

pub mod ascii;
pub mod iter;
pub mod string;
pub mod parse;
pub mod fmt;

pub use ascii::*;
pub use iter::*;
pub use string::*;
pub use parse::*;
pub use fmt::*;

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

    #[verifier::opaque]
    open spec fn as_str(self) -> Seq<char> 
        { decode_utf8(self) }

    #[verifier::opaque]
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

    #[verifier::opaque]
    open spec fn as_bytes(self) -> Seq<u8> 
        { encode_utf8(self) }

    open spec fn is_ascii(self) -> bool {
        forall |i: int| 0 <= i < self.len() ==> 0 <= #[trigger] self[i] <= 0x7f
    }
}

/// Lightweight lemmas for strings. 
/// Note that by default, `as_bytes()` and `as_str()` are fully specified for ASCII strings only 
/// (in which case the specs are verification-friendly). For non-ASCII UTF-8 strings, `vstd::utf8` 
/// can be used, but the full UTF8 spec might be expensive to reason about.
pub broadcast group lemma_str_view {
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

pub broadcast proof fn lemma_subrange_self<T>(s: Seq<T>)
    ensures (#[trigger] s.subrange(0, s.len() as int)) =~= s {}

/// Proof that lowering a string as bytes then lifting back is no-op.
pub broadcast proof fn lemma_str_lower_lift(s: Seq<char>)
    ensures #[trigger] s.as_bytes().as_str() =~= s,
{
    reveal(<Seq<char> as BytesView>::as_bytes);
    reveal(<Seq<u8> as StrView>::as_str);
    encode_utf8_decode_utf8(s);
}

/// Proof that lifting a UTF-8 byte sequence then lowering is no-op.
pub broadcast proof fn lemma_bytes_lift_lower(bytes: Seq<u8>)
    requires
        bytes.is_utf8(),
    ensures 
        #[trigger] bytes.as_str().as_bytes() =~= bytes,
{
    reveal(<Seq<char> as BytesView>::as_bytes);
    reveal(<Seq<u8> as StrView>::as_str);
    reveal(<Seq<u8> as StrView>::is_utf8);
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
    reveal(<Seq<char> as BytesView>::as_bytes);
    reveal(<Seq<u8> as StrView>::as_str);
    reveal(<Seq<u8> as StrView>::is_utf8);
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
    reveal(<Seq<char> as BytesView>::as_bytes);
    reveal(<Seq<u8> as StrView>::as_str);
    reveal(<Seq<u8> as StrView>::is_utf8);
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
    reveal(<Seq<char> as BytesView>::as_bytes);
    reveal(<Seq<u8> as StrView>::as_str);
    reveal(<Seq<u8> as StrView>::is_utf8);
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
    reveal(<Seq<char> as BytesView>::as_bytes);
    reveal(<Seq<u8> as StrView>::as_str);
    reveal(<Seq<u8> as StrView>::is_utf8);
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
    reveal(<Seq<char> as BytesView>::as_bytes);
    reveal(<Seq<u8> as StrView>::as_str);
    reveal(<Seq<u8> as StrView>::is_utf8);
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
    reveal(<Seq<char> as BytesView>::as_bytes);
    reveal(<Seq<u8> as StrView>::as_str);
    reveal(<Seq<u8> as StrView>::is_utf8);
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
    reveal(<Seq<u8> as StrView>::is_utf8);
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


#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExUtf8Error(Utf8Error);

impl ErrorSpec for Utf8Error {}

/// Enable `std::str::from_utf8`.
#[verifier::external_body]
pub fn from_utf8_checked(v: &[u8]) -> (res: Result<&str, Utf8Error>)
    ensures
        ({
            match res {
                Ok(s) => v@.is_utf8() && s@.as_bytes() =~= v@,
                Err(e) => {
                    &&& !v@.is_utf8() 
                    &&& e.is_str_utf8_error()
                },
            }
        }),
    no_unwind
{
    std::str::from_utf8(v)
}

/// Enable `std::str::from_utf8_unchecked`; note that this is no longer `unsafe`.
#[verifier::external_body]
pub fn from_utf8_verified(v: &[u8]) -> (s: &str)
    requires
        v@.is_utf8(),
    ensures
        s@ =~= v@.as_str(),
    no_unwind
{
    unsafe { std::str::from_utf8_unchecked(v) }
}

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

/// Enable basic (`&str`) pattern matching for `&str`.
pub trait StrSliceExecPatternFns {

    fn contains_str(&self, pat: &str) -> bool
        no_unwind;

    fn starts_with_str(&self, pat: &str) -> bool
        no_unwind;

    fn ends_with_str(&self, pat: &str) -> bool
        no_unwind;

    fn find_str(&self, pat: &str) -> Option<usize>
        no_unwind;

    fn rfind_str(&self, pat: &str) -> Option<usize>
        no_unwind;
    
    fn strip_prefix_str(&self, prefix: &str) -> Option<&str>
        no_unwind;
    
    fn strip_suffix_str(&self, suffix: &str) -> Option<&str>
        no_unwind;
        
}

/// Enables `&[start..end]` indexing for `&str`.
/// 
/// Note that this function no longer panics, but requires proving that `start` and `end` 
/// fall between code points. 
#[verifier::external_body]
pub fn str_subrange(s: &str, start: usize, end: usize) -> (ret: &str) 
    requires
        start <= end <= s@.as_bytes().len(),
        s@.as_bytes().take(start as int).is_utf8(),
        s@.as_bytes().take(end as int).is_utf8(),
    ensures
        ret@.as_bytes() =~= s@.as_bytes().subrange(start as int, end as int),
    no_unwind
{
    &s[start..end]
}

impl StrSliceExecPatternFns for str {

    /// Enable `str::contains`.
    #[verifier::external_body]
    fn contains_str(&self, pat: &str) -> (ret: bool) 
        returns 
            exists|i: int| 
                0 <= i <= self@.len() - pat@.len()
                && #[trigger] self@.subrange(i, i + pat@.len()) =~= pat@,
    {
        self.contains(pat)
    }

    /// Enable `str::starts_with`.
    #[verifier::external_body]
    fn starts_with_str(&self, pat: &str) -> (ret: bool)
        returns
            pat@.is_prefix_of(self@),
    {
        self.starts_with(pat)
    }

    /// Enable `str::ends_with`.
    #[verifier::external_body]
    fn ends_with_str(&self, pat: &str) -> (ret: bool)
        returns
            pat@.is_suffix_of(self@),
    {
        self.ends_with(pat)
    }

    /// Enable `str::find`.
    #[verifier::external_body]
    fn find_str(&self, pat: &str) -> (ret: Option<usize>)
        ensures
            ({
                let slen = self@.as_bytes().len();
                let plen = pat@.as_bytes().len();
                match ret {
                    Some(idx) => {
                        let idx = idx as int;
                        &&& idx <= slen - plen
                        &&& self@.as_bytes().subrange(idx, idx + plen) =~= pat@.as_bytes()
                        &&& !exists|i: int| 
                            0 <= i < idx 
                            && #[trigger] self@.as_bytes().subrange(i, i + plen) =~= pat@.as_bytes()
                    },
                    None => {
                        forall|i: int| 0 <= i <= slen - plen
                            ==> !(#[trigger] self@.as_bytes().subrange(i, i + plen) =~= pat@.as_bytes())
                    },
                }
            }),
    {
        self.find(pat)
    }

    /// Enable `str::rfind`.
    #[verifier::external_body]
    fn rfind_str(&self, pat: &str) -> (ret: Option<usize>)
        ensures
            ({
                let slen = self@.as_bytes().len();
                let plen = pat@.as_bytes().len();
                match ret {
                    Some(idx) => {
                        let idx = idx as int;
                        &&& idx <= slen - plen
                        &&& self@.as_bytes().subrange(idx, idx + plen) =~= pat@.as_bytes()
                        &&& !exists|i: int| 
                            idx < i <= slen - plen
                            && #[trigger] self@.as_bytes().subrange(i, i + plen) =~= pat@.as_bytes()
                    },
                    None => {
                        forall|i: int| 0 <= i <= slen - plen
                            ==> !(#[trigger] self@.as_bytes().subrange(i, i + plen) =~= pat@.as_bytes())
                    },
                }
            }),
    {
        self.rfind(pat)
    }

    /// Enable `str::strip_prefix`.
    #[verifier::external_body]
    fn strip_prefix_str(&self, prefix: &str) -> (ret: Option<&str>)
        ensures
            ({
                match ret {
                    Some(s) => {
                        &&& prefix@.is_prefix_of(self@)
                        &&& s@ =~= self@.skip(prefix@.len() as int)
                    },
                    None => !prefix@.is_prefix_of(self@)
                }
            }),
    {
        self.strip_prefix(prefix)
    }

    /// Enable `str::strip_suffix`.
    #[verifier::external_body]
    fn strip_suffix_str(&self, suffix: &str) -> (ret: Option<&str>)
        ensures
            ({
                match ret {
                    Some(s) => {
                        &&& suffix@.is_suffix_of(self@)
                        &&& s@ =~= self@.take((self@.len() - suffix@.len()) as int)
                    },
                    None => !suffix@.is_suffix_of(self@)
                }
            }),
    {
        self.strip_suffix(suffix)
    }
}

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
        ret@.len() <= s@.len(),
        exists |start: int| {
            &&& 0 <= start <= s@.len() - ret@.len()
            &&& #[trigger] s@.subrange(start, start + ret@.len()) =~= ret@
            &&& forall |i: int| 0 <= i < start ==> #[trigger] s@[i].is_ascii_whitespace()
            &&& forall |i: int| start + ret@.len() <= i < s@.len() ==> #[trigger] s@[i].is_ascii_whitespace()
        },
        ret@.len() > 0 ==> !ret@.first().is_ascii_whitespace() && !ret@.last().is_ascii_whitespace(),
    no_unwind
;

mod tests {
    use super::*;

    fn test_empty() {
        broadcast use lemma_str_view;
        let s = String::new();
        assert(s@.as_bytes().is_utf8());
        assert(Seq::<u8>::empty().is_utf8());
    }

    fn test_string_literal() -> (ret: String) 
        ensures ret@ =~= "abcd"@,
    {
        broadcast use lemma_str_view;
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
        broadcast use lemma_str_view;
        s.truncate(512);
    }

    fn test_utf8(s: &mut String) {
        broadcast use lemma_str_view;

        s.insert_str(0, "头");
        s.insert_str(s.len(), "尾");
        assert(s@ == "头"@ + old(s)@ + "尾"@);

        let ghost hlen = "头"@.as_bytes().len();
        let ghost tlen = "尾"@.as_bytes().len();
        let ghost len = s@.as_bytes().len();
        assert(s@.as_bytes().subrange(hlen as int, (len - tlen) as int) == old(s)@.as_bytes());
    }

    fn test_trim_ascii() {
        broadcast use lemma_str_view;

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
        broadcast use axiom_str_view;

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
        broadcast use lemma_str_view;
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

    fn test_from_utf8_checked() {
        broadcast use lemma_str_view;
        let good = vec![65u8, 66u8, 67u8];
        let bad = vec![0xffu8];
        assert(good@.is_utf8());

        let ok = from_utf8_checked(good.as_slice());
        let err = from_utf8_checked(bad.as_slice());

        assert(ok.is_ok());
        match err {
            Ok(_) => assert(bad@.is_utf8()),
            Err(_) => assert(!bad@.is_utf8()),
        }
    }

    fn test_from_utf8_verified() {
        broadcast use lemma_str_view;
        let bytes = vec![97u8, 98u8, 99u8];
        assert(bytes@.is_utf8());
        let s = from_utf8_verified(bytes.as_slice());
        assert(s@ =~= bytes@.as_str());
    }

    fn test_str_slice_contains_and_not_found() {
        broadcast use lemma_str_view;
        proof {
            reveal_strlit("abca");
            reveal_strlit("bca");
            reveal_strlit("zzz");
            reveal_strlit("abc");
        }

        let s = "abca";
        let contains_bca = s.contains_str("bca");
        let contains_zzz = s.contains_str("zzz");
        let find_zzz = s.find_str("zzz");
        let rfind_zzz = s.rfind_str("zzz");

        assert(exists|i: int|
            0 <= i <= s@.len() - "bca"@.len()
            && #[trigger] s@.subrange(i, i + "bca"@.len()) =~= "bca"@
        ) by {
            assert(s@.subrange(1, 1 + "bca"@.len() as int) =~= "bca"@);
        }
        assert(contains_bca);

        assert(s@.len() == 4 && s@.as_bytes().len() == 4);
        assert("zzz"@.len() == 3 && "zzz"@.as_bytes().len() == 3);
        
        assert(s@.subrange(0, 0 + "zzz"@.len() as int) =~= "abc"@);
        assert(s@.subrange(1, 1 + "zzz"@.len() as int) =~= "bca"@);
        assert(!("abc"@ =~= "zzz"@) && !("bca"@ =~= "zzz"@)) by {
            assert("abc"@[0] == 'a');
            assert("bca"@[0] == 'b');
            assert("zzz"@[0] == 'z');
        }

        proof {
            assert_by_contradiction!(!(exists|i: int|
                0 <= i <= s@.len() - "zzz"@.len()
                && #[trigger] s@.subrange(i, i + "zzz"@.len()) =~= "zzz"@
            ), {
                let i = choose|i: int|
                    0 <= i <= s@.len() - "zzz"@.len()
                    && #[trigger] s@.subrange(i, i + "zzz"@.len()) =~= "zzz"@;
                assert(0 <= i <= 1);
                let subrange = s@.subrange(i, i + "zzz"@.len());
                // assert(s@.subrange(i, i + "zzz"@.len()) =~= "zzz"@);
                assert(subrange =~= "abc"@ || subrange =~= "bca"@);
            });
        }

        assert(s@.as_bytes().subrange(0, 0 + "zzz"@.as_bytes().len() as int) =~= "abc"@.as_bytes());
        assert(s@.as_bytes().subrange(1, 1 + "zzz"@.as_bytes().len() as int) =~= "bca"@.as_bytes());
        assert(!("abc"@.as_bytes() =~= "zzz"@.as_bytes()) && !("bca"@.as_bytes() =~= "zzz"@.as_bytes())) by {
            assert("abc"@.as_bytes()[0] == 'a' as u8);
            assert("bca"@.as_bytes()[0] == 'b' as u8);
            assert("zzz"@.as_bytes()[0] == 'z' as u8);
        }

        proof {
            assert_by_contradiction!(!(exists|i: int|
                0 <= i <= s@.as_bytes().len() - "zzz"@.as_bytes().len()
                && #[trigger] s@.as_bytes().subrange(i, i + "zzz"@.as_bytes().len()) =~= "zzz"@.as_bytes()
            ), {
                let i = choose|i: int|
                    0 <= i <= s@.as_bytes().len() - "zzz"@.as_bytes().len()
                    && #[trigger] s@.as_bytes().subrange(i, i + "zzz"@.as_bytes().len()) =~= "zzz"@.as_bytes();
                assert(0 <= i <= 1);
                let subrange = s@.as_bytes().subrange(i, i + "zzz"@.as_bytes().len());
                // assert(s@.as_bytes().subrange(i, i + "zzz"@.as_bytes().len()) =~= "zzz"@.as_bytes());
                assert(subrange =~= "abc"@.as_bytes() || subrange =~= "bca"@.as_bytes());
            });
        }

        assert(!contains_zzz);
        assert(rfind_zzz.is_none() && find_zzz.is_none());
    }

    fn test_str_slice_find_rfind() {
        broadcast use lemma_str_view;
        proof {
            reveal_strlit("aba");
            reveal_strlit("a");
        }

        let s = "aba";
        let found = s.find_str("a");
        let rfound = s.rfind_str("a");
        assert(found == Some(0usize)) by {
            match found {
                Some(idx) => {
                    let i = idx as int;
                    assert(0 <= i <= s@.as_bytes().len() - "a"@.as_bytes().len());
                    assert(s@.as_bytes().subrange(i, i + "a"@.as_bytes().len()) =~= "a"@.as_bytes());
                    assert_by_contradiction!(i <= 0, {
                        assert(s@.as_bytes().subrange(0, 0 + "a"@.as_bytes().len() as int) =~= "a"@.as_bytes());
                    })
                }
                None => {}
            }
        }
        assert(rfound == Some(2usize)) by {
            match rfound {
                Some(idx) => {
                    let i = idx as int;
                    assert(0 <= i <= s@.as_bytes().len() - "a"@.as_bytes().len());
                    assert(s@.as_bytes().subrange(i, i + "a"@.as_bytes().len()) =~= "a"@.as_bytes());
                    assert_by_contradiction!(!(i < 2), {
                        assert(s@.as_bytes().subrange(2, 2 + "a"@.as_bytes().len() as int) =~= "a"@.as_bytes());
                    })
                }
                None => {}
            }
        }
    }

    fn test_str_slice_starts_with() {
        broadcast use lemma_str_view;
        proof {
            reveal_strlit("abcabc");
            reveal_strlit("abc");
            reveal_strlit("bca");
        }

        let s = "abcabc";
        let starts_with_abc = s.starts_with_str("abc");
        let starts_with_bca = s.starts_with_str("bca");

        assert(starts_with_abc == "abc"@.is_prefix_of(s@));
        assert(starts_with_bca == "bca"@.is_prefix_of(s@));
        assert(starts_with_abc);
        assert(!"bca"@.is_prefix_of(s@)) by {
            assert("bca"@[0] == 'b');
            assert(s@[0] == 'a');
        }
        assert(!starts_with_bca);
    }

    fn test_str_slice_ends_with() {
        broadcast use lemma_str_view;
        proof {
            reveal_strlit("abcabc");
            reveal_strlit("abc");
            reveal_strlit("bca");
        }

        let s = "abcabc";
        let ends_with_abc = s.ends_with_str("abc");
        let ends_with_bca = s.ends_with_str("bca");

        assert(ends_with_abc);
        assert(!"bca"@.is_suffix_of(s@)) by {
            assert("bca"@.last() == 'a');
            assert(s@.last() == 'c');
        }
        assert(!ends_with_bca);
    }
}

    
} // verus!