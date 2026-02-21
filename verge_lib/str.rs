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
//! Meanwhile, it is common to construct a string from raw bytes, using the `str::from_utf8()` 
//! method. In this case, this module also provides the `as_str()` and `as_bytes` functions to 
//! enable the conversion between the two views in `spec`, which involves the `is_utf8()` predicate. 
//! There is also basic support for ASCII strings where the byte-view and `char`-view unify.
//!
//! `Deref` Methods
//! In native Rust, `String` inherits all `&self` methods from `str` because it implements `Deref<Target=str>`.
//! However, `Deref` coercion is not automatically done in Verus, so an explicit `as_str()` is needed 
//! to call these methods (e.g., `s.as_str().is_char_boundary()`).
//!
//! Note that some methods exists natively for both types, such as `str::len()` and `String::len()`; 
//! in this case they are covered by `assume_specification`.
//!
//! Mid-String Mutation
//! Because of the UTF-8 nature of Rust strings, mid-string mutation (e.g., updating a character in the middle of 
//! a string) is already awkward. In Verge, such APIs are generally not exposed on purpose.
//! This essentially forces strings to be grow-only containers, which is the typical use case anyway.
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::math::min;

pub use std::str::{
    Utf8Error,
};

verus! {

pub mod ascii;
pub mod iter;
pub mod string;

pub use ascii::*;
pub use iter::*;
pub use string::*;

/// This trait allows viewing a type as a string (sequence of `char`s).
pub trait StrView {

    /// Casts `self` as a `char` sequence.
    spec fn as_str(&self) -> Seq<char>
        recommends self.is_utf8(),
    ;

    /// Predicate for asserting `self` can be viewed as a valid UTF-8 string.
    spec fn is_utf8(&self) -> bool;

    /// Predicate for asserting `self` can be viewed as a valid ASCII string.
    spec fn is_ascii(&self) -> bool;
}

impl StrView for Seq<u8> {

    uninterp spec fn as_str(&self) -> Seq<char>;

    uninterp spec fn is_utf8(&self) -> bool;

    open spec fn is_ascii(&self) -> bool {
        forall |i: int| #![auto] 0 <= i < self.len() ==> self[i] <= 0x7f
    }
}

/// This trait allows viewing a type as a byte sequence.
pub trait BytesView {
    /// Casts `self` as a `u8` sequence.
    spec fn as_bytes(&self) -> Seq<u8>;

    /// Predicate for asserting `self` can be viewed as a valid sequence of ASCII bytes.
    spec fn is_ascii(&self) -> bool;
}

impl BytesView for Seq<char> {
    uninterp spec fn as_bytes(&self) -> Seq<u8>;

    #[verifier::inline]
    open spec fn is_ascii(&self) -> bool {
        forall |i: int| 0 <= i < self.len() ==> 0 <= #[trigger] self[i] <= 0x7f
    }
}

pub broadcast group axiom_str_view {
    lemma_subrange_self,
    axiom_str_lower_lift,
    axiom_bytes_lift_lower,
    axiom_bytes_concat_lift,
    axiom_str_concat_lower,
    axiom_str_is_utf8,
    axiom_ascii_is_utf8,
    axiom_str_slice_is_ascii,
    axiom_string_is_ascii,
    axiom_ascii_bytes_as_str,
    axiom_ascii_str_as_bytes,
}

// TODO(xyx): this should be in a seq module
pub broadcast proof fn lemma_subrange_self<T>(s: Seq<T>)
    ensures (#[trigger] s.subrange(0, s.len() as int)) =~= s {}

/// Lowering a string as bytes then lifting back is no-op.
#[verifier::external_body]
pub broadcast axiom fn axiom_str_lower_lift(s: Seq<char>)
    ensures #[trigger] s.as_bytes().as_str() =~= s,
;

/// Lifting a UTF-8 byte sequence then lowering is no-op.
#[verifier::external_body]
pub broadcast axiom fn axiom_bytes_lift_lower(bytes: Seq<u8>)
    requires
        bytes.is_utf8(),
    ensures 
        #[trigger] bytes.as_str().as_bytes() =~= bytes,
;

/// Concatenation of UTF-8 byte sequences can be lifted as concatenation of strings.
#[verifier::external_body]
pub broadcast axiom fn axiom_bytes_concat_lift(b1: Seq<u8>, b2: Seq<u8>)
    requires
        b1.is_utf8() && b2.is_utf8(),
    ensures
        #![trigger b1 + b2]
        (b1 + b2).is_utf8(),
        (b1 + b2).as_str() =~= b1.as_str() + b2.as_str(),
;

/// Concatenation of strings can be lowered as concatenation of UTF-8 byte sequences.
#[verifier::external_body]
pub broadcast axiom fn axiom_str_concat_lower(s1: Seq<char>, s2: Seq<char>)
    ensures
        #[trigger] (s1 + s2).as_bytes() =~= s1.as_bytes() + s2.as_bytes(),
;

/// Any string can be viewed as a valid UTF-8 byte sequence.
#[verifier::external_body]
pub broadcast axiom fn axiom_str_is_utf8(s: Seq<char>)
    ensures (#[trigger] s.as_bytes()).is_utf8(),
;

/// Any valid ASCII byte sequence is also UTF-8.
#[verifier::external_body]
pub broadcast axiom fn axiom_ascii_is_utf8(bytes: Seq<u8>)
    requires
        bytes.is_ascii(),
    ensures
        #[trigger] bytes.is_utf8(),
;

/// Any ASCII string slice can be viewed as a valid ASCII `char` sequence.
#[verifier::external_body]
pub broadcast axiom fn axiom_str_slice_is_ascii(s: &str)
    ensures 
        (#[trigger] s.is_ascii()) <==> s@.is_ascii(),
;

/// Any ASCII string can be viewed as a valid ASCII `char` sequence.
#[verifier::external_body]
pub broadcast axiom fn axiom_string_is_ascii(s: &String)
    ensures 
        (#[trigger] s.is_ascii()) <==> s@.is_ascii(),
;

/// Conversion of ASCII bytes into strings is fully specified.
#[verifier::external_body]
pub broadcast axiom fn axiom_ascii_bytes_as_str(bytes: Seq<u8>)
    requires
        bytes.is_ascii(),
    ensures 
        (#[trigger] bytes.as_str()) =~= Seq::new(bytes.len(), |i: int| bytes[i] as char),
;

/// Conversion of ASCII strings into bytes is fully specified.
#[verifier::external_body]
pub broadcast axiom fn axiom_ascii_str_as_bytes(s: Seq<char>)
    requires
        s.is_ascii(),
    ensures 
        (#[trigger] s.as_bytes()) =~= Seq::new(s.len(), |i: int| s[i] as u8),
;

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExUtf8Error(Utf8Error);

/// Enable `std::str::from_utf8`.
#[verifier::external_body]
pub fn from_utf8_checked(v: &[u8]) -> (res: Result<&str, Utf8Error>)
    ensures
        ({
            match res {
                Ok(s) => v@.is_utf8() && s@.as_bytes() =~= v@,
                _ => !v@.is_utf8(),
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

/// Enable `str::as_bytes`.
pub assume_specification [ str::as_bytes ] (s: &str) -> (bytes: &[u8])
    ensures
        bytes@ =~= s@.as_bytes(),
    no_unwind
;

/// Enable `str::len`. Note that this returns length in bytes.
pub assume_specification [ str::len ] (s: &str) -> (ret: usize)
    ensures
        ret == s@.as_bytes().len(),
    no_unwind
;

/// Enable `str::is_char_boundary`.
pub assume_specification [ str::is_char_boundary ] (s: &str, index: usize) -> (ret: bool)
    returns
        index <= s@.as_bytes().len() && s@.as_bytes().take(index as int).is_utf8(),
    no_unwind
;

/// Enable `str::floor_char_boundary`.
pub assume_specification [ str::floor_char_boundary ] (s: &str, index: usize) -> (ret: usize)
    ensures
        ret <= s@.as_bytes().len() && ret <= index,
        s@.as_bytes().take(ret as int).is_utf8(),
        !exists|i: int| ret < i <= index && #[trigger] s@.as_bytes().take(i as int).is_utf8(),
    no_unwind
;

/// Enable `str::ceil_char_boundary`.
pub assume_specification [ str::ceil_char_boundary ] (s: &str, index: usize) -> (ret: usize)
    ensures
        ret <= s@.as_bytes().len() && ret >= min(index as int, s@.as_bytes().len() as int),
        s@.as_bytes().take(ret as int).is_utf8(),
        !exists|i: int| index <= i < ret && #[trigger] s@.as_bytes().take(i as int).is_utf8(),
    no_unwind
;

/// Enable basic (`&str`) pattern matching for `&str`.
pub trait StrSliceExecPatternFns {

    fn contains(&self, pat: &str) -> bool
        no_unwind;

    fn starts_with(&self, pat: &str) -> bool
        no_unwind;

    fn ends_with(&self, pat: &str) -> bool
        no_unwind;

    fn find(&self, pat: &str) -> Option<usize>
        no_unwind;

    fn rfind(&self, pat: &str) -> Option<usize>
        no_unwind;
    
    fn strip_prefix(&self, prefix: &str) -> Option<&str>
        no_unwind;
    
    fn strip_suffix(&self, suffix: &str) -> Option<&str>
        no_unwind;

    // TODO(rilin): trim_matches methods 
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
    fn contains(&self, pat: &str) -> (ret: bool) 
        returns 
            exists|i: int| 
                0 <= i <= self@.len() - pat@.len()
                && #[trigger] self@.subrange(i, i + pat@.len()) =~= pat@,
    {
        self.contains(pat)
    }

    /// Enable `str::starts_with`.
    #[verifier::external_body]
    fn starts_with(&self, pat: &str) -> (ret: bool)
        returns
            pat@.is_prefix_of(self@),
    {
        self.starts_with(pat)
    }

    /// Enable `str::ends_with`.
    #[verifier::external_body]
    fn ends_with(&self, pat: &str) -> (ret: bool)
        returns
            pat@.is_suffix_of(self@),
    {
        self.ends_with(pat)
    }

    /// Enable `str::find`.
    #[verifier::external_body]
    fn find(&self, pat: &str) -> (ret: Option<usize>)
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
    fn rfind(&self, pat: &str) -> (ret: Option<usize>)
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
    fn strip_prefix(&self, prefix: &str) -> (ret: Option<&str>)
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
    fn strip_suffix(&self, suffix: &str) -> (ret: Option<&str>)
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

/// Enable `str::make_ascii_lowercase`.
pub assume_specification [ str::make_ascii_lowercase ] (s: &mut str)
    ensures
        s@ =~= Seq::<char>::new(
            old(s)@.len(), |i: int| old(s)@[i].to_ascii_lowercase()),
    no_unwind
;

/// Enable `str::make_ascii_uppercase`.
pub assume_specification [ str::make_ascii_uppercase ] (s: &mut str)
    ensures
        s@ =~= Seq::<char>::new(
            old(s)@.len(), |i: int| old(s)@[i].to_ascii_uppercase()),
    no_unwind
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

/// Enable `str::trim_ascii_start`.
/// TODO(rilin): this does not immediately reveal `ret.len()` even if we know exactly what `s` is.
/// Add a proof function for it.
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
        broadcast use axiom_str_view;
        let s = String::new();
        assert(s@.as_bytes().is_utf8());
        assert(Seq::<u8>::empty().is_utf8());
    }

    fn test_string_literal() -> (ret: String) 
        ensures ret@ =~= "abcd"@,
    {
        broadcast use axiom_str_view;
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
        broadcast use axiom_str_view;
        s.truncate(512);
    }

    fn test_utf8(s: &mut String) {
        broadcast use axiom_str_view;

        s.insert_str(0, "头");
        s.insert_str(s.len(), "尾");
        assert(s@ == "头"@ + old(s)@ + "尾"@);

        let ghost hlen = "头"@.as_bytes().len();
        let ghost tlen = "尾"@.as_bytes().len();
        let ghost len = s@.as_bytes().len();
        assert(s@.as_bytes().subrange(hlen as int, (len - tlen) as int) == old(s)@.as_bytes());
    }

    // TODO(rilin): test more functions
}

    
} // verus!