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
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub mod iter;
pub mod string;

pub use iter::*;
pub use string::*;

/// This function casts a byte sequence into a `char` sequence in `spec` mode.
pub uninterp spec fn as_str(bytes: Seq<u8>) -> Seq<char>
    recommends is_utf8(bytes),
;

// TODO: implement these as trait methods

/// This function casts a `char` sequence into a byte sequence in `spec` mode.
pub uninterp spec fn as_bytes(s: Seq<char>) -> Seq<u8>;

/// Predicate for asserting that a sequence of bytes is valid UTF-8.
pub uninterp spec fn is_utf8(bytes: Seq<u8>) -> bool;

/// Predicate for asserting that a sequence of bytes is valid ASCII.
pub open spec fn is_ascii(bytes: Seq<u8>) -> bool {
    forall |i: int| #![auto] 0 <= i < bytes.len() ==> bytes[i] <= 0x7f
}

pub broadcast group axiom_str_bytes {
    axiom_as_bytes_as_str_noop,
    axiom_str_slice_is_utf8,
    axiom_string_is_utf8,
    axiom_ascii_is_utf8,
    axiom_str_slice_is_ascii,
    axiom_string_is_ascii,
    axiom_ascii_bytes_as_str,
    axiom_ascii_str_slice_as_bytes,
    axiom_ascii_string_as_bytes,
}

/// Converting into bytes then back to string is no-op.
#[verifier::external_body]
pub broadcast axiom fn axiom_as_bytes_as_str_noop(s: Seq<char>)
    ensures #[trigger] as_str(as_bytes(s)) =~= s,
;

/// Any string can be converted into valid UTF-8 byte sequence.
#[verifier::external_body]
pub broadcast axiom fn axiom_str_slice_is_utf8(s: &str)
    ensures is_utf8(#[trigger] as_bytes(s@)),
;

/// Any string can be converted into valid UTF-8 byte sequence.
#[verifier::external_body]
pub broadcast axiom fn axiom_string_is_utf8(s: &String)
    ensures is_utf8(#[trigger] as_bytes(s@)),
;

/// Any valid ASCII sequence is also UTF-8.
#[verifier::external_body]
pub broadcast axiom fn axiom_ascii_is_utf8(bytes: Seq<u8>)
    ensures is_ascii(bytes) ==> #[trigger] is_utf8(bytes),
;

/// Any ASCII string can be converted into valid ASCII byte sequence.
#[verifier::external_body]
pub broadcast axiom fn axiom_str_slice_is_ascii(s: &str)
    ensures s.is_ascii() ==> is_ascii(#[trigger] as_bytes(s@)),
;

/// Any ASCII string can be converted into valid ASCII byte sequence.
#[verifier::external_body]
pub broadcast axiom fn axiom_string_is_ascii(s: &String)
    ensures s.is_ascii() ==> is_ascii(#[trigger] as_bytes(s@)),
;

/// Conversion of ASCII bytes into strings is fully specified.
#[verifier::external_body]
pub broadcast axiom fn axiom_ascii_bytes_as_str(bytes: Seq<u8>)
    requires
        is_ascii(bytes),
    ensures 
        #[trigger] as_str(bytes) =~= bytes.map(|_i: int, b: u8| b as char),
;

/// Conversion of ASCII strings into bytes is fully specified.
#[verifier::external_body]
pub broadcast axiom fn axiom_ascii_str_slice_as_bytes(s: &str)
    requires
        s.is_ascii(),
    ensures 
        #[trigger] as_bytes(s@) =~= s@.map(|_i: int, c: char| c as u8),
;

/// Conversion of ASCII strings into bytes is fully specified.
#[verifier::external_body]
pub broadcast axiom fn axiom_ascii_string_as_bytes(s: &String)
    requires
        s.is_ascii(),
    ensures 
        #[trigger] as_bytes(s@) =~= s@.map(|_i: int, c: char| c as u8),
;

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExUtf8Error(std::str::Utf8Error);

/// Enable `std::str::from_utf8`.
#[verifier::external_body]
pub fn from_utf8_checked(v: &[u8]) -> (res: Result<&str, std::str::Utf8Error>)
    ensures
        ({
            match res {
                Ok(s) => is_utf8(v@) && s@ =~= as_str(v@),
                _ => !is_utf8(v@),
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
        is_utf8(v@),
    ensures
        s@ =~= as_str(v@),
    no_unwind
{
    unsafe { std::str::from_utf8_unchecked(v) }
}

/// Enable `str::as_bytes`.
pub assume_specification [ str::as_bytes ] (s: &str) -> (bytes: &[u8])
    ensures
        bytes@ =~= as_bytes(s@),
        is_utf8(as_bytes(s@)),
    no_unwind
;

/// Enable `str::len`. Note that this returns length in bytes.
pub assume_specification [ str::len ] (s: &str) -> (ret: usize)
    ensures
        ret == as_bytes(s@).len(),
    no_unwind
;

/// Enable `str::is_char_boundary`.
pub assume_specification [ str::is_char_boundary ] (s: &str, index: usize) -> (ret: bool)
    ensures
        index <= as_bytes(s@).len() && is_utf8(as_bytes(s@).take(index as int)),
    no_unwind
;

/// Enable `str::floor_char_boundary`.
pub assume_specification [ str::floor_char_boundary ] (s: &str, index: usize) -> (ret: usize)
    ensures
        0 <= ret <= as_bytes(s@).len() && is_utf8(as_bytes(s@).take(ret as int)),
        !exists|i: int| ret < i <= index && #[trigger] is_utf8(as_bytes(s@).take(i as int)),
    no_unwind
;

/// Enable `str::ceil_char_boundary`.
pub assume_specification [ str::ceil_char_boundary ] (s: &str, index: usize) -> (ret: usize)
    ensures
        0 <= ret <= as_bytes(s@).len() && is_utf8(as_bytes(s@).take(ret as int)),
        !exists|i: int| index <= i < ret && #[trigger] is_utf8(as_bytes(s@).take(i as int)),
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

    // TODO: other methods requires Iterator structs
}

// TODO: will need: str_subrange (get), lines, 
// make/to_ascii_lowercase/upper, trim_ascii, strip, trim_matches
// 

impl StrSliceExecPatternFns for str {

    /// Enable `str::contains`.
    #[verifier::external_body]
    fn contains(&self, pat: &str) -> (ret: bool) 
        ensures 
            ret <==> exists|i: int| 
                0 <= i <= self@.len() - pat@.len()
                && #[trigger] self@.subrange(i, i + pat@.len()) =~= pat@,
    {
        self.contains(pat)
    }

    /// Enable `str::starts_with`.
    #[verifier::external_body]
    fn starts_with(&self, pat: &str) -> (ret: bool)
        ensures
            ret <==> pat@.is_prefix_of(self@),
    {
        self.starts_with(pat)
    }

    /// Enable `str::ends_with`.
    #[verifier::external_body]
    fn ends_with(&self, pat: &str) -> (ret: bool)
        ensures
            ret <==> pat@.is_suffix_of(self@),
    {
        self.ends_with(pat)
    }

    /// Enable `str::find`.
    #[verifier::external_body]
    fn find(&self, pat: &str) -> (ret: Option<usize>)
        ensures
            ({
                let slen = as_bytes(self@).len();
                let plen = as_bytes(pat@).len();
                match ret {
                    Some(idx) => {
                        let idx = idx as int;
                        &&& idx <= slen - plen
                        &&& as_bytes(self@).subrange(idx, idx + plen) =~= as_bytes(pat@)
                        &&& !exists|i: int| 
                            0 <= i < idx 
                            && #[trigger] as_bytes(self@).subrange(i, i + plen) =~= as_bytes(pat@)
                    },
                    None => {
                        forall|i: int| 0 <= i <= slen - plen
                            ==> !(#[trigger] as_bytes(self@).subrange(i, i + plen) =~= as_bytes(pat@))
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
                let slen = as_bytes(self@).len();
                let plen = as_bytes(pat@).len();
                match ret {
                    Some(idx) => {
                        let idx = idx as int;
                        &&& idx <= slen - plen
                        &&& as_bytes(self@).subrange(idx, idx + plen) =~= as_bytes(pat@)
                        &&& !exists|i: int| 
                            idx < i <= slen - plen
                            && #[trigger] as_bytes(self@).subrange(i, i + plen) =~= as_bytes(pat@)
                    },
                    None => {
                        forall|i: int| 0 <= i <= slen - plen
                            ==> !(#[trigger] as_bytes(self@).subrange(i, i + plen) =~= as_bytes(pat@))
                    },
                }
                
            }),
    {
        self.rfind(pat)
    }
}

mod tests {
    use super::*;

    pub fn test_string_truncate(s: &mut String) 
        requires 
            old(s).is_ascii(),
            old(s)@.len() > 1024,
    {
        broadcast use axiom_str_bytes;
        s.truncate(512);
    }

    pub fn test_string_literal() -> (ret: String) 
        ensures ret@ =~= "abcd"@,
    {
        broadcast use axiom_str_bytes;
        proof { 
            reveal_strlit("abd");
            reveal_strlit("c");
            reveal_strlit("abcd");
        }

        let mut s = String::from_str("abd");
        s.insert_str(2, "c");
        s
    }
}

    
} // verus!