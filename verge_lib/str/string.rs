//! Specifications and lemmas for `std::String`.

use super::*;
pub use std::string::FromUtf8Error;

verus! {

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExFromUtf8Error(FromUtf8Error);

/// Enable `String::as_bytes`.
pub assume_specification [ String::as_bytes ] (s: &String) -> (bytes: &[u8])
    ensures
        bytes@ =~= s@.as_bytes(),
    no_unwind
;

/// Enable `String::len`.
///
/// Note that this returns length in bytes.
#[verifier::allow_in_spec]
pub assume_specification [ String::len ] (s: &String) -> (ret: usize)
    returns
        s@.as_bytes().len() as usize,
    no_unwind
;

/// Enable `String::is_empty`. 
#[verifier::allow_in_spec]
pub assume_specification [ String::is_empty ] (s: &String) -> (ret: bool)
    returns
        s@.len() == 0,
    no_unwind
;

/// Enable `String::with_capacity`.
pub assume_specification [ String::with_capacity ] (cap: usize) -> (s: String)
    ensures
        s@ =~= Seq::<char>::empty(),
;

/// Enable `String::from_utf8`.
pub assume_specification [ String::from_utf8 ] (vec: Vec<u8>) -> (ret: Result<String, FromUtf8Error>)
    ensures 
        ({
            match ret {
                Ok(s) => vec@.is_utf8() && s@ =~= vec@.as_str(),
                Err(e) => !vec@.is_utf8() && e.is_str_utf8_error(),
            }
        }),
;

/// Enable `String::into_bytes`.
pub assume_specification [ String::into_bytes ] (s: String) -> (bytes: Vec<u8>)
    ensures
        bytes@ =~= s@.as_bytes(),
    no_unwind
;

/// Enable `String::as_mut_str`.
pub assume_specification [ String::as_mut_str ] (s: &mut String) -> (ret: &mut str)
    ensures
        ret@ =~= old(s)@,
        final(ret)@ =~= final(s)@,
    no_unwind
;

/// Enable `String::clear`.
pub assume_specification [ String::clear ] (s: &mut String)
    ensures
        final(s)@ =~= Seq::<char>::empty(),
    no_unwind
;

/// Enable `String::push`. 
pub assume_specification [ String::push ] (s: &mut String, ch: char) 
    ensures
        final(s)@ =~= old(s)@.push(ch),
;

/// Enable `String::push_str`. 
pub assume_specification [ String::push_str ] (s: &mut String, string: &str) 
    ensures
        final(s)@ =~= old(s)@ + string@,
;

/// Enable `String::pop`. 
pub assume_specification [ String::pop ] (s: &mut String) -> (ch: Option<char>) 
    ensures
        old(s)@.len() > 0 ==> final(s)@ =~= old(s)@.drop_last() && ch == Some(old(s)@.last()),
        old(s)@.len() == 0 ==> final(s)@ =~= old(s)@ && ch.is_none(),
    no_unwind
;

/// Enable `String::reserve`. 
pub assume_specification [ String::reserve ] (s: &mut String, _amt: usize) 
    ensures
        final(s)@ =~= old(s)@,
;

/// Enable `String::reserve_exact`. 
pub assume_specification [ String::reserve_exact ] (s: &mut String, _amt: usize) 
    ensures
        final(s)@ =~= old(s)@,
;

/// Enable `String::insert`. 
///
/// Note that this function no longer panics, but requires proving that `idx` 
/// falls between code points. 
pub assume_specification [ String::insert ] (s: &mut String, idx: usize, ch: char) 
    requires
        is_char_boundary(s@.as_bytes(), idx as int),
    ensures
        final(s)@.as_bytes() =~= old(s)@.as_bytes().take(idx as int) + seq![ch].as_bytes() + old(s)@.as_bytes().skip(idx as int),
;

/// Enable `String::insert_str`. 
///
/// Note that this function no longer panics, but requires proving that `idx` 
/// falls between code points. 
pub assume_specification [ String::insert_str ] (s: &mut String, idx: usize, string: &str) 
    requires
        is_char_boundary(s@.as_bytes(), idx as int),
    ensures
        final(s)@.as_bytes() =~= old(s)@.as_bytes().take(idx as int) + string@.as_bytes() + old(s)@.as_bytes().skip(idx as int),
;

/// Enable `String::remove`. 
///
/// Note that this function no longer panics, but requires proving that `idx` is valid.
pub assume_specification [ String::remove ] (s: &mut String, idx: usize) -> (ret: char)
    requires
        is_char_boundary(s@.as_bytes(), idx as int),
        idx < s@.as_bytes().len(),
    ensures
        ret as u32 == decode_first_scalar(old(s)@.as_bytes().skip(idx as int)),
        final(s)@.as_bytes() =~= 
            old(s)@.as_bytes().take(idx as int) + pop_first_scalar(old(s)@.as_bytes().skip(idx as int)),
;

/// Enable `String::retain`. 
pub assume_specification<F> [ String::retain ] (s: &mut String, f: F)
    where
        F: FnMut(char) -> bool,
    ensures
        final(s)@ =~= old(s)@.filter(|c: char| call_ensures(f, (c,), true)),
;

/// Enable `String::split_off`. 
///
/// Note that this function no longer panics, but requires proving that `at` 
/// falls between code points.
pub assume_specification [ String::split_off ] (s: &mut String, at: usize) -> (rem: String)
    requires
        is_char_boundary(s@.as_bytes(), at as int),
    ensures
        final(s)@.as_bytes() =~= old(s)@.as_bytes().take(at as int),
        rem@.as_bytes() =~= old(s)@.as_bytes().skip(at as int),
;

/// Enable `String::truncate`. 
///
/// Note that this function no longer panics, but requires proving that `new_len` 
/// either falls between code points or is past the end of the string.
pub assume_specification [ String::truncate ] (s: &mut String, new_len: usize) 
    requires
        new_len > s@.as_bytes().len() || is_char_boundary(s@.as_bytes(), new_len as int),
    ensures
        new_len <= old(s)@.as_bytes().len() ==> final(s)@.as_bytes() =~= old(s)@.as_bytes().take(new_len as int),
        new_len > old(s)@.as_bytes().len() ==> final(s)@.as_bytes() =~= old(s)@.as_bytes(),
    no_unwind
;

/// Additional methods on `String`. 
pub trait StringAdditionalFns: Sized + View<V = Seq<char>> {
    fn from_utf8_verified(vec: Vec<u8>) -> (ret: Self)
        requires 
            vec@.is_utf8(),
        ensures
            ret@ =~= vec@.as_str(),
        no_unwind;
}

impl StringAdditionalFns for String {
    /// Enable `String::from_utf8_verified` which wraps `String::from_utf8_unchecked`; note that 
    /// this is no longer `unsafe`.
    #[verifier::external_body]
    fn from_utf8_verified(vec: Vec<u8>) -> (ret: String) {
        unsafe { String::from_utf8_unchecked(vec) }
    }
}

} // verus!
