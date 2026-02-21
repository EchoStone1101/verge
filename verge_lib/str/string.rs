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

/// Enable `String::len`. Note that this returns length in bytes.
pub assume_specification [ String::len ] (s: &String) -> (ret: usize)
    ensures
        ret == s@.as_bytes().len(),
    no_unwind
;

/// Enable `String::new`.
pub assume_specification [ String::new ] () -> (s: String)
    ensures
        s@ =~= Seq::<char>::empty(),
    no_unwind
;

/// Enable `String::with_capacity`.
pub assume_specification [ String::with_capacity ] (cap: usize) -> (s: String)
    ensures
        s@ =~= Seq::<char>::empty(),
;

/// Enable `String::into_bytes`.
pub assume_specification [ String::into_bytes ] (s: String) -> (bytes: Vec<u8>)
    ensures
        bytes@ =~= s@.as_bytes(),
    no_unwind
;

/// Enable `String::clear`.
pub assume_specification [ String::clear ] (s: &mut String)
    ensures
        s@ =~= Seq::<char>::empty(),
    no_unwind
;

/// Enable `String::push`. 
pub assume_specification [ String::push ] (s: &mut String, ch: char) 
    ensures
        s@ =~= old(s)@.push(ch),
;

/// Enable `String::pop`. 
pub assume_specification [ String::pop ] (s: &mut String) -> (ch: Option<char>) 
    ensures
        old(s)@.len() > 0 ==> s@ =~= old(s)@.drop_last() && ch == Some(old(s)@.last()),
        old(s)@.len() == 0 ==> s@ =~= old(s)@ && ch.is_none(),
    no_unwind
;

/// Enable `String::reserve`. 
pub assume_specification [ String::reserve ] (s: &mut String, _amt: usize) 
    ensures
        s@ =~= old(s)@,
;

/// Enable `String::reserve_exact`. 
pub assume_specification [ String::reserve_exact ] (s: &mut String, _amt: usize) 
    ensures
        s@ =~= old(s)@,
;

/// Enable `String::insert`. 
///
/// Note that this function no longer panics, but requires proving that `idx` 
/// falls between code points. 
pub assume_specification [ String::insert ] (s: &mut String, idx: usize, ch: char) 
    requires
        idx <= old(s)@.as_bytes().len(),
        old(s)@.as_bytes().take(idx as int).is_utf8(), 
        old(s)@.as_bytes().skip(idx as int).is_utf8(), 
    ensures
        s@.as_bytes() =~= old(s)@.as_bytes().take(idx as int) + seq![ch].as_bytes() + old(s)@.as_bytes().skip(idx as int),
;

/// Enable `String::insert_str`. 
///
/// Note that this function no longer panics, but requires proving that `idx` 
/// falls between code points. 
pub assume_specification [ String::insert_str ] (s: &mut String, idx: usize, string: &str) 
    requires
        idx <= old(s)@.as_bytes().len(),
        old(s)@.as_bytes().take(idx as int).is_utf8(),
        old(s)@.as_bytes().skip(idx as int).is_utf8(),
    ensures
        s@.as_bytes() =~= old(s)@.as_bytes().take(idx as int) + string@.as_bytes() + old(s)@.as_bytes().skip(idx as int),
;

/// Enable `String::split_off`. 
///
/// Note that this function no longer panics, but requires proving that `at` 
/// falls between code points.
pub assume_specification [ String::split_off ] (s: &mut String, at: usize) -> (rem: String)
    requires
        at <= old(s)@.as_bytes().len(),
        old(s)@.as_bytes().take(at as int).is_utf8(), 
        old(s)@.as_bytes().skip(at as int).is_utf8(), 
    ensures
        s@.as_bytes() =~= old(s)@.as_bytes().take(at as int),
        rem@.as_bytes() =~= old(s)@.as_bytes().skip(at as int),
;

/// Enable `String::truncate`. 
///
/// Note that this function no longer panics, but requires proving that `new_len` 
/// falls between code points.
pub assume_specification [ String::truncate ] (s: &mut String, new_len: usize) 
    requires
        new_len <= old(s)@.as_bytes().len(),
        old(s)@.as_bytes().take(new_len as int).is_utf8(), 
    ensures
        s@.as_bytes() =~= old(s)@.as_bytes().take(new_len as int),
    no_unwind
;

pub trait StringExecFromUtf8Fns {
    fn from_utf8_checked(vec: Vec<u8>) -> (res: Result<String, FromUtf8Error>)
        ensures 
            vec@.is_utf8() <==> res.is_ok(),
        no_unwind
    ;

    fn from_utf8_verified(vec: Vec<u8>) -> String
        requires 
            vec@.is_utf8(),
        no_unwind
    ;
}

impl StringExecFromUtf8Fns for String {

    /// Enable `String::from_utf8`.
    #[verifier::external_body]
    fn from_utf8_checked(vec: Vec<u8>) -> (res: Result<String, FromUtf8Error>)
        ensures 
            ({
                match res {
                    Ok(s) => s@ =~= vec@.as_str(),
                    _ => true,
                }
            }),
    {
        String::from_utf8(vec)
    }

    /// Enable `String::from_utf8_unchecked`; note that this is no longer `unsafe`.
    #[verifier::external_body]
    fn from_utf8_verified(vec: Vec<u8>) -> (s: String)
        ensures 
            s@ =~= vec@.as_str(),
    {
        unsafe { String::from_utf8_unchecked(vec) }
    }
}

} // verus!