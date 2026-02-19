//! Specifications and lemmas for `std::String`.

use super::*;

verus! {

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExFromUtf8Error(std::string::FromUtf8Error);

/// Enable `String::into_bytes`.
pub assume_specification [ String::into_bytes ] (s: String) -> (bytes: Vec<u8>)
    ensures
        bytes@ =~= as_bytes(s@),
        is_utf8(as_bytes(s@)),
    no_unwind
;

/// Enable `String::clear`.
pub assume_specification [ String::clear ] (s: &mut String)
    ensures
        s@ =~= Seq::<char>::empty(),
        is_utf8(as_bytes(s@)),
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
        idx <= as_bytes(old(s)@).len(),
        is_utf8(as_bytes(old(s)@).take(idx as int)), 
        is_utf8(as_bytes(old(s)@).skip(idx as int)), 
    ensures
        s@ =~= as_str(as_bytes(old(s)@).take(idx as int)).push(ch) + as_str(as_bytes(old(s)@).skip(idx as int)),
;

/// Enable `String::remove`. 
///
/// Note that this function no longer panics, but requires proving that `idx` 
/// falls between code points. 
pub assume_specification [ String::remove ] (s: &mut String, idx: usize) -> (ch: char)
    requires
        idx < as_bytes(old(s)@).len(),
        is_utf8(as_bytes(old(s)@).take(idx as int)), 
        is_utf8(as_bytes(old(s)@).skip(idx as int)), 
    ensures
        s@ =~= as_str(as_bytes(old(s)@).take(idx as int)) + as_str(as_bytes(old(s)@).skip(idx as int)).drop_first(),
        ch == as_str(as_bytes(old(s)@).skip(idx as int)).first(),
    no_unwind
;

/// Enable `String::insert_str`. 
///
/// Note that this function no longer panics, but requires proving that `idx` 
/// falls between code points. 
pub assume_specification [ String::insert_str ] (s: &mut String, idx: usize, string: &str) 
    requires
        idx <= as_bytes(old(s)@).len(),
        is_utf8(as_bytes(old(s)@).take(idx as int)), 
        is_utf8(as_bytes(old(s)@).skip(idx as int)), 
    ensures
        s@ =~= as_str(as_bytes(old(s)@).take(idx as int)) + string@ + as_str(as_bytes(old(s)@).skip(idx as int)),
;

/// Enable `String::truncate`. 
///
/// Note that this function no longer panics, but requires proving that `new_len` 
/// falls between code points.
pub assume_specification [ String::truncate ] (s: &mut String, new_len: usize) 
    requires
        new_len <= as_bytes(old(s)@).len(),
        is_utf8(as_bytes(old(s)@).take(new_len as int)), 
    ensures
        s@ =~= as_str(as_bytes(old(s)@).take(new_len as int)),
    no_unwind
;

pub trait StringExecFromUtf8Fns {

    /// Enable `String::from_utf8`.
    fn from_utf8_checked(vec: Vec<u8>) -> (res: Result<String, std::string::FromUtf8Error>)
        ensures 
            is_utf8(vec@) <==> res.is_ok(),
        no_unwind
    ;

    /// Enable `String::from_utf8_unchecked`; note that this is no longer `unsafe`.
    fn from_utf8_verified(vec: Vec<u8>) -> String
        requires 
            is_utf8(vec@),
        no_unwind
    ;
}

impl StringExecFromUtf8Fns for String {

    #[verifier::external_body]
    fn from_utf8_checked(vec: Vec<u8>) -> (res: Result<String, std::string::FromUtf8Error>)
        ensures 
            ({
                match res {
                    Ok(s) => s@ =~= as_str(vec@),
                    _ => true,
                }
            }),
            
    {
        String::from_utf8(vec)
    }

    #[verifier::external_body]
    fn from_utf8_verified(vec: Vec<u8>) -> (s: String)
        ensures 
            s@ =~= as_str(vec@),
    {
        unsafe { String::from_utf8_unchecked(vec) }
    }
}


} // verus!