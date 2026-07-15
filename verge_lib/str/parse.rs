//! Specifications and lemmas for parsing values from a string.
//!
//! This module specifies `std::str::FromStr` directly via `FromStrSpec`.
//! Implement `FromStrSpecImpl` for custom `FromStr` types to define the
//! validity predicate and value/error postconditions of `from_str()`.
use super::*;
use vstd::std_specs::result::{spec_unwrap_err, spec_unwrap};
use vstd::prelude::Integer;
pub use std::str::{
    ParseBoolError,
};
pub use std::num::{
    ParseIntError, IntErrorKind,
};
use std::str::FromStr;
use std::fmt::Debug;

verus! {

/// Specification for the `FromStr` trait.
///
/// Note that in general, the `from_str` method is not always `no_unwind` (for example, when creating `Self` involves 
/// heap allocation). `from_str_no_unwind()` explicitly models this.
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(FromStrSpec via FromStrSpecImpl)]
pub trait ExFromStr: Sized {
    type ExternalTraitSpecificationFor: FromStr;

    type Err;

    spec fn from_str_ok_ensures(s: Seq<char>, value: Self) -> bool;

    spec fn from_str_err_ensures(s: Seq<char>, err: Self::Err) -> bool;

    spec fn from_str_no_unwind() -> bool;

    fn from_str(s: &str) -> (res: Result<Self, Self::Err>)
        ensures
            res.is_ok() ==> Self::from_str_ok_ensures(s@, res->Ok_0),
            res.is_err() ==> Self::from_str_err_ensures(s@, res->Err_0),
        no_unwind when Self::from_str_no_unwind()
    ;
}

#[verifier::external_type_specification]
pub struct ExParseBoolError(ParseBoolError);

/// Enable `<bool as FromStr>::from_str`.
pub assume_specification [ <bool as FromStr>::from_str ] (s: &str) -> Result<bool, ParseBoolError>;

impl FromStrSpecImpl for bool {
    open spec fn from_str_ok_ensures(s: Seq<char>, value: bool) -> bool {
        &&& value <==> s == seq!['t', 'r', 'u', 'e']
        &&& !value <==> s == seq!['f', 'a', 'l', 's', 'e']
    }

    open spec fn from_str_err_ensures(s: Seq<char>, err: Self::Err) -> bool {
        &&& err.is_str_parse_error()
        &&& s != seq!['t', 'r', 'u', 'e'] && s != seq!['f', 'a', 'l', 's', 'e']
    }

    open spec fn from_str_no_unwind() -> bool { true }
}


#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExParseIntError(ParseIntError);

#[verifier::external_type_specification]
pub struct ExIntErrorKind(IntErrorKind);

pub uninterp spec fn spec_int_error_kind(e: &ParseIntError) -> &IntErrorKind;

/// Enable `ParseIntError::kind`.
#[verifier::when_used_as_spec(spec_int_error_kind)]
pub assume_specification[ ParseIntError::kind ](e: &ParseIntError) -> (kind: &IntErrorKind)
    ensures
        spec_int_error_kind(e) == kind,
;

/// This function encodes whether a string can be parsed as an arbitrarily large `int` in 
/// the supplied radix, ignoring machine-integer bounds.
#[verifier::opaque]
pub open spec fn str_is_valid_int_radix(s: Seq<char>, radix: int, signed: bool) -> bool
    recommends
        2 <= radix,
{
    &&& s.len() > 0
    &&& if s.first() == '+' || (signed && s.first() == '-') {
        &&& s.len() > 1
        &&& forall|i: int| 1 <= i < s.len() ==> #[trigger] char_is_digit_radix(s[i], radix)
    } else {
        forall|i: int| 0 <= i < s.len() ==> #[trigger] char_is_digit_radix(s[i], radix)
    }
}

/// This function encodes parsing an arbitrarily large `int` from a string in the supplied radix. 
#[verifier::opaque]
pub open spec fn spec_int_from_str_radix(s: Seq<char>, radix: int) -> int
    recommends
        2 <= radix,
        str_is_valid_int_radix(s, radix, true),
{
    if s.first() == '+' {
        spec_int_from_str_radix_rec(s.drop_first(), 0, radix)
    } else if s.first() == '-' {
        -spec_int_from_str_radix_rec(s.drop_first(), 0, radix)
    } else {
        spec_int_from_str_radix_rec(s, 0, radix)
    }
}

/// This function encodes parsing an unsigned digit sequence as an arbitrarily large `int`,
/// recursively, in the supplied radix.
pub open spec fn spec_int_from_str_radix_rec(s: Seq<char>, n: int, radix: int) -> int
    recommends
        2 <= radix,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] char_is_digit_radix(s[i], radix),
    decreases
        s.len(),
{
    if s.len() == 0 {
        n
    } else {
        spec_int_from_str_radix_rec(
            s.drop_first(),
            radix * n + char_digit_value(s.first()),
            radix,
        )
    }
}

/// Encodes whether `c` is an ASCII digit in the supplied radix.
pub open spec fn char_is_digit_radix(c: char, radix: int) -> bool
    recommends
        2 <= radix,
{
    0 <= char_digit_value(c) < radix
}

/// Encodes the numeric value of an ASCII radix digit.
///
/// Non-digits map to `-1`; use `char_is_digit_radix` when checking validity.
pub open spec fn char_digit_value(c: char) -> int {
    if (CHAR_ZERO as int) <= (c as u32) <= (CHAR_NINE as int) {
        (c as u32) as int - (CHAR_ZERO as int)
    } else if (CHAR_LOWER_A as int) <= (c as u32) <= (CHAR_LOWER_Z as int) {
        (c as u32) as int - (CHAR_LOWER_A as int) + 10
    } else if (CHAR_UPPER_A as int) <= (c as u32) <= (CHAR_UPPER_Z as int) {
        (c as u32) as int - (CHAR_UPPER_A as int) + 10
    } else {
        -1
    }
}

macro_rules! impl_from_str_signed_int {
    ($($ty:ident),+) => {
        verus! {
        $(
        impl FromStrSpecImpl for $ty {
            open spec fn from_str_ok_ensures(s: Seq<char>, value: $ty) -> bool {
                &&& str_is_valid_int_radix(s, 10, true)
                &&& value as int == spec_int_from_str_radix(s, 10)
                &&& ($ty::MIN as int) <= (value as int) <= ($ty::MAX as int)
            }
            open spec fn from_str_err_ensures(s: Seq<char>, err: Self::Err) -> bool {
                &&& err.is_str_parse_error()
                &&& err.kind() is Empty
                    ==> s.len() == 0
                &&& err.kind() is InvalidDigit
                    ==> s.len() > 0 && !str_is_valid_int_radix(s, 10, true)
                &&& err.kind() is PosOverflow
                    ==> s.len() > 0 
                    && str_is_valid_int_radix(s, 10, true) 
                    && spec_int_from_str_radix(s, 10) > ($ty::MAX as int)
                &&& err.kind() is NegOverflow
                    ==> s.len() > 0 
                    && str_is_valid_int_radix(s, 10, true) 
                    && spec_int_from_str_radix(s, 10) < ($ty::MIN as int)
                &&& !(err.kind() is Zero)
            }
            open spec fn from_str_no_unwind() -> bool { true }
        }
        
        pub assume_specification [ <$ty as FromStr>::from_str ] (s: &str) -> Result<$ty, ParseIntError>;

        pub assume_specification [ $ty::from_str_radix ] (s: &str, radix: u32) -> (res: Result<$ty, ParseIntError>)
            requires
                2 <= radix <= 36,
            ensures
                res.is_ok() ==> {
                    &&& str_is_valid_int_radix(s@, radix as int, true)
                    &&& res->Ok_0 as int == spec_int_from_str_radix(s@, radix as int)
                    &&& ($ty::MIN as int) <= (res->Ok_0 as int) <= ($ty::MAX as int)
                },
                res.is_err() ==> {
                    let err = res->Err_0;
                    &&& err.is_str_parse_error()
                    &&& err.kind() is Empty
                        ==> s@.len() == 0
                    &&& err.kind() is InvalidDigit
                        ==> s@.len() > 0 && !str_is_valid_int_radix(s@, radix as int, true)
                    &&& err.kind() is PosOverflow
                        ==> s@.len() > 0 
                        && str_is_valid_int_radix(s@, radix as int, true) 
                        && spec_int_from_str_radix(s@, radix as int) > ($ty::MAX as int)
                    &&& err.kind() is NegOverflow
                        ==> s@.len() > 0 
                        && str_is_valid_int_radix(s@, radix as int, true) 
                        && spec_int_from_str_radix(s@, radix as int) < ($ty::MIN as int)
                    &&& !(err.kind() is Zero)
                },
            no_unwind;
        )+
        }
    }
}

macro_rules! impl_from_str_unsigned_int {
    ($($ty:ident),+) => {
        verus! {
        $(
        impl FromStrSpecImpl for $ty {
            open spec fn from_str_ok_ensures(s: Seq<char>, value: $ty) -> bool {
                &&& str_is_valid_int_radix(s, 10, false)
                &&& value as int == spec_int_from_str_radix(s, 10)
                &&& (value as int) <= ($ty::MAX as int)
            }
            open spec fn from_str_err_ensures(s: Seq<char>, err: Self::Err) -> bool {
                &&& err.is_str_parse_error()
                &&& err.kind() is Empty
                    ==> s.len() == 0
                &&& err.kind() is InvalidDigit
                    ==> s.len() > 0 && !str_is_valid_int_radix(s, 10, false)
                &&& err.kind() is PosOverflow
                    ==> s.len() > 0 
                    && str_is_valid_int_radix(s, 10, false) 
                    && spec_int_from_str_radix(s, 10) > ($ty::MAX as int)
                &&& !(err.kind() is NegOverflow)
                &&& !(err.kind() is Zero)
            }
            open spec fn from_str_no_unwind() -> bool { true }
        }
        
        pub assume_specification [ <$ty as FromStr>::from_str ] (s: &str) -> Result<$ty, ParseIntError>;

        pub assume_specification [ $ty::from_str_radix ] (s: &str, radix: u32) -> (res: Result<$ty, ParseIntError>)
            requires
                2 <= radix <= 36,
            ensures
                res.is_ok() ==> {
                    &&& str_is_valid_int_radix(s@, radix as int, false)
                    &&& res->Ok_0 == spec_int_from_str_radix(s@, radix as int)
                    &&& (res->Ok_0 as int) <= ($ty::MAX as int)
                },
                res.is_err() ==> {
                    let err = res->Err_0;
                    &&& err.is_str_parse_error()
                    &&& err.kind() is Empty
                        ==> s@.len() == 0
                    &&& err.kind() is InvalidDigit
                        ==> s@.len() > 0 && !str_is_valid_int_radix(s@, radix as int, false)
                    &&& err.kind() is PosOverflow
                        ==> s@.len() > 0 
                        && str_is_valid_int_radix(s@, radix as int, false) 
                        && spec_int_from_str_radix(s@, radix as int) > ($ty::MAX as int)
                    &&& !(err.kind() is NegOverflow)
                    &&& !(err.kind() is Zero)
                },
            no_unwind;
        )+
        }
    }
}

impl_from_str_signed_int!(i8, i16, i32, i64, i128, isize);
impl_from_str_unsigned_int!(u8, u16, u32, u64, u128, usize);

} // verus!
