//! Specifications and lemmas for parsing values from a string.
//!
//! This module specifies `std::str::FromStr` directly via `FromStrSpec`.
//! Implement `FromStrSpecImpl` for custom `FromStr` types to define the
//! validity predicate and value/error postconditions of `from_str()`.
use super::*;
use vstd::std_specs::result::{spec_unwrap_err, spec_unwrap};
use vstd::prelude::Integer;
use vstd::assert_by_contradiction;
pub use std::str::ParseBoolError;
pub use std::char::ParseCharError;
pub use std::num::{ParseIntError, IntErrorKind};
use std::str::FromStr;
use std::fmt::Debug;

// XXX: Unfortunately, `vstd::string` currently has a separate `String::from_str` 
// defined via extension traits, which when `FromStr` is also in scope causes ambiguity. 

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
pub struct ExParseCharError(ParseCharError);

/// Enable `<char as FromStr>::from_str`.
pub assume_specification [ <char as FromStr>::from_str ] (s: &str) -> Result<char, <char as FromStr>::Err>;

impl FromStrSpecImpl for char {
    open spec fn from_str_ok_ensures(s: Seq<char>, value: char) -> bool {
        s == seq![value]
    }

    open spec fn from_str_err_ensures(s: Seq<char>, err: Self::Err) -> bool {
        &&& err.is_str_parse_error()
        &&& s.len() != 1
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
        spec_int_from_str_radix_rec(s.drop_first(), radix)
    } else if s.first() == '-' {
        -spec_int_from_str_radix_rec(s.drop_first(), radix)
    } else {
        spec_int_from_str_radix_rec(s, radix)
    }
}

/// This function encodes parsing an unsigned digit sequence as an arbitrarily large `int`,
/// recursively, in the supplied radix.
pub open spec fn spec_int_from_str_radix_rec(s: Seq<char>, radix: int) -> int
    recommends
        2 <= radix,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] char_is_digit_radix(s[i], radix),
    decreases
        s.len(),
{
    if s.len() == 0 {
        0
    } else {
        radix
        * spec_int_from_str_radix_rec(s.drop_last(), radix) 
        + char_digit_value(s.last())
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

/// This trait specifies round-tripping between `ToString` and `FromStr` - implementing
/// this trait for type `T` certifies that `T::from_str(t.to_string())` produces `t` itself.
///
/// Note that this definition uses strict `spec`-mode equality. As a result, it is 
/// generally only applicable to simple `Copy` types. For instance, `String` is not `FromToStr`
/// because the round-trip creates a new `String` which is not `spec`-mode equal to the old `String`.
pub trait FromToStr: ToString + FromStr {
    proof fn lemma_round_tripping(t: Self)
        ensures
            ({
                forall|s: String| #[trigger] t.to_string_ensures(s)
                    ==> Self::from_str_ok_ensures(s@, t) 
                    && !exists|err: <Self as FromStr>::Err| Self::from_str_err_ensures(s@, err)
            }),
    ;
}

impl FromToStr for bool {
    proof fn lemma_round_tripping(t: bool) {
        broadcast use crate::str::fmt::lemma_bool_to_string;

        assert forall|s: String| #[trigger] <bool as ToStringSpec>::to_string_ensures(&t, s) 
        implies <bool as FromStrSpec>::from_str_ok_ensures(s@, t) 
            && !exists|err: ParseBoolError| <bool as FromStrSpec>::from_str_err_ensures(s@, err)
        by {}
    }
}

impl FromToStr for char {
    proof fn lemma_round_tripping(t: char) {
        broadcast use crate::str::fmt::lemma_char_to_string;
        
        assert forall|s: String| #[trigger] <char as ToStringSpec>::to_string_ensures(&t, s) 
        implies <char as FromStrSpec>::from_str_ok_ensures(s@, t)
            && !exists|err: ParseCharError| <char as FromStrSpec>::from_str_err_ensures(s@, err)
        by {}
    }
}

macro_rules! proof_for_signed_int {
    ($($ty:ident),+) => {
        verus! {
        $(
        impl FromToStr for $ty {
            proof fn lemma_round_tripping(t: $ty) {
                broadcast use crate::str::fmt::lemma_int_to_string;

                assert forall|s: String| #[trigger] <$ty as ToStringSpec>::to_string_ensures(&t, s) 
                implies <$ty as FromStrSpec>::from_str_ok_ensures(s@, t)
                    && !exists|err: ParseIntError| <$ty as FromStrSpec>::from_str_err_ensures(s@, err)
                by { 
                    int_proofs::lemma_int_to_str_from_str(t as int, true);
                    assert_by_contradiction!(!exists|err: ParseIntError| <$ty as FromStrSpec>::from_str_err_ensures(s@, err), {
                        let err = choose|err: ParseIntError| <$ty as FromStrSpec>::from_str_err_ensures(s@, err);
                        assert(!(err.kind() is Empty)) by {
                            reveal(str_is_valid_int_radix);
                            assert(s@.len() > 0);
                        }
                        assert(!(err.kind() is InvalidDigit)) by {
                            assert(str_is_valid_int_radix(s@, 10, true));
                        }
                        assert(!(err.kind() is PosOverflow)) by {
                            assert(t <= $ty::MAX);
                        }
                        assert(!(err.kind() is NegOverflow)) by {
                            assert(t >= $ty::MIN);
                        }
                    });
                }
            }
        }
        )+
        }
    }
}

macro_rules! proof_for_unsigned_int {
    ($($ty:ident),+) => {
        verus! {
        $(
        impl FromToStr for $ty {
            proof fn lemma_round_tripping(t: $ty) {
                broadcast use crate::str::fmt::lemma_int_to_string;

                assert forall|s: String| #[trigger] <$ty as ToStringSpec>::to_string_ensures(&t, s) 
                implies <$ty as FromStrSpec>::from_str_ok_ensures(s@, t)
                    && !exists|err: ParseIntError| <$ty as FromStrSpec>::from_str_err_ensures(s@, err)
                by { 
                    int_proofs::lemma_int_to_str_from_str(t as int, false);
                    assert_by_contradiction!(!exists|err: ParseIntError| <$ty as FromStrSpec>::from_str_err_ensures(s@, err), {
                        let err = choose|err: ParseIntError| <$ty as FromStrSpec>::from_str_err_ensures(s@, err);
                        assert(!(err.kind() is Empty)) by {
                            reveal(str_is_valid_int_radix);
                            assert(s@.len() > 0);
                        }
                        assert(!(err.kind() is InvalidDigit)) by {
                            assert(str_is_valid_int_radix(s@, 10, false));
                        }
                        assert(!(err.kind() is PosOverflow)) by {
                            assert(t <= $ty::MAX);
                        }
                    });
                }
            }
        }
        )+
        }
    }
}

proof_for_signed_int!(i8, i16, i32, i64, i128, isize);
proof_for_unsigned_int!(u8, u16, u32, u64, u128, usize);

mod int_proofs {
    use super::*;
    use crate::str::fmt::{spec_int_to_str, spec_int_to_str_rec};
    use vstd::arithmetic::div_mod::{
        lemma_div_decreases, 
        lemma_fundamental_div_mod,
        lemma_mod_bound,
    };
    use vstd::calc;

    pub(super) proof fn lemma_int_to_str_from_str(n: int, signed: bool)
        requires
            n < 0 ==> signed,
        ensures
            str_is_valid_int_radix(spec_int_to_str(n), 10, signed),
            spec_int_from_str_radix(spec_int_to_str(n), 10) == n,
    {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal(spec_int_to_str);
        if n == 0 {
            assert(spec_int_to_str(0) == seq!['0']);
            reveal_with_fuel(spec_int_from_str_radix_rec, 3);
            assert(10 * 0 + 0 == 0);
        } else if n > 0 {
            lemma_int_to_str_valid_rec(n as nat);
            lemma_int_to_str_from_str_rec(n as nat);
            assert(char_is_digit_radix(spec_int_to_str_rec(n as nat).first(), 10));
        } else {
            assert(spec_int_to_str(n) == seq!['-'] + spec_int_to_str_rec((-n) as nat));
            calc!{
                (==)
                spec_int_from_str_radix(spec_int_to_str(n), 10); {}
                spec_int_from_str_radix(
                    seq!['-'] + spec_int_to_str_rec((-n) as nat),
                    10,
                ); {
                    assert((seq!['-'] + spec_int_to_str_rec((-n) as nat)).drop_first() == spec_int_to_str_rec((-n) as nat));
                }
                -spec_int_from_str_radix_rec(spec_int_to_str_rec((-n) as nat), 10); {
                    lemma_int_to_str_from_str_rec((-n) as nat);
                }
                -(-n); {}
                n;
            }
            lemma_int_to_str_valid_rec((-n) as nat);
        }
    }

    proof fn lemma_int_to_str_valid_rec(n: nat)
        ensures
            forall|i: int| 0 <= i < spec_int_to_str_rec(n).len() 
                ==> #[trigger] char_is_digit_radix(spec_int_to_str_rec(n)[i], 10),
        decreases n,
    {
        if n == 0 { /* base case */ } 
        else {
            lemma_div_decreases(n as int, 10);
            let s = spec_int_to_str_rec(n);
            assert(s == spec_int_to_str_rec(n / 10).push((n % 10 + CHAR_ZERO) as char));

            lemma_int_to_str_valid_rec(n / 10);
            assert forall|i: int| 0 <= i < s.len() - 1
            implies #[trigger] char_is_digit_radix(s[i], 10) 
            by {
                assert(s[i] == spec_int_to_str_rec(n / 10)[i]);
            }

            assert(char_is_digit_radix(s.last(), 10)) by {
                lemma_mod_bound(n as int, 10);
            }
        }
    }

    proof fn lemma_int_to_str_from_str_rec(n: nat)
        ensures
            spec_int_from_str_radix_rec(spec_int_to_str_rec(n), 10) == n,
        decreases n
    {
        if n == 0 { /* base case */ } 
        else {
            lemma_div_decreases(n as int, 10);
            let s = spec_int_to_str_rec(n);
            calc!{
                (==)
                spec_int_from_str_radix_rec(s, 10); {}
                10 * spec_int_from_str_radix_rec(s.drop_last(), 10) + char_digit_value(s.last()); {
                    assert(s.drop_last() == spec_int_to_str_rec(n / 10));
                    assert(char_digit_value(s.last()) == n % 10);
                }
                10 * spec_int_from_str_radix_rec(spec_int_to_str_rec(n / 10), 10) + (n % 10); {
                    lemma_int_to_str_from_str_rec(n / 10);
                }
                (10 * (n / 10) + (n % 10)) as int; {
                    lemma_fundamental_div_mod(n as int, 10);
                }
                n as int;
            }
        }
    }
}

} // verus!
