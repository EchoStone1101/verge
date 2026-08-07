//! Tests for `std::str::FromStr` and integer parsing APIs specified by Verge.

use vstd::prelude::*;
use verge::prelude::*;
use verge::str::*;
use std::str::FromStr;

verus! {

fn test_from_str_method_postconditions() {
    test!(matches!("true".parse::<bool>(), Ok(true)));
    test!(matches!("a".parse::<char>(), Ok('a')));
    test!(matches!("4".parse::<u32>(), Ok(4u32)));
}

fn test_from_str_bool_examples() {
    test!(matches!(<bool as FromStr>::from_str("true"), Ok(true)));
    test!(matches!(<bool as FromStr>::from_str("false"), Ok(false)));
    test!(<bool as FromStr>::from_str("x").is_err());
}

fn test_from_str_char_examples() {
    test!(matches!(<char as FromStr>::from_str("a"), Ok('a')));
    test!(<char as FromStr>::from_str("").is_err());
    test!(<char as FromStr>::from_str("abc").is_err());
}

fn test_int_from_str_boundary_cases() {
    test!(<u8 as FromStr>::from_str("255") == Ok(255));
    test!(<i8 as FromStr>::from_str("127") == Ok(127));
    test!(<i8 as FromStr>::from_str("-128") == Ok(-128));
}

fn test_int_from_str_error_kind_cases() {
    let empty = <u8 as FromStr>::from_str("");
    test!(empty.is_err());
    assert(empty->Err_0.kind() is Empty);

    let trailing_text = <u8 as FromStr>::from_str("123Hello");
    test!(trailing_text.is_err());
    assert(trailing_text->Err_0.kind() is InvalidDigit);

    let bare_minus = <i8 as FromStr>::from_str("-");
    test!(bare_minus.is_err());
    assert(bare_minus->Err_0.kind() is InvalidDigit);

    let unsigned_negative = <u8 as FromStr>::from_str("-1");
    test!(unsigned_negative.is_err());
    assert(unsigned_negative->Err_0.kind() is InvalidDigit);

    let u8_overflow = <u8 as FromStr>::from_str("256");
    test!(u8_overflow.is_err());
    assert(u8_overflow->Err_0.kind() is PosOverflow);

    let i8_pos_overflow = <i8 as FromStr>::from_str("128");
    test!(i8_pos_overflow.is_err());
    assert(i8_pos_overflow->Err_0.kind() is PosOverflow);

    let i8_neg_overflow = <i8 as FromStr>::from_str("-129");
    test!(i8_neg_overflow.is_err());
    assert(i8_neg_overflow->Err_0.kind() is NegOverflow);
}

fn test_from_str_radix_examples() {
    test!(matches!(u32::from_str_radix("1001", 2), Ok(9u32)));
    test!(matches!(u16::from_str_radix("ffff", 16), Ok(65535u16)));
    test!(matches!(u8::from_str_radix("z", 36), Ok(35u8)));

    let invalid_decimal = u8::from_str_radix("Z", 10);
    test!(invalid_decimal.is_err());
    assert(invalid_decimal->Err_0.kind() is InvalidDigit);

    let invalid_binary = u8::from_str_radix("_", 2);
    test!(invalid_binary.is_err());
    assert(invalid_binary->Err_0.kind() is InvalidDigit);
}

fn test_from_str_radix_leading_plus_boundary_from_core() {
    test!(i64::from_str_radix("+9223372036854775807", 10) == Ok(i64::MAX));
}

fn test_to_string_round_trips_are_usable() {
    test!(matches!(<bool as FromStr>::from_str((true.to_string()).as_str()), Ok(true)), {
        proof { <bool as FromToStr>::lemma_round_tripping(true) }
    });

    test!(matches!(<char as FromStr>::from_str(('q'.to_string()).as_str()), Ok('q')), {
        proof { <char as FromToStr>::lemma_round_tripping('q') }
    });

    test!(matches!(<i32 as FromStr>::from_str(((-123i32).to_string()).as_str()), Ok(-123i32)), {
        proof { <i32 as FromToStr>::lemma_round_tripping(-123i32) }
    });

    test!(matches!(<u32 as FromStr>::from_str((42u32.to_string()).as_str()), Ok(42u32)), {
        proof { <u32 as FromToStr>::lemma_round_tripping(42u32) }
    });
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "str::parse::from_str_method_postconditions",
        test_from_str_method_postconditions,
    );
    count += crate::run_test(
        "str::parse::from_str_bool_examples",
        test_from_str_bool_examples,
    );
    count += crate::run_test(
        "str::parse::from_str_char_examples",
        test_from_str_char_examples,
    );
    count += crate::run_test(
        "str::parse::int_from_str_boundary_cases",
        test_int_from_str_boundary_cases,
    );
    count += crate::run_test(
        "str::parse::int_from_str_error_kind_cases",
        test_int_from_str_error_kind_cases,
    );
    count += crate::run_test(
        "str::parse::from_str_radix_examples",
        test_from_str_radix_examples,
    );
    count += crate::run_test(
        "str::parse::from_str_radix_leading_plus_boundary_from_core",
        test_from_str_radix_leading_plus_boundary_from_core,
    );
    count += crate::run_test(
        "str::parse::to_string_round_trips_are_usable",
        test_to_string_round_trips_are_usable,
    );
    count
}
