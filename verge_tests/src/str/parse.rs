//! Tests for `std::str::FromStr` and integer parsing APIs specified by Verge.

use vstd::prelude::*;
use vstd::assert_by_contradiction;
use verge::prelude::*;
use verge::str::*;
use std::str::FromStr;

verus! {

fn test_from_str_method_postconditions() {
    test!(matches!("true".parse::<bool>(), Ok(true)), {
        proof { reveal_strlit("true") }
    });
    test!(matches!("a".parse::<char>(), Ok('a')), {
        proof { reveal_strlit("a") }
    });
    let parsed_four = "4".parse::<u32>();
    match parsed_four {
        Ok(value) => test!(value == 4u32, {
            proof {
                reveal_strlit("4");
                reveal(spec_int_from_str_radix);
                reveal_with_fuel(spec_int_from_str_radix_rec, 2);
            }
        }),
        Err(_) => {},
    }
}

fn test_from_str_bool_examples() {
    proof { 
        reveal_strlit("x");
        reveal_strlit("true");
        reveal_strlit("false");
    }
    test!(matches!(<bool as FromStr>::from_str("true"), Ok(true)));
    test!(matches!(<bool as FromStr>::from_str("false"), Ok(false)));
    test!(<bool as FromStr>::from_str("x").is_err(), {
        proof {
            assert_by_contradiction!(!exists|v: bool| <bool as verge::str::FromStrSpec>::from_str_ok_ensures("x"@, v), {
                let v = choose|v: bool| <bool as verge::str::FromStrSpec>::from_str_ok_ensures("x"@, v);
                assert("x"@ == "true"@ || "x"@ == "false"@);
            });
        }
    });
}

fn test_from_str_char_examples() {
    proof {
        reveal_strlit("a");
        reveal_strlit("");
        reveal_strlit("abc");
    }

    test!(matches!(<char as FromStr>::from_str("a"), Ok('a')));
    test!(<char as FromStr>::from_str("").is_err());
    test!(<char as FromStr>::from_str("abc").is_err());
}

fn test_int_from_str_boundary_cases() {
    broadcast use verge::cmp::result::group_result_ordering;
    broadcast use verge::str::parse::group_parse_error_comparison;
    proof {
        reveal_strlit("255");
        reveal_strlit("127");
        reveal_strlit("-128");
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 4);
    }
    
    // XXX: due to a bug in Verus's parser, `Ok(-128i8)` inside `matches!` is 
    // not accepted; thus direct `exec` comparison is used here.
    // As a by product this also showcases how proofs for that is done.
    test!(<u8 as FromStr>::from_str("255") == Ok(255), {
        assert(<u8 as FromStrSpec>::from_str_ok_ensures("255"@, 255u8));
    });
    test!(<i8 as FromStr>::from_str("127") == Ok(127), {
        assert(<i8 as FromStrSpec>::from_str_ok_ensures("127"@, 127i8));
    });
    test!(<i8 as FromStr>::from_str("-128") == Ok(-128), {
        assert(<i8 as FromStrSpec>::from_str_ok_ensures("-128"@, -128i8));
    });
}

fn test_int_from_str_error_kind_cases() {
    proof {
        reveal_strlit("");
        reveal_strlit("123Hello");
        reveal_strlit("-");
        reveal_strlit("-1");
        reveal_strlit("256");
        reveal_strlit("128");
        reveal_strlit("-129");
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 8);
    }

    let empty = <u8 as FromStr>::from_str("");
    test!(empty.is_err());
    assert(empty->Err_0.kind() is Empty);

    let trailing_text = <u8 as FromStr>::from_str("123Hello");
    test!(trailing_text.is_err());
    assert(trailing_text->Err_0.kind() is InvalidDigit) by {
        assert(!char_is_digit_radix("123Hello"@[3], 10));
    }

    let bare_minus = <i8 as FromStr>::from_str("-");
    test!(bare_minus.is_err());
    assert(bare_minus->Err_0.kind() is InvalidDigit);

    let unsigned_negative = <u8 as FromStr>::from_str("-1");
    test!(unsigned_negative.is_err());
    assert(unsigned_negative->Err_0.kind() is InvalidDigit) by {
        assert("-1"@[0] == '-');
        assert(!char_is_digit_radix("-1"@[0], 10));
        assert(!str_is_valid_int_radix("-1"@, 10, false));
    }

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
    proof {
        reveal_strlit("1001");
        reveal_strlit("ffff");
        reveal_strlit("z");
        reveal_strlit("Z");
        reveal_strlit("_");
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 8);
        assert(str_is_valid_int_radix("1001"@, 2, false));
        assert(spec_int_from_str_radix("1001"@, 2) == 9);
        assert(str_is_valid_int_radix("ffff"@, 16, false));
        assert(spec_int_from_str_radix("ffff"@, 16) == 65535);
        assert(str_is_valid_int_radix("z"@, 36, false));
        assert(spec_int_from_str_radix("z"@, 36) == 35);
    }

    if let Ok(value) = u32::from_str_radix("1001", 2) {
        test!(value == 9u32);
    }
    if let Ok(value) = u16::from_str_radix("ffff", 16) {
        test!(value == 65535u16);
    }
    if let Ok(value) = u8::from_str_radix("z", 36) {
        test!(value == 35u8);
    }

    let invalid_decimal = u8::from_str_radix("Z", 10);
    test!(invalid_decimal.is_err());
    assert(invalid_decimal->Err_0.kind() is InvalidDigit) by {
        assert(!char_is_digit_radix("Z"@[0], 10));
    }

    let invalid_binary = u8::from_str_radix("_", 2);
    test!(invalid_binary.is_err());
    assert(invalid_binary->Err_0.kind() is InvalidDigit);
}

fn test_from_str_radix_leading_plus_boundary_from_core() {
    broadcast use verge::cmp::result::group_result_ordering;
    broadcast use verge::str::parse::group_parse_error_comparison;
    proof {
        reveal_strlit("+9223372036854775807");
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 24);
        assert(str_is_valid_int_radix("+9223372036854775807"@, 10, true));
        assert(spec_int_from_str_radix("+9223372036854775807"@, 10) == i64::MAX);
    }
    if let Ok(value) = i64::from_str_radix("+9223372036854775807", 10) {
        test!(value == i64::MAX);
    }
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
    assert_eq!("4".parse::<u32>(), Ok(4));
    assert_eq!(u32::from_str_radix("1001", 2), Ok(9));
    assert_eq!(u16::from_str_radix("ffff", 16), Ok(65535));
    assert_eq!(u8::from_str_radix("z", 36), Ok(35));
    assert_eq!(i64::from_str_radix("+9223372036854775807", 10), Ok(i64::MAX));
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
