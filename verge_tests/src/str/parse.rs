//! Tests for `std::str::FromStr` and integer parsing APIs specified by Verge.

use vstd::prelude::*;
use verge::error::ErrorSpec;
use verge::prelude::*;
use verge::str::*;
use std::str::FromStr;

verus! {

fn test_parse_method_postconditions() {
    let parsed_bool = "true".parse::<bool>();
    let parsed_char = "a".parse::<char>();
    let parsed_u32 = "4".parse::<u32>();

    proof {
        reveal_strlit("true");
        reveal_strlit("a");
        reveal_strlit("4");
        assert(parsed_bool.is_ok());
        assert(parsed_char.is_ok());
        assert(parsed_u32.is_ok()) by {
            reveal(str_is_valid_int_radix);
            reveal(spec_int_from_str_radix);
            reveal_with_fuel(spec_int_from_str_radix_rec, 3);
        };
    }

    assert(matches!(parsed_bool, Ok(true)));
    assert(matches!(parsed_char, Ok('a')));
    assert(matches!(parsed_u32, Ok(4u32))) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 3);
    }
}

fn test_bool_from_str_core_examples() {
    let parsed_true = <bool as FromStr>::from_str("true");
    let parsed_false = <bool as FromStr>::from_str("false");
    let invalid = <bool as FromStr>::from_str("x");

    proof {
        reveal_strlit("true");
        reveal_strlit("false");
        reveal_strlit("x");
        assert("x"@.len() == 1);
        assert("true"@.len() == 4);
        assert("false"@.len() == 5);
        assert("x"@ != "true"@);
        assert("x"@ != "false"@);
        assert(parsed_true.is_ok());
        assert(parsed_false.is_ok());
        assert(invalid.is_err());
    }

    assert(matches!(parsed_true, Ok(true)));
    assert(matches!(parsed_false, Ok(false)));
    assert(matches!(invalid, Err(_)));
}

fn test_char_parse_core_examples() {
    let parsed = <char as FromStr>::from_str("a");
    let empty = <char as FromStr>::from_str("");
    let too_many = <char as FromStr>::from_str("abc");

    proof {
        reveal_strlit("a");
        reveal_strlit("");
        reveal_strlit("abc");
        assert(parsed.is_ok());
        assert(empty.is_err());
        assert(too_many.is_err());
    }

    assert(matches!(parsed, Ok('a')));
    assert(matches!(empty, Err(_)));
    assert(matches!(too_many, Err(_)));
}

fn test_u32_parse_small_upstream_example() {
    proof {
        reveal_strlit("4");
    }

    let parsed = "4".parse::<u32>();
    assert(parsed.is_ok()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 3);
    }
    assert(matches!(parsed, Ok(4u32))) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 3);
    }
}

fn test_int_parse_overflow_boundaries_from_core() {
    proof {
        reveal_strlit("255");
        reveal_strlit("256");
        reveal_strlit("127");
        reveal_strlit("128");
        reveal_strlit("-128");
        reveal_strlit("-129");
    }

    let u8_max = <u8 as FromStr>::from_str("255");
    assert(u8_max.is_ok()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }
    assert(matches!(u8_max, Ok(255u8))) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }

    let u8_overflow = <u8 as FromStr>::from_str("256");
    assert(u8_overflow.is_err()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }
    assert(u8_overflow->Err_0.is_str_parse_error());
    assert(u8_overflow->Err_0.kind() is PosOverflow) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }

    let i8_max = <i8 as FromStr>::from_str("127");
    assert(i8_max.is_ok()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }
    assert(matches!(i8_max, Ok(127i8))) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }

    let i8_pos_overflow = <i8 as FromStr>::from_str("128");
    assert(i8_pos_overflow.is_err()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }
    assert(i8_pos_overflow->Err_0.is_str_parse_error());
    assert(i8_pos_overflow->Err_0.kind() is PosOverflow) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }

    let i8_min = <i8 as FromStr>::from_str("-128");
    assert(i8_min.is_ok()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }
    // XXX(Verus): `matches!(i8_min, Ok(i8::MIN))` currently triggers an
    // internal "expected const constructor" error, so assert through `Ok_0`.
    assert(i8_min->Ok_0 as int == -128) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }

    let i8_neg_overflow = <i8 as FromStr>::from_str("-129");
    assert(i8_neg_overflow.is_err()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }
    assert(i8_neg_overflow->Err_0.is_str_parse_error());
    assert(i8_neg_overflow->Err_0.kind() is NegOverflow) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }
}

fn test_parse_int_error_kinds_from_core_invalid_and_empty() {
    proof {
        reveal_strlit("");
        reveal_strlit("123Hello");
        reveal_strlit("-");
        reveal_strlit("-1");
    }

    let empty = <u8 as FromStr>::from_str("");
    assert(empty.is_err()) by {
        reveal(str_is_valid_int_radix);
    }
    assert(empty->Err_0.is_str_parse_error());
    assert(empty->Err_0.kind() is Empty);

    let trailing_text = <u8 as FromStr>::from_str("123Hello");
    assert(trailing_text.is_err()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }
    assert(trailing_text->Err_0.is_str_parse_error());
    assert(trailing_text->Err_0.kind() is InvalidDigit) by {
        reveal(str_is_valid_int_radix);
        assert("123Hello"@ == seq!['1', '2', '3', 'H', 'e', 'l', 'l', 'o']);
        assert(!char_is_digit_radix('H', 10));
    }

    let bare_minus = <i8 as FromStr>::from_str("-");
    assert(bare_minus.is_err()) by {
        reveal(str_is_valid_int_radix);
    }
    assert(bare_minus->Err_0.is_str_parse_error());
    assert(bare_minus->Err_0.kind() is InvalidDigit) by {
        reveal(str_is_valid_int_radix);
    }

    let unsigned_negative = <u8 as FromStr>::from_str("-1");
    assert(unsigned_negative.is_err()) by {
        reveal(str_is_valid_int_radix);
        assert("-1"@ == seq!['-', '1']);
        assert(!char_is_digit_radix('-', 10));
    }
    assert(unsigned_negative->Err_0.is_str_parse_error());
    assert(unsigned_negative->Err_0.kind() is InvalidDigit) by {
        reveal(str_is_valid_int_radix);
        assert("-1"@ == seq!['-', '1']);
        assert(!char_is_digit_radix('-', 10));
    }
}

fn test_parse_int_error_kind_exact_variants_from_core() {
    proof {
        reveal_strlit("");
        reveal_strlit("123Hello");
        reveal_strlit("256");
    }

    let empty = <u8 as FromStr>::from_str("");
    let invalid_digit = <u8 as FromStr>::from_str("123Hello");
    let overflow = <u8 as FromStr>::from_str("256");

    assert(empty.is_err()) by {
        reveal(str_is_valid_int_radix);
    }
    assert(invalid_digit.is_err()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }
    assert(overflow.is_err()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }

    assert(empty->Err_0.is_str_parse_error());
    assert(empty->Err_0.kind() is Empty);
    assert(invalid_digit->Err_0.is_str_parse_error());
    assert(invalid_digit->Err_0.kind() is InvalidDigit) by {
        reveal(str_is_valid_int_radix);
        assert("123Hello"@ == seq!['1', '2', '3', 'H', 'e', 'l', 'l', 'o']);
        assert(!char_is_digit_radix('H', 10));
    }
    assert(overflow->Err_0.is_str_parse_error());
    assert(overflow->Err_0.kind() is PosOverflow) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 5);
    }
}

fn test_from_str_radix_core_examples() {
    proof {
        reveal_strlit("1001");
        reveal_strlit("ffff");
        reveal_strlit("z");
        reveal_strlit("Z");
        reveal_strlit("_");
    }

    let binary = u32::from_str_radix("1001", 2);
    assert(binary.is_ok()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 6);
    }
    assert(matches!(binary, Ok(9u32))) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 6);
    }

    let hex = u16::from_str_radix("ffff", 16);
    assert(hex.is_ok()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 6);
    }
    assert(matches!(hex, Ok(65535u16))) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 6);
    }

    let radix_36 = u8::from_str_radix("z", 36);
    assert(radix_36.is_ok()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 3);
    }
    assert(matches!(radix_36, Ok(35u8))) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 3);
    }

    let invalid_decimal = u8::from_str_radix("Z", 10);
    assert(invalid_decimal.is_err()) by {
        reveal(str_is_valid_int_radix);
        assert("Z"@ == seq!['Z']);
        assert(!char_is_digit_radix('Z', 10));
    }
    assert(invalid_decimal->Err_0.is_str_parse_error());
    assert(invalid_decimal->Err_0.kind() is InvalidDigit) by {
        reveal(str_is_valid_int_radix);
        assert("Z"@ == seq!['Z']);
        assert(!char_is_digit_radix('Z', 10));
    }

    let invalid_binary = u8::from_str_radix("_", 2);
    assert(invalid_binary.is_err()) by {
        reveal(str_is_valid_int_radix);
        assert("_"@ == seq!['_']);
        assert(!char_is_digit_radix('_', 2));
    }
    assert(invalid_binary->Err_0.is_str_parse_error());
    assert(invalid_binary->Err_0.kind() is InvalidDigit) by {
        reveal(str_is_valid_int_radix);
        assert("_"@ == seq!['_']);
        assert(!char_is_digit_radix('_', 2));
    }
}

// Upstream leading-plus boundary case.
// `reveal_with_fuel` is enough here; `by (compute)` was too expensive.
fn test_from_str_radix_leading_plus_boundary_from_core() {
    proof {
        reveal_strlit("+9223372036854775807");
    }

    let parsed = i64::from_str_radix("+9223372036854775807", 10);
    assert(parsed.is_ok()) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 20);
    }
    assert(parsed->Ok_0 as int == i64::MAX as int) by {
        reveal(str_is_valid_int_radix);
        reveal(spec_int_from_str_radix);
        reveal_with_fuel(spec_int_from_str_radix_rec, 20);
    }
}

fn test_to_string_round_trips_are_usable() {
    let b = true;
    let b_string = b.to_string();
    proof {
        <bool as FromToStr>::lemma_round_tripping(b);
    }
    let b_roundtrip = <bool as FromStr>::from_str(b_string.as_str());
    assert(b_roundtrip.is_ok());
    assert(matches!(b_roundtrip, Ok(b)));

    let c = 'q';
    let c_string = c.to_string();
    proof {
        <char as FromToStr>::lemma_round_tripping(c);
    }
    let c_roundtrip = <char as FromStr>::from_str(c_string.as_str());
    assert(c_roundtrip.is_ok());
    assert(matches!(c_roundtrip, Ok(c)));

    let n: i32 = -123;
    let n_string = n.to_string();
    proof {
        <i32 as FromToStr>::lemma_round_tripping(n);
    }
    let n_roundtrip = <i32 as FromStr>::from_str(n_string.as_str());
    assert(n_roundtrip.is_ok());
    assert(matches!(n_roundtrip, Ok(n)));

    let u: u32 = 42;
    let u_string = u.to_string();
    proof {
        <u32 as FromToStr>::lemma_round_tripping(u);
    }
    let u_roundtrip = <u32 as FromStr>::from_str(u_string.as_str());
    assert(u_roundtrip.is_ok());
    assert(matches!(u_roundtrip, Ok(u)));
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "str::parse::parse_method_postconditions",
        test_parse_method_postconditions,
    );
    count += crate::run_test(
        "str::parse::bool_from_str_core_examples",
        test_bool_from_str_core_examples,
    );
    count += crate::run_test(
        "str::parse::char_parse_core_examples",
        test_char_parse_core_examples,
    );
    count += crate::run_test(
        "str::parse::u32_parse_small_upstream_example",
        test_u32_parse_small_upstream_example,
    );
    count += crate::run_test(
        "str::parse::int_parse_overflow_boundaries_from_core",
        test_int_parse_overflow_boundaries_from_core,
    );
    count += crate::run_test(
        "str::parse::parse_int_error_kinds_from_core_invalid_and_empty",
        test_parse_int_error_kinds_from_core_invalid_and_empty,
    );
    count += crate::run_test(
        "str::parse::parse_int_error_kind_exact_variants_from_core",
        test_parse_int_error_kind_exact_variants_from_core,
    );
    count += crate::run_test(
        "str::parse::from_str_radix_core_examples",
        test_from_str_radix_core_examples,
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
