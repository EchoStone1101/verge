//! Tests for character and ASCII byte APIs.

use vstd::prelude::*;
use verge::prelude::*;
use verge::str::*;

verus! {

fn test_char_from_u32_core_boundaries() {
    test!(char::from_u32(0u32) == Some('\0'));
    test!(char::from_u32(0x61u32) == Some('a'));
    test!(char::from_u32(0xD7FFu32) == Some('\u{D7FF}'));
    test!(char::from_u32(0xD800u32) == None);
    test!(char::from_u32(0xDFFFu32) == None);
    test!(char::from_u32(0xE000u32) == Some('\u{E000}'));
    test!(char::from_u32(0x10FFFFu32) == Some('\u{10FFFF}'));
    test!(char::from_u32(0x110000u32) == None);
    test!(char::from_u32(0xFFFF_FFFFu32) == None);
}

fn test_char_from_digit_core_valid_radices() {
    test!(char::from_digit(0u32, 2u32) == Some('0'));
    test!(char::from_digit(1u32, 2u32) == Some('1'));
    test!(char::from_digit(2u32, 2u32) == None);
    test!(char::from_digit(9u32, 10u32) == Some('9'));
    test!(char::from_digit(10u32, 10u32) == None);
    test!(char::from_digit(10u32, 16u32) == Some('a'));
    test!(char::from_digit(15u32, 16u32) == Some('f'));
    test!(char::from_digit(35u32, 36u32) == Some('z'));
    test!(char::from_digit(36u32, 36u32) == None);
    test!(char::from_digit(10u32, 9u32) == None);
}

fn test_char_to_digit_core_valid_radices() {
    test!('0'.to_digit(10u32) == Some(0u32));
    test!('1'.to_digit(2u32) == Some(1u32));
    test!('2'.to_digit(3u32) == Some(2u32));
    test!('9'.to_digit(10u32) == Some(9u32));
    test!('a'.to_digit(16u32) == Some(10u32));
    test!('A'.to_digit(16u32) == Some(10u32));
    test!('z'.to_digit(36u32) == Some(35u32));
    test!('Z'.to_digit(36u32) == Some(35u32));
    test!('['.to_digit(36u32) == None);
    test!('`'.to_digit(36u32) == None);
    test!('{'.to_digit(36u32) == None);
    test!('$'.to_digit(36u32) == None);
    test!('@'.to_digit(16u32) == None);
    test!('G'.to_digit(16u32) == None);
    test!('g'.to_digit(16u32) == None);
    test!(' '.to_digit(10u32) == None);
    test!('/'.to_digit(10u32) == None);
    test!(':'.to_digit(10u32) == None);
    test!(':'.to_digit(11u32) == None);
}

fn test_char_is_digit_core_valid_radices() {
    test!('0'.is_digit(10u32));
    test!('1'.is_digit(2u32));
    test!(!'2'.is_digit(2u32));
    test!('9'.is_digit(10u32));
    test!('a'.is_digit(16u32));
    test!('A'.is_digit(16u32));
    test!('z'.is_digit(36u32));
    test!('Z'.is_digit(36u32));
    test!(!'G'.is_digit(16u32));
    test!(!'g'.is_digit(16u32));
    test!(!' '.is_digit(10u32));
}

fn test_char_len_utf8_core_widths() {
    test!('x'.len_utf8() == 1usize);
    test!('\u{e9}'.len_utf8() == 2usize);
    test!('\u{a66e}'.len_utf8() == 3usize);
    test!('\u{1f4a9}'.len_utf8() == 4usize);
}

fn test_ascii_classification_core_representatives() {
    test!(0x61u8.is_ascii());
    test!(0x7Fu8.is_ascii());
    test!(!0x80u8.is_ascii());
    test!('a'.is_ascii());
    test!('\u{7f}'.is_ascii());
    test!(!'\u{80}'.is_ascii());

    test!(0x61u8.is_ascii_alphabetic());
    test!(0x5Au8.is_ascii_alphabetic());
    test!(!0x30u8.is_ascii_alphabetic());
    test!('a'.is_ascii_alphabetic());
    test!('Z'.is_ascii_alphabetic());
    test!(!'0'.is_ascii_alphabetic());

    test!(0x39u8.is_ascii_alphanumeric());
    test!(!0x2Du8.is_ascii_alphanumeric());
    test!('Q'.is_ascii_alphanumeric());
    test!(!'-'.is_ascii_alphanumeric());

    test!(0x00u8.is_ascii_control());
    test!(0x1Fu8.is_ascii_control());
    test!(0x7Fu8.is_ascii_control());
    test!(!0x20u8.is_ascii_control());
    test!('\0'.is_ascii_control());
    test!('\u{007f}'.is_ascii_control());
    test!(!' '.is_ascii_control());

    test!(0x30u8.is_ascii_digit());
    test!(0x39u8.is_ascii_digit());
    test!(!0x61u8.is_ascii_digit());
    test!('0'.is_ascii_digit());
    test!('9'.is_ascii_digit());
    test!(!'a'.is_ascii_digit());

    test!(0x21u8.is_ascii_graphic());
    test!(0x7Eu8.is_ascii_graphic());
    test!(!0x20u8.is_ascii_graphic());
    test!('!'.is_ascii_graphic());
    test!('~'.is_ascii_graphic());
    test!(!' '.is_ascii_graphic());

    test!(0x39u8.is_ascii_hexdigit());
    test!(0x66u8.is_ascii_hexdigit());
    test!(0x46u8.is_ascii_hexdigit());
    test!(!0x67u8.is_ascii_hexdigit());
    test!('9'.is_ascii_hexdigit());
    test!('f'.is_ascii_hexdigit());
    test!('F'.is_ascii_hexdigit());
    test!(!'g'.is_ascii_hexdigit());

    test!(0x61u8.is_ascii_lowercase());
    test!(0x7Au8.is_ascii_lowercase());
    test!(!0x41u8.is_ascii_lowercase());
    test!('a'.is_ascii_lowercase());
    test!('z'.is_ascii_lowercase());
    test!(!'A'.is_ascii_lowercase());

    test!(0x21u8.is_ascii_punctuation());
    test!(0x2Fu8.is_ascii_punctuation());
    test!(0x3Au8.is_ascii_punctuation());
    test!(0x40u8.is_ascii_punctuation());
    test!(0x5Bu8.is_ascii_punctuation());
    test!(0x60u8.is_ascii_punctuation());
    test!(0x7Bu8.is_ascii_punctuation());
    test!(0x7Eu8.is_ascii_punctuation());
    test!(!0x30u8.is_ascii_punctuation());
    test!('!'.is_ascii_punctuation());
    test!('~'.is_ascii_punctuation());
    test!(!'0'.is_ascii_punctuation());

    test!(0x41u8.is_ascii_uppercase());
    test!(0x5Au8.is_ascii_uppercase());
    test!(!0x61u8.is_ascii_uppercase());
    test!('A'.is_ascii_uppercase());
    test!('Z'.is_ascii_uppercase());
    test!(!'a'.is_ascii_uppercase());

    test!(0x20u8.is_ascii_whitespace());
    test!(0x09u8.is_ascii_whitespace());
    test!(0x0Au8.is_ascii_whitespace());
    test!(0x0Cu8.is_ascii_whitespace());
    test!(0x0Du8.is_ascii_whitespace());
    test!(!0x0Bu8.is_ascii_whitespace());
    test!(' '.is_ascii_whitespace());
    test!('\t'.is_ascii_whitespace());
    test!('\n'.is_ascii_whitespace());
    test!('\u{000c}'.is_ascii_whitespace());
    test!('\r'.is_ascii_whitespace());
    test!(!'A'.is_ascii_whitespace());
}

fn test_char_unicode_predicates_ascii_backed() {
    test!('A'.is_alphabetic());
    test!(!'0'.is_alphabetic());
    test!('a'.is_lowercase());
    test!(!'A'.is_lowercase());
    test!('Z'.is_uppercase());
    test!(!'z'.is_uppercase());
    test!(' '.is_whitespace());
    test!(!'A'.is_whitespace());
    test!('7'.is_alphanumeric());
    test!(!'-'.is_alphanumeric());
    test!('\u{007f}'.is_control());
    test!(!'A'.is_control());
    test!('3'.is_numeric());
    test!(!'Q'.is_numeric());
}

fn test_char_unicode_predicates_non_ascii_core_cases() {
    // XXX: Verge doesn't module full Unicode categories in spec yet, 
    // so some facts require a (cheap) `exec`-mode proof.
    if 'ö'.is_lowercase() {
        test!('ö'.is_alphabetic(), {
            proof { axiom_non_ascii_categories('ö') }
        });
        test!(!'ö'.is_uppercase());
    }
    if '¾'.is_numeric() {
        test!(!'¾'.is_whitespace(), {
            proof { axiom_non_ascii_categories('¾') }
        });
        test!(!'¾'.is_alphabetic());
    }
    if '\u{92}'.is_control() {
        test!(!'\u{92}'.is_numeric(), {
            proof { axiom_non_ascii_categories('\u{92}') }
        });
    }
}

fn test_ascii_case_conversion_core_representatives() {
    test!(0x41u8.to_ascii_lowercase() == 0x61u8);
    test!(0x61u8.to_ascii_lowercase() == 0x61u8);
    test!(0x21u8.to_ascii_lowercase() == 0x21u8);
    test!('A'.to_ascii_lowercase() == 'a');
    test!('a'.to_ascii_lowercase() == 'a');
    test!('À'.to_ascii_lowercase() == 'À');
    test!('!'.to_ascii_lowercase() == '!');

    test!(0x61u8.to_ascii_uppercase() == 0x41u8);
    test!(0x41u8.to_ascii_uppercase() == 0x41u8);
    test!(0x21u8.to_ascii_uppercase() == 0x21u8);
    test!('a'.to_ascii_uppercase() == 'A');
    test!('A'.to_ascii_uppercase() == 'A');
    test!('à'.to_ascii_uppercase() == 'à');
    test!('!'.to_ascii_uppercase() == '!');
}

fn test_ascii_case_conversion_composes_with_predicates() {
    let char_lower = 'Q'.to_ascii_lowercase();
    let char_upper = 'q'.to_ascii_uppercase();
    let byte_lower = 0x5Au8.to_ascii_lowercase();
    let byte_upper = 0x7Au8.to_ascii_uppercase();

    test!(char_lower == 'q');
    test!(char_upper == 'Q');
    test!(char_lower.is_ascii_lowercase());
    test!(!char_lower.is_ascii_uppercase());
    test!(char_upper.is_ascii_uppercase());
    test!(!char_upper.is_ascii_lowercase());
    test!(char_lower.to_ascii_uppercase() == char_upper);
    test!(char_upper.to_ascii_lowercase() == char_lower);

    test!(byte_lower == 0x7Au8);
    test!(byte_upper == 0x5Au8);
    test!(byte_lower.is_ascii_lowercase());
    test!(!byte_lower.is_ascii_uppercase());
    test!(byte_upper.is_ascii_uppercase());
    test!(!byte_upper.is_ascii_lowercase());
    test!(byte_lower.to_ascii_uppercase() == byte_upper);
    test!(byte_upper.to_ascii_lowercase() == byte_lower);
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "str::chars::char_from_u32_core_boundaries",
        test_char_from_u32_core_boundaries,
    );
    count += crate::run_test(
        "str::chars::char_from_digit_core_valid_radices",
        test_char_from_digit_core_valid_radices,
    );
    count += crate::run_test(
        "str::chars::char_to_digit_core_valid_radices",
        test_char_to_digit_core_valid_radices,
    );
    count += crate::run_test(
        "str::chars::char_is_digit_core_valid_radices",
        test_char_is_digit_core_valid_radices,
    );
    count += crate::run_test(
        "str::chars::char_len_utf8_core_widths",
        test_char_len_utf8_core_widths,
    );
    count += crate::run_test(
        "str::chars::ascii_classification_core_representatives",
        test_ascii_classification_core_representatives,
    );
    count += crate::run_test(
        "str::chars::char_unicode_predicates_ascii_backed",
        test_char_unicode_predicates_ascii_backed,
    );
    count += crate::run_test(
        "str::chars::char_unicode_predicates_non_ascii_core_cases",
        test_char_unicode_predicates_non_ascii_core_cases,
    );
    count += crate::run_test(
        "str::chars::ascii_case_conversion_core_representatives",
        test_ascii_case_conversion_core_representatives,
    );
    count += crate::run_test(
        "str::chars::ascii_case_conversion_composes_with_predicates",
        test_ascii_case_conversion_composes_with_predicates,
    );
    count
}
