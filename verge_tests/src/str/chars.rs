//! Tests for character and ASCII byte APIs.

use vstd::prelude::*;
use verge::prelude::*;
use verge::str::*;

verus! {

fn test_char_from_u32_core_boundaries() {
    let nul = char::from_u32(0u32);
    let letter = char::from_u32(0x61u32);
    let before_surrogates = char::from_u32(0xD7FFu32);
    let surrogate_start = char::from_u32(0xD800u32);
    let surrogate_end = char::from_u32(0xDFFFu32);
    let after_surrogates = char::from_u32(0xE000u32);
    let max_scalar = char::from_u32(0x10FFFFu32);
    let past_max_scalar = char::from_u32(0x110000u32);
    let u32_max = char::from_u32(0xFFFF_FFFFu32);

    assert(nul == Some('\0'));
    crate::exec_assert(nul == Some('\0'));
    assert(letter == Some('a'));
    crate::exec_assert(letter == Some('a'));
    assert(before_surrogates == Some('\u{D7FF}'));
    crate::exec_assert(before_surrogates == Some('\u{D7FF}'));
    assert(surrogate_start == None);
    crate::exec_assert(surrogate_start == None);
    assert(surrogate_end == None);
    crate::exec_assert(surrogate_end == None);
    assert(after_surrogates == Some('\u{E000}'));
    crate::exec_assert(after_surrogates == Some('\u{E000}'));
    assert(max_scalar == Some('\u{10FFFF}'));
    crate::exec_assert(max_scalar == Some('\u{10FFFF}'));
    assert(past_max_scalar == None);
    crate::exec_assert(past_max_scalar == None);
    assert(u32_max == None);
    crate::exec_assert(u32_max == None);
}

fn test_char_from_digit_core_valid_radices() {
    let zero_base_2 = char::from_digit(0u32, 2u32);
    let one_base_2 = char::from_digit(1u32, 2u32);
    let two_base_2 = char::from_digit(2u32, 2u32);
    let nine_base_10 = char::from_digit(9u32, 10u32);
    let ten_base_10 = char::from_digit(10u32, 10u32);
    let ten_base_16 = char::from_digit(10u32, 16u32);
    let fifteen_base_16 = char::from_digit(15u32, 16u32);
    let thirty_five_base_36 = char::from_digit(35u32, 36u32);
    let thirty_six_base_36 = char::from_digit(36u32, 36u32);
    let ten_base_9 = char::from_digit(10u32, 9u32);

    assert(zero_base_2 == Some('0'));
    crate::exec_assert(zero_base_2 == Some('0'));
    assert(one_base_2 == Some('1'));
    crate::exec_assert(one_base_2 == Some('1'));
    assert(two_base_2 == None);
    crate::exec_assert(two_base_2 == None);
    assert(nine_base_10 == Some('9'));
    crate::exec_assert(nine_base_10 == Some('9'));
    assert(ten_base_10 == None);
    crate::exec_assert(ten_base_10 == None);
    assert(ten_base_16 == Some('a'));
    crate::exec_assert(ten_base_16 == Some('a'));
    assert(fifteen_base_16 == Some('f'));
    crate::exec_assert(fifteen_base_16 == Some('f'));
    assert(thirty_five_base_36 == Some('z'));
    crate::exec_assert(thirty_five_base_36 == Some('z'));
    assert(thirty_six_base_36 == None);
    crate::exec_assert(thirty_six_base_36 == None);
    assert(ten_base_9 == None);
    crate::exec_assert(ten_base_9 == None);
}

fn test_char_to_digit_core_valid_radices() {
    let zero_base_10 = '0'.to_digit(10u32);
    let one_base_2 = '1'.to_digit(2u32);
    let two_base_3 = '2'.to_digit(3u32);
    let nine_base_10 = '9'.to_digit(10u32);
    let lower_a_base_16 = 'a'.to_digit(16u32);
    let upper_a_base_16 = 'A'.to_digit(16u32);
    let lower_z_base_36 = 'z'.to_digit(36u32);
    let upper_z_base_36 = 'Z'.to_digit(36u32);
    let after_upper_base_36 = '['.to_digit(36u32);
    let before_lower_base_36 = '`'.to_digit(36u32);
    let after_lower_base_36 = '{'.to_digit(36u32);
    let symbol_base_36 = '$'.to_digit(36u32);
    let before_upper_base_16 = '@'.to_digit(16u32);
    let upper_g_base_16 = 'G'.to_digit(16u32);
    let lower_g_base_16 = 'g'.to_digit(16u32);
    let space_base_10 = ' '.to_digit(10u32);
    let before_digits_base_10 = '/'.to_digit(10u32);
    let after_digits_base_10 = ':'.to_digit(10u32);
    let after_digits_base_11 = ':'.to_digit(11u32);

    assert(zero_base_10 == Some(0u32));
    crate::exec_assert(zero_base_10 == Some(0u32));
    assert(one_base_2 == Some(1u32));
    crate::exec_assert(one_base_2 == Some(1u32));
    assert(two_base_3 == Some(2u32));
    crate::exec_assert(two_base_3 == Some(2u32));
    assert(nine_base_10 == Some(9u32));
    crate::exec_assert(nine_base_10 == Some(9u32));
    assert(lower_a_base_16 == Some(10u32));
    crate::exec_assert(lower_a_base_16 == Some(10u32));
    assert(upper_a_base_16 == Some(10u32));
    crate::exec_assert(upper_a_base_16 == Some(10u32));
    assert(lower_z_base_36 == Some(35u32));
    crate::exec_assert(lower_z_base_36 == Some(35u32));
    assert(upper_z_base_36 == Some(35u32));
    crate::exec_assert(upper_z_base_36 == Some(35u32));
    assert(after_upper_base_36 == None);
    crate::exec_assert(after_upper_base_36 == None);
    assert(before_lower_base_36 == None);
    crate::exec_assert(before_lower_base_36 == None);
    assert(after_lower_base_36 == None);
    crate::exec_assert(after_lower_base_36 == None);
    assert(symbol_base_36 == None);
    crate::exec_assert(symbol_base_36 == None);
    assert(before_upper_base_16 == None);
    crate::exec_assert(before_upper_base_16 == None);
    assert(upper_g_base_16 == None);
    crate::exec_assert(upper_g_base_16 == None);
    assert(lower_g_base_16 == None);
    crate::exec_assert(lower_g_base_16 == None);
    assert(space_base_10 == None);
    crate::exec_assert(space_base_10 == None);
    assert(before_digits_base_10 == None);
    crate::exec_assert(before_digits_base_10 == None);
    assert(after_digits_base_10 == None);
    crate::exec_assert(after_digits_base_10 == None);
    assert(after_digits_base_11 == None);
    crate::exec_assert(after_digits_base_11 == None);
}

fn test_char_is_digit_core_valid_radices() {
    assert('0'.is_digit(10u32));
    crate::exec_assert('0'.is_digit(10u32));
    assert('1'.is_digit(2u32));
    crate::exec_assert('1'.is_digit(2u32));
    assert(!'2'.is_digit(2u32));
    crate::exec_assert(!'2'.is_digit(2u32));
    assert('9'.is_digit(10u32));
    crate::exec_assert('9'.is_digit(10u32));
    assert('a'.is_digit(16u32));
    crate::exec_assert('a'.is_digit(16u32));
    assert('A'.is_digit(16u32));
    crate::exec_assert('A'.is_digit(16u32));
    assert('z'.is_digit(36u32));
    crate::exec_assert('z'.is_digit(36u32));
    assert('Z'.is_digit(36u32));
    crate::exec_assert('Z'.is_digit(36u32));
    assert(!'G'.is_digit(16u32));
    crate::exec_assert(!'G'.is_digit(16u32));
    assert(!'g'.is_digit(16u32));
    crate::exec_assert(!'g'.is_digit(16u32));
    assert(!' '.is_digit(10u32));
    crate::exec_assert(!' '.is_digit(10u32));
}

fn test_char_len_utf8_core_widths() {
    assert('x'.len_utf8() == 1usize);
    crate::exec_assert('x'.len_utf8() == 1usize);
    assert('\u{e9}'.len_utf8() == 2usize);
    crate::exec_assert('\u{e9}'.len_utf8() == 2usize);
    assert('\u{a66e}'.len_utf8() == 3usize);
    crate::exec_assert('\u{a66e}'.len_utf8() == 3usize);
    assert('\u{1f4a9}'.len_utf8() == 4usize);
    crate::exec_assert('\u{1f4a9}'.len_utf8() == 4usize);
}

fn test_ascii_classification_core_representatives() {
    assert(0x61u8.is_ascii());
    crate::exec_assert(0x61u8.is_ascii());
    assert(0x7Fu8.is_ascii());
    crate::exec_assert(0x7Fu8.is_ascii());
    assert(!0x80u8.is_ascii());
    crate::exec_assert(!0x80u8.is_ascii());
    assert('a'.is_ascii());
    crate::exec_assert('a'.is_ascii());
    assert('\u{7f}'.is_ascii());
    crate::exec_assert('\u{7f}'.is_ascii());
    assert(!'\u{80}'.is_ascii());
    crate::exec_assert(!'\u{80}'.is_ascii());

    assert(0x61u8.is_ascii_alphabetic());
    crate::exec_assert(0x61u8.is_ascii_alphabetic());
    assert(0x5Au8.is_ascii_alphabetic());
    crate::exec_assert(0x5Au8.is_ascii_alphabetic());
    assert(!0x30u8.is_ascii_alphabetic());
    crate::exec_assert(!0x30u8.is_ascii_alphabetic());
    assert('a'.is_ascii_alphabetic());
    crate::exec_assert('a'.is_ascii_alphabetic());
    assert('Z'.is_ascii_alphabetic());
    crate::exec_assert('Z'.is_ascii_alphabetic());
    assert(!'0'.is_ascii_alphabetic());
    crate::exec_assert(!'0'.is_ascii_alphabetic());

    assert(0x39u8.is_ascii_alphanumeric());
    crate::exec_assert(0x39u8.is_ascii_alphanumeric());
    assert(!0x2Du8.is_ascii_alphanumeric());
    crate::exec_assert(!0x2Du8.is_ascii_alphanumeric());
    assert('Q'.is_ascii_alphanumeric());
    crate::exec_assert('Q'.is_ascii_alphanumeric());
    assert(!'-'.is_ascii_alphanumeric());
    crate::exec_assert(!'-'.is_ascii_alphanumeric());

    assert(0x00u8.is_ascii_control());
    crate::exec_assert(0x00u8.is_ascii_control());
    assert(0x1Fu8.is_ascii_control());
    crate::exec_assert(0x1Fu8.is_ascii_control());
    assert(0x7Fu8.is_ascii_control());
    crate::exec_assert(0x7Fu8.is_ascii_control());
    assert(!0x20u8.is_ascii_control());
    crate::exec_assert(!0x20u8.is_ascii_control());
    assert('\0'.is_ascii_control());
    crate::exec_assert('\0'.is_ascii_control());
    assert('\u{007f}'.is_ascii_control());
    crate::exec_assert('\u{007f}'.is_ascii_control());
    assert(!' '.is_ascii_control());
    crate::exec_assert(!' '.is_ascii_control());

    assert(0x30u8.is_ascii_digit());
    crate::exec_assert(0x30u8.is_ascii_digit());
    assert(0x39u8.is_ascii_digit());
    crate::exec_assert(0x39u8.is_ascii_digit());
    assert(!0x61u8.is_ascii_digit());
    crate::exec_assert(!0x61u8.is_ascii_digit());
    assert('0'.is_ascii_digit());
    crate::exec_assert('0'.is_ascii_digit());
    assert('9'.is_ascii_digit());
    crate::exec_assert('9'.is_ascii_digit());
    assert(!'a'.is_ascii_digit());
    crate::exec_assert(!'a'.is_ascii_digit());

    assert(0x21u8.is_ascii_graphic());
    crate::exec_assert(0x21u8.is_ascii_graphic());
    assert(0x7Eu8.is_ascii_graphic());
    crate::exec_assert(0x7Eu8.is_ascii_graphic());
    assert(!0x20u8.is_ascii_graphic());
    crate::exec_assert(!0x20u8.is_ascii_graphic());
    assert('!'.is_ascii_graphic());
    crate::exec_assert('!'.is_ascii_graphic());
    assert('~'.is_ascii_graphic());
    crate::exec_assert('~'.is_ascii_graphic());
    assert(!' '.is_ascii_graphic());
    crate::exec_assert(!' '.is_ascii_graphic());

    assert(0x39u8.is_ascii_hexdigit());
    crate::exec_assert(0x39u8.is_ascii_hexdigit());
    assert(0x66u8.is_ascii_hexdigit());
    crate::exec_assert(0x66u8.is_ascii_hexdigit());
    assert(0x46u8.is_ascii_hexdigit());
    crate::exec_assert(0x46u8.is_ascii_hexdigit());
    assert(!0x67u8.is_ascii_hexdigit());
    crate::exec_assert(!0x67u8.is_ascii_hexdigit());
    assert('9'.is_ascii_hexdigit());
    crate::exec_assert('9'.is_ascii_hexdigit());
    assert('f'.is_ascii_hexdigit());
    crate::exec_assert('f'.is_ascii_hexdigit());
    assert('F'.is_ascii_hexdigit());
    crate::exec_assert('F'.is_ascii_hexdigit());
    assert(!'g'.is_ascii_hexdigit());
    crate::exec_assert(!'g'.is_ascii_hexdigit());

    assert(0x61u8.is_ascii_lowercase());
    crate::exec_assert(0x61u8.is_ascii_lowercase());
    assert(0x7Au8.is_ascii_lowercase());
    crate::exec_assert(0x7Au8.is_ascii_lowercase());
    assert(!0x41u8.is_ascii_lowercase());
    crate::exec_assert(!0x41u8.is_ascii_lowercase());
    assert('a'.is_ascii_lowercase());
    crate::exec_assert('a'.is_ascii_lowercase());
    assert('z'.is_ascii_lowercase());
    crate::exec_assert('z'.is_ascii_lowercase());
    assert(!'A'.is_ascii_lowercase());
    crate::exec_assert(!'A'.is_ascii_lowercase());

    assert(0x21u8.is_ascii_punctuation());
    crate::exec_assert(0x21u8.is_ascii_punctuation());
    assert(0x2Fu8.is_ascii_punctuation());
    crate::exec_assert(0x2Fu8.is_ascii_punctuation());
    assert(0x3Au8.is_ascii_punctuation());
    crate::exec_assert(0x3Au8.is_ascii_punctuation());
    assert(0x40u8.is_ascii_punctuation());
    crate::exec_assert(0x40u8.is_ascii_punctuation());
    assert(0x5Bu8.is_ascii_punctuation());
    crate::exec_assert(0x5Bu8.is_ascii_punctuation());
    assert(0x60u8.is_ascii_punctuation());
    crate::exec_assert(0x60u8.is_ascii_punctuation());
    assert(0x7Bu8.is_ascii_punctuation());
    crate::exec_assert(0x7Bu8.is_ascii_punctuation());
    assert(0x7Eu8.is_ascii_punctuation());
    crate::exec_assert(0x7Eu8.is_ascii_punctuation());
    assert(!0x30u8.is_ascii_punctuation());
    crate::exec_assert(!0x30u8.is_ascii_punctuation());
    assert('!'.is_ascii_punctuation());
    crate::exec_assert('!'.is_ascii_punctuation());
    assert('~'.is_ascii_punctuation());
    crate::exec_assert('~'.is_ascii_punctuation());
    assert(!'0'.is_ascii_punctuation());
    crate::exec_assert(!'0'.is_ascii_punctuation());

    assert(0x41u8.is_ascii_uppercase());
    crate::exec_assert(0x41u8.is_ascii_uppercase());
    assert(0x5Au8.is_ascii_uppercase());
    crate::exec_assert(0x5Au8.is_ascii_uppercase());
    assert(!0x61u8.is_ascii_uppercase());
    crate::exec_assert(!0x61u8.is_ascii_uppercase());
    assert('A'.is_ascii_uppercase());
    crate::exec_assert('A'.is_ascii_uppercase());
    assert('Z'.is_ascii_uppercase());
    crate::exec_assert('Z'.is_ascii_uppercase());
    assert(!'a'.is_ascii_uppercase());
    crate::exec_assert(!'a'.is_ascii_uppercase());

    assert(0x20u8.is_ascii_whitespace());
    crate::exec_assert(0x20u8.is_ascii_whitespace());
    assert(0x09u8.is_ascii_whitespace());
    crate::exec_assert(0x09u8.is_ascii_whitespace());
    assert(0x0Au8.is_ascii_whitespace());
    crate::exec_assert(0x0Au8.is_ascii_whitespace());
    assert(0x0Cu8.is_ascii_whitespace());
    crate::exec_assert(0x0Cu8.is_ascii_whitespace());
    assert(0x0Du8.is_ascii_whitespace());
    crate::exec_assert(0x0Du8.is_ascii_whitespace());
    assert(!0x0Bu8.is_ascii_whitespace());
    crate::exec_assert(!0x0Bu8.is_ascii_whitespace());
    assert(' '.is_ascii_whitespace());
    crate::exec_assert(' '.is_ascii_whitespace());
    assert('\t'.is_ascii_whitespace());
    crate::exec_assert('\t'.is_ascii_whitespace());
    assert('\n'.is_ascii_whitespace());
    crate::exec_assert('\n'.is_ascii_whitespace());
    assert('\u{000c}'.is_ascii_whitespace());
    crate::exec_assert('\u{000c}'.is_ascii_whitespace());
    assert('\r'.is_ascii_whitespace());
    crate::exec_assert('\r'.is_ascii_whitespace());
    assert(!'A'.is_ascii_whitespace());
    crate::exec_assert(!'A'.is_ascii_whitespace());
}

fn test_char_unicode_predicates_ascii_backed() {
    assert('A'.is_alphabetic());
    crate::exec_assert('A'.is_alphabetic());
    assert(!'0'.is_alphabetic());
    crate::exec_assert(!'0'.is_alphabetic());
    assert('a'.is_lowercase());
    crate::exec_assert('a'.is_lowercase());
    assert(!'A'.is_lowercase());
    crate::exec_assert(!'A'.is_lowercase());
    assert('Z'.is_uppercase());
    crate::exec_assert('Z'.is_uppercase());
    assert(!'z'.is_uppercase());
    crate::exec_assert(!'z'.is_uppercase());
    assert(' '.is_whitespace());
    crate::exec_assert(' '.is_whitespace());
    assert(!'A'.is_whitespace());
    crate::exec_assert(!'A'.is_whitespace());
    assert('7'.is_alphanumeric());
    crate::exec_assert('7'.is_alphanumeric());
    assert(!'-'.is_alphanumeric());
    crate::exec_assert(!'-'.is_alphanumeric());
    assert('\u{007f}'.is_control());
    crate::exec_assert('\u{007f}'.is_control());
    assert(!'A'.is_control());
    crate::exec_assert(!'A'.is_control());
    assert('3'.is_numeric());
    crate::exec_assert('3'.is_numeric());
    assert(!'Q'.is_numeric());
    crate::exec_assert(!'Q'.is_numeric());
}

fn test_char_unicode_predicates_non_ascii_core_cases() {
    // XXX: Verge doesn't module full Unicode categories in spec yet, 
    // so some facts require a (cheap) `exec`-mode proof.
    if 'ö'.is_lowercase() {
        proof { axiom_non_ascii_categories('ö') }
        crate::exec_assert('ö'.is_alphabetic());
        crate::exec_assert(!'ö'.is_uppercase());
    }
    if '¾'.is_numeric() {
        proof { axiom_non_ascii_categories('¾') }
        crate::exec_assert(!'¾'.is_whitespace());
        crate::exec_assert(!'¾'.is_alphabetic());
    }
    if '\u{92}'.is_control() {
        proof { axiom_non_ascii_categories('\u{92}') }
        crate::exec_assert(!'\u{92}'.is_numeric());
    }
}

fn test_ascii_case_conversion_core_representatives() {
    let byte_lower = 0x41u8.to_ascii_lowercase();
    let byte_lower_idempotent = 0x61u8.to_ascii_lowercase();
    let byte_symbol_lower = 0x21u8.to_ascii_lowercase();
    let char_lower = 'A'.to_ascii_lowercase();
    let char_lower_idempotent = 'a'.to_ascii_lowercase();
    let char_non_ascii_lower = 'À'.to_ascii_lowercase();
    let char_symbol_lower = '!'.to_ascii_lowercase();

    assert(byte_lower == 0x61u8);
    crate::exec_assert(byte_lower == 0x61u8);
    assert(byte_lower_idempotent == 0x61u8);
    crate::exec_assert(byte_lower_idempotent == 0x61u8);
    assert(byte_symbol_lower == 0x21u8);
    crate::exec_assert(byte_symbol_lower == 0x21u8);
    assert(char_lower == 'a');
    crate::exec_assert(char_lower == 'a');
    assert(char_lower_idempotent == 'a');
    crate::exec_assert(char_lower_idempotent == 'a');
    assert(char_non_ascii_lower == 'À');
    crate::exec_assert(char_non_ascii_lower == 'À');
    assert(char_symbol_lower == '!');
    crate::exec_assert(char_symbol_lower == '!');

    let byte_upper = 0x61u8.to_ascii_uppercase();
    let byte_upper_idempotent = 0x41u8.to_ascii_uppercase();
    let byte_symbol_upper = 0x21u8.to_ascii_uppercase();
    let char_upper = 'a'.to_ascii_uppercase();
    let char_upper_idempotent = 'A'.to_ascii_uppercase();
    let char_non_ascii_upper = 'à'.to_ascii_uppercase();
    let char_symbol_upper = '!'.to_ascii_uppercase();

    assert(byte_upper == 0x41u8);
    crate::exec_assert(byte_upper == 0x41u8);
    assert(byte_upper_idempotent == 0x41u8);
    crate::exec_assert(byte_upper_idempotent == 0x41u8);
    assert(byte_symbol_upper == 0x21u8);
    crate::exec_assert(byte_symbol_upper == 0x21u8);
    assert(char_upper == 'A');
    crate::exec_assert(char_upper == 'A');
    assert(char_upper_idempotent == 'A');
    crate::exec_assert(char_upper_idempotent == 'A');
    assert(char_non_ascii_upper == 'à');
    crate::exec_assert(char_non_ascii_upper == 'à');
    assert(char_symbol_upper == '!');
    crate::exec_assert(char_symbol_upper == '!');
}

fn test_ascii_case_conversion_composes_with_predicates() {
    let char_lower = 'Q'.to_ascii_lowercase();
    let char_upper = 'q'.to_ascii_uppercase();
    let byte_lower = 0x5Au8.to_ascii_lowercase();
    let byte_upper = 0x7Au8.to_ascii_uppercase();

    assert(char_lower == 'q');
    crate::exec_assert(char_lower == 'q');
    assert(char_upper == 'Q');
    crate::exec_assert(char_upper == 'Q');
    assert(char_lower.is_ascii_lowercase());
    crate::exec_assert(char_lower.is_ascii_lowercase());
    assert(!char_lower.is_ascii_uppercase());
    crate::exec_assert(!char_lower.is_ascii_uppercase());
    assert(char_upper.is_ascii_uppercase());
    crate::exec_assert(char_upper.is_ascii_uppercase());
    assert(!char_upper.is_ascii_lowercase());
    crate::exec_assert(!char_upper.is_ascii_lowercase());
    assert(char_lower.to_ascii_uppercase() == char_upper);
    crate::exec_assert(char_lower.to_ascii_uppercase() == char_upper);
    assert(char_upper.to_ascii_lowercase() == char_lower);
    crate::exec_assert(char_upper.to_ascii_lowercase() == char_lower);

    assert(byte_lower == 0x7Au8);
    crate::exec_assert(byte_lower == 0x7Au8);
    assert(byte_upper == 0x5Au8);
    crate::exec_assert(byte_upper == 0x5Au8);
    assert(byte_lower.is_ascii_lowercase());
    crate::exec_assert(byte_lower.is_ascii_lowercase());
    assert(!byte_lower.is_ascii_uppercase());
    crate::exec_assert(!byte_lower.is_ascii_uppercase());
    assert(byte_upper.is_ascii_uppercase());
    crate::exec_assert(byte_upper.is_ascii_uppercase());
    assert(!byte_upper.is_ascii_lowercase());
    crate::exec_assert(!byte_upper.is_ascii_lowercase());
    assert(byte_lower.to_ascii_uppercase() == byte_upper);
    crate::exec_assert(byte_lower.to_ascii_uppercase() == byte_upper);
    assert(byte_upper.to_ascii_lowercase() == byte_lower);
    crate::exec_assert(byte_upper.to_ascii_lowercase() == byte_lower);
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
