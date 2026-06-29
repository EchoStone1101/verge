//! Tests for ASCII character and byte APIs.

use vstd::prelude::*;
use verge::prelude::*;
use verge::str::*;

verus! {

fn test_u8_is_ascii() {
    let ascii = 65u8;
    let non_ascii = 0x80u8;

    assert(ascii.is_ascii());
    assert(!non_ascii.is_ascii());
}

fn test_char_is_ascii() {
    let ascii = 'A';
    let non_ascii = '世';

    assert(ascii.is_ascii());
    assert(!non_ascii.is_ascii());
}

fn test_u8_is_ascii_alphabetic() {
    let alphabetic = 65u8;
    let non_alphabetic = 48u8;

    assert(alphabetic.is_ascii_alphabetic());
    assert(!non_alphabetic.is_ascii_alphabetic());
}

fn test_char_is_ascii_alphabetic() {
    let alphabetic = 'z';
    let non_alphabetic = '0';

    assert(alphabetic.is_ascii_alphabetic());
    assert(!non_alphabetic.is_ascii_alphabetic());
}

fn test_u8_is_ascii_alphanumeric() {
    let alphanumeric = 57u8;
    let non_alphanumeric = 45u8;

    assert(alphanumeric.is_ascii_alphanumeric());
    assert(!non_alphanumeric.is_ascii_alphanumeric());
}

fn test_char_is_ascii_alphanumeric() {
    let alphanumeric = 'Q';
    let non_alphanumeric = '-';

    assert(alphanumeric.is_ascii_alphanumeric());
    assert(!non_alphanumeric.is_ascii_alphanumeric());
}

fn test_u8_is_ascii_control() {
    let control = 0x1Fu8;
    let non_control = 0x20u8;

    assert(control.is_ascii_control());
    assert(!non_control.is_ascii_control());
}

fn test_char_is_ascii_control() {
    let control = '\u{007f}';
    let non_control = 'A';

    assert(control.is_ascii_control());
    assert(!non_control.is_ascii_control());
}

fn test_u8_is_ascii_digit() {
    let digit = 48u8;
    let non_digit = 65u8;

    assert(digit.is_ascii_digit());
    assert(!non_digit.is_ascii_digit());
}

fn test_char_is_ascii_digit() {
    let digit = '9';
    let non_digit = 'a';

    assert(digit.is_ascii_digit());
    assert(!non_digit.is_ascii_digit());
}

fn test_u8_is_ascii_graphic() {
    let graphic = 0x21u8;
    let non_graphic = 0x20u8;

    assert(graphic.is_ascii_graphic());
    assert(!non_graphic.is_ascii_graphic());
}

fn test_char_is_ascii_graphic() {
    let graphic = '~';
    let non_graphic = ' ';

    assert(graphic.is_ascii_graphic());
    assert(!non_graphic.is_ascii_graphic());
}

fn test_u8_is_ascii_hexdigit() {
    let hexdigit = 70u8;
    let non_hexdigit = 71u8;

    assert(hexdigit.is_ascii_hexdigit());
    assert(!non_hexdigit.is_ascii_hexdigit());
}

fn test_char_is_ascii_hexdigit() {
    let hexdigit = 'a';
    let non_hexdigit = 'g';

    assert(hexdigit.is_ascii_hexdigit());
    assert(!non_hexdigit.is_ascii_hexdigit());
}

fn test_u8_is_ascii_lowercase() {
    let lowercase = 97u8;
    let non_lowercase = 65u8;

    assert(lowercase.is_ascii_lowercase());
    assert(!non_lowercase.is_ascii_lowercase());
}

fn test_char_is_ascii_lowercase() {
    let lowercase = 'm';
    let non_lowercase = 'M';

    assert(lowercase.is_ascii_lowercase());
    assert(!non_lowercase.is_ascii_lowercase());
}

fn test_u8_is_ascii_punctuation() {
    let punctuation = 0x21u8;
    let non_punctuation = 0x30u8;

    assert(punctuation.is_ascii_punctuation());
    assert(!non_punctuation.is_ascii_punctuation());
}

fn test_char_is_ascii_punctuation() {
    let punctuation = '!';
    let non_punctuation = '0';

    assert(punctuation.is_ascii_punctuation());
    assert(!non_punctuation.is_ascii_punctuation());
}

fn test_u8_is_ascii_uppercase() {
    let uppercase = 90u8;
    let non_uppercase = 122u8;

    assert(uppercase.is_ascii_uppercase());
    assert(!non_uppercase.is_ascii_uppercase());
}

fn test_char_is_ascii_uppercase() {
    let uppercase = 'M';
    let non_uppercase = 'm';

    assert(uppercase.is_ascii_uppercase());
    assert(!non_uppercase.is_ascii_uppercase());
}

fn test_u8_is_ascii_whitespace() {
    let whitespace = 0x20u8;
    let non_whitespace = 65u8;

    assert(whitespace.is_ascii_whitespace());
    assert(!non_whitespace.is_ascii_whitespace());
}

fn test_char_is_ascii_whitespace() {
    let whitespace = ' ';
    let non_whitespace = 'A';

    assert(whitespace.is_ascii_whitespace());
    assert(!non_whitespace.is_ascii_whitespace());
}

fn test_u8_to_ascii_lowercase() {
    let uppercase = 65u8;
    let non_uppercase = 49u8;

    assert(uppercase.to_ascii_lowercase() == 97u8);
    assert(non_uppercase.to_ascii_lowercase() == non_uppercase);
}

fn test_char_to_ascii_lowercase() {
    let uppercase = 'A';
    let non_uppercase = '1';

    assert(uppercase.to_ascii_lowercase() == 'a');
    assert(non_uppercase.to_ascii_lowercase() == non_uppercase);
}

fn test_u8_to_ascii_uppercase() {
    let lowercase = 97u8;
    let non_lowercase = 49u8;

    assert(lowercase.to_ascii_uppercase() == 65u8);
    assert(non_lowercase.to_ascii_uppercase() == non_lowercase);
}

fn test_char_to_ascii_uppercase() {
    let lowercase = 'a';
    let non_lowercase = '1';

    assert(lowercase.to_ascii_uppercase() == 'A');
    assert(non_lowercase.to_ascii_uppercase() == non_lowercase);
}

fn test_char_from_u32_ascii_scalar() {
    let letter = char::from_u32(65u32);
    let nul = char::from_u32(0u32);

    assert(letter == Some('A'));
    assert(nul == Some('\0'));
}

fn test_char_from_u32_invalid_scalar_values() {
    let surrogate = char::from_u32(0xD800u32);
    let non_scalar = char::from_u32(0x110000u32);

    assert(surrogate == None);
    assert(non_scalar == None);
}

fn test_char_from_digit_decimal_success_and_none() {
    let digit = char::from_digit(7u32, 10u32);
    let out_of_range = char::from_digit(10u32, 10u32);

    assert(digit == Some('7'));
    assert(out_of_range == None);
}

fn test_char_from_digit_hex_alphabetic_success() {
    let lower = char::from_digit(10u32, 16u32);
    let upper_bound = char::from_digit(15u32, 16u32);

    assert(lower == Some('a'));
    assert(upper_bound == Some('f'));
}

fn test_char_is_digit_radix_10() {
    assert('0'.is_digit(10u32));
    assert('9'.is_digit(10u32));
    assert(!'a'.is_digit(10u32));
}

fn test_char_is_digit_radix_16() {
    assert('9'.is_digit(16u32));
    assert('a'.is_digit(16u32));
    assert('F'.is_digit(16u32));
    assert(!'g'.is_digit(16u32));
}

fn test_char_to_digit_radix_10() {
    assert('0'.to_digit(10u32) == Some(0u32));
    assert('8'.to_digit(10u32) == Some(8u32));
    assert('a'.to_digit(10u32) == None);
}

fn test_char_to_digit_radix_16() {
    assert('9'.to_digit(16u32) == Some(9u32));
    assert('a'.to_digit(16u32) == Some(10u32));
    assert('F'.to_digit(16u32) == Some(15u32));
    assert('g'.to_digit(16u32) == None);
}

fn test_char_len_utf8_ascii_and_non_ascii() {
    assert('A'.len_utf8() == 1usize);
    assert('é'.len_utf8() == 2usize);
    assert('世'.len_utf8() == 3usize);
}

fn test_char_unicode_predicates_ascii_positive() {
    assert('A'.is_alphabetic());
    assert('a'.is_lowercase());
    assert('Z'.is_uppercase());
    assert(' '.is_whitespace());
    assert('7'.is_alphanumeric());
    assert('\u{007f}'.is_control());
    assert('3'.is_numeric());
}

fn test_char_unicode_predicates_ascii_negative() {
    assert(!'0'.is_alphabetic());
    assert(!'A'.is_lowercase());
    assert(!'z'.is_uppercase());
    assert(!'A'.is_whitespace());
    assert(!'-'.is_alphanumeric());
    assert(!'A'.is_control());
    assert(!'A'.is_numeric());
}

fn test_ascii_control_covers_full_control_range() {
    assert(0u8.is_ascii_control());
    assert(0x1Fu8.is_ascii_control());
    assert(0x7Fu8.is_ascii_control());
    assert(!0x20u8.is_ascii_control());

    assert('\0'.is_ascii_control());
    assert('\n'.is_ascii_control());
    assert('\u{007f}'.is_ascii_control());
    assert(!' '.is_ascii_control());
}

fn test_char_ascii_case_conversion_composes_with_predicates() {
    let lower = 'Q'.to_ascii_lowercase();
    let upper = 'q'.to_ascii_uppercase();

    assert(lower == 'q');
    assert(upper == 'Q');
    assert(lower.is_ascii_lowercase());
    assert(!lower.is_ascii_uppercase());
    assert(upper.is_ascii_uppercase());
    assert(!upper.is_ascii_lowercase());
    assert(lower.to_ascii_uppercase() == upper);
    assert(upper.to_ascii_lowercase() == lower);
}

fn test_u8_ascii_case_conversion_composes_with_predicates() {
    let lower = 90u8.to_ascii_lowercase();
    let upper = 122u8.to_ascii_uppercase();

    assert(lower == 122u8);
    assert(upper == 90u8);
    assert(lower.is_ascii_lowercase());
    assert(!lower.is_ascii_uppercase());
    assert(upper.is_ascii_uppercase());
    assert(!upper.is_ascii_lowercase());
    assert(lower.to_ascii_uppercase() == upper);
    assert(upper.to_ascii_lowercase() == lower);
}

} // verus!
