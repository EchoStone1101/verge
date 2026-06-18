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

} // verus!
