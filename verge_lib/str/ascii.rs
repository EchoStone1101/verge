//! ASCII-related specifications.

use super::*;

verus! {

/// Helper macro to introduce specification for both `u8` and `char`.
macro_rules! assume_specification_for_u8_and_char {
    (
        [$method:ident; $specu8:ident, $specchar:ident] ($this:ident) -> ($ret:ident: $rty:ty) 
            returns ($($body:tt)+),
            no_unwind
    ) => {
        verus! {
            pub open spec fn $specu8($this: &u8) -> $rty 
                { $($body)+ }
            pub open spec fn $specchar($this: &char) -> $rty 
                { $($body)+ }
            #[verifier::when_used_as_spec($specu8)]
            pub assume_specification [ u8::$method ] ($this: &u8) -> ($ret: $rty)
                returns $($body)+,
                no_unwind
            ;
            #[verifier::when_used_as_spec($specchar)]
            pub assume_specification [ char::$method ] ($this: &char) -> ($ret: $rty)
                returns $($body)+,
                no_unwind
            ;
        }
    };
}

/// Enables `u8|char::is_ascii`.
assume_specification_for_u8_and_char!([is_ascii; u8_is_ascii, char_is_ascii](this) -> (ret: bool)
    returns
        (0 <= *this <= 0x7F),
    no_unwind
);

/// Enables `u8|char::is_ascii_alphabetic`.
assume_specification_for_u8_and_char!(
    [is_ascii_alphabetic; u8_is_ascii_alphabetic, char_is_ascii_alphabetic](this) -> (ret: bool)
    returns
        (0x41 <= *this <= 0x5A || 0x61 <= *this <= 0x7A),
    no_unwind
);

/// Enables `u8|char::is_ascii_alphanumeric`.
assume_specification_for_u8_and_char!(
    [is_ascii_alphanumeric; u8_is_ascii_alphanumeric, char_is_ascii_alphanumeric](this) -> (ret: bool)
    returns
        (0x41 <= *this <= 0x5A || 0x61 <= *this <= 0x7A || 0x30 <= *this <= 0x39),
    no_unwind
);

/// Enables `u8|char::is_ascii_control`.
assume_specification_for_u8_and_char!(
    [is_ascii_control; u8_is_ascii_control, char_is_ascii_control](this) -> (ret: bool)
    returns
        (*this == 0x0 || *this == 0x1F || *this == 0x7F),
    no_unwind
);

/// Enables `u8|char::is_ascii_digit`.
assume_specification_for_u8_and_char!(
    [is_ascii_digit; u8_is_ascii_digit, char_is_ascii_digit](this) -> (ret: bool)
    returns
        (0x30 <= *this <= 0x39),
    no_unwind
);

/// Enables `u8|char::is_ascii_graphic`.
assume_specification_for_u8_and_char!(
    [is_ascii_graphic; u8_is_ascii_graphic, char_is_ascii_graphic](this) -> (ret: bool)
    returns
        (0x21 <= *this <= 0x7E),
    no_unwind
);

/// Enables `u8|char::is_ascii_hexdigit`.
assume_specification_for_u8_and_char!(
    [is_ascii_hexdigit; u8_is_ascii_hexdigit, char_is_ascii_hexdigit](this) -> (ret: bool)
    returns
        (0x30 <= *this <= 0x39 || 0x41 <= *this <= 0x46 || 0x61 <= *this <= 0x66),
    no_unwind
);

/// Enables `u8|char::is_ascii_lowercase`.
assume_specification_for_u8_and_char!(
    [is_ascii_lowercase; u8_is_ascii_lowercase, char_is_ascii_lowercase](this) -> (ret: bool)
    returns
        (0x61 <= *this <= 0x7A),
    no_unwind
);

/// Enables `u8|char::is_ascii_punctuation`.
assume_specification_for_u8_and_char!(
    [is_ascii_punctuation; u8_is_ascii_punctuation, char_is_ascii_punctuation](this) -> (ret: bool)
    returns
        (0x21 <= *this <= 0x2F || 0x3A <= *this <= 0x40 || 0x5B <= *this <= 0x60 || 0x7B <= *this <= 0x7E),
    no_unwind
);

/// Enables `u8|char::is_ascii_uppercase`.
assume_specification_for_u8_and_char!(
    [is_ascii_uppercase; u8_is_ascii_uppercase, char_is_ascii_uppercase](this) -> (ret: bool)
    returns
        (0x41 <= *this <= 0x5A),
    no_unwind
);

/// Enables `u8|char::is_ascii_whitespace`.
assume_specification_for_u8_and_char!(
    [is_ascii_whitespace; u8_is_ascii_whitespace, char_is_ascii_whitespace](this) -> (ret: bool)
    returns
        (*this == 0x20 || *this == 0x9 || *this == 0xA || *this == 0xC || *this == 0xD),
    no_unwind
);

/// Enables `u8::to_ascii_lowercase`.
pub open spec fn u8_to_ascii_lowercase(this: &u8) -> u8 
    { if this.is_ascii_uppercase() { (*this + 0x20) as u8 } else { *this } }
#[verifier::when_used_as_spec(u8_to_ascii_lowercase)]
pub assume_specification [ u8::to_ascii_lowercase ](this: &u8) -> (ret: u8)
    returns
        if this.is_ascii_uppercase() { (*this + 0x20) as u8 } else { *this }
    no_unwind
;

/// Enables `char::to_ascii_lowercase`.
pub open spec fn char_to_ascii_lowercase(this: &char) -> char 
    { if this.is_ascii_uppercase() { (*this as u8 + 0x20) as char } else { *this } }
#[verifier::when_used_as_spec(char_to_ascii_lowercase)]
pub assume_specification [ char::to_ascii_lowercase ](this: &char) -> (ret: char)
    returns
        if this.is_ascii_uppercase() { (*this as u8 + 0x20) as char } else { *this } 
    no_unwind
;

/// Enables `u8::to_ascii_uppercase`.
pub open spec fn u8_to_ascii_uppercase(this: &u8) -> u8 
    { if this.is_ascii_lowercase() { (*this - 0x20) as u8 } else { *this } }
#[verifier::when_used_as_spec(u8_to_ascii_uppercase)]
pub assume_specification [ u8::to_ascii_uppercase ](this: &u8) -> (ret: u8)
    returns
        if this.is_ascii_lowercase() { (*this - 0x20) as u8 } else { *this } 
    no_unwind
;

/// Enables `char::to_ascii_uppercase`.
pub open spec fn char_to_ascii_uppercase(this: &char) -> char 
    { if this.is_ascii_lowercase() { (*this as u8 - 0x20) as char } else { *this } }
#[verifier::when_used_as_spec(char_to_ascii_uppercase)]
pub assume_specification [ char::to_ascii_uppercase ](this: &char) -> (ret: char)
    returns
        if this.is_ascii_lowercase() { (*this as u8 - 0x20) as char } else { *this }
    no_unwind
;

} // verus!