//! Character-related string specifications.

use super::*;

verus! {

// Helper macros to introduce specifications.

macro_rules! assume_specification_for_u8 {
    (
        [$method:ident via $spec:ident] ($($arg:ident : $aty:ty),+) -> ($ret:ident: $rty:ty) 
            $(requires ($($requires:tt)+),)?
            returns ($($body:tt)+),
            no_unwind
    ) => {
        verus! {
            pub open spec fn $spec($($arg : $aty),+) -> $rty 
            recommends $($($requires)+)?
                { $($body)+ }
            #[verifier::when_used_as_spec($spec)]
            pub assume_specification [ u8::$method ] ($($arg : $aty),+) -> ($ret: $rty)
                requires $($($requires)+)?
                returns $spec($($arg),+),
                no_unwind
            ;
        }
    };
}

macro_rules! assume_specification_for_char {
    (
        [$method:ident via $spec:ident] ($($arg:ident : $aty:ty),+) -> ($ret:ident: $rty:ty) 
            $(requires ($($requires:tt)+),)?
            returns ($($body:tt)+),
            no_unwind
    ) => {
        verus! {
            pub open spec fn $spec($($arg : $aty),+) -> $rty 
            recommends $($($requires)+)?
                { $($body)+ }
            #[verifier::when_used_as_spec($spec)]
            pub assume_specification [ char::$method ] ($($arg : $aty),+) -> ($ret: $rty)
                requires $($($requires)+)?
                returns $spec($($arg),+),
                no_unwind
            ;
        }
    };
}

macro_rules! assume_specification_for_u8_and_char {
    (
        [$method:ident; $specu8:ident, $specchar:ident] ($this:ident $(,$arg:ident : $aty:ty)*) -> ($ret:ident: $rty:ty) 
            $(requires ($($requires:tt)+),)?
            returns ($($body:tt)+),
            no_unwind
    ) => {
        assume_specification_for_u8!(
            [$method via $specu8] ($this: &u8 $(,$arg : $aty)*) -> ($ret: $rty)
            $(requires ($($requires)+),)?
            returns ($($body)+),
            no_unwind
        );
        assume_specification_for_char!(
            [$method via $specchar] ($this: &char $(,$arg : $aty)*) -> ($ret: $rty)
            $(requires ($($requires)+),)?
            returns ($($body)+),
            no_unwind
        );
    };
}

// consts

pub const CHAR_ZERO: u32 = '0' as u32;
pub const CHAR_NINE: u32 = '9' as u32;
pub const CHAR_LOWER_A: u32 = 'a' as u32;
pub const CHAR_LOWER_Z: u32 = 'z' as u32;
pub const CHAR_UPPER_A: u32 = 'A' as u32;
pub const CHAR_UPPER_Z: u32 = 'Z' as u32;
pub const CHAR_NUL: u32 = '\0' as u32;
pub const CHAR_SEP: u32 = '\u{001f}' as u32;
pub const CHAR_DEL: u32 = '\u{007f}' as u32;
pub const CHAR_SPACE: u32 = ' ' as u32;
pub const CHAR_TAB: u32 = '\t' as u32;
pub const CHAR_LF: u32 = '\n' as u32;
pub const CHAR_FF: u32 = '\u{000c}' as u32;
pub const CHAR_CR: u32 = '\r' as u32;

/// Enables `char::from_u32`.
assume_specification_for_char!(
    [from_u32 via char_from_u32] (i: u32) -> (ret: Option<char>) 
    returns (
        if is_scalar(i) { Some(i as char) } else { None }
    ),
    no_unwind
);

/// Enables `char::from_digit`.
assume_specification_for_char!(
    [from_digit via char_from_digit] (num: u32, radix: u32) -> (ret: Option<char>) 
    requires 
        (2 <= radix <= 36),
    returns (
        if 0 <= num < radix {
            Some((CHAR_ZERO + num) as u32 as char)
        } else if 10 <= num < radix {
            Some((CHAR_LOWER_A + num - 10) as u32 as char)
        } else {
            None
        }
    ),
    no_unwind
);

/// Enables `char::is_digit`.
assume_specification_for_char!(
    [is_digit via char_is_digit] (this: char, radix: u32) -> (ret: bool) 
    requires 
        (2 <= radix <= 36),
    returns (
        ||| CHAR_ZERO <= (this as u32) < CHAR_ZERO + radix
        ||| radix > 10 && (
            CHAR_LOWER_A <= (this as u32) < CHAR_LOWER_A + radix - 10
            || CHAR_UPPER_A <= (this as u32) < CHAR_UPPER_A + radix - 10
        )
    ),
    no_unwind
);

/// Enables `char::to_digit`.
assume_specification_for_char!(
    [to_digit via char_to_digit] (this: char, radix: u32) -> (ret: Option<u32>) 
    requires 
        (2 <= radix <= 36),
    returns (
        if CHAR_ZERO <= (this as u32) < CHAR_ZERO + min(10, radix as int) {
            Some((this as u32 - CHAR_ZERO) as u32)
        } else if CHAR_LOWER_A <= (this as u32) < CHAR_LOWER_A + radix - 10 {
            Some(((this as u32 - CHAR_LOWER_A) + 10) as u32)
        } else if CHAR_UPPER_A <= (this as u32) < CHAR_UPPER_A + radix - 10 {
            Some(((this as u32 - CHAR_UPPER_A) + 10) as u32)
        } else {
            None
        }
    ),
    no_unwind
);

/// Enables `char::len_utf8`.
assume_specification_for_char!(
    [len_utf8 via char_len_utf8] (this: char) -> (ret: usize) 
    returns 
        (encode_scalar(this as u32).len() as usize),
    no_unwind
);

pub uninterp spec fn is_non_ascii_alphabetic(this: char) -> bool;
pub uninterp spec fn is_non_ascii_lowercase(this: char) -> bool;
pub uninterp spec fn is_non_ascii_uppercase(this: char) -> bool;
pub uninterp spec fn is_non_ascii_whitespace(this: char) -> bool;
pub uninterp spec fn is_non_ascii_control(this: char) -> bool;
pub uninterp spec fn is_non_ascii_numberic(this: char) -> bool;

/// Enables `char::is_alphabetic`.
assume_specification_for_char!(
    [is_alphabetic via char_is_alphabetic](this: char) -> (ret: bool)
    returns
        (this.is_ascii_alphabetic() || is_non_ascii_alphabetic(this)),
    no_unwind
);

/// Enables `char::is_lowercase`.
assume_specification_for_char!(
    [is_lowercase via char_is_lowercase](this: char) -> (ret: bool)
    returns
        (this.is_ascii_lowercase() || is_non_ascii_lowercase(this)),
    no_unwind
);

/// Enables `char::is_uppercase`.
assume_specification_for_char!(
    [is_uppercase via char_is_uppercase](this: char) -> (ret: bool)
    returns
        (this.is_ascii_uppercase() || is_non_ascii_uppercase(this)),
    no_unwind
);

/// Enables `char::is_whitespace`.
assume_specification_for_char!(
    [is_whitespace via char_is_whitespace](this: char) -> (ret: bool)
    returns
        (this.is_ascii_whitespace() || is_non_ascii_whitespace(this)),
    no_unwind
);

/// Enables `char::is_alphanumeric`.
assume_specification_for_char!(
    [is_alphanumeric via char_is_alphanumeric](this: char) -> (ret: bool)
    returns
        (this.is_ascii_alphanumeric() || is_non_ascii_alphabetic(this) || is_non_ascii_numberic(this)),
    no_unwind
);

/// Enables `char::is_control`.
assume_specification_for_char!(
    [is_control via char_is_control](this: char) -> (ret: bool)
    returns
        (this.is_ascii_control() || is_non_ascii_control(this)),
    no_unwind
);

/// Enables `char::is_numeric`.
assume_specification_for_char!(
    [is_numeric via char_is_numeric](this: char) -> (ret: bool)
    returns
        (this.is_ascii_digit() || is_non_ascii_numberic(this)),
    no_unwind
);

/// Enables `u8|char::is_ascii`.
assume_specification_for_u8_and_char!([is_ascii; u8_is_ascii, char_is_ascii](this) -> (ret: bool)
    returns
        (0 <= *this <= CHAR_DEL),
    no_unwind
);

/// Enables `u8|char::is_ascii_alphabetic`.
assume_specification_for_u8_and_char!(
    [is_ascii_alphabetic; u8_is_ascii_alphabetic, char_is_ascii_alphabetic](this) -> (ret: bool)
    returns
        (CHAR_LOWER_A <= *this <= CHAR_LOWER_Z || CHAR_UPPER_A <= *this <= CHAR_UPPER_Z),
    no_unwind
);

/// Enables `u8|char::is_ascii_alphanumeric`.
assume_specification_for_u8_and_char!(
    [is_ascii_alphanumeric; u8_is_ascii_alphanumeric, char_is_ascii_alphanumeric](this) -> (ret: bool)
    returns (
        CHAR_ZERO <= *this <= CHAR_NINE 
        || CHAR_LOWER_A <= *this <= CHAR_LOWER_Z 
        || CHAR_UPPER_A <= *this <= CHAR_UPPER_Z 
    ),
    no_unwind
);

/// Enables `u8|char::is_ascii_control`.
assume_specification_for_u8_and_char!(
    [is_ascii_control; u8_is_ascii_control, char_is_ascii_control](this) -> (ret: bool)
    returns
        (*this == CHAR_NUL || *this == CHAR_SEP || *this == CHAR_DEL),
    no_unwind
);

/// Enables `u8|char::is_ascii_digit`.
assume_specification_for_u8_and_char!(
    [is_ascii_digit; u8_is_ascii_digit, char_is_ascii_digit](this) -> (ret: bool)
    returns
        (CHAR_ZERO <= *this <= CHAR_NINE),
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
    returns (
        CHAR_ZERO <= *this <= CHAR_NINE 
        || CHAR_LOWER_A <= *this < CHAR_LOWER_A + 6 
        || CHAR_UPPER_A <= *this < CHAR_UPPER_A + 6
    ),
    no_unwind
);

/// Enables `u8|char::is_ascii_lowercase`.
assume_specification_for_u8_and_char!(
    [is_ascii_lowercase; u8_is_ascii_lowercase, char_is_ascii_lowercase](this) -> (ret: bool)
    returns
        (CHAR_LOWER_A <= *this <= CHAR_LOWER_Z),
    no_unwind
);

/// Enables `u8|char::is_ascii_punctuation`.
assume_specification_for_u8_and_char!(
    [is_ascii_punctuation; u8_is_ascii_punctuation, char_is_ascii_punctuation](this) -> (ret: bool)
    returns (
        0x21 <= *this <= 0x2F 
        || 0x3A <= *this <= 0x40 
        || 0x5B <= *this <= 0x60 
        || 0x7B <= *this <= 0x7E
    ),
    no_unwind
);

/// Enables `u8|char::is_ascii_uppercase`.
assume_specification_for_u8_and_char!(
    [is_ascii_uppercase; u8_is_ascii_uppercase, char_is_ascii_uppercase](this) -> (ret: bool)
    returns
        (CHAR_UPPER_A <= *this <= CHAR_UPPER_Z),
    no_unwind
);

/// Enables `u8|char::is_ascii_whitespace`.
assume_specification_for_u8_and_char!(
    [is_ascii_whitespace; u8_is_ascii_whitespace, char_is_ascii_whitespace](this) -> (ret: bool)
    returns (
        *this == CHAR_SPACE 
        || *this == CHAR_TAB 
        || *this == CHAR_LF 
        || *this == CHAR_FF 
        || *this == CHAR_CR
    ),
    no_unwind
);

/// Enables `u8::to_ascii_lowercase`.
assume_specification_for_u8!(
    [to_ascii_lowercase via u8_to_ascii_lowercase] (this: &u8) -> (ret: u8)
    returns (
        if this.is_ascii_uppercase() { 
            (*this + (CHAR_LOWER_A - CHAR_UPPER_A)) as u8 
        } else { 
            *this 
        }
    ),
    no_unwind
);

/// Enables `char::to_ascii_lowercase`.
assume_specification_for_char!(
    [to_ascii_lowercase via char_to_ascii_lowercase] (this: &char) -> (ret: char)
    returns (
        if this.is_ascii_uppercase() { 
            (*this as u8 + (CHAR_LOWER_A - CHAR_UPPER_A)) as char 
        } else { 
            *this 
        }
    ),
    no_unwind
);

/// Enables `u8::to_ascii_uppercase`.
assume_specification_for_u8!(
    [to_ascii_uppercase via u8_to_ascii_uppercase] (this: &u8) -> (ret: u8)
    returns (
        if this.is_ascii_lowercase() { 
            (*this - (CHAR_LOWER_A - CHAR_UPPER_A)) as u8 
        } else { 
            *this 
        }
    ),
    no_unwind
);

/// Enables `char::to_ascii_uppercase`.
assume_specification_for_char!(
    [to_ascii_uppercase via char_to_ascii_uppercase] (this: &char) -> (ret: char)
    returns (
        if this.is_ascii_lowercase() { 
            (*this as u8 - (CHAR_LOWER_A - CHAR_UPPER_A)) as char 
        } else { 
            *this 
        }
    ),
    no_unwind
);


} // verus!
