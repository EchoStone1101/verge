use vstd::prelude::*;

use std::num::ParseIntError;

verus! {
    pub open spec fn spec_trim_ascii_start(s: Seq<u8>) -> Seq<u8> 
        decreases s.len()
    {
        if s.len() == 0 {
            s
        } else if s[0].spec_is_ascii_whitespace() {
            spec_trim_ascii_start(s.skip(1))
        } else {
            s
        }
    }

    pub open spec fn spec_trim_ascii_end(s: Seq<u8>) -> Seq<u8> 
        decreases s.len()
    {
        if s.len() == 0 {
            s
        } else if s[s.len() - 1].spec_is_ascii_whitespace() {
            spec_trim_ascii_end(s.take(s.len() - 1))
        } else {
            s
        }
    }

    pub open spec fn spec_seq_find(s: Seq<u8>, idx: int, pred: spec_fn(u8) -> bool) -> Option<int> 
        recommends 0 <= idx <= s.len(),
        decreases s.len() - idx,
    {
        if idx >= s.len() {
            None
        } else if pred(s[idx]) {
            Some(idx)
        } else {
            spec_seq_find(s, idx + 1, pred)
        }
    }

    pub open spec fn spec_ascii_to_unsigned_number(s: Seq<u8>, idx: int, result: int, radix: int, is_positive: bool) -> Option<int> 
        recommends 0 <= idx <= s.len(),
        decreases s.len() - idx,
    {
        if idx >= s.len() {
            if is_positive { Some(result) } else { Some(-result) }
        } else {
            match spec_ascii_to_digit(s[idx], radix) {
                None => None,
                Some(digit) => spec_ascii_to_unsigned_number(s, idx + 1, result * radix + digit, radix, is_positive),
            }
        }
    }

    pub open spec fn spec_ascii_to_number(s: Seq<u8>, radix: int) -> Option<int> {
        if s.len() == 0 {
            None
        } else if s[0].spec_is_ascii_alphanumeric() {
            spec_ascii_to_unsigned_number(s, 0, 0, radix, true)
        }
        else {
            match s[0] {
                // '+' sign
                0x2B => spec_ascii_to_unsigned_number(s.skip(1), 0, 0, radix, true),
                // '-' sign
                0x2D => spec_ascii_to_unsigned_number(s.skip(1), 0, 0, radix, false),
                _ => None
            }
        }
    }
    
    pub assume_specification [<[u8]>::is_ascii] (s: &[u8]) -> (b: bool)
        ensures b <==> forall |i: int| #![auto] 0 <= i < s.len() ==> s[i].spec_is_ascii();

    pub assume_specification [<[u8]>::trim_ascii_start] (s: &[u8]) -> (ret: &[u8])
        ensures 
            s.len() >= ret.len() 
            && ret@ =~= spec_trim_ascii_start(s@) 
            && ret@ =~= s@.skip(s.len() - ret.len())
            && ret.len() > 0 ==> !ret[0].spec_is_ascii_whitespace()
            && forall |i: int| #![auto] 0 <= i < s.len() - ret.len() ==> s[i].spec_is_ascii_whitespace();

    pub assume_specification [<[u8]>::trim_ascii_end] (s: &[u8]) -> (ret: &[u8])
        ensures 
            s.len() >= ret.len() 
            && ret@ =~= spec_trim_ascii_end(s@)
            && ret@ =~= s@.take(ret.len() as int)
            && ret.len() > 0 ==> !ret[ret.len() - 1].spec_is_ascii_whitespace()
            && forall |i: int| #![auto] ret.len() <= i < s.len() ==> s[i].spec_is_ascii_whitespace();

    // pub assume_specification [<[u8]>::trim_ascii] (s: &[u8]) -> (ret: &[u8])
    //     ensures s.len() >= ret.len() && ret@ =~= spec_trim_ascii_end(spec_trim_ascii_start(s@));

    // Note: split_at_mut is not supported in Verus yet
    pub assume_specification<T> [<[T]>::split_at] (s: &[T], mid: usize) -> (result: (&[T], &[T]))
        requires mid <= s.len()
        ensures 
            s.len() == result.0.len() + result.1.len(),
            s@.take(mid as int) =~= result.0@,
            s@.skip(mid as int) =~= result.1@,
            s@ =~= result.0@ + result.1@;
    
    pub assume_specification<T> [<[T]>::split_at_checked] (s: &[T], mid: usize) -> (result: Option<(&[T], &[T])>)
        ensures
            match result {
                None => s.len() < mid,
                Some((left, right)) => mid <= s.len() &&
                    s.len() == left.len() + right.len() &&
                    s@.take(mid as int) =~= left@ &&
                    s@.skip(mid as int) =~= right@ &&
                    s@ =~= left@ + right@,
            };
    
    #[verifier::external_body]
    pub fn split_match<F: Fn(u8) -> bool>(s: &[u8], pred: F, spec_pred: spec_fn(u8) -> bool) -> (result: (&[u8], Option<&[u8]>))
        ensures
            match spec_seq_find(s@, 0, spec_pred) {
                None => result.0@ =~= s@ && result.1.is_none() && forall |i: int| 0 <= i < s.len() ==> !spec_pred(s[i]),
                Some(idx) => result.1.is_some() &&s@ =~= result.0@ + seq![s[idx]] + result.1.unwrap()@,
            }
    {
        for i in 0..s.len() {
            if pred(s[i]) {
                return (&s[..i], Some(&s[i+1..]));
            }
        }
        (s, None)
    }
}


// Specifications for u8 ASCII methods
verus! {

pub open spec fn spec_ascii_to_digit(x: u8, radix: int) -> Option<int> {
    let digit = {
        if radix < 2 || radix > 36 {
            None
        } else if x.spec_is_ascii_digit() {
            Some(x - 0x30)
        } else if x.spec_is_ascii_uppercase() {
            Some(x - 0x41 + 10)
        } else if x.spec_is_ascii_lowercase() {
            Some(x - 0x61 + 10)
        } else {
            None
        }
    };

    match digit {
        Some(d) if d < radix => Some(d),
        _ => None,
    }
} 

pub assume_specification[ u8::is_ascii ] (x: &u8) -> (b: bool) 
    ensures b <==> *x <= 127;

pub assume_specification[ u8::is_ascii_whitespace ] (x: &u8) -> (b: bool) 
    // matches!(*self, b'\t' | b'\n' | b'\x0C' | b'\r' | b' ')
    ensures b <==> *x == 0x09 || *x == 0x0A || *x == 0x0C || *x == 0x0D || *x == 0x20;

pub assume_specification[ u8::is_ascii_alphabetic ] (x: &u8) -> (b: bool)
    // matches!(*self, b'A'..=b'Z' | b'a'..=b'z')
    ensures b <==> (0x41 <= *x <= 0x5A) || (0x61 <= *x <= 0x7A);

pub assume_specification[ u8::is_ascii_digit ] (x: &u8) -> (b: bool)
    // matches!(*self, b'0'..=b'9')
    ensures b <==> (0x30 <= *x <= 0x39);

pub assume_specification[ u8::is_ascii_alphanumeric ] (x: &u8) -> (b: bool)
    // matches!(*self, b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9')
    ensures b <==> (0x41 <= *x <= 0x5A) || (0x61 <= *x <= 0x7A) || (0x30 <= *x <= 0x39);

pub assume_specification[ u8::is_ascii_lowercase ] (x: &u8) -> (b: bool)
    // matches!(*self, b'a'..=b'z')
    ensures b <==> (0x61 <= *x <= 0x7A);

pub assume_specification[ u8::is_ascii_uppercase ] (x: &u8) -> (b: bool)
    // matches!(*self, b'A'..=b'Z')
    ensures b <==> (0x41 <= *x <= 0x5A);

pub trait AsciiSpec {
    spec fn spec_is_ascii(&self) -> bool;
    spec fn spec_is_ascii_whitespace(&self) -> bool;
    spec fn spec_is_ascii_alphabetic(&self) -> bool;
    spec fn spec_is_ascii_digit(&self) -> bool;
    spec fn spec_is_ascii_alphanumeric(&self) -> bool;
    spec fn spec_is_ascii_lowercase(&self) -> bool;
    spec fn spec_is_ascii_uppercase(&self) -> bool;
}

impl AsciiSpec for u8 {
    open spec fn spec_is_ascii(&self) -> bool {
        *self <= 127
    }

    open spec fn spec_is_ascii_whitespace(&self) -> bool {
        *self == 0x09 || *self == 0x0A || *self == 0x0C || *self == 0x0D || *self == 0x20
    }

    open spec fn spec_is_ascii_alphabetic(&self) -> bool {
        (0x41 <= *self <= 0x5A) || (0x61 <= *self <= 0x7A)
    }

    open spec fn spec_is_ascii_digit(&self) -> bool {
        (0x30 <= *self <= 0x39)
    }

    open spec fn spec_is_ascii_alphanumeric(&self) -> bool {
        (0x41 <= *self <= 0x5A) || (0x61 <= *self <= 0x7A) || (0x30 <= *self <= 0x39)
    }

    open spec fn spec_is_ascii_lowercase(&self) -> bool {
        (0x61 <= *self <= 0x7A)
    }

    open spec fn spec_is_ascii_uppercase(&self) -> bool {
        (0x41 <= *self <= 0x5A)
    }
}

}


verus! {
    #[verifier::external_body]
    pub struct ExParseIntError(ParseIntError);

    pub trait FromAsciiVerified: Sized {
        fn from_ascii_verified(s: &[u8], radix: u32) -> Result<Self, ExParseIntError>
            requires forall |i: int| #![auto] 0 <= i < s.len() ==> s[i].spec_is_ascii();
    }

    impl FromAsciiVerified for u8 {
        #[verifier::external_body]
        fn from_ascii_verified(s: &[u8], radix: u32) -> (result: Result<Self, ExParseIntError>) 
            ensures match result {
                Ok(x) => {
                    let i = spec_ascii_to_number(s@, radix as int).unwrap();
                    i == x && u8::MIN <= i <= u8::MAX
                },
                Err(_) => match spec_ascii_to_number(s@, radix as int) {
                    None => true,
                    Some(i) => i < u8::MIN || i > u8::MAX,
                },
            }
        {
            Ok(u8::from_str_radix(std::str::from_utf8(s).unwrap(), radix).map_err(ExParseIntError)?)
        }
    }

    impl FromAsciiVerified for u16 {
        #[verifier::external_body]
        fn from_ascii_verified(s: &[u8], radix: u32) -> (result: Result<Self, ExParseIntError>) 
            ensures match result {
                Ok(x) => {
                    let i = spec_ascii_to_number(s@, radix as int).unwrap();
                    i == x && u16::MIN <= i <= u16::MAX
                },
                Err(_) => match spec_ascii_to_number(s@, radix as int) {
                    None => true,
                    Some(i) => i < u16::MIN || i > u16::MAX,
                },
            }
        {
            Ok(u16::from_str_radix(std::str::from_utf8(s).unwrap(), radix).map_err(ExParseIntError)?)
        }
    }

    impl FromAsciiVerified for u32 {
        #[verifier::external_body]
        fn from_ascii_verified(s: &[u8], radix: u32) -> (result: Result<Self, ExParseIntError>) 
            ensures match result {
                Ok(x) => {
                    let i = spec_ascii_to_number(s@, radix as int).unwrap();
                    i == x && u32::MIN <= i <= u32::MAX
                },
                Err(_) => match spec_ascii_to_number(s@, radix as int) {
                    None => true,
                    Some(i) => i < u32::MIN || i > u32::MAX,
                },
            }
        {
            Ok(u32::from_str_radix(std::str::from_utf8(s).unwrap(), radix).map_err(ExParseIntError)?)
        }
    }

    impl FromAsciiVerified for u64 {
        #[verifier::external_body]
        fn from_ascii_verified(s: &[u8], radix: u32) -> (result: Result<Self, ExParseIntError>) 
            ensures match result {
                Ok(x) => {
                    let i = spec_ascii_to_number(s@, radix as int).unwrap();
                    i == x && u64::MIN <= i <= u64::MAX
                },
                Err(_) => match spec_ascii_to_number(s@, radix as int) {
                    None => true,
                    Some(i) => i < u64::MIN || i > u64::MAX,
                },
            }
        {
            Ok(u64::from_str_radix(std::str::from_utf8(s).unwrap(), radix).map_err(ExParseIntError)?)
        }
    }

    impl FromAsciiVerified for i8 {
        #[verifier::external_body]
        fn from_ascii_verified(s: &[u8], radix: u32) -> (result: Result<Self, ExParseIntError>) 
            ensures match result {
                Ok(x) => {
                    let i = spec_ascii_to_number(s@, radix as int).unwrap();
                    i == x && i8::MIN <= i <= i8::MAX
                },
                Err(_) => match spec_ascii_to_number(s@, radix as int) {
                    None => true,
                    Some(i) => i < i8::MIN || i > i8::MAX,
                },
            }
        {
            Ok(i8::from_str_radix(std::str::from_utf8(s).unwrap(), radix).map_err(ExParseIntError)?)
        }
    }

    impl FromAsciiVerified for i16 {
        #[verifier::external_body]
        fn from_ascii_verified(s: &[u8], radix: u32) -> (result: Result<Self, ExParseIntError>) 
            ensures match result {
                Ok(x) => {
                    let i = spec_ascii_to_number(s@, radix as int).unwrap();
                    i == x && i16::MIN <= i <= i16::MAX
                },
                Err(_) => match spec_ascii_to_number(s@, radix as int) {
                    None => true,
                    Some(i) => i < i16::MIN || i > i16::MAX,
                },
            }
        {
            Ok(i16::from_str_radix(std::str::from_utf8(s).unwrap(), radix).map_err(ExParseIntError)?)
        }
    }

    impl FromAsciiVerified for i32 {
        #[verifier::external_body]
        fn from_ascii_verified(s: &[u8], radix: u32) -> (result: Result<Self, ExParseIntError>) 
            ensures match result {
                Ok(x) => {
                    let i = spec_ascii_to_number(s@, radix as int).unwrap();
                    i == x && i32::MIN <= i <= i32::MAX
                },
                Err(_) => match spec_ascii_to_number(s@, radix as int) {
                    None => true,
                    Some(i) => i < i32::MIN || i > i32::MAX,
                },
            }
        {
            Ok(i32::from_str_radix(std::str::from_utf8(s).unwrap(), radix).map_err(ExParseIntError)?)
        }
    }

    impl FromAsciiVerified for i64 {
        #[verifier::external_body]
        fn from_ascii_verified(s: &[u8], radix: u32) -> (result: Result<Self, ExParseIntError>) 
            ensures match result {
                Ok(x) => {
                    let i = spec_ascii_to_number(s@, radix as int).unwrap();
                    i == x && i64::MIN <= i <= i64::MAX
                },
                Err(_) => match spec_ascii_to_number(s@, radix as int) {
                    None => true,
                    Some(i) => i < i64::MIN || i > i64::MAX,
                },
            }
        {
            Ok(i64::from_str_radix(std::str::from_utf8(s).unwrap(), radix).map_err(ExParseIntError)?)
        }
    }

}
