//! Specifications and lemmas for formatting types into strings.
//!
//! Currently, Verge adds support for a selection of primitive `Display` types by further specifying 
//! their `to_string()` method. The `format!` macro and formatters remain external.
//! The `Debug` trait is also exposed, but the specification is left deliberately uninterpreted
//! because of its volatile nature.
use super::*;
use std::fmt::{Display, Debug};
use std::rc::Rc;

/// This function defines the result of displaying `T` as a string.
/// 
/// It is left uninterpreted by default; implementations can add further specifications 
/// as is appropriate, by introducing axioms with `define_spec_to_string!`.
pub use vstd::string::to_string_from_display_ensures;

verus! {

/// Further specifies `to_string_from_display_ensures` for `T`.
#[macro_export]
macro_rules! define_spec_to_string {
    ($axiom:ident($t:ident: &$ty:ty) -> ($s:ident: String) { $($def:tt)* }) => {
        verus! {
        #[verifier::external_body]
        pub axiom fn $axiom($t: &$ty, $s: String) 
            ensures
                to_string_from_display_ensures::<$ty>($t, $s) == { $($def)* },
        ;
        }
    };
}

pub use define_spec_to_string;

/// Specifies `<bool as ToString>::to_string`.
define_spec_to_string!(
    lemma_bool_to_string(b: &bool) -> (s: String) {
        &&& *b <==> s@ == seq!['t', 'r', 'u', 'e']
        &&& !*b <==> s@ == seq!['f', 'a', 'l', 's', 'e']
    } 
);

/// Specifies `<char as ToString>::to_string`.
define_spec_to_string!(
    lemma_char_to_string(c: &char) -> (s: String) {
        s@ == seq![*c]
    } 
);

/// This function encodes displaying an (arbitrarily large) decimal `int` into a string.
#[verifier::opaque]
pub open spec fn spec_int_to_str(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else if n > 0 {
        spec_int_to_str_rec(n as nat)
    } else {
        seq!['-'] + spec_int_to_str_rec((-n) as nat)
    }
}

pub open spec fn spec_int_to_str_rec(n: nat) -> Seq<char> 
    decreases n,
{
    if n == 0 {
        seq![]
    } else {
        use vstd::arithmetic::div_mod::lemma_div_decreases;
        proof { lemma_div_decreases(n as int, 10) } // proof for `decreases`
        seq![(n % 10 + 0x30) as char] + spec_int_to_str_rec(n / 10)
    }
}

/// Specifies `<i8 as ToString>::to_string`.
define_spec_to_string!(
    lemma_i8_to_string(n: &i8) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<i16 as ToString>::to_string`.
define_spec_to_string!(
    lemma_i16_to_string(n: &i16) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<i32 as ToString>::to_string`.
define_spec_to_string!(
    lemma_i32_to_string(n: &i32) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<i64 as ToString>::to_string`.
define_spec_to_string!(
    lemma_i64_to_string(n: &i64) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<i128 as ToString>::to_string`.
define_spec_to_string!(
    lemma_i128_to_string(n: &i128) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<isize as ToString>::to_string`.
define_spec_to_string!(
    lemma_isize_to_string(n: &isize) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<u8 as ToString>::to_string`.
define_spec_to_string!(
    lemma_u8_to_string(n: &u8) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<u16 as ToString>::to_string`.
define_spec_to_string!(
    lemma_u16_to_string(n: &u16) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<u32 as ToString>::to_string`.
define_spec_to_string!(
    lemma_u32_to_string(n: &u32) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<u64 as ToString>::to_string`.
define_spec_to_string!(
    lemma_u64_to_string(n: &u64) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<u128 as ToString>::to_string`.
define_spec_to_string!(
    lemma_u128_to_string(n: &u128) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<usize as ToString>::to_string`.
define_spec_to_string!(
    lemma_usize_to_string(n: &usize) -> (s: String) {
        s@ == spec_int_to_str(*n as int)
    } 
);

/// Specifies `<String as ToString>::to_string`.
define_spec_to_string!(
    lemma_string_to_string(s: &String) -> (string: String) {
        string@ == s@ && string.is_ascii() == s.is_ascii()
    } 
);

/// Specifies `<&T as ToString>::to_string`, where `T: Display + ?Sized`.
#[verifier::external_body]
pub axiom fn lemma_ref_to_string<T: Display + ?Sized>(t: &&T, s: String) 
    ensures
        to_string_from_display_ensures::<&T>(t, s) == to_string_from_display_ensures::<T>(*t, s)
;

/// Specifies `<Box<T> as ToString>::to_string`, where `T: Display + ?Sized`.
#[verifier::external_body]
pub axiom fn lemma_box_to_string<T: Display + ?Sized>(t: &Box<T>, s: String) 
    ensures
        to_string_from_display_ensures::<Box<T>>(t, s) == to_string_from_display_ensures::<T>(&*t, s)
;

/// Specifies `<Rc<T> as ToString>::to_string`, where `T: Display + ?Sized`.
#[verifier::external_body]
pub axiom fn lemma_rc_to_string<T: Display + ?Sized>(t: &Rc<T>, s: String) 
    ensures
        to_string_from_display_ensures::<Rc<T>>(t, s) == to_string_from_display_ensures::<T>(&*t, s)
;


/// Enables printing the value `t` as `Debug`.
#[verifier::external_body]
pub fn debug_format<T: Debug + ?Sized>(t: &T) -> (s: String) 
    ensures
        debug_format_ensures::<T>(t, s),
{
    format!("{:?}", t)
}

/// This function defines the result of printing `T` as `Debug`. It is always uninterpreted.
pub uninterp spec fn debug_format_ensures<T: Debug + ?Sized>(
    t: &T,
    s: String,
) -> bool;

// TODO(rilin): tests; also prove int -> to_string -> from_str is id

} // verus!


