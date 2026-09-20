//! Tests for string formatting APIs.

use std::rc::Rc;
use vstd::prelude::*;
use verge::prelude::*;
use verge::str::*;

verus! {

pub struct CustomToken {
    pub shout: bool,
}

#[derive(Debug)]
struct DebugToken {
    value: bool,
}

impl ToStringSpecImpl for CustomToken {
    open spec fn to_string_ensures(&self, s: String) -> bool {
        if self.shout {
            s@ =~= seq!['O', 'K']
        } else {
            s@ =~= seq!['o', 'k']
        }
    }
}

impl ToString for CustomToken {
    fn to_string(&self) -> (s: String)
        ensures
            self.shout ==> s@ =~= seq!['O', 'K'],
            !self.shout ==> s@ =~= seq!['o', 'k'],
    {
        proof {
            reveal_strlit("OK");
            reveal_strlit("ok");
        }
        if self.shout {
            String::from_str("OK")
        } else {
            String::from_str("ok")
        }
    }
}

fn test_integer_to_string_lengths() {
    broadcast use lemma_int_to_string;
    proof {
        reveal(spec_int_to_str);
        reveal_with_fuel(spec_int_to_str_rec, 4);
    }
    test!(1i32.to_string().len() == 1usize);
    test!((-1i32).to_string().len() == 2usize);
    test!(200i32.to_string().len() == 3usize);
    test!(2i32.to_string().len() == 1usize);
}

fn test_bool_to_string_lengths() {
    broadcast use lemma_bool_to_string;
    test!(true.to_string().len() == 4usize);
    test!(false.to_string().len() == 5usize);
}

fn test_string_to_string_length() {
    broadcast use lemma_string_to_string;
    proof { reveal_strlit("hi"); }
    test!(String::from_str("hi").to_string().len() == 2usize);
}

fn test_char_to_string_from_upstream_char_conversion() {
    broadcast use lemma_char_to_string;

    // Adapted from Rust's `alloc/tests/string.rs::test_from_char`.
    test!('a'.to_string().len() == 1usize);
    test!('x'.to_string().len() == 1usize);
}

fn test_reference_and_pointer_to_string_delegation() {
    broadcast use lemma_bool_to_string;
    broadcast use lemma_char_to_string;
    broadcast use lemma_ref_to_string;
    broadcast use lemma_mut_ref_to_string;
    broadcast use lemma_box_to_string;
    broadcast use lemma_rc_to_string;

    test!((&true).to_string().len() == 4usize);

    test!((&mut false).to_string().len() == 5usize);

    test!(Box::new('b').to_string().len() == 1usize);
    test!(Rc::new('r').to_string().len() == 1usize);
}

fn test_custom_to_string_spec_and_exec_behavior() {
    test!(CustomToken { shout: false }.to_string().len() == 2usize);
    test!(CustomToken { shout: true }.to_string().len() == 2usize);
}

fn test_debug_format_callability_and_uninterpreted_spec() {
    let token = DebugToken { value: true };
    let s = debug_format(&token);
    proof {
        assert(debug_format_ensures::<DebugToken>(&token, s));
    }
    test!(s.len() == s.as_bytes().len());

    // `debug_format_ensures` is intentionally uninterpreted, so this test only
    // checks downstream callability and availability of the postcondition.
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "str::fmt::integer_to_string_lengths",
        test_integer_to_string_lengths,
    );
    count += crate::run_test(
        "str::fmt::bool_to_string_lengths",
        test_bool_to_string_lengths,
    );
    count += crate::run_test(
        "str::fmt::string_to_string_length",
        test_string_to_string_length,
    );
    count += crate::run_test(
        "str::fmt::char_to_string_from_upstream_char_conversion",
        test_char_to_string_from_upstream_char_conversion,
    );
    count += crate::run_test(
        "str::fmt::reference_and_pointer_to_string_delegation",
        test_reference_and_pointer_to_string_delegation,
    );
    count += crate::run_test(
        "str::fmt::custom_to_string_spec_and_exec_behavior",
        test_custom_to_string_spec_and_exec_behavior,
    );
    count += crate::run_test(
        "str::fmt::debug_format_callability_and_uninterpreted_spec",
        test_debug_format_callability_and_uninterpreted_spec,
    );
    count
}
