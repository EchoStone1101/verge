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

fn test_upstream_simple_types_to_string() {
    broadcast use lemma_bool_to_string;
    broadcast use lemma_int_to_string;
    broadcast use lemma_string_to_string;

    proof {
        reveal_strlit("hi");
        reveal(spec_int_to_str);
        reveal_with_fuel(spec_int_to_str_rec, 4);
    }

    // Migrated from Rust's `alloc/tests/string.rs::test_simple_types`.
    let one = 1i32.to_string();
    assert(one@ =~= seq!['1']);
    let one_len = one.len();
    assert(one_len == 1usize);
    crate::exec_assert(one_len == 1usize);

    let minus_one = (-1i32).to_string();
    assert(minus_one@ =~= seq!['-', '1']);
    let minus_one_len = minus_one.len();
    assert(minus_one_len == 2usize);
    crate::exec_assert(minus_one_len == 2usize);

    let two_hundred = 200i32.to_string();
    assert(two_hundred@ =~= seq!['2', '0', '0']);
    let two_hundred_len = two_hundred.len();
    assert(two_hundred_len == 3usize);
    crate::exec_assert(two_hundred_len == 3usize);

    let two = 2i32.to_string();
    assert(two@ =~= seq!['2']);

    let true_s = true.to_string();
    assert(true_s@ =~= seq!['t', 'r', 'u', 'e']);
    let true_len = true_s.len();
    assert(true_len == 4usize);
    crate::exec_assert(true_len == 4usize);

    let false_s = false.to_string();
    assert(false_s@ =~= seq!['f', 'a', 'l', 's', 'e']);
    let false_len = false_s.len();
    assert(false_len == 5usize);
    crate::exec_assert(false_len == 5usize);

    let source = String::from_str("hi");
    let copied = source.to_string();
    assert(copied@ =~= seq!['h', 'i']);
    let copied_len = copied.len();
    assert(copied_len == 2usize);
    crate::exec_assert(copied_len == 2usize);
}

fn test_char_to_string_from_upstream_char_conversion() {
    broadcast use lemma_char_to_string;

    // Adapted from Rust's `alloc/tests/string.rs::test_from_char`.
    let a = 'a'.to_string();
    assert(a@ =~= seq!['a']);
    let a_len = a.len();
    assert(a_len == 1usize);
    crate::exec_assert(a_len == 1usize);

    let x = 'x'.to_string();
    assert(x@ =~= seq!['x']);
    let x_len = x.len();
    assert(x_len == 1usize);
    crate::exec_assert(x_len == 1usize);
}

fn test_reference_and_pointer_to_string_delegation() {
    broadcast use lemma_bool_to_string;
    broadcast use lemma_char_to_string;
    broadcast use lemma_ref_to_string;
    broadcast use lemma_mut_ref_to_string;
    broadcast use lemma_box_to_string;
    broadcast use lemma_rc_to_string;

    let b = true;
    let b_ref = &b;
    let ref_s = b_ref.to_string();
    assert(ref_s@ =~= seq!['t', 'r', 'u', 'e']);
    let ref_len = ref_s.len();
    assert(ref_len == 4usize);
    crate::exec_assert(ref_len == 4usize);

    let mut b_mut_value = false;
    let b_mut = &mut b_mut_value;
    let mut_ref_s = b_mut.to_string();
    assert(mut_ref_s@ =~= seq!['f', 'a', 'l', 's', 'e']);
    let mut_ref_len = mut_ref_s.len();
    assert(mut_ref_len == 5usize);
    crate::exec_assert(mut_ref_len == 5usize);

    let boxed = Box::new('b');
    let box_s = boxed.to_string();
    assert(box_s@ =~= seq!['b']);
    let box_len = box_s.len();
    assert(box_len == 1usize);
    crate::exec_assert(box_len == 1usize);

    let rc = Rc::new('r');
    let rc_s = rc.to_string();
    assert(rc_s@ =~= seq!['r']);
    let rc_len = rc_s.len();
    assert(rc_len == 1usize);
    crate::exec_assert(rc_len == 1usize);
}

fn test_custom_to_string_spec_and_exec_behavior() {
    let quiet = CustomToken { shout: false };
    let quiet_s = quiet.to_string();
    assert(ToStringSpec::to_string_ensures(&quiet, quiet_s));
    assert(quiet_s@ =~= seq!['o', 'k']);
    let quiet_len = quiet_s.len();
    assert(quiet_len == 2usize);
    crate::exec_assert(quiet_len == 2usize);

    let loud = CustomToken { shout: true };
    let loud_s = loud.to_string();
    assert(ToStringSpec::to_string_ensures(&loud, loud_s));
    assert(loud_s@ =~= seq!['O', 'K']);
    let loud_len = loud_s.len();
    assert(loud_len == 2usize);
    crate::exec_assert(loud_len == 2usize);
}

fn test_debug_format_callability_and_uninterpreted_spec() {
    let token = DebugToken { value: true };
    let s = debug_format(&token);
    assert(debug_format_ensures::<DebugToken>(&token, s));

    // `debug_format_ensures` is intentionally uninterpreted, so this test only
    // checks downstream callability and availability of the postcondition.
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "str::fmt::upstream_simple_types_to_string",
        test_upstream_simple_types_to_string,
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
