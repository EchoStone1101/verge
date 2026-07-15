//! Tests for `std::String` APIs specified by Verge.

use vstd::prelude::*;
use vstd::assert_seqs_equal;
use vstd::utf8::*;
use verge::error::ErrorSpec;
use verge::prelude::*;
use verge::str::*;

verus! {

fn keep_not_b(character: char) -> (ret: bool)
    ensures
        ret == (character != 'b'),
{
    character != 'b'
}

fn test_views_and_capacity_are_callable() {
    broadcast use group_str_axioms;

    let mut text = String::with_capacity(16);
    let empty = text.is_empty();
    let len = text.len();
    let bytes = text.as_bytes();

    assert(text@ =~= Seq::<char>::empty());
    assert(empty);
    crate::exec_assert(empty);
    assert(len == 0usize);
    crate::exec_assert(len == 0usize);
    assert(bytes@ =~= Seq::<u8>::empty());
    crate::exec_assert(bytes.len() == 0usize);

    proof {
        reveal_strlit("abc");
    }
    text.push_str("abc");

    let nonempty = text.is_empty();
    let len = text.len();
    let bytes = text.as_bytes();
    assert(text@ =~= seq!['a', 'b', 'c']);
    assert(!nonempty);
    crate::exec_assert(!nonempty);
    assert(len == 3usize);
    crate::exec_assert(len == 3usize);
    assert(bytes@ =~= seq![97u8, 98u8, 99u8]);
    crate::exec_assert(bytes.len() == 3usize);
}

fn test_from_utf8_ok_err_and_verified() {
    broadcast use group_str_axioms;

    let good = vec![104u8, 101u8, 108u8, 108u8, 111u8];
    assert(good@.is_utf8());
    let good_result = String::from_utf8(good);
    let good_is_ok = good_result.is_ok();
    assert(good_is_ok);
    crate::exec_assert(good_is_ok);
    match good_result {
        Ok(text) => {
            assert(text@ =~= seq!['h', 'e', 'l', 'l', 'o']);
            let len = text.len();
            assert(len == 5usize);
            crate::exec_assert(len == 5usize);
        }
        Err(_) => {
            assert(false);
        }
    }

    let bad = vec![0xffu8];
    assert(!bad@.is_utf8());
    let bad_result = String::from_utf8(bad);
    let bad_is_err = bad_result.is_err();
    assert(bad_is_err);
    crate::exec_assert(bad_is_err);
    match bad_result {
        Ok(_) => {
            assert(false);
        }
        Err(error) => {
            assert(error.is_str_utf8_error());
        }
    }

    let verified_bytes = vec![97u8, 98u8, 99u8];
    assert(verified_bytes@.is_utf8());
    let verified = String::from_utf8_verified(verified_bytes);
    assert(verified@ =~= seq!['a', 'b', 'c']);
    let verified_len = verified.len();
    assert(verified_len == 3usize);
    crate::exec_assert(verified_len == 3usize);
}

fn test_into_bytes_roundtrip_is_callable() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("abc");
    }

    let mut text = String::with_capacity(4);
    text.push_str("abc");
    let bytes = text.into_bytes();

    assert(bytes@ =~= seq![97u8, 98u8, 99u8]);
    crate::exec_assert(bytes.len() == 3usize);

    let roundtrip = String::from_utf8(bytes);
    let roundtrip_is_ok = roundtrip.is_ok();
    assert(roundtrip_is_ok);
    crate::exec_assert(roundtrip_is_ok);
}

fn test_as_mut_str_exposes_current_view() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("abc");
    }

    let mut text = String::with_capacity(4);
    text.push_str("abc");
    let ghost before = text@;
    {
        let view = text.as_mut_str();
        assert(view@ =~= before);
    }
    assert(text@ =~= before);
    crate::exec_assert(text.len() == 3usize);
}

fn test_push_pop_and_clear_core_cases() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("");
        reveal_strlit("abc");
    }

    let mut text = String::with_capacity(16);
    text.push_str("");
    assert(text@ =~= Seq::<char>::empty());
    crate::exec_assert(text.len() == 0usize);

    text.push_str("abc");
    assert(text@ =~= seq!['a', 'b', 'c']);
    crate::exec_assert(text.len() == 3usize);

    text.push('b');
    text.push('¢');
    text.push('€');
    text.push('𤭢');
    assert(text@ =~= seq!['a', 'b', 'c', 'b', '¢', '€', '𤭢']);

    let four_byte = text.pop();
    assert(four_byte == Some('𤭢'));
    crate::exec_assert(four_byte == Some('𤭢'));
    let three_byte = text.pop();
    assert(three_byte == Some('€'));
    crate::exec_assert(three_byte == Some('€'));
    let two_byte = text.pop();
    assert(two_byte == Some('¢'));
    crate::exec_assert(two_byte == Some('¢'));
    let one_byte = text.pop();
    assert(one_byte == Some('b'));
    crate::exec_assert(one_byte == Some('b'));

    text.clear();
    assert(text@ =~= Seq::<char>::empty());
    let empty = text.is_empty();
    assert(empty);
    crate::exec_assert(empty);
    let none = text.pop();
    assert(none.is_none());
    crate::exec_assert(none.is_none());
}

fn test_reserve_preserves_contents() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("cap");
    }

    let mut text = String::with_capacity(3);
    text.push_str("cap");
    let ghost before = text@;

    text.reserve(8usize);
    assert(text@ =~= before);
    crate::exec_assert(text.len() == 3usize);

    text.reserve_exact(8usize);
    assert(text@ =~= before);
    crate::exec_assert(text.len() == 3usize);
}

fn test_insert_ascii_boundary() {
    broadcast use group_str_axioms;

    let mut text = String::with_capacity(1);
    text.insert(0usize, 'a');
    assert(text@.as_bytes() =~= seq![97u8]);
    let len = text.len();
    assert(len == 1usize);
    crate::exec_assert(len == 1usize);
}

fn test_insert_str_ascii_boundary() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("bc");
    }

    let mut text = String::with_capacity(2);
    text.insert_str(0usize, "bc");
    assert(text@.as_bytes() =~= seq![98u8, 99u8]);
    let len = text.len();
    assert(len == 2usize);
    crate::exec_assert(len == 2usize);
}

fn test_remove_ascii_boundary() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("abcd");
    }

    let mut text = String::from_str("abcd");
    let removed = text.remove(1usize);

    assert(removed as u32 == decode_first_scalar(seq![98u8, 99u8, 100u8]));
    assert(text@.as_bytes() =~= seq![97u8, 99u8, 100u8]);
    let removed_len = text.len();
    assert(removed_len == 3usize);
    crate::exec_assert(removed_len == 3usize);
}

fn test_split_off_and_truncate_ascii_boundaries() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("ABCD");
    }

    let mut text = String::with_capacity(8);
    text.push_str("ABCD");
    let remainder = text.split_off(2usize);
    let prefix_len = text.len();
    let remainder_len = remainder.len();
    assert(prefix_len == 2usize);
    assert(remainder_len == 2usize);
    crate::exec_assert(prefix_len == 2usize);
    crate::exec_assert(remainder_len == 2usize);

    let empty = text.split_off(2usize);
    assert(empty@ =~= Seq::<char>::empty());
    crate::exec_assert(empty.is_empty());
    let prefix_len = text.len();
    assert(prefix_len == 2usize);
    crate::exec_assert(prefix_len == 2usize);

    text.truncate(1usize);
    assert(text@.as_bytes() =~= seq![65u8]);
    crate::exec_assert(text.len() == 1usize);
    text.truncate(0usize);
    assert(text@ =~= Seq::<char>::empty());
    crate::exec_assert(text.is_empty());
}

fn test_truncate_past_end_is_noop() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("12345");
    }

    let mut text = String::with_capacity(5);
    text.push_str("12345");
    let ghost before = text@;
    assert(text@.as_bytes().len() == 5);
    text.truncate(6usize);
    assert(text@.as_bytes() =~= before.as_bytes());
    let len = text.len();
    assert(len == 5usize);
    crate::exec_assert(len == 5usize);
}

fn test_retain_with_named_predicate() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("abc");
    }

    let mut text = String::with_capacity(4);
    text.push_str("abc");
    let mut keep_not_b_closure = |character: char| -> (ret: bool)
        requires
            true,
        ensures
            ret == (character != 'b'),
    {
        character != 'b'
    };
    let keep_a = keep_not_b_closure('a');
    let keep_b = keep_not_b_closure('b');
    let keep_c = keep_not_b_closure('c');
    assert(keep_a);
    assert(!keep_b);
    assert(keep_c);

    text.retain(keep_not_b_closure);
    proof {
        let pred = |character: char| call_ensures(keep_not_b_closure, (character,), true);
        reveal_with_fuel(Seq::<_>::filter, 4);
        assert(text@ =~= "abc"@.filter(pred));
        assert(pred('a'));
        assert(!pred('b'));
        assert(pred('c'));
        assert_seqs_equal!(text@ == seq!['a', 'c']);
    };
    let retained_len = text.len();
    assert(retained_len == 2usize);
    crate::exec_assert(retained_len == 2usize);

    let last = text.pop();
    assert(last == Some('c'));
    crate::exec_assert(last == Some('c'));
    let first = text.pop();
    assert(first == Some('a'));
    crate::exec_assert(first == Some('a'));
}

fn test_panicking_indices_are_blocked_by_preconditions() {
    broadcast use group_str_axioms;

    let empty = String::with_capacity(0);
    assert(empty@.as_bytes().len() == 0);
    assert(!is_char_boundary(empty@.as_bytes(), 1));

    proof {
        let hello = seq![72u8, 101u8, 108u8, 108u8, 111u8];
        assert(hello.is_utf8());
        assert(hello.len() == 5);
        assert(!is_char_boundary(hello, 6));
    }
}

// XXX(Verus): The upstream mid-codepoint panic cases, such as inserting at
// byte 1 of "ệ", should also be expressible as failed preconditions. Directly
// proving concrete non-ASCII UTF-8 byte sequences valid currently needs more
// low-level UTF-8 arithmetic than is appropriate for these API smoke tests.

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "str::string::views_and_capacity_are_callable",
        test_views_and_capacity_are_callable,
    );
    count += crate::run_test(
        "str::string::from_utf8_ok_err_and_verified",
        test_from_utf8_ok_err_and_verified,
    );
    count += crate::run_test(
        "str::string::into_bytes_roundtrip_is_callable",
        test_into_bytes_roundtrip_is_callable,
    );
    count += crate::run_test(
        "str::string::as_mut_str_exposes_current_view",
        test_as_mut_str_exposes_current_view,
    );
    count += crate::run_test(
        "str::string::push_pop_and_clear_core_cases",
        test_push_pop_and_clear_core_cases,
    );
    count += crate::run_test(
        "str::string::reserve_preserves_contents",
        test_reserve_preserves_contents,
    );
    count += crate::run_test(
        "str::string::insert_ascii_boundary",
        test_insert_ascii_boundary,
    );
    count += crate::run_test(
        "str::string::insert_str_ascii_boundary",
        test_insert_str_ascii_boundary,
    );
    count += crate::run_test(
        "str::string::remove_ascii_boundary",
        test_remove_ascii_boundary,
    );
    count += crate::run_test(
        "str::string::split_off_and_truncate_ascii_boundaries",
        test_split_off_and_truncate_ascii_boundaries,
    );
    count += crate::run_test(
        "str::string::truncate_past_end_is_noop",
        test_truncate_past_end_is_noop,
    );
    count += crate::run_test(
        "str::string::retain_with_named_predicate",
        test_retain_with_named_predicate,
    );
    count
}
