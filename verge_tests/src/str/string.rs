//! Tests for `std::String` APIs specified by Verge.

use vstd::prelude::*;
use vstd::assert_seqs_equal;
use vstd::utf8::*;
use verge::error::ErrorSpec;
use verge::prelude::*;
use verge::str::*;

verus! {

fn test_views_and_capacity_are_callable() {
    broadcast use group_str_axioms;

    let mut text = String::with_capacity(16);
    test!(text.is_empty());
    test!(text.len() == 0usize);
    test!(text.as_bytes().len() == 0usize);

    proof {
        reveal_strlit("abc");
    }
    text.push_str("abc");

    test!(!text.is_empty());
    test!(text.len() == 3usize);
    test!(text.as_bytes().len() == 3usize);
}

fn test_from_utf8_ok_err_and_verified() {
    broadcast use group_str_axioms;

    let good = vec![104u8, 101u8, 108u8, 108u8, 111u8];
    assert(good@.is_utf8());
    let good_result = String::from_utf8(good);
    test!(good_result.is_ok());
    match good_result {
        Ok(text) => {
            test!(text.len() == 5usize);
        }
        Err(_) => {
            test!(false);
        }
    }

    let bad = vec![0xffu8];
    assert(!bad@.is_utf8());
    let bad_result = String::from_utf8(bad);
    test!(bad_result.is_err());
    match bad_result {
        Ok(_) => {
            test!(false);
        }
        Err(error) => {
            proof {
                assert(error.is_str_utf8_error());
            }
        }
    }

    let verified_bytes = vec![97u8, 98u8, 99u8];
    assert(verified_bytes@.is_utf8());
    test!(String::from_utf8_verified(verified_bytes).len() == 3usize);
}

fn test_into_bytes_roundtrip_is_callable() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("abc");
    }

    let mut text = String::with_capacity(4);
    text.push_str("abc");
    let bytes = text.into_bytes();

    test!(bytes.len() == 3usize);

    test!(String::from_utf8(bytes).is_ok());
}

fn test_as_mut_str_exposes_current_view() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("abc");
    }

    let mut text = String::with_capacity(4);
    text.push_str("abc");
    test!(text.as_mut_str().len() == 3usize);
    test!(text.len() == 3usize);
}

fn test_push_pop_and_clear_core_cases() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("");
        reveal_strlit("abc");
    }

    let mut text = String::with_capacity(16);
    text.push_str("");
    test!(text.len() == 0usize);

    text.push_str("abc");
    test!(text.len() == 3usize);

    text.push('b');
    text.push('¢');
    text.push('€');
    text.push('𤭢');

    test!(text.pop() == Some('𤭢'));
    test!(text.pop() == Some('€'));
    test!(text.pop() == Some('¢'));
    test!(text.pop() == Some('b'));

    text.clear();
    test!(text.is_empty());
    test!(text.pop().is_none());
}

fn test_reserve_preserves_contents() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("cap");
    }

    let mut text = String::with_capacity(3);
    text.push_str("cap");
    text.reserve(8usize);
    test!(text.len() == 3usize);

    text.reserve_exact(8usize);
    test!(text.len() == 3usize);
}

fn test_insert_ascii_boundary() {
    broadcast use group_str_axioms;

    let mut text = String::with_capacity(1);
    text.insert(0usize, 'a');
    test!(text.len() == 1usize);
}

fn test_insert_str_ascii_boundary() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("bc");
    }

    let mut text = String::with_capacity(2);
    text.insert_str(0usize, "bc");
    test!(text.len() == 2usize);
}

fn test_remove_ascii_boundary() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("abcd");
    }

    let mut text = String::from_str("abcd");
    proof {
        assert(text@ =~= "abcd"@);
        assert(text@.is_ascii());
        lemma_ascii_str_as_bytes(text@);
        assert(text@.as_bytes() =~= seq![97u8, 98u8, 99u8, 100u8]);
        assert(is_char_boundary(text@.as_bytes(), 1));
        assert(1 < text@.as_bytes().len());
    }
    let removed = text.remove(1usize);
    test!(removed == 'b');
    test!(text.len() == 3usize);
}

fn test_split_off_and_truncate_ascii_boundaries() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("ABCD");
    }

    let mut text = String::with_capacity(8);
    text.push_str("ABCD");
    test!(text.split_off(2usize).len() == 2usize);
    test!(text.len() == 2usize);

    test!(text.split_off(2usize).is_empty());
    test!(text.len() == 2usize);

    text.truncate(1usize);
    test!(text.len() == 1usize);
    text.truncate(0usize);
    test!(text.is_empty());
}

fn test_truncate_past_end_is_noop() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("12345");
    }

    let mut text = String::with_capacity(5);
    text.push_str("12345");
    text.truncate(6usize);
    test!(text.len() == 5usize);
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
    test!(keep_not_b_closure('a'));
    test!(!keep_not_b_closure('b'));
    test!(keep_not_b_closure('c'));

    text.retain(keep_not_b_closure);
    test!(text.len() == 2usize, {
        reveal_with_fuel(Seq::<_>::filter, 4);
    });

    test!(text.pop() == Some('c'));
    test!(text.pop() == Some('a'));
}

fn test_panicking_indices_are_blocked_by_preconditions() {
    broadcast use group_str_axioms;

    let empty = String::with_capacity(0);
    test!(empty.len() == 0usize);
    proof {
        assert(!is_char_boundary(empty@.as_bytes(), 1));

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
