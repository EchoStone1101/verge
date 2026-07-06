//! Tests for `verge::str::String` APIs.

use vstd::prelude::*;
use vstd::assert_seqs_equal;
use vstd::utf8::*;
use verge::error::ErrorSpec;
use verge::prelude::*;
use verge::str::*;

verus! {

fn keep_not_b(c: char) -> (ret: bool)
    ensures
        ret == (c != 'b'),
{
    c != 'b'
}

fn test_as_bytes_len_and_is_empty_specs(s: &String) {
    broadcast use group_str_axioms;

    let bytes = s.as_bytes();
    let len = s.len();
    let is_empty = s.is_empty();

    assert(bytes@ =~= s@.as_bytes());
    assert(len == bytes@.len());
    assert(is_empty == (s@.len() == 0));
}

fn test_with_capacity_creates_empty_string() {
    broadcast use group_str_axioms;

    let s = String::with_capacity(16);
    let bytes = s.as_bytes();
    let is_empty = s.is_empty();
    let len = s.len();

    assert(s@ =~= Seq::<char>::empty());
    assert(is_empty);
    assert(len == 0);
    assert(bytes@ =~= Seq::<u8>::empty());
}

fn test_ascii_literal_views() {
    broadcast use group_str_axioms;
    proof { reveal_strlit("abc"); }

    let s = String::from_str("abc");
    let bytes = s.as_bytes();
    let is_empty = s.is_empty();
    let len = s.len();

    assert(s@ =~= seq!['a', 'b', 'c']);
    assert(bytes@ =~= seq![97u8, 98u8, 99u8]);
    assert(len == 3);
    assert(!is_empty);
}

fn test_from_utf8_generic_post(vec: Vec<u8>) {
    broadcast use group_str_axioms;

    let ghost bytes = vec@;
    let ret = String::from_utf8(vec);

    match ret {
        Ok(s) => {
            assert(bytes.is_utf8());
            assert(s@ =~= bytes.as_str());
        }
        Err(e) => {
            assert(!bytes.is_utf8());
            assert(e.is_str_utf8_error());
        }
    }
}

fn test_from_utf8_ok_and_err_examples() {
    broadcast use group_str_axioms;

    let good = vec![65u8, 66u8, 67u8];
    assert(good@.is_utf8());
    let ok = String::from_utf8(good);
    match ok {
        Ok(s) => {
            assert(s@ =~= seq!['A', 'B', 'C']);
        }
        Err(_) => {
            assert(false);
        }
    }

    let bad = vec![0xffu8];
    assert(!bad@.is_utf8());
    let err = String::from_utf8(bad);
    match err {
        Ok(_) => {
            assert(false);
        }
        Err(e) => {
            assert(e.is_str_utf8_error());
        }
    }
}

fn test_from_utf8_verified_generic(vec: Vec<u8>)
    requires
        vec@.is_utf8(),
{
    broadcast use group_str_axioms;

    let ghost bytes = vec@;
    let s = String::from_utf8_verified(vec);

    assert(s@ =~= bytes.as_str());
}

fn test_from_utf8_verified_example() {
    broadcast use group_str_axioms;

    let bytes = vec![97u8, 98u8, 99u8];
    assert(bytes@.is_utf8());
    let s = String::from_utf8_verified(bytes);

    assert(s@ =~= seq!['a', 'b', 'c']);
}

fn test_into_bytes_generic(s: String) {
    broadcast use group_str_axioms;

    let ghost before = s@;
    let bytes = s.into_bytes();

    assert(bytes@ =~= before.as_bytes());
}

fn test_into_bytes_example() {
    broadcast use group_str_axioms;
    proof { reveal_strlit("abc"); }

    let s = String::from_str("abc");
    let bytes = s.into_bytes();

    assert(bytes@ =~= seq![97u8, 98u8, 99u8]);
}

fn test_as_mut_str_exposes_current_view(s: &mut String) {
    broadcast use group_str_axioms;

    let ghost before = s@;
    {
        let r = s.as_mut_str();
        assert(r@ =~= before);
    }
    assert(s@ =~= before);
}

fn test_clear_generic(s: &mut String) {
    broadcast use group_str_axioms;

    s.clear();

    let is_empty = s.is_empty();
    assert(s@ =~= Seq::<char>::empty());
    assert(is_empty);
}

fn test_push_and_push_str_generic(s: &mut String, suffix: &str, ch: char) {
    broadcast use group_str_axioms;

    let ghost before_push = s@;
    s.push(ch);
    assert(s@ =~= before_push.push(ch));

    let ghost before_suffix = s@;
    s.push_str(suffix);
    assert(s@ =~= before_suffix + suffix@);
}

fn test_push_pop_and_clear_example() {
    broadcast use group_str_axioms;
    proof { reveal_strlit("bc"); }

    let mut s = String::with_capacity(4);
    s.push('a');
    assert(s@ =~= seq!['a']);

    s.push_str("bc");
    assert(s@ =~= seq!['a', 'b', 'c']);

    let c = s.pop();
    assert(c == Some('c'));
    assert(s@ =~= seq!['a', 'b']);

    s.clear();
    let is_empty = s.is_empty();
    assert(s@ =~= Seq::<char>::empty());
    assert(is_empty);

    let none = s.pop();
    assert(none.is_none());
    assert(s@ =~= Seq::<char>::empty());
}

fn test_pop_generic(s: &mut String) {
    broadcast use group_str_axioms;

    let ghost before = s@;
    let ch = s.pop();

    proof {
        if before.len() == 0 {
            assert(s@ =~= before);
            assert(ch.is_none());
        } else {
            assert(s@ =~= before.drop_last());
            assert(ch == Some(before.last()));
        }
    }
}

fn test_reserve_preserves_view(s: &mut String, amt: usize) {
    broadcast use group_str_axioms;

    let ghost before = s@;
    s.reserve(amt);
    assert(s@ =~= before);

    s.reserve_exact(amt);
    assert(s@ =~= before);
}

fn test_reserve_examples() {
    broadcast use group_str_axioms;
    proof { reveal_strlit("cap"); }

    let mut s = String::from_str("cap");
    s.reserve(8);
    assert(s@ =~= seq!['c', 'a', 'p']);
    s.reserve_exact(4);
    assert(s@ =~= seq!['c', 'a', 'p']);
}

fn test_insert_generic_byte_post(s: &mut String, idx: usize, ch: char)
    requires
        is_char_boundary(old(s)@.as_bytes(), idx as int),
{
    broadcast use group_str_axioms;

    let ghost before = s@;
    s.insert(idx, ch);

    assert(s@.as_bytes() =~= before.as_bytes().take(idx as int) + seq![ch].as_bytes() + before.as_bytes().skip(idx as int));
}

fn test_insert_str_generic_byte_post(s: &mut String, idx: usize, inserted: &str)
    requires
        is_char_boundary(old(s)@.as_bytes(), idx as int),
{
    broadcast use group_str_axioms;

    let ghost before = s@;
    s.insert_str(idx, inserted);

    assert(s@.as_bytes() =~= before.as_bytes().take(idx as int) + inserted@.as_bytes() + before.as_bytes().skip(idx as int));
}

fn test_insert_example() {
    broadcast use group_str_axioms;

    let mut s = String::with_capacity(1);
    s.insert(0, 'a');
    assert(s@.as_bytes() =~= seq![97u8]);
}

fn test_insert_str_example() {
    broadcast use group_str_axioms;
    proof { reveal_strlit("bc"); }

    let mut t = String::with_capacity(2);
    t.insert_str(0, "bc");
    assert(t@.as_bytes() =~= seq![98u8, 99u8]);
}

fn test_remove_generic_byte_post(s: &mut String, idx: usize) -> (ret: char)
    requires
        is_char_boundary(old(s)@.as_bytes(), idx as int),
        idx < old(s)@.as_bytes().len(),
    ensures
        ret as u32 == decode_first_scalar(old(s)@.as_bytes().skip(idx as int)),
{
    broadcast use group_str_axioms;

    let ghost before = s@;
    let removed = s.remove(idx);

    assert(removed as u32 == decode_first_scalar(before.as_bytes().skip(idx as int)));
    assert(s@.as_bytes() =~= before.as_bytes().take(idx as int) + pop_first_scalar(before.as_bytes().skip(idx as int)));
    removed
}

fn test_remove_example() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("abcd");
    }

    let mut s = String::from_str("abcd");
    let removed = s.remove(1);

    assert(removed as u32 == decode_first_scalar(seq![98u8, 99u8, 100u8]));
    assert(s@.as_bytes() =~= seq![97u8, 99u8, 100u8]);
}

fn test_retain_with_named_predicate() {
    broadcast use group_str_axioms;
    proof { reveal_strlit("abc"); }

    let mut s = String::from_str("abc");
    s.retain(keep_not_b);

    assert(s@ =~= "abc"@.filter(|c: char| call_ensures(keep_not_b, (c,), true)));
}

fn test_retain_with_annotated_closure() {
    broadcast use group_str_axioms;
    proof { reveal_strlit("abc"); }

    let mut s = String::from_str("abc");
    let mut keep_not_b_closure = |c: char| -> (ret: bool)
        requires
            true,
        ensures
            ret == (c != 'b'),
    {
        c != 'b'
    };
    let keep_a = keep_not_b_closure('a');
    let keep_b = keep_not_b_closure('b');
    let keep_c = keep_not_b_closure('c');
    assert(keep_a);
    assert(!keep_b);
    assert(keep_c);
    s.retain(keep_not_b_closure);

    proof {
        let pred = |c: char| call_ensures(keep_not_b_closure, (c,), true);
        reveal_with_fuel(Seq::<_>::filter, 4);
        assert(s@ =~= "abc"@.filter(pred));
        assert(pred('a'));
        assert(!pred('b'));
        assert(pred('c'));
        assert_seqs_equal!(s@ == seq!['a', 'c']);
    }
}

fn test_split_off_generic_byte_post(s: &mut String, at: usize) -> (rem: String)
    requires
        is_char_boundary(old(s)@.as_bytes(), at as int),
    ensures
        final(s)@.as_bytes() =~= old(s)@.as_bytes().take(at as int),
        rem@.as_bytes() =~= old(s)@.as_bytes().skip(at as int),
{
    broadcast use group_str_axioms;

    let ghost before = s@;
    let rem = s.split_off(at);

    assert(s@.as_bytes() =~= before.as_bytes().take(at as int));
    assert(rem@.as_bytes() =~= before.as_bytes().skip(at as int));
    rem
}

fn test_split_off_example() {
    broadcast use group_str_axioms;

    let mut s = String::with_capacity(4);
    let tail = s.split_off(0);

    assert(s@.as_bytes() =~= Seq::<u8>::empty());
    assert(tail@.as_bytes() =~= Seq::<u8>::empty());
}

fn test_truncate_generic_byte_post(s: &mut String, new_len: usize)
    requires
        is_char_boundary(old(s)@.as_bytes(), new_len as int),
{
    broadcast use group_str_axioms;

    let ghost before = s@;
    s.truncate(new_len);

    assert(s@.as_bytes() =~= before.as_bytes().take(new_len as int));
}

fn test_truncate_example() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("abcd");
    }

    let mut s = String::from_str("abcd");
    s.truncate(2);
    assert(s@.as_bytes() =~= seq![97u8, 98u8]);

    s.truncate(0);
    assert(s@.as_bytes() =~= Seq::<u8>::empty());
}

// `String::retain` direct closure examples need an explicit executable closure
// postcondition so callers can connect `call_ensures(f, (c,), true)` to the
// intended predicate. See `test_retain_with_annotated_closure` above.

} // verus!
