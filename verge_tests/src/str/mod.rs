//! Tests for core string APIs.

use vstd::prelude::*;
use vstd::assert_by_contradiction;
use verge::prelude::*;
use verge::str::*;

mod chars;
mod fmt;
mod iter;
mod pattern;
mod string;

verus! {

fn test_empty() {
    broadcast use group_str_axioms;
    let s = String::new();
    assert(s@.as_bytes().is_utf8());
    assert(Seq::<u8>::empty().is_utf8());
}

fn test_string_literal() -> (ret: String)
    ensures ret@ =~= "abcd"@,
{
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("abd");
        reveal_strlit("c");
        reveal_strlit("abcd");
    }

    let mut s = String::from_str("abd");
    s.insert_str(2, "c");
    s
}

fn test_string_truncate(s: &mut String)
    requires
        old(s).is_ascii(),
        old(s)@.len() > 1024,
{
    broadcast use group_str_axioms;
    s.truncate(512);
}

fn test_utf8(s: &mut String) {
    broadcast use group_str_axioms;

    s.insert_str(0, "头");
    s.insert_str(s.len(), "尾");
    assert(s@ == "头"@ + old(s)@ + "尾"@);

    let ghost hlen = "头"@.as_bytes().len();
    let ghost tlen = "尾"@.as_bytes().len();
    let ghost len = s@.as_bytes().len();
    assert(s@.as_bytes().subrange(hlen as int, (len - tlen) as int) == old(s)@.as_bytes());
}

fn test_trim_ascii() {
    broadcast use group_str_axioms;

    proof {
        reveal_strlit("  abc  ");
        reveal_strlit("  abc");
        reveal_strlit("abc  ");
        reveal_strlit("abc");
    }

    let s = "  abc  ";
    let x = "abc  ";
    let y = "  abc";
    let z = "abc";
    let trim_start = s.trim_ascii_start();
    let trim_end = s.trim_ascii_end();
    assert(trim_start@ =~= x@) by {
        let ghost start = s@.len() - trim_start@.len();
        assert(trim_start@ =~= s@.skip(start));
        assert_by_contradiction!(start <= 2, {
            assert(start > 2);
            // assert(s@[2] == 'a');
            assert(s@[2].is_ascii_whitespace());
        });
        assert_by_contradiction!(start >= 2, {
            assert(start < 2);
            assert(s@[start].is_ascii_whitespace());
        });
        assert(start == 2);
        assert(trim_start@ =~= s@.skip(2));
        assert(x@ =~= s@.skip(2));
    }
    assert(trim_end@ =~= y@) by {
        let ghost end = trim_end@.len();
        assert_by_contradiction!(end >= 5, {
            // assert(s@[4] == 'c');
            assert(s@[4].is_ascii_whitespace());
        });
        assert_by_contradiction!(end <= 5, {
            assert(end > 5);
            assert(s@[end as int].is_ascii_whitespace());
        });
        assert(end == 5);
        assert(trim_end@ =~= s@.take(5));
        assert(y@ =~= s@.take(5));
    }
    let s1 = s.trim_ascii_start().trim_ascii_end();
    let s2 = s.trim_ascii_end().trim_ascii_start();
    let s3 = s.trim_ascii();
    assert(s1@ =~= z@) by {
        let ghost end = s1@.len();
        assert(s1@ =~= trim_start@.take(end as int));
        assert_by_contradiction!(end >= 3, {
            assert(end < 3);
            assert(trim_start@[2].is_ascii_whitespace());
        });
        assert_by_contradiction!(end <= 3, {
            assert(end > 3);
            assert(s1@[end - 1] == trim_start@[end - 1]);
            assert(trim_start@[end - 1].is_ascii_whitespace());
        });
        assert(end == 3);
        assert(s1@ =~= trim_start@.take(3));
        assert(z@ =~= trim_start@.take(3));
    }
    assert(s2@ =~= z@) by {
        let ghost start = trim_end@.len() - s2@.len();
        assert(s2@ =~= trim_end@.skip(start));
        assert_by_contradiction!(start <= 2, {
            assert(start > 2);
            assert(trim_end@[2].is_ascii_whitespace());
        });
        assert_by_contradiction!(start >= 2, {
            assert(start < 2);
            assert(trim_end@[start].is_ascii_whitespace());
        });
        assert(start == 2);
        assert(s2@ =~= trim_end@.skip(2));
        assert(z@ =~= trim_end@.skip(2));
    }
    assert(s1@ =~= s3@);
    assert(s1@ =~= s2@);
    assert(s2@ =~= s3@);
}

fn test_trim_ascii_order_independent(s: &str) {
    broadcast use group_str_axioms;

    let trim_start = s.trim_ascii_start();
    let trim_end = s.trim_ascii_end();
    let s1 = trim_start.trim_ascii_end();
    let s2 = trim_end.trim_ascii_start();
    let s3 = s.trim_ascii();
    assert(s1@ =~= s3@);

    let ghost start1 = s@.len() - trim_start@.len();
    let ghost end1 = start1 + s1@.len();
    let ghost start2 = trim_end@.len() - s2@.len();
    let ghost end2 = trim_end@.len() as int;

    assert(s1@ =~= s@.subrange(start1, end1));
    assert(s2@ =~= s@.subrange(start2, end2));


    proof {
        if s1@.len() == 0 {
            assert(forall |i: int| 0 <= i < s@.len() ==> #[trigger] s@[i].is_ascii_whitespace());
            assert(s2@.len() == 0);
        } else {
            assert(exists |i: int| 0 <= i < s@.len() && #[trigger] s@[i].is_ascii_whitespace() == false);
            assert(s2@.len() > 0);

            assert_by_contradiction!(start1 == start2, {
                if start1 < start2 {
                    //   s        = [ ... | s[start1] ...  | s[start2] ... ]
                    //                    ^                ^
                    //                  start1           start2
                    //   s1       =       [ s[start1] ... ]
                    //   trim_end = [ s[0] ... ... ... ... ... ... ... ... s[end2 - 1] ]
                    //   s2       =                        [ s[start2] ... s[end2 - 1] ]
                    //
                    // Since start1 < start2, the char at `s[start1]` is still in the
                    // prefix removed by `trim_end.trim_ascii_start()`, so it must be
                    // ASCII whitespace. But the same char is also the first char of
                    // `s1`, and a nonempty `trim_ascii_start()` result cannot start
                    // with ASCII whitespace. Contradiction.
                    assert(trim_end@[start1] == s@[start1]);
                    assert(trim_end@[start1].is_ascii_whitespace()) by { assert(start1 < start2); };
                    assert(s1@.first() == s@[start1]);
                    assert(!s1@.first().is_ascii_whitespace());
                } else {
                    assert(s@[start2].is_ascii_whitespace()) by { assert(start2 < start1); };
                    assert(s2@.first() == s@[start2]);
                    assert(!s2@.first().is_ascii_whitespace());
                }
            });

            assert_by_contradiction!(end1 == end2, {
                if end1 < end2 {
                    let j = end2 - 1 - start1;
                    assert(trim_start@[j] == s@[end2 - 1]);
                    assert(trim_start@[j].is_ascii_whitespace()) by { assert(end1 < end2); };
                    assert(s2@.last() == s@[end2 - 1]);
                    assert(!s2@.last().is_ascii_whitespace());
                } else {
                    assert(s@[end1 - 1].is_ascii_whitespace()) by { assert(end1 > end2); };
                    assert(s1@.last() == s@[end1 - 1]);
                    assert(!s1@.last().is_ascii_whitespace());
                }
            });
        }
    }
    assert(s1@ =~= s2@);
}

fn test_case_sensitive() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("ABC");
        reveal_strlit("AbC");
        reveal_strlit("abc");
    }

    let upper = "ABC";
    let lower = "abc";
    let s = "AbC";
    let mut s1 = s.to_ascii_uppercase();
    let mut s2 = s.to_ascii_lowercase();
    assert(s1@ == upper@);
    assert(s2@ == lower@);
}

fn test_from_utf8() {
    broadcast use group_str_axioms;
    let good = vec![65u8, 66u8, 67u8];
    let bad = vec![0xffu8];
    assert(good@.is_utf8());

    let ok = str::from_utf8(good.as_slice());
    let err = str::from_utf8(bad.as_slice());

    assert(ok.is_ok());
    match err {
        Ok(_) => assert(bad@.is_utf8()),
        Err(_) => assert(!bad@.is_utf8()),
    }
}

fn test_from_utf8_verified() {
    broadcast use group_str_axioms;
    let bytes = vec![97u8, 98u8, 99u8];
    assert(bytes@.is_utf8());
    let s = str::from_utf8_verified(bytes.as_slice());
    assert(s@ =~= bytes@.as_str());
}

fn test_str_get(s: &mut str)
    requires
        s@.is_ascii(),
        s@.len() > 10,
{
    broadcast use group_str_axioms;
    let s1 = s.get(0..2);
    assert(s1 is Some);
    let s2 = &s[3..4];
    let s3 = s.get_mut(5..6);
    assert(s3 is Some);
}

fn test_collect() {
    broadcast use group_str_axioms;
    let array = &['a', 'b', 'c'];
    let s = array.into_iter().collect::<Box<str>>();

    assert(s@.len() == 3);
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_suite("str::chars", chars::run);
    count
}
