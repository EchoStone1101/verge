//! Tests for core string APIs.

use vstd::prelude::*;
use vstd::assert_by_contradiction;
use verge::prelude::*;
use verge::str::*;

mod chars;
mod fmt;
mod iter;
mod parse;
mod pattern;
mod string;

verus! {

/// Fresh downstream sanity test for empty-string construction.
/// It is not a direct Rust core/std migration; it checks the basic UTF-8 invariants of `String::new`.
fn test_empty() {
    broadcast use group_str_axioms;
    let s = String::new();
    assert(s@.as_bytes().is_utf8());
    assert(Seq::<u8>::empty().is_utf8());
}

/// Fresh downstream smoke test for `String::from_str` and `insert_str`.
/// It is not a direct Rust core/std migration; it checks the exact literal-building path used here.
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

/// Fresh downstream mutation test for truncation on a long ASCII string.
/// It is not a direct Rust core/std migration; it checks the exec API and the required `truncate` precondition.
fn test_string_truncate(s: &mut String)
    requires
        old(s).is_ascii(),
        old(s)@.len() > 1024,
{
    broadcast use group_str_axioms;
    s.truncate(512);
}

/// Fresh downstream UTF-8 preservation smoke test for insertion and append operations.
/// It is not a direct Rust core/std migration; it checks exact composed UTF-8 views after mutation.
fn test_utf8() {
    broadcast use group_str_axioms;

    proof {
        reveal_strlit("abc");
        reveal_strlit("头");
        reveal_strlit("尾");
    }

    let mut s = String::from_str("abc");
    let ghost before = s@;
    s.insert_str(0, "头");
    s.push_str("尾");
    assert(s@ == "头"@ + before + "尾"@);

    let ghost hlen = "头"@.as_bytes().len();
    let ghost tlen = "尾"@.as_bytes().len();
    let ghost len = s@.as_bytes().len();
    assert(s@.as_bytes().subrange(hlen as int, (len - tlen) as int) == before.as_bytes());
}

/// Migrated from Rust core/std ASCII trim examples and core ASCII whitespace coverage.
/// Port status: partial; full upstream semantics were attempted, with unsupported exact cases deferred via `ISSUE TODO(Verge):` notes below.
fn test_trim_ascii() {
    broadcast use group_str_axioms;

    proof {
        reveal_strlit("");
        reveal_strlit("  ");
        reveal_strlit("  abc  ");
        reveal_strlit("  abc");
        reveal_strlit("abc  ");
        reveal_strlit("abc");
    }

    let empty = "";
    let spaces = "  ";
    let empty_trim_start = empty.trim_ascii_start();
    let empty_trim_end = empty.trim_ascii_end();
    let spaces_trim_start = spaces.trim_ascii_start();
    let spaces_trim_end = spaces.trim_ascii_end();

    test!(!'\u{000b}'.is_ascii_whitespace());
    test!(empty_trim_start == empty, {
        proof {
            assert(empty_trim_start@ =~= empty@);
            reveal_with_fuel(verge::cmp::lexico_eq, 4);
        }
    });
    test!(empty_trim_end == empty, {
        proof {
            assert(empty_trim_end@ =~= empty@);
            reveal_with_fuel(verge::cmp::lexico_eq, 4);
        }
    });
    test!(spaces_trim_start == empty, {
        proof {
            assert(spaces_trim_start@ =~= empty@);
            reveal_with_fuel(verge::cmp::lexico_eq, 4);
        }
    });
    test!(spaces_trim_end == empty, {
        proof {
            assert(spaces_trim_end@ =~= empty@);
            reveal_with_fuel(verge::cmp::lexico_eq, 4);
        }
    });

    let s = "  abc  ";
    let x = "abc  ";
    let y = "  abc";
    let z = "abc";
    let trim_start = s.trim_ascii_start();
    let trim_end = s.trim_ascii_end();
    test!(trim_start == x, {
        proof {
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
            reveal_with_fuel(verge::cmp::lexico_eq, 8);
        }
    });
    test!(trim_end == y, {
        proof {
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
            reveal_with_fuel(verge::cmp::lexico_eq, 8);
        }
    });
    let s1 = s.trim_ascii_start().trim_ascii_end();
    let s2 = s.trim_ascii_end().trim_ascii_start();
    let s3 = s.trim_ascii();
    test!(s1 == z, {
        proof {
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
            reveal_with_fuel(verge::cmp::lexico_eq, 8);
        }
    });
    test!(s2 == z, {
        proof {
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
            reveal_with_fuel(verge::cmp::lexico_eq, 8);
        }
    });
    test!(s3 == z, {
        proof {
            assert(s3@ =~= s1@);
            assert(s1@ =~= z@);
            reveal_with_fuel(verge::cmp::lexico_eq, 8);
        }
    });
    assert(s1@ =~= s3@);
    assert(s1@ =~= s2@);
    assert(s2@ =~= s3@);

}

// ISSUE TODO(Verge): Upstream `core/src/str/mod.rs` trim-ASCII examples also assert
// exact U+3000 boundary behavior:
// - `" \t \u{3000}hello world\n".trim_ascii_start() == "\u{3000}hello world\n"`
// - `"\r hello world\u{3000}\n ".trim_ascii_end() == "\r hello world\u{3000}"`
// - `"\r hello world\n ".trim_ascii() == "hello world"`
// - `"  ".trim_ascii() == ""` and `"".trim_ascii() == ""`
// These are not active because the current downstream `trim_ascii` specs expose an
// existential interior slice and suffix/prefix facts, but do not provide literal
// subrange/equality lemmas strong enough to prove these exact `&str` runtime assertions.
// fn test_trim_ascii_upstream_doc_examples_deferred() {
//     assert_eq!(" \t \u{3000}hello world\n".trim_ascii_start(), "\u{3000}hello world\n");
//     assert_eq!("\r hello world\u{3000}\n ".trim_ascii_end(), "\r hello world\u{3000}");
//     assert_eq!("\r hello world\n ".trim_ascii(), "hello world");
//     assert_eq!("  ".trim_ascii(), "");
//     assert_eq!("".trim_ascii(), "");
// }

/// Fresh downstream proof that ASCII trim is independent of endpoint order.
/// It is not a direct Rust core/std migration; it remains proof-only because it is quantified over any `&str`.
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

/// Fresh downstream smoke test for ASCII case conversion helpers.
/// It is not a direct Rust core/std migration; it checks exact upper/lowercase results on a mixed-case input.
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

/// Fresh downstream smoke test for `str::from_utf8` on valid and invalid byte slices.
/// It is not a direct Rust core/std migration; it checks the success and error branches used by the Verge wrapper.
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

/// Fresh downstream smoke test for `str::from_utf8_verified`.
/// It is not a direct Rust core/std migration; it checks the verified conversion path on a concrete ASCII buffer.
fn test_from_utf8_verified() {
    broadcast use group_str_axioms;
    let bytes = vec![97u8, 98u8, 99u8];
    assert(bytes@.is_utf8());
    let s = str::from_utf8_verified(bytes.as_slice());
    assert(s@ =~= bytes@.as_str());
}

/// Fresh downstream indexing and mutable-slice access smoke test for `str::get` / `get_mut`.
/// It is not a direct Rust core/std migration; it checks callability and the expected `Some` results on a long ASCII string.
fn test_str_get(s: &mut str)
    requires
        s@.is_ascii(),
        s@.len() > 10,
{
    broadcast use group_str_axioms;
    let s1 = s.get(0..2);
    assert(s1 is Some);
    let _ = &s[3..4];
    let s3 = s.get_mut(5..6);
    assert(s3 is Some);
}

/// Migrated from Rust core/std character-iterator and string `FromIterator` tests.
/// Port status: partial; full upstream semantics were attempted, with exact `String` collection/extension cases deferred via `ISSUE TODO(Verge):` notes below.
fn test_collect() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("");
        reveal_strlit("ประเทศไทย中");
    }

    let empty = "";
    let empty_collected = empty.chars().collect::<Box<str>>();
    let empty_string = empty_collected.into_string();
    let empty_expected = String::from(empty);
    test!(empty_string == empty_expected, {
        proof {
            assert(empty_string@ =~= empty_expected@);
            reveal_with_fuel(verge::cmp::lexico_eq, 4);
        }
    });

    let data = "ประเทศไทย中";
    let data_collected = data.chars().collect::<Box<str>>();
    let data_string = data_collected.into_string();
    let data_expected = String::from(data);
    test!(data_string == data_expected, {
        proof {
            assert(data_string@ =~= data_expected@);
            reveal_with_fuel(verge::cmp::lexico_eq, 64);
        }
    });

    let s = (&['a', 'b', 'c']).into_iter().collect::<Box<str>>();

    test!(s.len() == 3usize, {
        proof {
            assert(s@.len() == 3);
            assert(s@ =~= seq!['a', 'b', 'c']);
            assert(s@.is_ascii());
            assert(s@.as_bytes().len() == 3);
        }
    });
}

// ISSUE TODO(Verge): Upstream `alloctests/tests/str.rs::test_collect` and
// `alloctests/tests/string.rs::test_from_iterator` assert exact `String` results:
// - `let s: String = empty.chars().collect(); assert_eq!(empty, s);`
// - `let s: String = "ประเทศไทย中".chars().collect(); assert_eq!("ประเทศไทย中", s);`
// - `let a: String = s.chars().collect(); assert_eq!(s, a);`
// - `b.extend(u.chars())`, `[t, u].into_iter().collect::<String>()`, and `d.extend(vec![u])` all equal `"ศไทย中华Việt Nam"`.
// These are not active because Verge currently specifies the needed `FromIterator`
// contracts for `Box<str>`, not `String`, and there are no downstream specs for
// `String::extend` over `char` or `&str` iterators.
// fn test_collect_upstream_string_from_iterator_deferred() {
//     let empty = "";
//     let s: String = empty.chars().collect();
//     assert_eq!(empty, s);
//     let data = "ประเทศไทย中";
//     let s: String = data.chars().collect();
//     assert_eq!(data, s);
//
//     let s = "ศไทย中华Việt Nam".to_string();
//     let t = "ศไทย中华";
//     let u = "Việt Nam";
//     let a: String = s.chars().collect();
//     assert_eq!(s, a);
//     let mut b = t.to_string();
//     b.extend(u.chars());
//     assert_eq!(s, b);
//     let c: String = [t, u].into_iter().collect();
//     assert_eq!(s, c);
//     let mut d = t.to_string();
//     d.extend(vec![u]);
//     assert_eq!(s, d);
// }

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test("str::trim_ascii", test_trim_ascii);
    count += crate::run_test("str::collect", test_collect);
    count += crate::run_suite("str::chars", chars::run);
    count += crate::run_suite("str::fmt", fmt::run);
    count += crate::run_suite("str::iter", iter::run);
    count += crate::run_suite("str::parse", parse::run);
    count += crate::run_suite("str::pattern", pattern::run);
    count += crate::run_suite("str::string", string::run);
    count
}
