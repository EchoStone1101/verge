//! Executable downstream-style tests for public string pattern APIs.

use vstd::prelude::*;
use verge::prelude::*;
use verge::seq::SeqAdditionalSpec;
use verge::str::*;

verus! {

/// Migrated from Rust core/std `test_starts_with`, `test_ends_with`, and `contains_weird_cases`.
/// Port status: partial; it keeps representative runtime checks rather than the full upstream boolean matrix.
fn test_contains_starts_ends_representatives() {
    broadcast use group_str_contains;
    broadcast use group_str_starts_with;
    broadcast use group_str_ends_with;

    proof {
        reveal_strlit("Mary had a little lamb");
        reveal_strlit("little");
    }

    let text = "Mary had a little lamb";

    test!(text.contains('M'));
    test!(text.contains("little"), {
        assert(text@.subrange(11, 17) =~= "little"@);
    });
    test!(text.starts_with('M'));
    test!(text.ends_with('b'));
}

/// Migrated from Rust core/std `test_find`, `test_rfind`, and `test_find_str`.
/// Port status: partial; it keeps representative success cases, but not the exact byte-offset assertions.
fn test_find_and_rfind_representatives() {
    broadcast use group_str_find;
    broadcast use group_str_rfind;

    proof {
        reveal_strlit("bananas");
        reveal_strlit("na");
    }

    let text = "bananas";

    test!(text.find('a').is_some());
    test!(text.find("na").is_some(), {
        assert(text@.subrange(2, 4) =~= "na"@);
    });
    test!(text.rfind('a').is_some());
    test!(text.rfind("na").is_some());

    // TODO(Verge): keep exact byte-offset checks such as
    // `text.find('a') == Some(1usize)` and `text.rfind("na") == Some(4usize)`
    // commented until downstream tests have concise UTF-8 byte-offset proof helpers.
}

/// Migrated from Rust core/std `test_split_once` and `test_rsplit_once`.
/// Port status: partial; it keeps presence and delimiter-splitting checks, not the exact `assert_eq!` result matrix.
fn test_split_once_and_rsplit_once_representatives() {
    broadcast use group_str_contains;
    broadcast use group_str_split_once;
    broadcast use group_str_rsplit_once;

    proof {
        reveal_strlit("cfg=alpha=beta");
    }

    let text = "cfg=alpha=beta";

    let first = text.split_once('=');
    test!(first.is_some(), {
        assert(text@[3] == '=');
    });
    match first {
        Some((head, _tail)) => {
            test!(!head.contains('='));
        }
        None => test!(false),
    }

    let last = text.rsplit_once('=');
    test!(last.is_some());
    match last {
        Some((_head, tail)) => {
            test!(!tail.contains('='));
        }
        None => test!(false),
    }
}

/// Migrated from Rust core/std `test_trim_start_matches`, `test_trim_end_matches`, `test_trim_matches`, and whitespace-trim examples.
/// Port status: partial; it keeps representative endpoint checks, not the full upstream output table.
fn test_trim_matches_representatives() {
    broadcast use group_str_starts_with;
    broadcast use group_str_ends_with;
    broadcast use group_str_trim_start_matches;
    broadcast use group_str_trim_end_matches;
    broadcast use group_str_trim_matches;

    proof {
        reveal_strlit("111foo111");
        reveal_strlit("abcabcxyzabc");
        reveal_strlit("abc");
    }

    let numeric = "111foo111";

    test!(!numeric.trim_start_matches('1').starts_with('1'));

    test!(!numeric.trim_end_matches('1').ends_with('1'));

    let trim_char = numeric.trim_matches('1');
    test!(!trim_char.starts_with('1'));
    test!(!trim_char.ends_with('1'));

    let repeated = "abcabcxyzabc";

    test!(!repeated.trim_start_matches("abc").starts_with("abc"));

    test!(!repeated.trim_end_matches("abc").ends_with("abc"));
}

/// Migrated from Rust core/std `strip_prefix` / `strip_suffix` behavior examples.
/// Port status: partial; it checks presence/absence and prefix/suffix soundness, not the exact returned slices.
fn test_strip_prefix_and_suffix_representatives() {
    broadcast use group_str_strip_prefix;
    broadcast use group_str_strip_suffix;

    proof {
        reveal_strlit("foobar");
        reveal_strlit("foo");
        reveal_strlit("bar");
    }

    let text = "foobar";

    test!(text.strip_prefix("foo").is_some());
    test!(text.strip_prefix('z').is_none());
    test!(text.strip_suffix("bar").is_some());
    test!(text.strip_suffix('z').is_none());
}

/// Fresh downstream smoke test for slice-pattern matching.
/// It is not a direct Rust core/std migration.
fn test_char_slice_pattern_representatives() {
    broadcast use group_str_contains;
    broadcast use group_str_starts_with;
    broadcast use group_str_ends_with;
    broadcast use group_str_trim_matches;

    proof {
        reveal_strlit("-+-core-+");
    }

    let marks: &[char] = &['-', '+'];
    let text = "-+-core-+";

    test!(text.contains(marks));
    test!(text.starts_with(marks));
    test!(text.ends_with(marks));

    let trimmed = text.trim_matches(marks);
    test!(!trimmed.starts_with(marks));
    test!(!trimmed.ends_with(marks));
}

/// Migrated from Rust core/std empty-pattern behavior around `find`, `rfind`, `split_once`, `rsplit_once`, `strip_prefix`, and `strip_suffix`.
/// Port status: partial; only the `is_some()` / `is_none()` outcomes are executable today, not the exact offsets and slices.
fn test_empty_pattern_corner_case() {
    broadcast use group_str_find;
    broadcast use group_str_rfind;
    broadcast use group_str_split_once;
    broadcast use group_str_rsplit_once;
    broadcast use group_str_strip_prefix;
    broadcast use group_str_strip_suffix;

    proof {
        reveal_strlit("abc");
        reveal_strlit("");
    }

    let text = "abc";

    test!(text.find("").is_some());
    test!(text.rfind("").is_some());
    test!(text.split_once("").is_some());
    test!(text.rsplit_once("").is_some());
    test!(text.strip_prefix("").is_some());
    test!(text.strip_suffix("").is_some());

    // TODO(Verge): exact empty-pattern byte offsets and returned slices, e.g.
    // `text.find("") == Some(0usize)` and `text.rsplit_once("") == Some((text, ""))`,
    // need concise downstream proof helpers before becoming executable asserts here.
}

/// Fresh downstream corner-case test for overlapping string patterns.
/// It is not a direct Rust core/std migration.
fn test_overlapping_pattern_corner_case() {
    broadcast use group_str_contains;
    broadcast use group_str_find;
    broadcast use group_str_rfind;

    proof {
        reveal_strlit("aaaa");
        reveal_strlit("aa");
    }

    let text = "aaaa";

    test!(text.contains("aa"));
    test!(text.find("aa").is_some());
    test!(text.rfind("aa").is_some());

    // TODO(Verge): exact overlapping string-pattern assertions such as
    // `text.split_once("aa") == Some(("", "aa"))` and
    // `text.trim_start_matches("aa") == ""` exceed the desired proof weight
    // for this downstream smoke suite today.
}

/// Fresh downstream composition test for `split_once` and `contains`.
/// It is not a direct Rust core/std migration.
fn test_split_contains_composition_case() {
    broadcast use group_str_contains;
    broadcast use group_str_split_once;

    proof {
        reveal_strlit("key::value");
    }

    let text = "key::value";
    let split = text.split_once(':');
    test!(split.is_some(), {
        assert(text@[3] == ':');
    });
    match split {
        Some((head, _tail)) => {
            test!(!head.contains(':'));
        }
        None => test!(false),
    }
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "str::pattern::contains_starts_ends_representatives",
        test_contains_starts_ends_representatives,
    );
    count += crate::run_test(
        "str::pattern::find_and_rfind_representatives",
        test_find_and_rfind_representatives,
    );
    count += crate::run_test(
        "str::pattern::split_once_and_rsplit_once_representatives",
        test_split_once_and_rsplit_once_representatives,
    );
    count += crate::run_test(
        "str::pattern::trim_matches_representatives",
        test_trim_matches_representatives,
    );
    count += crate::run_test(
        "str::pattern::strip_prefix_and_suffix_representatives",
        test_strip_prefix_and_suffix_representatives,
    );
    count += crate::run_test(
        "str::pattern::char_slice_pattern_representatives",
        test_char_slice_pattern_representatives,
    );
    count += crate::run_test(
        "str::pattern::empty_pattern_corner_case",
        test_empty_pattern_corner_case,
    );
    count += crate::run_test(
        "str::pattern::overlapping_pattern_corner_case",
        test_overlapping_pattern_corner_case,
    );
    count += crate::run_test(
        "str::pattern::split_contains_composition_case",
        test_split_contains_composition_case,
    );
    count
}
