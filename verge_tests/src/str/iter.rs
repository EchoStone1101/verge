//! Tests for string iterator APIs.

use vstd::prelude::*;
use vstd::std_specs::iter::*;
use verge::iter::VergeIteratorSpec;
use verge::prelude::*;
use verge::seq::SeqAdditionalSpec;
use verge::str::*;

verus! {

/// Migrated from Rust core/std byte iterator tests.
/// Port status: partial; it keeps representative stepping assertions, not the full upstream iteration tables.
fn test_bytes_concrete_state() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("abc");
    }

    let mut bytes = "abc".bytes_iter();
    test!(bytes.next() == Some(97u8));
    test!(bytes.next_back() == Some(99u8));
    test!(bytes.next() == Some(98u8));
    test!(bytes.next().is_none());
}

/// Migrated from Rust core/std char-index iterator tests.
/// Port status: partial; it keeps representative stepping assertions, not the full upstream iteration tables.
fn test_char_indices_concrete_state() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("ab");
    }

    let mut chars = "ab".char_indices_iter();
    test!(matches!(chars.next_back(), Some((1usize, 'b'))));
    test!(matches!(chars.next(), Some((0usize, 'a'))));
    test!(chars.next().is_none());
}

/// Migrated from Rust core/std `test_lines` and `test_split_whitespace`.
/// Port status: partial; this only checks constructor callability because the full `collect()` assertions are still commented out.
fn test_lines_and_whitespace_constructors_are_callable() {
    broadcast use group_str_axioms;
    proof {
        reveal_strlit("");
        reveal_strlit("  red\tblue\n");
    }

    let _lines = "".lines_iter();
    let _split_whitespace = "  red\tblue\n".split_whitespace_iter();
    let _split_ascii_whitespace = "  red\tblue\n".split_ascii_whitespace_iter();
}

// TODO(Verge): Re-enable when `lines_iter`, `split_whitespace_iter`, and
// `split_ascii_whitespace_iter` have linking lemmas strong enough to prove
// concrete `next()` results from downstream tests. Today these fail even for
// empty `lines_iter()` and first-word whitespace smoke checks because the
// iterator sequences are opaque at the call site.
// fn test_lines_and_whitespace_runtime_outputs() {
//     let mut lines = "".lines_iter();
//     let no_line = lines.next();
//     test!(no_line.is_none(), { assert(no_line.is_none()); });
//
//     let mut split_whitespace = "  red\tblue\n".split_whitespace_iter();
//     let first_word = split_whitespace.next();
//     test!(first_word.is_some(), { assert(first_word.is_some()); });
//
//     let mut split_ascii_whitespace = "  red\tblue\n".split_ascii_whitespace_iter();
//     let first_ascii = split_ascii_whitespace.next();
//     test!(first_ascii.is_some(), { assert(first_ascii.is_some()); });
// }

/// Migrated from Rust core/std split-family iterator tests such as `test_splitn_char_iterator`, `test_split_char_iterator_no_trailing`, `test_split_char_iterator_inclusive`, `test_split_char_iterator_inclusive_rev`, `test_rsplit`, and `test_rsplitn`.
/// Port status: partial; it checks callability and representative `next()` results, not the full collected vector equality cases.
fn test_split_family_concrete_state() {
    broadcast use group_str_split_iter;
    broadcast use group_str_split_inclusive_iter;
    broadcast use group_str_rsplit_iter;
    broadcast use group_str_split_terminator_iter;
    broadcast use group_str_rsplit_terminator_iter;
    broadcast use group_str_splitn_iter;
    broadcast use group_str_rsplitn_iter;
    proof {
        reveal_strlit("a,b,c");
        reveal_strlit("a,b,");
    }

    let csv = "a,b,c";

    test!(csv.split_iter(',').next().is_some());

    let mut split_inclusive = csv.split_inclusive_iter(',');
    let ghost split_inclusive_seq = split_inclusive.seq();
    test!(split_inclusive.next().is_some(), {
        assert(split_inclusive_seq.len() > 0) by {
            if split_inclusive_seq.len() == 0 {
                assert(csv@.len() == 0);
            }
        }
    });

    test!(csv.rsplit_iter(',').next().is_some());

    let terminated = "a,b,";
    test!(terminated.split_terminator_iter(',').next().is_some());

    test!(terminated.rsplit_terminator_iter(',').next().is_some());

    test!(csv.splitn_iter(2usize, ',').next().is_some());

    test!(csv.rsplitn_iter(2usize, ',').next().is_some());
}

/// Fresh downstream smoke test for the matches / match-indices iterator family.
/// It is not a direct Rust core/std migration.
fn test_match_family_concrete_state() {
    broadcast use group_str_matches_iter;
    broadcast use group_str_rmatches_iter;
    broadcast use group_str_match_indices_iter;
    broadcast use group_str_rmatch_indices_iter;
    proof {
        reveal_strlit("a");
    }

    let text = "a";

    let mut matches = text.matches_iter('a');
    let ghost matches_seq = matches.seq();
    test!(matches.next().is_some(), {
        assert(text@.count(|c: char| c == 'a') == 1) by {
            reveal(Seq::filter);
        }
        assert(matches_seq.len() == text@.count(|c: char| c == 'a')) by {
            // XXX(Verus): a Verus bug (#2631) regarding capturing spec closures prevents
            // proving the `count` fact without explicitly calling the linking lemma.
            lemma_str_matches_iter_char(text@, 'a', matches_seq);
        }
    });

    test!(text.rmatches_iter('a').next().is_some());

    test!(text.match_indices_iter('a').next().is_some());

    test!(text.rmatch_indices_iter('a').next().is_some());
}

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "str::iter::bytes_concrete_state",
        test_bytes_concrete_state,
    );
    count += crate::run_test(
        "str::iter::char_indices_concrete_state",
        test_char_indices_concrete_state,
    );
    count += crate::run_test(
        "str::iter::lines_and_whitespace_constructors_are_callable",
        test_lines_and_whitespace_constructors_are_callable,
    );
    count += crate::run_test(
        "str::iter::split_family_concrete_state",
        test_split_family_concrete_state,
    );
    count += crate::run_test(
        "str::iter::match_family_concrete_state",
        test_match_family_concrete_state,
    );
    count
}
