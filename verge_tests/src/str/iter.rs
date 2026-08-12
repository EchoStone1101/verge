//! Tests for string iterator APIs.

use vstd::prelude::*;
use vstd::std_specs::iter::IteratorSpec;
use verge::iter::{iter_count, iter_last, iter_nth, VergeIteratorSpec};
use verge::prelude::*;
use verge::str::*;

verus! {

/// Migrated from Rust core/std `test_bytesator`, `test_bytes_revator`,
/// `test_bytesator_nth`, `test_bytesator_count`, and `test_bytesator_last`.
/// Port status: active assertions are restored; proof derivations are deferred.
fn test_bytes_iter() {
    let text = "ศไทย中华Việt Nam";
    let expected = [
        224u8, 184u8, 168u8, 224u8, 185u8, 132u8, 224u8, 184u8, 151u8,
        224u8, 184u8, 162u8, 228u8, 184u8, 173u8, 229u8, 141u8, 142u8,
        86u8, 105u8, 225u8, 187u8, 135u8, 116u8, 32u8, 78u8, 97u8, 109u8,
    ];

    let mut bytes = text.bytes_iter();
    test!(bytes.next() == Some(expected[0]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[1]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[2]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[3]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[4]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[5]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[6]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[7]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[8]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[9]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[10]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[11]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[12]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[13]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[14]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[15]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[16]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[17]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[18]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[19]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[20]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[21]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[22]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[23]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[24]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[25]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[26]), { proof { admit(); } });
    test!(bytes.next() == Some(expected[27]), { proof { admit(); } });
    test!(bytes.next().is_none(), { proof { admit(); } });

    let mut reverse = text.bytes_iter().rev();
    test!(reverse.next() == Some(expected[27]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[26]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[25]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[24]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[23]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[22]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[21]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[20]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[19]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[18]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[17]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[16]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[15]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[14]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[13]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[12]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[11]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[10]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[9]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[8]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[7]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[6]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[5]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[4]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[3]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[2]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[1]), { proof { admit(); } });
    test!(reverse.next() == Some(expected[0]), { proof { admit(); } });
    test!(reverse.next().is_none(), { proof { admit(); } });

    let mut nth_bytes = text.bytes_iter();
    test!(iter_nth(&mut nth_bytes, 2usize) == Some(expected[2]), { proof { admit(); } });
    test!(iter_nth(&mut nth_bytes, 10usize) == Some(expected[13]), { proof { admit(); } });
    test!(iter_nth(&mut nth_bytes, 200usize).is_none(), { proof { admit(); } });

    test!(iter_count(text.bytes_iter()) == 28usize, { proof { admit(); } });
    test!(iter_last(text.bytes_iter()) == Some(expected[27]), { proof { admit(); } });
}

/// Migrated from Rust core/std char-index iterator tests.
/// Port status: active representative state assertions; proof derivations are deferred.
fn test_char_indices_concrete_state() {
    let mut chars = "ab".char_indices_iter();
    test!(chars.next_back() == Some((1usize, 'b')), { proof { admit(); } });
    test!(chars.next() == Some((0usize, 'a')), { proof { admit(); } });
    test!(chars.next().is_none(), { proof { admit(); } });
}

/// Migrated from Rust core/std `test_char_indicesator`,
/// `test_char_indices_revator`, and `test_char_indices_last`.
/// Port status: active assertions are restored; proof derivations are deferred.
fn test_char_indices_full_upstream_attempt() {
    let text = "ศไทย中华Việt Nam";
    let expected = [
        (0usize, 'ศ'),
        (3usize, 'ไ'),
        (6usize, 'ท'),
        (9usize, 'ย'),
        (12usize, '中'),
        (15usize, '华'),
        (18usize, 'V'),
        (19usize, 'i'),
        (20usize, 'ệ'),
        (23usize, 't'),
        (24usize, ' '),
        (25usize, 'N'),
        (26usize, 'a'),
        (27usize, 'm'),
    ];
    let expected_rev = [
        (27usize, 'm'),
        (26usize, 'a'),
        (25usize, 'N'),
        (24usize, ' '),
        (23usize, 't'),
        (20usize, 'ệ'),
        (19usize, 'i'),
        (18usize, 'V'),
        (15usize, '华'),
        (12usize, '中'),
        (9usize, 'ย'),
        (6usize, 'ท'),
        (3usize, 'ไ'),
        (0usize, 'ศ'),
    ];

    let mut chars = text.char_indices_iter();
    test!(chars.next() == Some(expected[0]), { proof { admit(); } });
    test!(chars.next() == Some(expected[1]), { proof { admit(); } });
    test!(chars.next() == Some(expected[2]), { proof { admit(); } });
    test!(chars.next() == Some(expected[3]), { proof { admit(); } });
    test!(chars.next() == Some(expected[4]), { proof { admit(); } });
    test!(chars.next() == Some(expected[5]), { proof { admit(); } });
    test!(chars.next() == Some(expected[6]), { proof { admit(); } });
    test!(chars.next() == Some(expected[7]), { proof { admit(); } });
    test!(chars.next() == Some(expected[8]), { proof { admit(); } });
    test!(chars.next() == Some(expected[9]), { proof { admit(); } });
    test!(chars.next() == Some(expected[10]), { proof { admit(); } });
    test!(chars.next() == Some(expected[11]), { proof { admit(); } });
    test!(chars.next() == Some(expected[12]), { proof { admit(); } });
    test!(chars.next() == Some(expected[13]), { proof { admit(); } });
    test!(chars.next().is_none(), { proof { admit(); } });

    let mut reverse = text.char_indices_iter().rev();
    test!(reverse.next() == Some(expected_rev[0]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[1]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[2]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[3]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[4]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[5]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[6]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[7]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[8]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[9]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[10]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[11]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[12]), { proof { admit(); } });
    test!(reverse.next() == Some(expected_rev[13]), { proof { admit(); } });
    test!(reverse.next().is_none(), { proof { admit(); } });

    let mut nth_chars = text.char_indices_iter();
    test!(iter_nth(&mut nth_chars, 8usize) == Some((20usize, 'ệ')), { proof { admit(); } });
    test!(iter_last(text.char_indices_iter()) == Some((27usize, 'm')), { proof { admit(); } });
}

/// Migrated from Rust core/std `test_lines` and `test_split_whitespace`.
/// Port status: constructors and representative outputs are active; full proof
/// derivations are deferred.
fn test_lines_and_whitespace_constructors_are_callable() {
    let mut lines = "".lines_iter();
    test!(lines.next().is_none(), { proof { admit(); } });

    let mut split_whitespace = "  red\tblue\n".split_whitespace_iter();
    test!(split_whitespace.next() == Some("red"), { proof { admit(); } });
    test!(split_whitespace.next() == Some("blue"), { proof { admit(); } });
    test!(split_whitespace.next().is_none(), { proof { admit(); } });

    let mut split_ascii_whitespace = "  red\tblue\n".split_ascii_whitespace_iter();
    test!(split_ascii_whitespace.next() == Some("red"), { proof { admit(); } });
    test!(split_ascii_whitespace.next() == Some("blue"), { proof { admit(); } });
    test!(split_ascii_whitespace.next().is_none(), { proof { admit(); } });
}

/// Migrated from Rust core/std `test_lines`.
/// Port status: active upstream output rows with local proof placeholders.
fn test_lines() {
    let mut lines = "".lines_iter();
    test!(lines.next().is_none(), { proof { admit(); } });

    let mut lines = "\n".lines_iter();
    test!(lines.next() == Some(""), { proof { admit(); } });
    test!(lines.next().is_none(), { proof { admit(); } });

    let mut lines = "\n2nd".lines_iter();
    test!(lines.next() == Some(""), { proof { admit(); } });
    test!(lines.next() == Some("2nd"), { proof { admit(); } });
    test!(lines.next().is_none(), { proof { admit(); } });

    let mut lines = "\r\n".lines_iter();
    test!(lines.next() == Some(""), { proof { admit(); } });
    test!(lines.next().is_none(), { proof { admit(); } });

    let mut lines = "bare\r".lines_iter();
    test!(lines.next() == Some("bare\r"), { proof { admit(); } });
    test!(lines.next().is_none(), { proof { admit(); } });

    let mut lines = "bare\rcr".lines_iter();
    test!(lines.next() == Some("bare\rcr"), { proof { admit(); } });
    test!(lines.next().is_none(), { proof { admit(); } });

    let mut lines = "Text\n\r".lines_iter();
    test!(lines.next() == Some("Text"), { proof { admit(); } });
    test!(lines.next() == Some("\r"), { proof { admit(); } });
    test!(lines.next().is_none(), { proof { admit(); } });

    let mut lines = "\nMäry häd ä little lämb\n\r\nLittle lämb\n".lines_iter();
    test!(lines.next() == Some(""), { proof { admit(); } });
    test!(lines.next() == Some("Märy häd ä little lämb"), { proof { admit(); } });
    test!(lines.next() == Some(""), { proof { admit(); } });
    test!(lines.next() == Some("Little lämb"), { proof { admit(); } });
    test!(lines.next().is_none(), { proof { admit(); } });

    let mut lines = "\r\nMäry häd ä little lämb\n\nLittle lämb".lines_iter();
    test!(lines.next() == Some(""), { proof { admit(); } });
    test!(lines.next() == Some("Märy häd ä little lämb"), { proof { admit(); } });
    test!(lines.next() == Some(""), { proof { admit(); } });
    test!(lines.next() == Some("Little lämb"), { proof { admit(); } });
    test!(lines.next().is_none(), { proof { admit(); } });
}

/// Migrated from Rust core/std `test_split_whitespace`.
/// Port status: active upstream output rows with local proof placeholders.
fn test_split_whitespace() {
    let data = "\n \tMäry   häd\tä  little lämb\nLittle lämb\n";
    let mut words = data.split_whitespace_iter();
    test!(words.next() == Some("Märy"), { proof { admit(); } });
    test!(words.next() == Some("häd"), { proof { admit(); } });
    test!(words.next() == Some("ä"), { proof { admit(); } });
    test!(words.next() == Some("little"), { proof { admit(); } });
    test!(words.next() == Some("lämb"), { proof { admit(); } });
    test!(words.next() == Some("Little"), { proof { admit(); } });
    test!(words.next() == Some("lämb"), { proof { admit(); } });
    test!(words.next().is_none(), { proof { admit(); } });
}

/// Migrated from the Rust core/std `split_ascii_whitespace` examples.
/// Port status: active ASCII and non-ASCII separator cases with local proof placeholders.
fn test_split_ascii_whitespace() {
    let data = "\n \tMäry   häd\tä  little lämb\nLittle lämb\n";
    let mut words = data.split_ascii_whitespace_iter();
    test!(words.next() == Some("Märy"), { proof { admit(); } });
    test!(words.next() == Some("häd"), { proof { admit(); } });
    test!(words.next() == Some("ä"), { proof { admit(); } });
    test!(words.next() == Some("little"), { proof { admit(); } });
    test!(words.next() == Some("lämb"), { proof { admit(); } });
    test!(words.next() == Some("Little"), { proof { admit(); } });
    test!(words.next() == Some("lämb"), { proof { admit(); } });
    test!(words.next().is_none(), { proof { admit(); } });

    let mut non_ascii_separator = "red\u{00a0}blue".split_ascii_whitespace_iter();
    test!(non_ascii_separator.next() == Some("red\u{00a0}blue"), { proof { admit(); } });
    test!(non_ascii_separator.next().is_none(), { proof { admit(); } });
}

/// Migrated from Rust core/std split-family iterator tests such as
/// `test_splitn_char_iterator`, `test_split_char_iterator_no_trailing`,
/// `test_split_char_iterator_inclusive`, `test_split_char_iterator_inclusive_rev`,
/// `test_rsplit`, and `test_rsplitn`.
/// Port status: the monomorphic `split_ch_iter` representative is active.
fn test_split_family_concrete_state() {
    let mut split = "a,b,c".split_ch_iter(',');
    test!(split.next() == Some("a"), { proof { admit(); } });
    test!(split.next() == Some("b"), { proof { admit(); } });
    test!(split.next() == Some("c"), { proof { admit(); } });
    test!(split.next().is_none(), { proof { admit(); } });
}

// ISSUE: The upstream split-family tests below require pattern-specific
// iterator constructors that are not part of the current downstream surface.
// Keep these proof goals here until the corresponding public APIs return.
//
// fn test_splitn_char_iterator() {
//     // `splitn_iter` is unavailable; retain the upstream rows:
//     // "\nMäry häd ä little lämb\nLittle lämb\n" splitn(4, ' ')
//     //   -> ["\nMäry", "häd", "ä", "little lämb\nLittle lämb\n"]
//     // the same rows with a closure pattern, and the Unicode `ä` rows.
// }
//
// fn test_split_char_iterator_no_trailing() {
//     // `split_iter` and `split_terminator_iter` are unavailable; retain the
//     // upstream newline and trailing-empty-element proof goals.
// }
//
// fn test_split_char_iterator_inclusive() {
//     // `split_inclusive_iter` is unavailable; retain forward inclusive rows
//     // for newline and stateful uppercase predicates.
// }
//
// fn test_split_char_iterator_inclusive_rev() {
//     // `split_inclusive_iter().rev()` is unavailable; retain reverse newline
//     // and stateful uppercase predicate rows.
// }
//
// fn test_rsplit() {
//     // `rsplit_iter` is unavailable; retain char, string, and closure rows.
// }
//
// fn test_rsplitn() {
//     // `rsplitn_iter` is unavailable; retain char, string, and closure rows.
// }
//
// fn test_splitator() {
//     // The upstream string-pattern `split` rows remain deferred with the
//     // expected vectors for empty, Unicode, and repeated delimiters.
// }

// ISSUE: The upstream `test_split_once` and `test_rsplit_once` cases are
// pattern operations rather than iterator APIs and are intentionally left out
// of this iterator migration until their downstream contracts are restored.

// ISSUE: The upstream match-family iterator tests are unavailable after the
// pattern iterator surface was removed. Preserve the fresh proof goals without
// compiling calls to unavailable methods.
//
// /// Fresh downstream smoke test for the matches / match-indices iterator family.
// /// It is not a direct Rust core/std migration; Port status: deferred.
// fn test_match_family_concrete_state() {
//     // `matches_iter`, `rmatches_iter`, `match_indices_iter`, and
//     // `rmatch_indices_iter` are unavailable.
//     // The intended active goals are the first matching "a" slice and its
//     // `(0, "a")` match-index result, in both directions.
// }

} // verus!

pub fn run() -> usize {
    let mut count = 0;
    count += crate::run_test(
        "str::iter::bytes_iter",
        test_bytes_iter,
    );
    count += crate::run_test(
        "str::iter::char_indices_concrete_state",
        test_char_indices_concrete_state,
    );
    count += crate::run_test(
        "str::iter::char_indices_full_upstream_attempt",
        test_char_indices_full_upstream_attempt,
    );
    count += crate::run_test(
        "str::iter::lines_and_whitespace_constructors_are_callable",
        test_lines_and_whitespace_constructors_are_callable,
    );
    count += crate::run_test(
        "str::iter::lines",
        test_lines,
    );
    count += crate::run_test(
        "str::iter::split_whitespace",
        test_split_whitespace,
    );
    count += crate::run_test(
        "str::iter::split_ascii_whitespace",
        test_split_ascii_whitespace,
    );
    count += crate::run_test(
        "str::iter::split_family_concrete_state",
        test_split_family_concrete_state,
    );
    // ISSUE: `test_match_family_concrete_state` remains commented because the
    // pattern iterator constructors are unavailable in this migration.
    count
}
