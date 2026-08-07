//! Tests for string iterator APIs.

use vstd::prelude::*;
use vstd::assert_seqs_equal;
use vstd::std_specs::iter::*;
use vstd::std_specs::range::*;
use vstd::utf8::*;
use verge::iter::{iter_count, iter_last, iter_nth, VergeIteratorSpec};
use verge::prelude::*;
use verge::seq::SeqAdditionalSpec;
use verge::str::*;

verus! {

proof fn lemma_encode_utf8_flatten(chars: Seq<char>)
    ensures
        encode_utf8(chars) == chars.map_values(|ch: char| encode_scalar(ch as u32)).flatten(),
    decreases
        chars.len(),
{
    reveal_with_fuel(encode_utf8, 1);
    reveal_with_fuel(Seq::<_>::flatten, 1);
    if chars.len() == 0 {
        assert(chars.map_values(|ch: char| encode_scalar(ch as u32)).len() == 0);
        assert(chars.map_values(|ch: char| encode_scalar(ch as u32)).flatten() == seq![]);
    } else {
        let encoded = chars.map_values(|ch: char| encode_scalar(ch as u32));
        let tail = chars.drop_first();
        let encoded_tail = tail.map_values(|ch: char| encode_scalar(ch as u32));
        lemma_encode_utf8_flatten(tail);
        assert(encoded[0] == encode_scalar(chars[0] as u32));
        assert_seqs_equal!(encoded.drop_first() == encoded_tail);
        assert(encoded.flatten() == encoded[0] + encoded.drop_first().flatten());
        assert(encoded.drop_first().flatten() == encode_utf8(tail));
        assert(encode_utf8(chars) == encode_scalar(chars[0] as u32) + encode_utf8(tail));
    }
}

/// Migrated from Rust core/std `test_bytesator`, `test_bytes_revator`,
/// `test_bytesator_nth`, `test_bytesator_count`, and `test_bytesator_last`.
/// Port status: done.
fn test_bytes_iter() {
    broadcast use group_str_axioms;
    broadcast use group_iter_axioms;
    broadcast use vstd::array::group_array_axioms;
    broadcast use vstd::array::group_array_axioms;
    broadcast use group_range_axioms;
    broadcast use vstd::array::group_array_axioms;
    let text = "ศไทย中华Việt Nam";
    let expected = [
        224u8, 184u8, 168u8, 224u8, 185u8, 132u8, 224u8, 184u8, 151u8,
        224u8, 184u8, 162u8, 228u8, 184u8, 173u8, 229u8, 141u8, 142u8,
        86u8, 105u8, 225u8, 187u8, 135u8, 116u8, 32u8, 78u8, 97u8, 109u8,
    ];
    let ghost expected_seq = expected@;
    let ghost expected_rev = expected_seq.reverse();
    proof {
        reveal_strlit("ศไทย中华Việt Nam");
        let literal = text@;

        assert(encode_scalar(0xe28u32) == seq![224u8, 184u8, 168u8]) by (bit_vector);
        assert(encode_scalar(0xe44u32) == seq![224u8, 185u8, 132u8]) by (bit_vector);
        assert(encode_scalar(0xe17u32) == seq![224u8, 184u8, 151u8]) by (bit_vector);
        assert(encode_scalar(0xe22u32) == seq![224u8, 184u8, 162u8]) by (bit_vector);
        assert(encode_scalar(0x4e2du32) == seq![228u8, 184u8, 173u8]) by (bit_vector);
        assert(encode_scalar(0x534eu32) == seq![229u8, 141u8, 142u8]) by (bit_vector);
        assert(encode_scalar(0x1ec7u32) == seq![225u8, 187u8, 135u8]) by (bit_vector);
        assert(encode_scalar(0x56u32) == seq![86u8]) by (bit_vector);
        assert(encode_scalar(0x69u32) == seq![105u8]) by (bit_vector);
        assert(encode_scalar(0x74u32) == seq![116u8]) by (bit_vector);
        assert(encode_scalar(0x20u32) == seq![32u8]) by (bit_vector);
        assert(encode_scalar(0x4eu32) == seq![78u8]) by (bit_vector);
        assert(encode_scalar(0x61u32) == seq![97u8]) by (bit_vector);
        assert(encode_scalar(0x6du32) == seq![109u8]) by (bit_vector);

        lemma_encode_utf8_flatten(literal);
        reveal_with_fuel(Seq::<_>::flatten, 15);
        assert(literal.as_bytes() == expected@);
        assert(expected_rev == expected@.reverse());
    }

    let mut i = 0usize;
    for b in iter: text.bytes_iter()
        invariant
            iter.seq() == expected@,
            i == iter.index(),
    {
        test!(b == expected[i], {
            assert(i < expected@.len());
            assert(b == iter.seq()[i as int]);
        });
        i += 1;
    }

    let mut ri = 0usize;
    for b in rev_iter: text.bytes_iter().rev()
        invariant
            rev_iter.seq() == expected_rev,
            expected_rev == expected@.reverse(),
            expected_rev.len() == expected@.len(),
            ri == rev_iter.index(),
    {
        test!(b == expected[expected.len() - 1 - ri], {
            assert(ri < expected@.len());
            assert(b == rev_iter.seq()[ri as int]);
            assert(rev_iter.seq()[ri as int] == expected_rev[ri as int]);
        });
        ri += 1;
    }

    let mut nth_bytes = text.bytes_iter();
    test!(iter_nth(&mut nth_bytes, 2usize) == Some(168u8));
    test!(iter_nth(&mut nth_bytes, 10usize) == Some(184u8));
    test!(iter_nth(&mut nth_bytes, 200usize).is_none());

    test!(iter_count(text.bytes_iter()) == 28usize);
    test!(iter_last(text.bytes_iter()) == Some(109u8));
}

/// Migrated from Rust core/std char-index iterator tests.
/// Port status: partial.
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

/// Migrated from Rust core/std `test_char_indicesator`, `test_char_indices_revator`,
/// and `test_char_indices_last`.
/// Port status: done.
fn test_char_indices_full_upstream_attempt() {
    broadcast use group_str_axioms;
    broadcast use group_iter_axioms;
    proof {
        reveal_strlit("ศไทย中华Việt Nam");
    }

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
    proof {
        let literal = text@;

        assert_seqs_equal!(expected_rev@ == expected@.reverse());

        assert(encode_scalar(0xe28u32) == seq![224u8, 184u8, 168u8]) by (bit_vector);
        assert(encode_scalar(0xe44u32) == seq![224u8, 185u8, 132u8]) by (bit_vector);
        assert(encode_scalar(0xe17u32) == seq![224u8, 184u8, 151u8]) by (bit_vector);
        assert(encode_scalar(0xe22u32) == seq![224u8, 184u8, 162u8]) by (bit_vector);
        assert(encode_scalar(0x4e2du32) == seq![228u8, 184u8, 173u8]) by (bit_vector);
        assert(encode_scalar(0x534eu32) == seq![229u8, 141u8, 142u8]) by (bit_vector);
        assert(encode_scalar(0x1ec7u32) == seq![225u8, 187u8, 135u8]) by (bit_vector);
        assert(encode_scalar(0x56u32) == seq![86u8]) by (bit_vector);
        assert(encode_scalar(0x69u32) == seq![105u8]) by (bit_vector);
        assert(encode_scalar(0x74u32) == seq![116u8]) by (bit_vector);
        assert(encode_scalar(0x20u32) == seq![32u8]) by (bit_vector);
        assert(encode_scalar(0x4eu32) == seq![78u8]) by (bit_vector);
        assert(encode_scalar(0x61u32) == seq![97u8]) by (bit_vector);
        assert(encode_scalar(0x6du32) == seq![109u8]) by (bit_vector);

        assert(literal.len() == expected@.len());
        assert_seqs_equal!(literal.map(|i: int, c: char| (literal.take(i).as_bytes().len() as usize, c)) == expected@, i => {
            lemma_encode_utf8_flatten(literal.take(i));
            reveal_with_fuel(Seq::<_>::flatten, 15);
            assert(literal[i] == expected@[i].1);
            assert(literal.take(i).as_bytes().len() == expected@[i].0);
        });
    }

    let mut chars = text.char_indices_iter();
    let mut i = 0usize;
    for pair in iter: chars
        invariant
            iter.seq() == expected@,
            i == iter.index(),
    {
        let expected_pair = {
            proof {
                assert(i < iter.seq().len());
                assert(i < expected@.len());
            }
            expected[i]
        };
        test!(pair.0 == expected_pair.0 && pair.1 == expected_pair.1, {
            assert(i < iter.seq().len());
            assert(i < expected@.len());
            assert(pair == iter.seq()[i as int]);
            assert(pair == expected@[i as int]);
            assert(expected_pair == expected[i as int]);
            assert(pair == expected_pair);
            assert(pair.0 == expected_pair.0);
            assert(pair.1 == expected_pair.1);
        });
        i += 1;
    }

    let mut rev_chars = text.char_indices_iter().rev();
    let mut ri = 0usize;
    for pair in rev_iter: rev_chars
        invariant
            rev_iter.seq() == expected_rev@,
            expected_rev@ == expected@.reverse(),
            expected_rev@.len() == expected@.len(),
            ri == rev_iter.index(),
    {
        let expected_pair = {
            proof {
                assert(ri < rev_iter.seq().len());
                assert(ri < expected_rev@.len());
            }
            expected_rev[ri]
        };
        test!(pair.0 == expected_pair.0 && pair.1 == expected_pair.1, {
            assert(ri < rev_iter.seq().len());
            assert(ri < expected_rev@.len());
            assert(pair == rev_iter.seq()[ri as int]);
            assert(pair == expected_rev@[ri as int]);
            assert(expected_pair == expected_rev[ri as int]);
            assert(pair == expected_pair);
            assert(pair.0 == expected_pair.0);
            assert(pair.1 == expected_pair.1);
        });
        ri += 1;
    }

    let mut nth_chars = text.char_indices_iter();
    let nth_char = iter_nth(&mut nth_chars, 8usize);
    test!(matches!(nth_char, Some((20usize, 'ệ'))), {
        assert(nth_char == Some((20usize, 'ệ')));
    });

    let last_char = iter_last(text.char_indices_iter());
    test!(matches!(last_char, Some((27usize, 'm'))), {
        assert(last_char == Some((27usize, 'm')));
    });
}

/// Migrated from Rust core/std `test_lines` and `test_split_whitespace`.
/// Port status: partial; constructor callability is active, and the full upstream `collect()` attempt is marked ISSUE below.
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

// ISSUE TODO(Verge): Re-enable when `lines_iter`, `split_whitespace_iter`, and
// `split_ascii_whitespace_iter` have linking lemmas strong enough to prove
// the full upstream `collect()` assertions. Today these fail even for empty
// `lines_iter()` and first-word whitespace smoke checks because the iterator
// sequences are opaque at the call site. Upstream rows include `"" -> []`,
// `"\n" -> [""]`, CRLF normalization, and Unicode whitespace words from
// `"\n \tMäry   häd\tä  little lämb\nLittle lämb\n"`.
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
/// Port status: partial; representative first-value facts are active, and the full upstream collected-vector attempt is marked ISSUE below.
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

    let mut split = csv.split_iter(',');
    let ghost split_seq = split.seq();
    proof {
        lemma_str_split_iter_char(csv@, ',', split_seq);
        assert(split_seq.len() > 0);
    }
    let split_first = split.next();
    test!(split_first.is_some(), {
        proof {
            assert(split_first == Some(split_seq[0]));
        }
    });
    match split_first {
        Some(part) => {
            proof {
                assert(part == split_seq[0]);
                assert(!part@.contains(','));
            }
        },
        None => test!(false),
    }

    let mut split_inclusive = csv.split_inclusive_iter(',');
    let ghost split_inclusive_seq = split_inclusive.seq();
    proof {
        lemma_str_split_inclusive_iter_char(csv@, ',', split_inclusive_seq);
        assert(split_inclusive_seq.len() > 0) by {
            if split_inclusive_seq.len() == 0 {
                assert(csv@.len() == 0);
            }
        }
    }
    let split_inclusive_first = split_inclusive.next();
    test!(split_inclusive_first.is_some(), {
        proof {
            assert(split_inclusive_first == Some(split_inclusive_seq[0]));
        }
    });
    match split_inclusive_first {
        Some(part) => {
            proof {
                assert(part == split_inclusive_seq[0]);
                assert(part@.len() > 0);
                assert(!part@.drop_last().contains(','));
            }
        },
        None => test!(false),
    }

    let mut rsplit = csv.rsplit_iter(',');
    let ghost rsplit_seq = rsplit.seq();
    proof {
        lemma_str_rsplit_iter_char(csv@, ',', rsplit_seq);
        assert(rsplit_seq.len() > 0);
    }
    let rsplit_first = rsplit.next();
    test!(rsplit_first.is_some(), {
        proof {
            assert(rsplit_first == Some(rsplit_seq[0]));
        }
    });
    match rsplit_first {
        Some(part) => {
            proof {
                assert(part == rsplit_seq[0]);
                assert(!part@.contains(','));
            }
        },
        None => test!(false),
    }

    let terminated = "a,b,";
    let mut split_terminator = terminated.split_terminator_iter(',');
    let ghost split_terminator_seq = split_terminator.seq();
    proof {
        lemma_str_split_terminator_iter_char(terminated@, ',', split_terminator_seq);
        assert(split_terminator_seq.len() > 0);
    }
    let split_terminator_first = split_terminator.next();
    test!(split_terminator_first.is_some(), {
        proof {
            assert(split_terminator_first == Some(split_terminator_seq[0]));
        }
    });
    match split_terminator_first {
        Some(part) => {
            proof {
                assert(part == split_terminator_seq[0]);
                assert(!part@.contains(','));
            }
        },
        None => test!(false),
    }

    let mut rsplit_terminator = terminated.rsplit_terminator_iter(',');
    let ghost rsplit_terminator_seq = rsplit_terminator.seq();
    proof {
        lemma_str_rsplit_terminator_iter_char(terminated@, ',', rsplit_terminator_seq);
        assert(rsplit_terminator_seq.len() > 0);
    }
    let rsplit_terminator_first = rsplit_terminator.next();
    test!(rsplit_terminator_first.is_some(), {
        proof {
            assert(rsplit_terminator_first == Some(rsplit_terminator_seq[0]));
        }
    });
    match rsplit_terminator_first {
        Some(part) => {
            proof {
                assert(part == rsplit_terminator_seq[0]);
                assert(!part@.contains(','));
            }
        },
        None => test!(false),
    }

    let mut splitn = csv.splitn_iter(2usize, ',');
    let ghost splitn_seq = splitn.seq();
    proof {
        lemma_str_splitn_iter_char(csv@, 2usize, ',', splitn_seq);
        assert(splitn_seq.len() > 0);
    }
    let splitn_first = splitn.next();
    test!(splitn_first.is_some(), {
        proof {
            assert(splitn_first == Some(splitn_seq[0]));
        }
    });
    match splitn_first {
        Some(part) => {
            proof {
                assert(part == splitn_seq[0]);
                assert(!part@.contains(','));
            }
        },
        None => test!(false),
    }

    let mut rsplitn = csv.rsplitn_iter(2usize, ',');
    let ghost rsplitn_seq = rsplitn.seq();
    proof {
        lemma_str_rsplitn_iter_char(csv@, 2usize, ',', rsplitn_seq);
        assert(rsplitn_seq.len() > 0);
    }
    let rsplitn_first = rsplitn.next();
    test!(rsplitn_first.is_some(), {
        proof {
            assert(rsplitn_first == Some(rsplitn_seq[0]));
        }
    });
    match rsplitn_first {
        Some(part) => {
            proof {
                assert(part == rsplitn_seq[0]);
                assert(!part@.contains(','));
            }
        },
        None => test!(false),
    }
}

// ISSUE TODO(Verge): Full upstream split-family semantics are not active yet.
// The original Rust tests assert complete collected vectors for `splitn`,
// `split`, `split_terminator`, `split_inclusive`, reverse
// `split_inclusive`, `rsplit`, `rsplitn`, and `rsplitn` with both ASCII and
// Unicode delimiters. Exact runtime string equality for these vectors still
// needs downstream-accessible generated assume lemmas, e.g.:
// fn test_split_family_exact_runtime_values_with_assume_lemmas() {
//     broadcast use group_str_split_iter;
//     proof { reveal_strlit("a,b,c"); }
//     let csv = "a,b,c";
//     let mut split = csv.split_iter(',');
//     let ghost split_seq = split.seq();
//     proof {
//         lemma_str_split_iter_char_surjective(csv@, ',', seq!["a"@, "b"@, "c"@]);
//         lemma_str_split_iter_char_injective(
//             csv@, ',', split_seq, csv@, ',', seq!["a"@, "b"@, "c"@],
//         );
//     }
//     test!(matches!(split.next(), Some("a")));
// }

/// Fresh downstream smoke test for the matches / match-indices iterator family.
/// It is not a direct Rust core/std migration; Port status: fresh/non-migrated; partial representative coverage supported by current public lemmas.
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
    proof {
        lemma_str_matches_iter_char(text@, 'a', matches_seq);
        assert(text@.count(|c: char| c == 'a') == 1) by {
            reveal(Seq::filter);
        }
        assert(matches_seq.len() == 1);
    }
    let matches_first = matches.next();
    test!(matches_first.is_some(), {
        proof {
            assert(matches_first == Some(matches_seq[0]));
        }
    });
    match matches_first {
        Some(part) => {
            proof {
                assert(part == matches_seq[0]);
                assert(part@ == seq!['a']);
            }
        },
        None => test!(false),
    }

    let mut rmatches = text.rmatches_iter('a');
    let ghost rmatches_seq = rmatches.seq();
    proof {
        lemma_str_rmatches_iter_char(text@, 'a', rmatches_seq);
        assert(text@.count(|c: char| c == 'a') == 1) by {
            reveal(Seq::filter);
        }
        assert(rmatches_seq.len() == 1);
    }
    let rmatches_first = rmatches.next();
    test!(rmatches_first.is_some(), {
        proof {
            assert(rmatches_first == Some(rmatches_seq[0]));
        }
    });
    match rmatches_first {
        Some(part) => {
            proof {
                assert(part == rmatches_seq[0]);
                assert(part@ == seq!['a']);
            }
        },
        None => test!(false),
    }

    let mut match_indices = text.match_indices_iter('a');
    let ghost match_indices_seq = match_indices.seq();
    proof {
        lemma_str_match_indices_iter_char(text@, 'a', match_indices_seq);
        assert(text@.count(|c: char| c == 'a') == 1) by {
            reveal(Seq::filter);
        }
        assert(match_indices_seq.len() == 1);
        assert(match_indices_seq[0].0 == 0usize);
    }
    let match_indices_first = match_indices.next();
    test!(matches!(match_indices_first, Some((0usize, _))), {
        proof {
            assert(match_indices_first == Some(match_indices_seq[0]));
        }
    });
    match match_indices_first {
        Some((offset, part)) => {
            proof {
                assert(offset == 0usize);
                assert(part == match_indices_seq[0].1);
                assert(part@ == seq!['a']);
            }
        },
        None => test!(false),
    }

    let mut rmatch_indices = text.rmatch_indices_iter('a');
    let ghost rmatch_indices_seq = rmatch_indices.seq();
    proof {
        lemma_str_rmatch_indices_iter_char(text@, 'a', rmatch_indices_seq);
        assert(text@.count(|c: char| c == 'a') == 1) by {
            reveal(Seq::filter);
        }
        assert(rmatch_indices_seq.len() == 1);
        assert(rmatch_indices_seq[0].0 == 0usize);
    }
    let rmatch_indices_first = rmatch_indices.next();
    test!(matches!(rmatch_indices_first, Some((0usize, _))), {
        proof {
            assert(rmatch_indices_first == Some(rmatch_indices_seq[0]));
        }
    });
    match rmatch_indices_first {
        Some((offset, part)) => {
            proof {
                assert(offset == 0usize);
                assert(part == rmatch_indices_seq[0].1);
                assert(part@ == seq!['a']);
            }
        },
        None => test!(false),
    }
}

// ISSUE TODO(Verge): exact runtime `&str` equality for matches needs the generated
// view-based injectivity lemmas to be public downstream, e.g.:
// fn test_matches_exact_runtime_values_with_assume_lemmas() {
//     broadcast use group_str_matches_iter;
//     proof { reveal_strlit("a"); }
//     let text = "a";
//     let mut matches = text.matches_iter('a');
//     let ghost matches_seq = matches.seq();
//     proof {
//         lemma_str_matches_iter_char_surjective(text@, 'a', seq!["a"@]);
//         lemma_str_matches_iter_char_injective(text@, 'a', matches_seq, text@, 'a', seq!["a"@]);
//     }
//     test!(matches!(matches.next(), Some("a")));
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
        "str::iter::split_family_concrete_state",
        test_split_family_concrete_state,
    );
    count += crate::run_test(
        "str::iter::match_family_concrete_state",
        test_match_family_concrete_state,
    );
    count
}
