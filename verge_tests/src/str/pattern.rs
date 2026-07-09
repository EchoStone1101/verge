//! External-crate tests for public string pattern APIs.

use vstd::prelude::*;
use vstd::utf8::{decode_utf8, is_char_boundary};
use verge::iter::VergeIteratorSpec;
use verge::prelude::*;
use verge::seq::SeqAdditionalSpec;
use verge::str::*;

verus! {

fn test_contains_char_public(s: &str, ch: char) {
    broadcast use group_str_contains;

    let ret = s.contains(ch);
    assert(ret <==> s@.contains(ch));
}

fn test_contains_string_public(s: &str, pat: &str) {
    broadcast use group_str_contains;

    let ret = s.contains(pat);
    assert(ret <==> pat@.is_subrange_of(s@));
}

fn test_contains_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_contains;

    let ret = s.contains(chars);
    assert(ret <==> exists|i: int| 0 <= i < s@.len() && #[trigger] chars@.contains(s@[i]));
}

fn test_starts_with_char_public(s: &str, ch: char) {
    broadcast use group_str_starts_with;

    let ret = s.starts_with(ch);
    assert(ret <==> s@.len() > 0 && s@.first() == ch);
}

fn test_starts_with_string_public(s: &str, pat: &str) {
    broadcast use group_str_starts_with;

    let ret = s.starts_with(pat);
    assert(ret <==> pat@.is_prefix_of(s@));
}

fn test_starts_with_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_starts_with;

    let ret = s.starts_with(chars);
    assert(ret <==> s@.len() > 0 && chars@.contains(s@.first()));
}

fn test_ends_with_char_public(s: &str, ch: char) {
    broadcast use group_str_ends_with;

    let ret = s.ends_with(ch);
    assert(ret <==> s@.len() > 0 && s@.last() == ch);
}

fn test_ends_with_string_public(s: &str, pat: &str) {
    broadcast use group_str_ends_with;

    let ret = s.ends_with(pat);
    assert(ret <==> pat@.is_suffix_of(s@));
}

fn test_ends_with_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_ends_with;

    let ret = s.ends_with(chars);
    assert(ret <==> s@.len() > 0 && chars@.contains(s@.last()));
}

fn test_find_char_public(s: &str, ch: char) {
    broadcast use group_str_find;

    let ret = s.find(ch);
    match ret {
        None => {
            assert(!s@.contains(ch));
        },
        Some(k) => {
            let ghost k_ch = decode_utf8(s@.as_bytes().take(k as int)).len() as int;
            assert(is_char_boundary(s@.as_bytes(), k as int));
            assert(k_ch < s@.len());
            assert(s@[k_ch] == ch);
            assert(forall |i: int| 0 <= i < k_ch ==> #[trigger] s@[i] != ch);
        },
    }
}

fn test_find_string_public(s: &str, pat: &str) {
    broadcast use group_str_find;

    let ret = s.find(pat);
    match ret {
        None => {
            assert(!pat@.is_subrange_of(s@));
        },
        Some(k) => {
            let ghost k_ch = decode_utf8(s@.as_bytes().take(k as int)).len() as int;
            assert(is_char_boundary(s@.as_bytes(), k as int));
            assert(k_ch <= s@.len() - pat@.len());
            assert(pat@ == s@.subrange(k_ch, k_ch + pat@.len()));
            assert(forall |i: int| 0 <= i < k_ch
                ==> pat@ != #[trigger] s@.subrange(i, i + pat@.len()));
        },
    }
}

fn test_find_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_find;

    let ret = s.find(chars);
    match ret {
        None => {
            assert(forall |i: int| 0 <= i < s@.len() ==> !(#[trigger] chars@.contains(s@[i])));
        },
        Some(k) => {
            let ghost k_ch = decode_utf8(s@.as_bytes().take(k as int)).len() as int;
            assert(is_char_boundary(s@.as_bytes(), k as int));
            assert(k_ch < s@.len());
            assert(chars@.contains(s@[k_ch]));
            assert(forall |i: int| 0 <= i < k_ch ==> !(#[trigger] chars@.contains(s@[i])));
        },
    }
}

fn test_rfind_char_public(s: &str, ch: char) {
    broadcast use group_str_rfind;

    let ret = s.rfind(ch);
    match ret {
        None => {
            assert(!s@.contains(ch));
        },
        Some(k) => {
            let ghost k_ch = decode_utf8(s@.as_bytes().take(k as int)).len() as int;
            assert(is_char_boundary(s@.as_bytes(), k as int));
            assert(k_ch < s@.len());
            assert(s@[k_ch] == ch);
            assert(forall |i: int| k_ch < i < s@.len() ==> #[trigger] s@[i] != ch);
        },
    }
}

fn test_rfind_string_public(s: &str, pat: &str) {
    broadcast use group_str_rfind;

    let ret = s.rfind(pat);
    match ret {
        None => {
            assert(!pat@.is_subrange_of(s@));
        },
        Some(k) => {
            let ghost k_ch = decode_utf8(s@.as_bytes().take(k as int)).len() as int;
            assert(is_char_boundary(s@.as_bytes(), k as int));
            assert(k_ch <= s@.len() - pat@.len());
            assert(pat@ == s@.subrange(k_ch, k_ch + pat@.len()));
            assert(forall |i: int| k_ch < i <= s@.len() - pat@.len()
                ==> pat@ != #[trigger] s@.subrange(i, i + pat@.len()));
        },
    }
}

fn test_rfind_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_rfind;

    let ret = s.rfind(chars);
    match ret {
        None => {
            assert(forall |i: int| 0 <= i < s@.len() ==> !(#[trigger] chars@.contains(s@[i])));
        },
        Some(k) => {
            let ghost k_ch = decode_utf8(s@.as_bytes().take(k as int)).len() as int;
            assert(is_char_boundary(s@.as_bytes(), k as int));
            assert(k_ch < s@.len());
            assert(chars@.contains(s@[k_ch]));
            assert(forall |i: int| k_ch < i < s@.len() ==> !(#[trigger] chars@.contains(s@[i])));
        },
    }
}

fn test_split_iter_char_public(s: &str, ch: char) {
    broadcast use group_str_split_iter;

    let iter = s.split_iter(ch);
    assert(iter.seq().len() > 0);
    assert(forall |i: int| 0 <= i < iter.seq().len() ==> !(#[trigger] iter.seq()[i]@.contains(ch)));
}

fn test_split_inclusive_iter_char_public(s: &str, ch: char) {
    broadcast use group_str_split_inclusive_iter;

    let iter = s.split_inclusive_iter(ch);
    assert(s@ =~= iter.seq().map_values(|piece: &str| piece@).flatten());
    assert(forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
        iter.seq()[i]@.len() > 0 && !iter.seq()[i]@.drop_last().contains(ch));
    assert(forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() - 1 ==>
        iter.seq()[i]@.last() == ch);
}

fn test_rsplit_iter_char_public(s: &str, ch: char) {
    broadcast use group_str_rsplit_iter;

    let iter = s.rsplit_iter(ch);
    assert(iter.seq().len() > 0);
    assert(forall |i: int| 0 <= i < iter.seq().len() ==> !(#[trigger] iter.seq()[i]@.contains(ch)));
}

fn test_split_terminator_iter_char_public(s: &str, ch: char) {
    broadcast use group_str_split_terminator_iter;

    let iter = s.split_terminator_iter(ch);
    assert((s@.len() == 0) == (iter.seq().len() == 0));
    assert(forall |i: int| 0 <= i < iter.seq().len() ==> !(#[trigger] iter.seq()[i]@.contains(ch)));
}

fn test_rsplit_terminator_iter_char_public(s: &str, ch: char) {
    broadcast use group_str_rsplit_terminator_iter;

    let iter = s.rsplit_terminator_iter(ch);
    assert((s@.len() == 0) == (iter.seq().len() == 0));
    assert(forall |i: int| 0 <= i < iter.seq().len() ==> !(#[trigger] iter.seq()[i]@.contains(ch)));
}

fn test_splitn_iter_char_public(s: &str, n: usize, ch: char) {
    broadcast use group_str_splitn_iter;

    let iter = s.splitn_iter(n, ch);
    assert(iter.seq().len() <= n);
    assert(n > 0 ==> iter.seq().len() > 0);
    assert(forall |i: int| 0 <= i < iter.seq().len() - 1 ==> !(#[trigger] iter.seq()[i]@.contains(ch)));
    assert(iter.seq().len() < n ==> !iter.seq().last()@.contains(ch));
}

fn test_rsplitn_iter_char_public(s: &str, n: usize, ch: char) {
    broadcast use group_str_rsplitn_iter;

    let iter = s.rsplitn_iter(n, ch);
    assert(iter.seq().len() <= n);
    assert(n > 0 ==> iter.seq().len() > 0);
    assert(forall |i: int| 0 <= i < iter.seq().len() - 1 ==> !(#[trigger] iter.seq()[i]@.contains(ch)));
    assert(iter.seq().len() < n ==> !iter.seq().last()@.contains(ch));
}

fn test_split_once_char_public(s: &str, ch: char) {
    broadcast use group_str_split_once;

    let ret = s.split_once(ch);
    match ret {
        None => {
            assert(!s@.contains(ch));
        },
        Some((head, tail)) => {
            assert(!head@.contains(ch));
            assert(s@ == head@.push(ch) + tail@);
        },
    }
}

fn test_split_once_string_public(s: &str, pat: &str) {
    broadcast use group_str_split_once;

    let ret = s.split_once(pat);
    match ret {
        None => {
            assert(!pat@.is_subrange_of(s@));
        },
        Some((head, tail)) => {
            assert(pat@.len() == 0 ==> head@.len() == 0 && tail@ == s@);
            assert(pat@.len() > 0 ==> s@ == head@ + pat@ + tail@);
        },
    }
}

fn test_split_once_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_split_once;

    let ret = s.split_once(chars);
    match ret {
        None => {
            assert(forall |i: int| 0 <= i < s@.len() ==> !(#[trigger] chars@.contains(s@[i])));
        },
        Some((head, tail)) => {
            assert(forall |i: int| 0 <= i < head@.len() ==> !(#[trigger] chars@.contains(head@[i])));
            assert(head@.is_prefix_of(s@));
            assert(tail@.is_suffix_of(s@));
            assert(head@.len() + tail@.len() == s@.len() - 1);
            assert(chars@.contains(s@[head@.len() as int]));
        },
    }
}

fn test_rsplit_once_char_public(s: &str, ch: char) {
    broadcast use group_str_rsplit_once;

    let ret = s.rsplit_once(ch);
    match ret {
        None => {
            assert(!s@.contains(ch));
        },
        Some((head, tail)) => {
            assert(!tail@.contains(ch));
            assert(s@ == head@.push(ch) + tail@);
        },
    }
}

fn test_rsplit_once_string_public(s: &str, pat: &str) {
    broadcast use group_str_rsplit_once;

    let ret = s.rsplit_once(pat);
    match ret {
        None => {
            assert(!pat@.is_subrange_of(s@));
        },
        Some((head, tail)) => {
            assert(pat@.len() == 0 ==> tail@.len() == 0 && head@ == s@);
            assert(pat@.len() > 0 ==> s@ == head@ + pat@ + tail@);
        },
    }
}

fn test_rsplit_once_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_rsplit_once;

    let ret = s.rsplit_once(chars);
    match ret {
        None => {
            assert(forall |i: int| 0 <= i < s@.len() ==> !(#[trigger] chars@.contains(s@[i])));
        },
        Some((head, tail)) => {
            assert(forall |i: int| 0 <= i < tail@.len() ==> !(#[trigger] chars@.contains(tail@[i])));
            assert(head@.is_prefix_of(s@));
            assert(tail@.is_suffix_of(s@));
            assert(head@.len() + tail@.len() == s@.len() - 1);
            assert(chars@.contains(s@[head@.len() as int]));
        },
    }
}

fn test_matches_iter_char_public(s: &str, ch: char) {
    broadcast use group_str_matches_iter;

    let iter = s.matches_iter(ch);
    // XXX(Verus): a Verus bug (#2631) regarding capturing spec closures prevents
    // proving the `count` fact without explicitly calling the linking lemma.
    proof { lemma_str_matches_iter_char(s@, ch, iter.seq()) }
    assert(iter.seq().len() == s@.count(|c: char| c == ch));
    assert(forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
        iter.seq()[i]@ == seq![ch]);
}

fn test_rmatches_iter_char_public(s: &str, ch: char) {
    broadcast use group_str_rmatches_iter;

    let iter = s.rmatches_iter(ch);
    // XXX(Verus): a Verus bug (#2631) regarding capturing spec closures prevents
    // proving the `count` fact without explicitly calling the linking lemma.
    proof { lemma_str_rmatches_iter_char(s@, ch, iter.seq()) }
    assert(iter.seq().len() == s@.count(|c: char| c == ch));
    assert(forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
        iter.seq()[i]@ == seq![ch]);
}

fn test_match_indices_iter_char_public(s: &str, ch: char) {
    broadcast use group_str_match_indices_iter;

    let iter = s.match_indices_iter(ch);
    // XXX(Verus): a Verus bug (#2631) regarding capturing spec closures prevents
    // proving the `count` fact without explicitly calling the linking lemma.
    proof { lemma_str_match_indices_iter_char(s@, ch, iter.seq()) }
    assert(iter.seq().len() == s@.count(|c: char| c == ch));
    assert(forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
        iter.seq()[i].1@ == seq![ch]);
    assert(forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() - 1 ==>
        iter.seq()[i].0 < iter.seq()[i + 1].0);
}

fn test_rmatch_indices_iter_char_public(s: &str, ch: char) {
    broadcast use group_str_rmatch_indices_iter;

    let iter = s.rmatch_indices_iter(ch);
    // XXX(Verus): a Verus bug (#2631) regarding capturing spec closures prevents
    // proving the `count` fact without explicitly calling the linking lemma.
    proof { lemma_str_rmatch_indices_iter_char(s@, ch, iter.seq()) }
    assert(iter.seq().len() == s@.count(|c: char| c == ch));
    assert(forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
        iter.seq()[i].1@ == seq![ch]);
    assert(forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() - 1 ==>
        iter.seq()[i].0 > iter.seq()[i + 1].0);
}

fn test_split_whitespace_iter_public(s: &str) {
    let iter = s.split_whitespace_iter();
}

fn test_split_ascii_whitespace_iter_public(s: &str) {
    let iter = s.split_ascii_whitespace_iter();
}

fn test_trim_matches_char_public(s: &str, ch: char) {
    broadcast use group_str_trim_matches;

    let ret = s.trim_matches(ch);
    assert(ret@.is_subrange_of(s@));
    assert(ret@.len() > 0 ==> ret@.first() != ch && ret@.last() != ch);
}

fn test_trim_matches_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_trim_matches;

    let ret = s.trim_matches(chars);
    assert(ret@.is_subrange_of(s@));
    assert(ret@.len() > 0 ==> !chars@.contains(ret@.first()) && !chars@.contains(ret@.last()));
}

// Attempted string-pattern mirror:
// fn test_trim_matches_string_public(s: &str, pat: &str) { let _ = s.trim_matches(pat); }
// `trim_matches` currently has public char/closure/chars lemmas, but no public
// `lemma_str_trim_matches_string`; downstream tests use the string start/end variants instead.

fn test_trim_start_matches_char_public(s: &str, ch: char) {
    broadcast use group_str_trim_start_matches;

    let ret = s.trim_start_matches(ch);
    assert(ret@.is_suffix_of(s@));
    assert(ret@.len() > 0 ==> ret@.first() != ch);
    assert(forall |i: int| 0 <= i < s@.len() - ret@.len() ==> #[trigger] s@[i] == ch);
}

fn test_trim_start_matches_string_public(s: &str, pat: &str)
    requires
        pat@.len() > 0,
{
    broadcast use group_str_trim_start_matches;

    let ret = s.trim_start_matches(pat);
    assert(ret@.is_suffix_of(s@));
    assert(ret@.len() > 0 ==> !pat@.is_prefix_of(ret@));
    assert((s@.len() - ret@.len()) % pat@.len() as int == 0);
    assert(forall |i: int| 0 <= i < s@.len() - ret@.len() && i % pat@.len() as int == 0
        ==> #[trigger] s@.subrange(i, i + pat@.len()) == pat@);
}

fn test_trim_start_matches_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_trim_start_matches;

    let ret = s.trim_start_matches(chars);
    assert(ret@.is_suffix_of(s@));
    assert(ret@.len() > 0 ==> !chars@.contains(ret@.first()));
    assert(forall |i: int| 0 <= i < s@.len() - ret@.len() ==> #[trigger] chars@.contains(s@[i]));
}

fn test_trim_end_matches_char_public(s: &str, ch: char) {
    broadcast use group_str_trim_end_matches;

    let ret = s.trim_end_matches(ch);
    assert(ret@.is_prefix_of(s@));
    assert(ret@.len() > 0 ==> ret@.last() != ch);
    assert(forall |i: int| ret@.len() <= i < s@.len() ==> #[trigger] s@[i] == ch);
}

fn test_trim_end_matches_string_public(s: &str, pat: &str)
    requires
        pat@.len() > 0,
{
    broadcast use group_str_trim_end_matches;

    let ret = s.trim_end_matches(pat);
    assert(ret@.is_prefix_of(s@));
    assert(ret@.len() > 0 ==> !pat@.is_suffix_of(ret@));
    assert((s@.len() - ret@.len()) % pat@.len() as int == 0);
    assert(forall |i: int| 0 <= i < s@.len() - ret@.len() && i % pat@.len() as int == 0
        ==> #[trigger] s@.subrange(ret@.len() + i, ret@.len() + i + pat@.len()) == pat@);
}

fn test_trim_end_matches_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_trim_end_matches;

    let ret = s.trim_end_matches(chars);
    assert(ret@.is_prefix_of(s@));
    assert(ret@.len() > 0 ==> !chars@.contains(ret@.last()));
    assert(forall |i: int| ret@.len() <= i < s@.len() ==> #[trigger] chars@.contains(s@[i]));
}

fn test_strip_prefix_char_public(s: &str, ch: char) {
    broadcast use group_str_strip_prefix;

    let ret = s.strip_prefix(ch);
    match ret {
        None => {
            assert(s@.len() == 0 || (s@.len() > 0 && s@.first() != ch));
        },
        Some(rest) => {
            assert(s@.len() > 0);
            assert(s@.first() == ch);
            assert(rest@ == s@.drop_first());
        },
    }
}

fn test_strip_prefix_string_public(s: &str, pat: &str) {
    broadcast use group_str_strip_prefix;

    let ret = s.strip_prefix(pat);
    match ret {
        None => {
            assert(!pat@.is_prefix_of(s@));
        },
        Some(rest) => {
            assert(pat@.is_prefix_of(s@));
            assert(rest@ == s@.skip(pat@.len() as int));
        },
    }
}

fn test_strip_prefix_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_strip_prefix;

    let ret = s.strip_prefix(chars);
    match ret {
        None => {
            assert(s@.len() == 0 || (s@.len() > 0 && !chars@.contains(s@.first())));
        },
        Some(rest) => {
            assert(s@.len() > 0);
            assert(chars@.contains(s@.first()));
            assert(rest@ == s@.drop_first());
        },
    }
}

fn test_strip_suffix_char_public(s: &str, ch: char) {
    broadcast use group_str_strip_suffix;

    let ret = s.strip_suffix(ch);
    match ret {
        None => {
            assert(s@.len() == 0 || (s@.len() > 0 && s@.last() != ch));
        },
        Some(rest) => {
            assert(s@.len() > 0);
            assert(s@.last() == ch);
            assert(rest@ == s@.drop_last());
        },
    }
}

fn test_strip_suffix_string_public(s: &str, pat: &str) {
    broadcast use group_str_strip_suffix;

    let ret = s.strip_suffix(pat);
    match ret {
        None => {
            assert(!pat@.is_suffix_of(s@));
        },
        Some(rest) => {
            assert(pat@.is_suffix_of(s@));
            assert(rest@ == s@.take(s@.len() - pat@.len()));
        },
    }
}

fn test_strip_suffix_chars_public(s: &str, chars: &[char]) {
    broadcast use group_str_strip_suffix;

    let ret = s.strip_suffix(chars);
    match ret {
        None => {
            assert(s@.len() == 0 || (s@.len() > 0 && !chars@.contains(s@.last())));
        },
        Some(rest) => {
            assert(s@.len() > 0);
            assert(chars@.contains(s@.last()));
            assert(rest@ == s@.drop_last());
        },
    }
}

fn test_pattern_composition_strip_after_split(s: &str, ch: char) {
    broadcast use group_str_split_once;
    broadcast use group_str_strip_prefix;

    let ret = s.split_once(ch);
    match ret {
        None => {
            assert(!s@.contains(ch));
        },
        Some((_head, tail)) => {
            let stripped = tail.strip_prefix(ch);
            match stripped {
                None => {
                    assert(tail@.len() == 0 || (tail@.len() > 0 && tail@.first() != ch));
                },
                Some(rest) => {
                    assert(tail@.len() > 0);
                    assert(tail@.first() == ch);
                    assert(rest@ == tail@.drop_first());
                },
            }
        },
    }
}

} // verus!
