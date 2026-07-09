//! Tests for string iterator APIs.

use vstd::prelude::*;
use vstd::assert_by_contradiction;
use vstd::std_specs::iter::*;
use verge::iter::VergeIteratorSpec;
use verge::prelude::*;
use verge::seq::SeqAdditionalSpec;
use verge::str::*;

verus! {

fn test_char_indices() {
    broadcast use verge::str::group_str_view;
    proof { reveal_strlit("ab"); }

    let s = "ab";
    for (i, c) in iter: s.char_indices_iter()
        invariant
            iter.seq() == seq![(0usize, 'a'), (1usize, 'b')],
    {
        assert(c.is_ascii());
    }
    for (i, c) in iter: s.char_indices_iter().rev()
        invariant
            iter.seq() == seq![(1usize, 'b'), (0usize, 'a')],
    {
        assert(c.is_ascii());
    }
}

fn test_bytes_iter_sequence_and_nexts() {
    broadcast use group_str_axioms;
    proof { reveal_strlit("abc"); }

    let s = "abc";
    let mut iter = s.bytes_iter();

    assert(iter.idx() == 0);
    assert(iter.ridx() == 3);
    assert(iter.seq() =~= seq![97u8, 98u8, 99u8]);
    assert(vstd::std_specs::iter::IteratorSpec::remaining(&iter) =~= seq![97u8, 98u8, 99u8]);

    let first = iter.next();
    assert(first == Some(97u8));
    assert(vstd::std_specs::iter::IteratorSpec::remaining(&iter) =~= seq![98u8, 99u8]);

    let last = iter.next_back();
    assert(last == Some(99u8));
    assert(vstd::std_specs::iter::IteratorSpec::remaining(&iter) =~= seq![98u8]);

    let middle = iter.next();
    assert(middle == Some(98u8));
    assert(vstd::std_specs::iter::IteratorSpec::remaining(&iter) =~= Seq::<u8>::empty());

    let none = iter.next();
    assert(none.is_none());
}

fn test_char_indices_iterator_state() {
    broadcast use group_str_axioms;
    proof { reveal_strlit("abc"); }

    let s = "abc";
    let mut iter = s.char_indices_iter();

    assert(iter.idx() == 0);
    assert(iter.ridx() == 3);
    assert(iter.seq() =~= seq![(0usize, 'a'), (1usize, 'b'), (2usize, 'c')]);
    assert(vstd::std_specs::iter::IteratorSpec::remaining(&iter) =~= seq![(0usize, 'a'), (1usize, 'b'), (2usize, 'c')]);

    let first = iter.next();
    assert(first == Some((0usize, 'a')));
    assert(vstd::std_specs::iter::IteratorSpec::remaining(&iter) =~= seq![(1usize, 'b'), (2usize, 'c')]);

    let last = iter.next_back();
    assert(last == Some((2usize, 'c')));
    assert(vstd::std_specs::iter::IteratorSpec::remaining(&iter) =~= seq![(1usize, 'b')]);
}

fn test_lines_iter_public_post(s: &str) {
    let iter = s.lines_iter();

    assert(iter.idx() == 0);
    assert(iter.ridx() == iter.seq().len());
    assert(forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
        forall |j: int| #![trigger iter.seq()[i]@[j]] 0 <= j < iter.seq()[i]@.len() ==>
            iter.seq()[i]@[j] != '\n');
}

fn test_split_iter_char_uses_public_post(s: &str, ch: char) {
    broadcast use group_str_split_iter;

    let split = s.split_iter(ch);
    assert(split.seq().len() > 0);
    assert(forall |i: int| #![trigger split.seq()[i]] 0 <= i < split.seq().len() ==> !split.seq()[i]@.contains(ch));
}

fn test_split_inclusive_iter_char_uses_public_post(s: &str, ch: char) {
    broadcast use group_str_split_inclusive_iter;

    let inclusive = s.split_inclusive_iter(ch);
    assert(s@ =~= inclusive.seq().map_values(|ss: &str| ss@).flatten());
    assert(forall |i: int| #![trigger inclusive.seq()[i]] 0 <= i < inclusive.seq().len() ==>
        inclusive.seq()[i]@.len() > 0 && !inclusive.seq()[i]@.drop_last().contains(ch));
    assert(forall |i: int| #![trigger inclusive.seq()[i]] 0 <= i < inclusive.seq().len() - 1 ==>
        inclusive.seq()[i]@.last() == ch);
}

fn test_rsplit_iter_char_uses_public_post(s: &str, ch: char) {
    broadcast use group_str_rsplit_iter;

    let rsplit = s.rsplit_iter(ch);
    assert(rsplit.seq().len() > 0);
    assert(forall |i: int| #![trigger rsplit.seq()[i]] 0 <= i < rsplit.seq().len() ==> !rsplit.seq()[i]@.contains(ch));
}

fn test_split_terminator_iter_char_uses_public_post(s: &str, ch: char) {
    broadcast use group_str_split_terminator_iter;

    let terminator = s.split_terminator_iter(ch);
    assert((s@.len() == 0) == (terminator.seq().len() == 0));
    assert(forall |i: int| #![trigger terminator.seq()[i]] 0 <= i < terminator.seq().len() ==> !terminator.seq()[i]@.contains(ch));
}

fn test_rsplit_terminator_iter_char_uses_public_post(s: &str, ch: char) {
    broadcast use group_str_rsplit_terminator_iter;

    let rterminator = s.rsplit_terminator_iter(ch);
    assert((s@.len() == 0) == (rterminator.seq().len() == 0));
    assert(forall |i: int| #![trigger rterminator.seq()[i]] 0 <= i < rterminator.seq().len() ==> !rterminator.seq()[i]@.contains(ch));
}

fn test_splitn_iter_char_uses_public_post(s: &str, ch: char, n: usize) {
    broadcast use group_str_splitn_iter;

    let splitn = s.splitn_iter(n, ch);
    assert(splitn.seq().len() <= n);
    assert(n > 0 ==> splitn.seq().len() > 0);
    assert(forall |i: int| #![trigger splitn.seq()[i]] 0 <= i < splitn.seq().len() - 1 ==> !splitn.seq()[i]@.contains(ch));
}

fn test_rsplitn_iter_char_uses_public_post(s: &str, ch: char, n: usize) {
    broadcast use group_str_rsplitn_iter;

    let rsplitn = s.rsplitn_iter(n, ch);
    assert(rsplitn.seq().len() <= n);
    assert(n > 0 ==> rsplitn.seq().len() > 0);
    assert(forall |i: int| #![trigger rsplitn.seq()[i]] 0 <= i < rsplitn.seq().len() - 1 ==> !rsplitn.seq()[i]@.contains(ch));
}

fn test_matches_iter_char_uses_public_post(s: &str, ch: char) {
    broadcast use group_str_matches_iter;

    let matches = s.matches_iter(ch);
    assert(matches.seq().len() == s@.count(|c: char| c == ch)) by {
        // XXX(Verus): a Verus bug (#2631) regarding capturing spec closures prevents
        // proving the `count` fact without explicitly calling the linking lemma.
        lemma_str_matches_iter_char(s@, ch, matches.seq());
    }
    assert(forall |i: int| #![trigger matches.seq()[i]] 0 <= i < matches.seq().len() ==> matches.seq()[i]@ == seq![ch]);
}

fn test_rmatches_iter_char_uses_public_post(s: &str, ch: char) {
    broadcast use group_str_rmatches_iter;

    let rmatches = s.rmatches_iter(ch);
    assert(rmatches.seq().len() == s@.count(|c: char| c == ch)) by {
        // XXX(Verus): bug (#2631) 
        lemma_str_rmatches_iter_char(s@, ch, rmatches.seq());
    }
    assert(forall |i: int| #![trigger rmatches.seq()[i]] 0 <= i < rmatches.seq().len() ==> rmatches.seq()[i]@ == seq![ch]);
}

fn test_match_indices_iter_char_uses_public_post(s: &str, ch: char) {
    broadcast use group_str_match_indices_iter;

    let indices = s.match_indices_iter(ch);
    assert(indices.seq().len() == s@.count(|c: char| c == ch)) by {
        // XXX(Verus): bug (#2631) 
        lemma_str_match_indices_iter_char(s@, ch, indices.seq());
    }
    assert(forall |i: int| #![trigger indices.seq()[i]] 0 <= i < indices.seq().len() ==> indices.seq()[i].1@ == seq![ch]);
    assert(forall |i: int| #![trigger indices.seq()[i]] 0 <= i < indices.seq().len() - 1 ==> indices.seq()[i].0 < indices.seq()[i + 1].0);
}

fn test_rmatch_indices_iter_char_uses_public_post(s: &str, ch: char) {
    broadcast use group_str_rmatch_indices_iter;

    let rindices = s.rmatch_indices_iter(ch);
    assert(rindices.seq().len() == s@.count(|c: char| c == ch)) by {
        // XXX(Verus): bug (#2631) 
        lemma_str_rmatch_indices_iter_char(s@, ch, rindices.seq());
    }
    assert(forall |i: int| #![trigger rindices.seq()[i]] 0 <= i < rindices.seq().len() ==> rindices.seq()[i].1@ == seq![ch]);
    assert(forall |i: int| #![trigger rindices.seq()[i]] 0 <= i < rindices.seq().len() - 1 ==> rindices.seq()[i].0 > rindices.seq()[i + 1].0);
}

fn test_string_pattern_iterator_posts(s: &str, n: usize) {
    broadcast use group_str_axioms;
    broadcast use group_str_split_iter;
    broadcast use group_str_matches_iter;
    proof { reveal_strlit(","); }

    let pat = ",";
    assert(pat@.len() > 0);

    let split = s.split_iter(pat);
    assert(split.seq().len() > 0);
    assert(!(pat@.is_subrange_of(split.seq().last()@)));

    let rsplit = s.rsplit_iter(pat);

    let splitn = s.splitn_iter(n, pat);

    let rsplitn = s.rsplitn_iter(n, pat);

    let matches = s.matches_iter(pat);
    assert(forall |i: int| #![trigger matches.seq()[i]] 0 <= i < matches.seq().len() ==> matches.seq()[i]@ == pat@);

    let rmatches = s.rmatches_iter(pat);

    let indices = s.match_indices_iter(pat);

    let rindices = s.rmatch_indices_iter(pat);
}

fn test_whitespace_iterators_expose_public_posts(s: &str) {
    let split = s.split_whitespace_iter();

    let ascii = s.split_ascii_whitespace_iter();
}

fn test_line_and_split_for_loop_smoke() {
    broadcast use group_str_axioms;
    broadcast use group_str_split_iter;
    proof {
        reveal_strlit("first\nsecond\r\nthird");
        reveal_strlit("a,b,c");
    }

    let lines = "first\nsecond\r\nthird";
    for line in iter: lines.lines_iter()
        invariant
            forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                forall |j: int| #![trigger iter.seq()[i]@[j]] 0 <= j < iter.seq()[i]@.len() ==>
                    iter.seq()[i]@[j] != '\n',
    {
        assert(forall |j: int| #![trigger line@[j]] 0 <= j < line@.len() ==> line@[j] != '\n');
    }

    let csv = "a,b,c";
    for piece in iter: csv.split_iter(',')
        invariant
            str_split_iter_post(csv@, ',', iter.seq()),
            forall |i: int| 0 <= i < iter.seq().len() ==> !(#[trigger] iter.seq()[i]@.contains(',')),
    {
        assert(!piece@.contains(','));
    }
}

fn test_split_family_for_loop_smoke() {
    broadcast use group_str_axioms;
    broadcast use group_str_split_inclusive_iter;
    broadcast use group_str_rsplit_iter;
    broadcast use group_str_split_terminator_iter;
    broadcast use group_str_rsplit_terminator_iter;
    broadcast use group_str_splitn_iter;
    broadcast use group_str_rsplitn_iter;
    proof { reveal_strlit("a,b,c,"); }

    let csv = "a,b,c,";
    for piece in iter: csv.split_inclusive_iter(',')
        invariant
            str_split_inclusive_iter_post(csv@, ',', iter.seq()),
            forall |i: int| #![trigger iter.seq()[i]@] 0 <= i < iter.seq().len() ==>
                iter.seq()[i]@.len() > 0 && !iter.seq()[i]@.drop_last().contains(','),
    {
        assert(piece@.len() > 0);
        assert(!piece@.drop_last().contains(','));
    }

    for piece in iter: csv.rsplit_iter(',')
        invariant
            str_rsplit_iter_post(csv@, ',', iter.seq()),
            forall |i: int| 0 <= i < iter.seq().len() ==> !(#[trigger] iter.seq()[i]@.contains(',')),
    {
        assert(!piece@.contains(','));
    }

    for piece in iter: csv.split_terminator_iter(',')
        invariant
            str_split_terminator_iter_post(csv@, ',', iter.seq()),
            forall |i: int| 0 <= i < iter.seq().len() ==> !(#[trigger] iter.seq()[i]@.contains(',')),
    {
        assert(!piece@.contains(','));
    }

    for piece in iter: csv.rsplit_terminator_iter(',')
        invariant
            str_rsplit_terminator_iter_post(csv@, ',', iter.seq()),
            forall |i: int| 0 <= i < iter.seq().len() ==> !(#[trigger] iter.seq()[i]@.contains(',')),
    {
        assert(!piece@.contains(','));
    }

    for piece in iter: csv.splitn_iter(2usize, ',')
        invariant
            str_splitn_iter_post(csv@, 2usize, ',', iter.seq()),
            iter.seq().len() <= 2usize,
            forall |i: int| 0 <= i < iter.seq().len() - 1 ==> !(#[trigger] iter.seq()[i]@.contains(',')),
    {
        assert(piece@.len() >= 0);
    }

    for piece in iter: csv.rsplitn_iter(2usize, ',')
        invariant
            str_rsplitn_iter_post(csv@, 2usize, ',', iter.seq()),
            iter.seq().len() <= 2usize,
            forall |i: int| 0 <= i < iter.seq().len() - 1 ==> !(#[trigger] iter.seq()[i]@.contains(',')),
    {
        assert(piece@.len() >= 0);
    }
}

fn test_match_family_for_loop_smoke() {
    broadcast use group_str_axioms;
    broadcast use group_str_matches_iter;
    broadcast use group_str_rmatches_iter;
    broadcast use group_str_match_indices_iter;
    broadcast use group_str_rmatch_indices_iter;
    proof { reveal_strlit("abracadabra"); }

    let text = "abracadabra";
    for m in iter: text.matches_iter('a')
        invariant
            str_matches_iter_post(text@, 'a', iter.seq()),
            forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                iter.seq()[i]@ == seq!['a'],
    {
        assert(m@ == seq!['a']);
    }

    for m in iter: text.rmatches_iter('a')
        invariant
            str_rmatches_iter_post(text@, 'a', iter.seq()),
            forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                iter.seq()[i]@ == seq!['a'],
    {
        assert(m@ == seq!['a']);
    }

    for (_pos, m) in iter: text.match_indices_iter('a')
        invariant
            str_match_indices_iter_post(text@, 'a', iter.seq()),
            forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                iter.seq()[i].1@ == seq!['a'],
    {
        assert(m@ == seq!['a']);
    }

    for (_pos, m) in iter: text.rmatch_indices_iter('a')
        invariant
            str_rmatch_indices_iter_post(text@, 'a', iter.seq()),
            forall |i: int| #![trigger iter.seq()[i]] 0 <= i < iter.seq().len() ==>
                iter.seq()[i].1@ == seq!['a'],
    {
        assert(m@ == seq!['a']);
    }
}

fn test_whitespace_for_loop_smoke() {
    broadcast use group_str_axioms;
    proof { reveal_strlit(" red\tblue\n"); }

    let text = " red\tblue\n";
    for word in iter: text.split_whitespace_iter()
        invariant
            str_split_whitespace_iter_post(text@, iter.seq()),
    {
        assert(word@.len() >= 0);
    }

    for word in iter: text.split_ascii_whitespace_iter()
        invariant
            str_split_ascii_whitespace_iter_post(text@, iter.seq()),
    {
        assert(word@.len() >= 0);
    }
}

} // verus!
