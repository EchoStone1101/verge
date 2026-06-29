// Internal helper lemmas for `str::pattern` linking proofs.

use super::*;

verus! {

// --- Private helper lemmas for str::pattern linking proofs ---

//~doc-skip
pub(super) proof fn lemma_join_uncons(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() > 0,
        seq.len() + 1 == gap.len(),
    ensures
        join(seq, gap) == gap[0] + seq[0] + join(seq.skip(1), gap.skip(1)),
{
    reveal_with_fuel(Seq::<_>::flatten, 3);
    let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
    let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
    let rest = join(seq.skip(1), gap.skip(1));
    assert(parts.len() > 0);
    assert(parts.first() == seq[0] + gap[1]);
    assert_seqs_equal!(parts.drop_first() == rest_parts);
    assert(rest == gap[1] + rest_parts.flatten());
    lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
    assert(parts.flatten() == seq[0] + rest);
    assert(join(seq, gap) == gap[0] + parts.flatten());
    lemma_concat_associative(gap[0], seq[0], rest);
    assert(join(seq, gap) == gap[0] + seq[0] + rest);
}

//~doc-skip
pub(super) proof fn lemma_join_runcons(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() > 0,
        seq.len() + 1 == gap.len(),
    ensures
        join(seq, gap) == join(seq.drop_last(), gap.drop_last()) + seq.last() + gap.last(),
    decreases
        seq.len(),
{
    reveal_with_fuel(Seq::<_>::flatten, 3);
    if seq.len() == 1 {
        calc!{
            (==)
            join(seq, gap); {}
            gap[0] + seq[0] + gap[1]; {}
            join(seq.drop_last(), gap.drop_last()) + seq.last() + gap.last();
        }
    } else {
        calc!{
            (==)
            join(seq, gap); { lemma_join_uncons(seq, gap) }
            gap[0] + seq[0] + join(seq.skip(1), gap.skip(1)); { lemma_join_runcons(seq.skip(1), gap.skip(1)) }
            gap[0] + seq[0] + join(seq.skip(1).drop_last(), gap.skip(1).drop_last())
                + seq.skip(1).last() + gap.skip(1).last();
                {
                    lemma_join_uncons(seq.drop_last(), gap.drop_last());
                    assert(seq.drop_last().skip(1) == seq.skip(1).drop_last());
                    assert(gap.drop_last().skip(1) == gap.skip(1).drop_last());
                    assert(seq.skip(1).last() == seq.last());
                    assert(gap.skip(1).last() == gap.last());
                }
            join(seq.drop_last(), gap.drop_last()) + seq.last() + gap.last();
        }
    }
}

//~doc-skip
pub(super) proof fn lemma_rjoin_uncons(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() > 0,
        seq.len() + 1 == gap.len(),
    ensures
        rjoin(seq, gap) == rjoin(seq.skip(1), gap.skip(1)) + seq[0] + gap[0],
{
    reveal_with_fuel(Seq::<_>::flatten_alt, 4);
    let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
    let rest = rjoin(seq.skip(1), gap.skip(1));
    assert(parts.len() > 0);
    assert(parts.first() == gap[1] + seq[0]);
    assert_seqs_equal!(parts.drop_first() == rest_parts);
    assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
    assert(parts.reverse().last() == parts.first());
    assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
    lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
    assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
    assert(rjoin(seq, gap) == parts.reverse().flatten_alt() + gap[0]);
    assert(rjoin(seq, gap) == rest + seq[0] + gap[0]);
}

//~doc-skip
pub(super) proof fn lemma_rjoin_runcons(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() > 0,
        seq.len() + 1 == gap.len(),
    ensures
        rjoin(seq, gap) == gap.last() + seq.last() + rjoin(seq.drop_last(), gap.drop_last()),
    decreases
        seq.len(),
{
    if seq.len() == 1 {
        reveal_with_fuel(Seq::<_>::flatten_alt, 3);
        assert(gap.last() == gap[1]);
        assert(gap.drop_last().last() == gap[0]);
        assert_seqs_equal!(seq.drop_last() == seq![]);
        calc!{
            (==)
            rjoin(seq, gap); {}
            gap[1] + seq[0] + gap[0]; {}
            gap.last() + seq.last() + rjoin(seq.drop_last(), gap.drop_last());
        }
    } else {
        let rest_seq = seq.skip(1);
        let rest_gap = gap.skip(1);
        lemma_rjoin_uncons(seq, gap);
        lemma_rjoin_runcons(rest_seq, rest_gap);
        lemma_rjoin_uncons(seq.drop_last(), gap.drop_last());
        assert(rest_seq.drop_last() == seq.skip(1).drop_last());
        assert(gap.skip(1).drop_last() == gap.drop_last().skip(1));
        assert(seq.drop_last().skip(1) == seq.skip(1).drop_last());
        assert(rest_seq.last() == seq.last());
        assert(rest_gap.last() == gap.last());
        let middle = rjoin(seq.skip(1).drop_last(), gap.skip(1).drop_last());
        calc!{
            (==)
            rjoin(seq, gap); {}
            rjoin(rest_seq, rest_gap) + seq[0] + gap[0]; {}
            (gap.last() + seq.last() + middle) + seq[0] + gap[0];
                {
                    assert(rjoin(rest_seq, rest_gap) == gap.last() + seq.last() + middle);
                }
            gap.last() + seq.last() + (middle + seq[0] + gap[0]);
                {
                    lemma_concat_associative(gap.last(), seq.last(), middle);
                    lemma_concat_associative(gap.last() + seq.last(), middle, seq[0]);
                    lemma_concat_associative(gap.last() + seq.last() + middle, seq[0], gap[0]);
                    lemma_concat_associative(middle, seq[0], gap[0]);
                    lemma_concat_associative(gap.last(), seq.last(), middle + seq[0] + gap[0]);
                    assert(rjoin(seq.drop_last(), gap.drop_last()) == middle + seq[0] + gap[0]);
                }
            gap.last() + seq.last() + rjoin(seq.drop_last(), gap.drop_last());
        }
    }
}

//~doc-skip
pub(super) proof fn lemma_join_alt(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
    ensures
        join(seq, gap) == seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(),
    decreases
        seq.len(),
{
    if seq.len() == 0 {
        assert(join(seq, gap) == gap.last());
        assert(seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten().len() == 0);
    } else {
        calc!{
            (==)
            join(seq, gap); { lemma_join_uncons(seq, gap) }
            gap[0] + seq[0] + join(seq.skip(1), gap.skip(1)); { lemma_join_alt(seq.skip(1), gap.skip(1)) }
            (gap[0] + seq[0]) + seq.skip(1).map(|i: int, ss: Seq<char>| gap.skip(1)[i] + ss).flatten() + gap.last(); {
                assert(seq.map(|i: int, ss: Seq<char>| gap[i] + ss).first() == gap[0] + seq[0]);
                assert(seq.map(|i: int, ss: Seq<char>| gap[i] + ss).drop_first() == seq.skip(1).map(|i: int, ss: Seq<char>| gap.skip(1)[i] + ss));
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
            seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last();
        }
    }
}

//~doc-skip
pub(super) proof fn lemma_join_split_at(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k <= seq.len(),
    ensures
        join(seq, gap) == seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss).flatten()
            + join(seq.skip(k), gap.skip(k)),
    decreases
        k,
{
    if k == 0 {
        assert_seqs_equal!(seq.skip(k) == seq);
        assert_seqs_equal!(gap.skip(k) == gap);
        assert(seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss).len() == 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
    } else {
        let rest_seq = seq.skip(1);
        let rest_gap = gap.skip(1);
        lemma_join_uncons(seq, gap);
        lemma_join_split_at(rest_seq, rest_gap, k - 1);

        let parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss);
        let rest_parts = rest_seq.take(k - 1).map(|i: int, ss: Seq<char>| rest_gap[i] + ss);
        assert(parts.len() > 0);
        assert(parts.first() == gap[0] + seq[0]);
        assert_seqs_equal!(parts.drop_first() == rest_parts, i => {
            assert(parts.drop_first()[i] == parts[i + 1]);
            assert(seq.take(k)[i + 1] == seq[i + 1]);
            assert(rest_seq.take(k - 1)[i] == rest_seq[i]);
            assert(rest_seq[i] == seq[i + 1]);
            assert(rest_gap[i] == gap[i + 1]);
        });
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(parts.flatten() == (gap[0] + seq[0]) + rest_parts.flatten());
        assert(join(seq, gap) == (gap[0] + seq[0]) + join(rest_seq, rest_gap));
        assert(join(rest_seq, rest_gap) == rest_parts.flatten() + join(rest_seq.skip(k - 1), rest_gap.skip(k - 1)));
        assert_seqs_equal!(rest_seq.skip(k - 1) == seq.skip(k));
        assert_seqs_equal!(rest_gap.skip(k - 1) == gap.skip(k));
        lemma_concat_associative(gap[0] + seq[0], rest_parts.flatten(), join(seq.skip(k), gap.skip(k)));
        assert(join(seq, gap) == parts.flatten() + join(seq.skip(k), gap.skip(k)));
    }
}

//~doc-skip
pub(super) proof fn lemma_join_split_at_alt(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k <= seq.len(),
    ensures
        join(seq, gap) == join(seq.take(k), gap.take(k + 1))
            + seq.skip(k).map(|i: int, ss: Seq<char>| ss + gap.skip(k + 1)[i]).flatten()
{
    if k == seq.len() {
        assert(seq.skip(k).len() == 0);
        assert(seq.take(k) == seq);
        assert(gap.take(k + 1) == gap);
    } else {
        lemma_join_split_match_at(seq, gap, k);
        calc!{
            (==)
            seq[k] + join(seq.skip(k + 1), gap.skip(k + 1)); {}
            seq[k] + gap.skip(k + 1)[0]
                + gap.skip(k + 1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(k + 1)[i] + ss).flatten();
                {
                    let s1 = gap.skip(k + 1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(k + 1)[i] + ss);
                    let s2 = seq.skip(k).map(|i: int, ss: Seq<char>| ss + gap.skip(k + 1)[i]).drop_first();
                    assert_seqs_equal!(s1 == s2);
                    assert(seq[k] + gap.skip(k + 1)[0] == seq.skip(k).map(|i: int, ss: Seq<char>| ss + gap.skip(k + 1)[i]).first());
                }
            seq.skip(k).map(|i: int, ss: Seq<char>| ss + gap.skip(k + 1)[i]).flatten();
        }
    }
}

//~doc-skip
pub(super) proof fn lemma_join_split_match_at(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k < seq.len(),
    ensures
        join(seq, gap) == join(seq.take(k), gap.take(k + 1))
            + seq[k] + join(seq.skip(k + 1), gap.skip(k + 1)),
{
    lemma_join_split_at(seq, gap, k);
    lemma_join_uncons(seq.skip(k), gap.skip(k));
    lemma_join_alt(seq.take(k), gap.take(k + 1));
    let parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss).flatten();
    let prefix = join(seq.take(k), gap.take(k + 1));
    let rest = join(seq.skip(k + 1), gap.skip(k + 1));
    assert(seq.skip(k)[0] == seq[k]);
    assert(gap.skip(k)[0] == gap[k]);
    assert(seq.skip(k).skip(1) == seq.skip(k + 1));
    assert(gap.skip(k).skip(1) == gap.skip(k + 1));
    assert(join(seq.skip(k), gap.skip(k)) == gap[k] + seq[k] + rest);
    assert(gap.take(k + 1).last() == gap[k]);
    lemma_join_alt(seq.take(k), gap.take(k + 1));
    let prefix_parts = seq.take(k).map(|i: int, ss: Seq<char>| gap.take(k + 1)[i] + ss).flatten();
    assert_seqs_equal!(seq.take(k).map(|i: int, ss: Seq<char>| gap.take(k + 1)[i] + ss)
        == seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss), i => {
        assert(gap.take(k + 1)[i] == gap[i]);
    });
    assert_seqs_equal!(prefix_parts == parts);
    assert_seqs_equal!(prefix == parts + gap[k]);
    lemma_concat_associative(parts, gap[k], seq[k] + rest);
    lemma_concat_associative(parts + gap[k], seq[k], rest);
    assert(join(seq, gap) == prefix + seq[k] + rest);
}

//~doc-skip
pub(super) proof fn lemma_rjoin_alt(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
    ensures
        rjoin(seq, gap) == seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss).reverse().flatten_alt() + gap.first(),
{
    let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let alt_parts = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
    assert_seqs_equal!(parts == alt_parts, i => {
        assert(gap.drop_first()[i] == gap[i + 1]);
    });
}

//~doc-skip
pub(super) proof fn lemma_rjoin_alt_for_matches(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
    ensures
        rjoin(seq, gap) == gap.last() + seq.map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().flatten_alt(),
    decreases
        seq.len(),
{
    if seq.len() == 0 {
        assert(gap.last() == gap.first());
        assert(seq.map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
    } else {
        lemma_rjoin_uncons(seq, gap);
        lemma_rjoin_alt_for_matches(seq.skip(1), gap.skip(1));

        let parts = seq.map(|i: int, ss: Seq<char>| ss + gap[i]);
        let rest_parts = seq.skip(1).map(|i: int, ss: Seq<char>| ss + gap.skip(1)[i]);
        assert(parts.len() > 0);
        assert(parts.first() == seq[0] + gap[0]);
        assert_seqs_equal!(parts.drop_first() == rest_parts, i => {
            assert(parts.drop_first()[i] == parts[i + 1]);
            assert(seq.skip(1)[i] == seq[i + 1]);
            assert(gap.skip(1)[i] == gap[i + 1]);
        });
        assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
        assert(parts.reverse().last() == parts.first());
        assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (seq[0] + gap[0]));
        assert(rjoin(seq.skip(1), gap.skip(1)) == gap.last() + rest_parts.reverse().flatten_alt());
        lemma_concat_associative(gap.last(), rest_parts.reverse().flatten_alt(), seq[0] + gap[0]);
        assert(rjoin(seq, gap) == gap.last() + parts.reverse().flatten_alt());
    }
}

//~doc-skip
pub(super) proof fn lemma_rjoin_split_at(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k <= seq.len(),
    ensures
        rjoin(seq, gap) == rjoin(seq.skip(k), gap.skip(k))
            + seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().flatten_alt(),
    decreases
        k,
{
    if k == 0 {
        assert_seqs_equal!(seq.skip(k) == seq);
        assert_seqs_equal!(gap.skip(k) == gap);
        assert(seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
    } else {
        let rest_seq = seq.skip(1);
        let rest_gap = gap.skip(1);
        lemma_rjoin_uncons(seq, gap);
        lemma_rjoin_split_at(rest_seq, rest_gap, k - 1);

        let parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
        let rest_parts = rest_seq.take(k - 1).map(|i: int, ss: Seq<char>| ss + rest_gap[i]);
        assert(parts.len() > 0);
        assert(parts.first() == seq[0] + gap[0]);
        assert_seqs_equal!(parts.drop_first() == rest_parts, i => {
            assert(parts.drop_first()[i] == parts[i + 1]);
            assert(seq.take(k)[i + 1] == seq[i + 1]);
            assert(rest_seq.take(k - 1)[i] == rest_seq[i]);
            assert(rest_seq[i] == seq[i + 1]);
            assert(rest_gap[i] == gap[i + 1]);
        });
        assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
        assert(parts.reverse().last() == parts.first());
        assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (seq[0] + gap[0]));
        assert(rjoin(seq, gap) == rjoin(rest_seq, rest_gap) + seq[0] + gap[0]);
        assert(rjoin(rest_seq, rest_gap) == rjoin(rest_seq.skip(k - 1), rest_gap.skip(k - 1)) + rest_parts.reverse().flatten_alt());
        assert_seqs_equal!(rest_seq.skip(k - 1) == seq.skip(k));
        assert_seqs_equal!(rest_gap.skip(k - 1) == gap.skip(k));
        lemma_concat_associative(rjoin(seq.skip(k), gap.skip(k)), rest_parts.reverse().flatten_alt(), seq[0] + gap[0]);
        assert(rjoin(seq, gap) == rjoin(seq.skip(k), gap.skip(k)) + parts.reverse().flatten_alt());
    }
}

//~doc-skip
pub(super) proof fn lemma_rjoin_split_match_at(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k < seq.len(),
    ensures
        rjoin(seq, gap) == rjoin(seq.skip(k + 1), gap.skip(k + 1))
            + seq[k] + rjoin(seq.take(k), gap.take(k + 1)),
{
    lemma_rjoin_split_at(seq, gap, k);
    lemma_rjoin_uncons(seq.skip(k), gap.skip(k));
    let rest = rjoin(seq.skip(k + 1), gap.skip(k + 1));
    let suffix = rjoin(seq.take(k), gap.take(k + 1));
    let parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().flatten_alt();
    assert(seq.skip(k)[0] == seq[k]);
    assert(gap.skip(k)[0] == gap[k]);
    assert(seq.skip(k).skip(1) == seq.skip(k + 1));
    assert(gap.skip(k).skip(1) == gap.skip(k + 1));
    assert(rjoin(seq.skip(k), gap.skip(k)) == rest + seq[k] + gap[k]);
    assert(gap.take(k + 1).last() == gap[k]);
    lemma_rjoin_split_at(seq.take(k), gap.take(k + 1), k);
    assert(seq.take(k).skip(k) == seq![]);
    assert(gap.take(k + 1).skip(k) == seq![gap[k]]);
    assert(rjoin(seq.take(k).skip(k), gap.take(k + 1).skip(k)) == gap[k]);
    assert_seqs_equal!(seq.take(k).take(k).map(|i: int, ss: Seq<char>| ss + gap.take(k + 1)[i])
        == seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]), i => {
        assert(gap.take(k + 1)[i] == gap[i]);
    });
    assert(suffix == gap[k] + parts);
    lemma_concat_associative(rest, seq[k], gap[k] + parts);
    lemma_concat_associative(rest + seq[k], gap[k], parts);
    assert(rjoin(seq, gap) == rest + seq[k] + suffix);
}

//~doc-skip
pub(super) proof fn lemma_flatten_singleton_pred(seq: Seq<Seq<char>>, pred: spec_fn(char) -> bool)
    requires
        forall |i: int| 0 <= i < seq.len() ==> #[trigger] seq[i].len() == 1 && pred(seq[i][0]),
    ensures
        seq.flatten().len() == seq.len(),
        forall |i: int| 0 <= i < seq.flatten().len() ==> #[trigger] pred(seq.flatten()[i]),
{
    lemma_seq_flatten_same_length(seq, 1);
    assert(seq.flatten().len() == seq.len()) by {
        assert(seq.flatten().len() == seq.len() * 1);
    }
    assert forall |i: int| 0 <= i < seq.flatten().len()
    implies #[trigger] pred(seq.flatten()[i]) by {
        assert(seq.flatten().subrange(i * 1, (i + 1) * 1) == seq[i]);
        assert(seq.flatten()[i] == seq[i][0]);
    }
}

//~doc-skip
pub(super) proof fn lemma_flatten_alt_singleton_pred(seq: Seq<Seq<char>>, pred: spec_fn(char) -> bool)
    requires
        forall |i: int| 0 <= i < seq.len() ==> #[trigger] seq[i].len() == 1 && pred(seq[i][0]),
    ensures
        seq.flatten_alt().len() == seq.len(),
        forall |i: int| 0 <= i < seq.flatten_alt().len() ==> #[trigger] pred(seq.flatten_alt()[i]),
{
    seq.lemma_flatten_and_flatten_alt_are_equivalent();
    lemma_flatten_singleton_pred(seq, pred);
}

//~doc-skip
pub(super) proof fn lemma_flatten_same_seq(seq: Seq<Seq<char>>, pat: Seq<char>)
    requires
        forall |i: int| 0 <= i < seq.len() ==> #[trigger] seq[i] =~= pat,
    ensures
        seq.flatten().len() == seq.len() * pat.len(),
        forall |i: int| 0 <= i < seq.len()
            ==> #[trigger] seq.flatten().subrange(i * pat.len(), (i + 1) * pat.len()) == pat,
{
    assert forall |i: int| 0 <= i < seq.len()
    implies #[trigger] seq[i].len() == pat.len() by {
        assert(seq[i] =~= pat);
    }
    lemma_seq_flatten_same_length(seq, pat.len() as nat);
    assert forall |i: int| 0 <= i < seq.len()
    implies #[trigger] seq.flatten().subrange(i * pat.len(), (i + 1) * pat.len()) == pat by {
        assert(seq.flatten().subrange(i * pat.len(), (i + 1) * pat.len()) == seq[i]);
        assert(seq[i] =~= pat);
    }
}

//~doc-skip
pub(super) proof fn lemma_flatten_alt_same_seq(seq: Seq<Seq<char>>, pat: Seq<char>)
    requires
        forall |i: int| 0 <= i < seq.len() ==> #[trigger] seq[i] =~= pat,
    ensures
        seq.flatten_alt().len() == seq.len() * pat.len(),
{
    seq.lemma_flatten_and_flatten_alt_are_equivalent();
    lemma_flatten_same_seq(seq, pat);
}

//~doc-skip
pub(super) proof fn lemma_trim_string_block_index(i: int, blocks: int, plen: int)
    requires
        plen > 0,
        0 <= i < blocks * plen,
        i % plen == 0,
    ensures
        0 <= i / plen < blocks,
        i == (i / plen) * plen,
{
    lemma_fundamental_div_mod(i, plen);
    assert(i == plen * (i / plen));
    assert(i == (i / plen) * plen) by {
        broadcast use lemma_mul_is_commutative;
    }
    assert(0 <= i / plen) by {
        lemma_div_pos_is_pos(i, plen);
    }
    assert(i / plen < blocks) by {
        assert(i < blocks * plen);
        lemma_mul_strict_inequality_converse(i / plen, blocks, plen);
    }
}

//~doc-skip
pub(super) proof fn lemma_trim_string_flatten_block(
    flat: Seq<char>, seq: Seq<Seq<char>>, pat: Seq<char>, i: int,
)
    requires
        pat.len() > 0,
        flat == seq.flatten(),
        forall |j: int| 0 <= j < seq.len() ==> #[trigger] seq[j] =~= pat,
        0 <= i < flat.len(),
        i % pat.len() as int == 0,
    ensures
        i + pat.len() <= flat.len(),
        flat.subrange(i, i + pat.len()) == pat,
{
    let plen = pat.len() as int;
    let block = i / plen;
    lemma_flatten_same_seq(seq, pat);
    assert(flat.len() == seq.len() * pat.len());
    lemma_trim_string_block_index(i, seq.len() as int, plen);
    assert(i == block * plen);
    assert(0 <= block < seq.len());
    assert(block * plen == block * pat.len()) by (nonlinear_arith)
        requires plen == pat.len() {};
    assert((block + 1) * plen == (block + 1) * pat.len()) by (nonlinear_arith)
        requires plen == pat.len() {};
    assert(i == block * pat.len()) by (nonlinear_arith)
        requires i == block * plen, plen == pat.len() {};
    assert(block + 1 <= seq.len());
    assert(i + pat.len() == (block + 1) * pat.len()) by (nonlinear_arith)
        requires i == block * pat.len(), pat.len() > 0 {};
    assert((block + 1) * pat.len() <= seq.len() * pat.len()) by (nonlinear_arith)
        requires 0 <= block, block + 1 <= seq.len(), pat.len() > 0 {};
    assert(i + pat.len() <= flat.len());
    assert(flat.subrange(block * pat.len(), (block + 1) * pat.len()) == pat);
}

//~doc-skip
pub(super) proof fn lemma_concat_left_subrange(left: Seq<char>, right: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= left.len(),
    ensures
        (left + right).subrange(start, end) == left.subrange(start, end),
{
    assert_seqs_equal!((left + right).subrange(start, end) == left.subrange(start, end));
}

//~doc-skip
pub(super) proof fn lemma_concat_right_subrange(left: Seq<char>, right: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= right.len(),
    ensures
        (left + right).subrange(left.len() + start, left.len() + end) == right.subrange(start, end),
{
    assert_seqs_equal!((left + right).subrange(left.len() + start, left.len() + end)
        == right.subrange(start, end));
}

//~doc-skip
pub(super) proof fn lemma_string_join_not_prefix(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, pat: Seq<char>)
    requires
        pat.len() > 0,
        seq.len() > 0,
        seq.len() + 1 == gap.len(),
        seq[0] =~= pat,
        gap[0].len() > 0,
        !pat.is_prefix_of(gap[0] + pat),
    ensures
        !pat.is_prefix_of(join(seq, gap)),
{
    let ret = join(seq, gap);
    lemma_join_uncons(seq, gap);
    assert(ret == gap[0] + seq[0] + join(seq.skip(1), gap.skip(1)));
    if pat.is_prefix_of(ret) {
        assert(pat.len() <= ret.len());
        assert(ret.subrange(0, pat.len() as int) == pat);
        assert(seq[0] == pat);
        let rest = join(seq.skip(1), gap.skip(1));
        assert(ret == gap[0] + pat + rest);
        lemma_concat_left_subrange(gap[0] + pat, rest, 0, pat.len() as int);
        assert((gap[0] + pat).subrange(0, pat.len() as int) == ret.subrange(0, pat.len() as int));
        assert(pat.is_prefix_of(gap[0] + pat));
    }
}

//~doc-skip
pub(super) proof fn lemma_string_rjoin_not_suffix(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, pat: Seq<char>)
    requires
        pat.len() > 0,
        seq.len() > 0,
        seq.len() + 1 == gap.len(),
        seq[0] =~= pat,
        gap[0].len() > 0,
        !pat.is_suffix_of(pat + gap[0]),
    ensures
        !pat.is_suffix_of(rjoin(seq, gap)),
{
    let ret = rjoin(seq, gap);
    lemma_rjoin_uncons(seq, gap);
    assert(ret == rjoin(seq.skip(1), gap.skip(1)) + seq[0] + gap[0]);
    if pat.is_suffix_of(ret) {
        assert(pat.len() <= ret.len());
        assert(ret.subrange(ret.len() - pat.len(), ret.len() as int) == pat);
        assert(seq[0] == pat);
        let rest = rjoin(seq.skip(1), gap.skip(1));
        assert(ret == rest + pat + gap[0]);
        lemma_concat_right_subrange(rest, pat + gap[0], (pat + gap[0]).len() - pat.len(), (pat + gap[0]).len() as int);
        assert((pat + gap[0]).subrange((pat + gap[0]).len() - pat.len(), (pat + gap[0]).len() as int)
            == ret.subrange(ret.len() - pat.len(), ret.len() as int));
        assert(pat.is_suffix_of(pat + gap[0]));
    }
}

//~doc-skip
pub(super) proof fn lemma_join_empty_gap_prefix_parts(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        0 <= k <= seq.len(),
        forall |i: int| 0 <= i < k ==> #[trigger] gap[i].len() == 0,
    ensures
        seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss).flatten()
            == seq.take(k).flatten(),
{
    let parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss);
    assert_seqs_equal!(parts == seq.take(k), i => {
        assert(gap[i].len() == 0);
        assert(gap[i] + seq.take(k)[i] == seq.take(k)[i]);
    });
}

//~doc-skip
pub(super) proof fn lemma_join_empty_gap_suffix_parts(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, start: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= start <= seq.len(),
        forall |i: int| start + 1 <= i < gap.len() ==> #[trigger] gap[i].len() == 0,
    ensures
        seq.skip(start).map(|i: int, ss: Seq<char>| ss + gap.skip(start + 1)[i]).flatten()
            == seq.skip(start).flatten(),
{
    let parts = seq.skip(start).map(|i: int, ss: Seq<char>| ss + gap.skip(start + 1)[i]);
    assert_seqs_equal!(parts == seq.skip(start), i => {
        assert(gap.skip(start + 1)[i] == gap[start + 1 + i]);
        assert(gap[start + 1 + i].len() == 0);
        assert(seq.skip(start)[i] + gap.skip(start + 1)[i] == seq.skip(start)[i]);
    });
}

//~doc-skip
pub(super) proof fn lemma_rjoin_empty_gap_prefix_parts(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k <= seq.len(),
        forall |i: int| 0 <= i < k ==> #[trigger] gap[i].len() == 0,
    ensures
        ({
            let parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
            parts.reverse().flatten_alt() == seq.take(k).reverse().flatten_alt()
        }),
{
    let parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
    assert_seqs_equal!(parts == seq.take(k), i => {
        assert(gap[i].len() == 0);
        assert(seq.take(k)[i] + gap[i] == seq.take(k)[i]);
    });
    assert(parts.reverse().flatten_alt() =~= seq.take(k).reverse().flatten_alt());
}

//~doc-skip
pub(super) proof fn lemma_rjoin_empty_gap_prefix_parts_pred(
    seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, k: int, pred: spec_fn(char) -> bool,
)
    requires
        seq.len() + 1 == gap.len(),
        0 <= k <= seq.len(),
        forall |i: int| 0 <= i < k ==> #[trigger] gap[i].len() == 0,
        forall |i: int| 0 <= i < k ==> #[trigger] seq[i].len() == 1 && pred(seq[i][0]),
    ensures
        ({
            let parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
            &&& parts.reverse().flatten_alt().len() == k
            &&& forall |i: int| 0 <= i < parts.reverse().flatten_alt().len()
                ==> #[trigger] pred(parts.reverse().flatten_alt()[i])
        }),
{
    let parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
    assert_seqs_equal!(parts == seq.take(k), i => {
        assert(gap[i].len() == 0);
        assert(seq.take(k)[i] + gap[i] == seq.take(k)[i]);
    });
    assert forall |i: int| 0 <= i < seq.take(k).len()
    implies #[trigger] seq.take(k)[i].len() == 1 && pred(seq.take(k)[i][0]) by {
        assert(seq.take(k)[i] == seq[i]);
    }
    assert forall |i: int| 0 <= i < seq.take(k).reverse().len()
    implies #[trigger] seq.take(k).reverse()[i].len() == 1 && pred(seq.take(k).reverse()[i][0]) by {
        assert(seq.take(k).reverse()[i] == seq.take(k)[seq.take(k).len() - 1 - i]);
    }
    assert(parts.reverse().flatten_alt() =~= seq.take(k).reverse().flatten_alt());
    lemma_flatten_alt_singleton_pred(seq.take(k).reverse(), pred);
    assert(parts.reverse().flatten_alt().len() == k);
}

//~doc-skip
pub(super) proof fn lemma_join_trim_decomposition(
    seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, head: int, tail: int,
)
    requires
        seq.len() + 1 == gap.len(),
        0 <= head,
        0 <= tail,
        head + tail < gap.len(),
        forall |i: int| 0 <= i < head ==> #[trigger] gap[i].len() == 0,
        forall |i: int| gap.len() - tail <= i < gap.len() ==> #[trigger] gap[i].len() == 0,
    ensures
        join(seq, gap) == seq.take(head).flatten()
            + join(seq.subrange(head, seq.len() - tail), gap.subrange(head, gap.len() - tail))
            + seq.skip(seq.len() - tail).flatten(),
{
    let mid_len = seq.len() - head - tail;
    assert(0 <= mid_len <= seq.len() - head);
    lemma_join_split_at(seq, gap, head);
    lemma_join_empty_gap_prefix_parts(seq, gap, head);
    lemma_join_split_at_alt(seq.skip(head), gap.skip(head), mid_len);
    assert(seq.skip(head).take(mid_len) == seq.subrange(head, seq.len() - tail));
    assert(gap.skip(head).take(mid_len + 1) == gap.subrange(head, gap.len() - tail));
    assert(seq.skip(head).skip(mid_len) == seq.skip(seq.len() - tail));
    assert(gap.skip(head).skip(mid_len + 1) == gap.skip(gap.len() - tail));
    assert forall |i: int| seq.len() - tail + 1 <= i < gap.len()
    implies #[trigger] gap[i].len() == 0 by {
        assert(seq.len() - tail + 1 == gap.len() - tail);
    }
    lemma_join_empty_gap_suffix_parts(seq, gap, seq.len() - tail);
    let prefix = seq.take(head).flatten();
    let mid = join(seq.subrange(head, seq.len() - tail), gap.subrange(head, gap.len() - tail));
    let suffix = seq.skip(seq.len() - tail).flatten();
    lemma_concat_associative(prefix, mid, suffix);
}

//~doc-skip
pub(super) proof fn lemma_join_boundary_gaps(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
        gap.first().len() > 0,
        gap.last().len() > 0,
    ensures
        join(seq, gap).len() > 0,
        join(seq, gap).first() == gap.first().first(),
        join(seq, gap).last() == gap.last().last(),
{
    if seq.len() == 0 {
        assert(gap.len() == 1);
        assert(join(seq, gap) == gap.first());
        assert(gap.first() == gap.last());
    } else {
        lemma_join_uncons(seq, gap);
        assert(join(seq, gap) == gap.first() + seq.first() + join(seq.skip(1), gap.skip(1)));
        assert(join(seq, gap).first() == gap.first().first());
        lemma_join_runcons(seq, gap);
        assert(join(seq, gap) == join(seq.drop_last(), gap.drop_last()) + seq.last() + gap.last());
        assert(join(seq, gap).last() == gap.last().last());
    }
}

//~doc-skip
pub(super) proof fn lemma_join_first_gap(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
        gap.first().len() > 0,
    ensures
        join(seq, gap).len() > 0,
        join(seq, gap).first() == gap.first().first(),
{
    if seq.len() == 0 {
        assert(gap.len() == 1);
        assert(join(seq, gap) == gap.first());
    } else {
        lemma_join_uncons(seq, gap);
        assert(join(seq, gap) == gap.first() + seq.first() + join(seq.skip(1), gap.skip(1)));
        assert(join(seq, gap).first() == gap.first().first());
    }
}

//~doc-skip
pub(super) proof fn lemma_rjoin_last_first_gap(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
        gap.first().len() > 0,
    ensures
        rjoin(seq, gap).len() > 0,
        rjoin(seq, gap).last() == gap.first().last(),
{
    if seq.len() == 0 {
        assert(gap.len() == 1);
        assert(rjoin(seq, gap) == gap.first());
    } else {
        lemma_rjoin_uncons(seq, gap);
        assert(rjoin(seq, gap) == rjoin(seq.skip(1), gap.skip(1)) + seq.first() + gap.first());
        assert(rjoin(seq, gap).last() == gap.first().last());
    }
}

//~doc-skip
pub(super) proof fn lemma_trimmed_concat_skip_rskip(
    left: Seq<char>, ret: Seq<char>, right: Seq<char>, pred: spec_fn(char) -> bool,
)
    requires
        ret.len() > 0,
        !pred(ret.first()),
        !pred(ret.last()),
        forall |i: int| 0 <= i < left.len() ==> #[trigger] pred(left[i]),
        forall |i: int| 0 <= i < right.len() ==> #[trigger] pred(right[i]),
    ensures
        ret == (left + ret + right).skip_while(pred).rskip_while(pred),
{
    let suffix = ret + right;
    let whole = left + suffix;
    assert(whole == left + ret + right) by {
        lemma_concat_associative(left, ret, right);
    }
    assert(suffix.is_suffix_of(whole));
    assert(suffix.len() > 0);
    assert(suffix.first() == ret.first());
    assert forall |i: int| 0 <= i < whole.len() - suffix.len()
    implies #[trigger] pred(whole[i]) by {
        assert(whole[i] == left[i]);
    }
    lemma_seq_skip_while_defines(whole, pred, suffix);
    assert(ret.is_prefix_of(suffix));
    assert forall |i: int| ret.len() <= i < suffix.len()
    implies #[trigger] pred(suffix[i]) by {
        assert(suffix[i] == right[i - ret.len()]);
    }
    lemma_seq_rskip_while_defines(suffix, pred, ret);
}

//~doc-skip
pub(super) proof fn lemma_trimmed_concat_skip(
    left: Seq<char>, ret: Seq<char>, pred: spec_fn(char) -> bool,
)
    requires
        ret.len() > 0,
        !pred(ret.first()),
        forall |i: int| 0 <= i < left.len() ==> #[trigger] pred(left[i]),
    ensures
        ret == (left + ret).skip_while(pred),
{
    let whole = left + ret;
    assert(ret.is_suffix_of(whole));
    assert forall |i: int| 0 <= i < whole.len() - ret.len()
    implies #[trigger] pred(whole[i]) by {
        assert(whole[i] == left[i]);
    }
    lemma_seq_skip_while_defines(whole, pred, ret);
}

//~doc-skip
pub(super) proof fn lemma_trimmed_concat_rskip(
    ret: Seq<char>, right: Seq<char>, pred: spec_fn(char) -> bool,
)
    requires
        ret.len() > 0,
        !pred(ret.last()),
        forall |i: int| 0 <= i < right.len() ==> #[trigger] pred(right[i]),
    ensures
        ret == (ret + right).rskip_while(pred),
{
    let whole = ret + right;
    assert(ret.is_prefix_of(whole));
    assert forall |i: int| ret.len() <= i < whole.len()
    implies #[trigger] pred(whole[i]) by {
        assert(whole[i] == right[i - ret.len()]);
    }
    lemma_seq_rskip_while_defines(whole, pred, ret);
}

//~doc-skip
pub(super) proof fn lemma_call_false_not_true<F>(f: F, c: char)
    where
        F: FnMut(char) -> bool,
    requires
        is_deterministic(f) && is_total(f),
        call_ensures(f, (c,), false),
    ensures
        !call_ensures(f, (c,), true),
{
    assert(call_requires(f, (c,)));
    if call_ensures(f, (c,), true) {
        assert(call_ensures(f, (c,), false));
        assert(false == true);
    }
}


//~doc-skip
pub(super) proof fn lemma_join_empty_gap(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
        gap.all(|ss: Seq<char>| ss.len() == 0),
    ensures
        join(seq, gap) == seq.flatten(),
    decreases
        seq.len(),
{
    let pred = |ss: Seq<char>| ss.len() == 0;
    if seq.len() == 0 {
        assert(join(seq, gap) == gap[0]);
        assert(pred(gap[0]));
        assert(join(seq, gap).len() == 0);
        assert(seq.flatten().len() == 0);
    } else {
        calc!{
            (==)
            join(seq, gap); { lemma_join_uncons(seq, gap) }
            gap[0] + seq[0] + join(seq.skip(1), gap.skip(1)); { assert(pred(gap[0])) }
            seq[0] + join(seq.skip(1), gap.skip(1)); { lemma_join_empty_gap(seq.skip(1), gap.skip(1)) }
            seq[0] + seq.skip(1).flatten(); {}
            seq.flatten();
        }
    }
}

//~doc-skip
pub(super) proof fn lemma_rjoin_empty_gap(seq: Seq<Seq<char>>, gap: Seq<Seq<char>>)
    requires
        seq.len() + 1 == gap.len(),
        gap.all(|ss: Seq<char>| ss.len() == 0),
    ensures
        rjoin(seq, gap) == seq.reverse().flatten_alt(),
    decreases
        seq.len(),
{
    let pred = |ss: Seq<char>| ss.len() == 0;
    if seq.len() == 0 {
        assert(rjoin(seq, gap) == gap[0]);
        assert(pred(gap[0]));
        assert(rjoin(seq, gap).len() == 0);
        assert(seq.reverse().flatten_alt().len() == 0);
    } else {
        lemma_rjoin_uncons(seq, gap);
        lemma_rjoin_empty_gap(seq.skip(1), gap.skip(1));
        assert(pred(gap[0]));
        assert(rjoin(seq, gap) == seq.skip(1).reverse().flatten_alt() + seq[0]);
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        assert(seq.reverse().drop_last() == seq.skip(1).reverse());
        assert(seq.reverse().last() == seq[0]);
        assert(seq.reverse().flatten_alt() == seq.skip(1).reverse().flatten_alt() + seq[0]);
    }
}

//~doc-skip
pub(super) proof fn lemma_str_matches_count(
    seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, pred: spec_fn(char) -> bool,
)
    requires
        gap.len() == seq.len() + 1,
        forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() ==> gap[i].all(|c: char| !pred(c)),
        forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> seq[i].len() == 1 && pred(seq[i][0]),
    ensures
        join(seq, gap).count(pred) == seq.len(),
    decreases
        seq.len(),
{
    if seq.len() == 0 {
        assert(gap.len() == 1);
        assert_seqs_equal!(join(seq, gap) == gap[0]);
        gap[0].lemma_all_neg_filter_empty(pred);
    } else {
        let rest_seq = seq.drop_first();
        let rest_gap = gap.drop_first();
        assert(rest_gap.len() == rest_seq.len() + 1);
        assert forall |i: int| #![trigger rest_gap[i]] 0 <= i < rest_gap.len()
            implies rest_gap[i].all(|c: char| !pred(c)) by {
            assert(rest_gap[i] == gap[i + 1]);
        }
        assert forall |i: int| #![trigger rest_seq[i]] 0 <= i < rest_seq.len()
            implies rest_seq[i].len() == 1 && pred(rest_seq[i][0]) by {
            assert(rest_seq[i] == seq[i + 1]);
        }
        lemma_str_matches_count(rest_seq, rest_gap, pred);

        let rest = join(rest_seq, rest_gap);
        let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
        let rest_parts = rest_gap.drop_first().map(|i: int, ss: Seq<char>| rest_seq[i] + ss);
        assert(parts.len() > 0);
        assert(parts.first() == seq[0] + gap[1]);
        assert_seqs_equal!(parts.drop_first() == rest_parts, i => {
            assert(gap.drop_first().drop_first()[i] == gap[i + 2]);
            assert(rest_gap.drop_first()[i] == gap[i + 2]);
            assert(rest_seq[i] == seq[i + 1]);
        });
        reveal_with_fuel(Seq::<_>::flatten, 3);
        assert(rest == gap[1] + rest_parts.flatten());
        lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
        assert(parts.flatten() == seq[0] + rest);
        assert(join(seq, gap) == gap[0] + parts.flatten());
        lemma_concat_associative(gap[0], seq[0], rest);
        assert(join(seq, gap) == gap[0] + seq[0] + rest);
        gap[0].lemma_all_neg_filter_empty(pred);
        assert(seq[0].filter(pred).len() == 1) by {
            reveal(Seq::filter);
            assert(seq[0].last() == seq[0][0]);
            assert(seq[0].drop_last().len() == 0);
        }
        Seq::<char>::filter_distributes_over_add(gap[0], seq[0], pred);
        Seq::<char>::filter_distributes_over_add(gap[0] + seq[0], rest, pred);
        assert(join(seq, gap).filter(pred).len() == rest.filter(pred).len() + 1);
    }
}

//~doc-skip
pub(super) proof fn lemma_str_rmatches_count(
    seq: Seq<Seq<char>>, gap: Seq<Seq<char>>, pred: spec_fn(char) -> bool,
)
    requires
        gap.len() == seq.len() + 1,
        forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() ==> gap[i].all(|c: char| !pred(c)),
        forall |i: int| #![trigger seq[i]] 0 <= i < seq.len() ==> seq[i].len() == 1 && pred(seq[i][0]),
    ensures
        rjoin(seq, gap).count(pred) == seq.len(),
    decreases
        seq.len(),
{
    if seq.len() == 0 {
        assert(gap.len() == 1);
        assert_seqs_equal!(rjoin(seq, gap) == gap[0]);
        gap[0].lemma_all_neg_filter_empty(pred);
    } else {
        let rest_seq = seq.drop_first();
        let rest_gap = gap.drop_first();
        assert(rest_gap.len() == rest_seq.len() + 1);
        assert forall |i: int| #![trigger rest_gap[i]] 0 <= i < rest_gap.len()
            implies rest_gap[i].all(|c: char| !pred(c)) by {
            assert(rest_gap[i] == gap[i + 1]);
        }
        assert forall |i: int| #![trigger rest_seq[i]] 0 <= i < rest_seq.len()
            implies rest_seq[i].len() == 1 && pred(rest_seq[i][0]) by {
            assert(rest_seq[i] == seq[i + 1]);
        }
        lemma_str_rmatches_count(rest_seq, rest_gap, pred);

        let rest = rjoin(rest_seq, rest_gap);
        let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
        let rest_parts = rest_gap.drop_first().map(|i: int, ss: Seq<char>| ss + rest_seq[i]);
        assert(parts.len() > 0);
        assert(parts.first() == gap[1] + seq[0]);
        assert_seqs_equal!(parts.drop_first() == rest_parts, i => {
            assert(gap.drop_first().drop_first()[i] == gap[i + 2]);
            assert(rest_gap.drop_first()[i] == gap[i + 2]);
            assert(rest_seq[i] == seq[i + 1]);
        });
        assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
        assert(parts.reverse().last() == parts.first());
        reveal_with_fuel(Seq::<_>::flatten_alt, 4);
        assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
        assert(rjoin(seq, gap) == parts.reverse().flatten_alt() + gap[0]);
        assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
        lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
        assert(parts.reverse().flatten_alt() == rest + seq[0]);
        lemma_concat_associative(rest, seq[0], gap[0]);
        assert(rjoin(seq, gap) == rest + seq[0] + gap[0]);
        gap[0].lemma_all_neg_filter_empty(pred);
        assert(seq[0].filter(pred).len() == 1) by {
            reveal(Seq::filter);
            assert(seq[0].last() == seq[0][0]);
            assert(seq[0].drop_last().len() == 0);
        }
        Seq::<char>::filter_distributes_over_add(rest, seq[0], pred);
        Seq::<char>::filter_distributes_over_add(rest + seq[0], gap[0], pred);
        assert(rjoin(seq, gap).filter(pred).len() == rest.filter(pred).len() + 1);
    }
}

}
