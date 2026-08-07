// Internal proof module for `str::trim_matches` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, ch; ret)]
pub broadcast proof fn lemma_str_trim_matches_char(s: Seq<char>, ch: char, ret: Seq<char>)
    requires
        #[trigger] str_trim_matches_post(s, ch, ret),
    ensures
        ret.is_subrange_of(s),
        ret.len() > 0 ==>
            ret.first() != ch && ret.last() != ch,
        ret == s.skip_while(|c: char| c == ch).rskip_while(|c: char| c == ch),
{
    axiom_char_matches_post(s, ch);
    reveal(str_trim_matches_post);
    let (seq, gap) = spec_matches(s, ch);
    let pred = |c: char| c == ch;
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        lemma_join_empty_gap(seq, gap);
        assert(s == seq.flatten());
        assert forall |i: int| 0 <= i < seq.len() 
        implies #[trigger] seq[i] == seq![ch]
        by { assert(seq[i] =~= seq![ch]) }
        lemma_seq_flatten_same_length(seq, 1);

        assert(seq.len() == s.len());
        assert forall |i: int| 0 <= i < s.len()
        implies #[trigger] pred(s[i])
        by {
            assert(s[i] == s.subrange(i * 1, (i + 1) * 1)[0]);
            assert(s.subrange(i * 1, (i + 1) * 1) == seq[i]);
        }
        assert(s.skip_while(pred).len() == 0) by {
            lemma_seq_count_while_lower_bound(s, pred, s.len() as int);
        }
        assert(s.skip_while(pred).rskip_while(pred).len() == 0) by {
            lemma_seq_rskip_while_ensures(s.skip_while(pred), pred);
        }
        assert(ret.len() == 0);
        lemma_seq_is_subrange_alt(s, ret);
    } else {
        let pred2 = |ss: Seq<char>| ss.len() == 0;
        let head = gap.count_while(pred2) as int;
        let tail = gap.rcount_while(pred2) as int;
        lemma_seq_take_while_ensures(gap, pred2);
        lemma_seq_rtake_while_ensures(gap, pred2);
        assert(head + tail < gap.len()) by {
            let k = choose|i: int| 0 <= i < gap.len() && !(#[trigger] pred2(gap[i]));
            lemma_seq_count_while_upper_bound(gap, pred2, k);
            lemma_seq_rcount_while_upper_bound(gap, pred2, k);
        };

        assert forall |i: int| 0 <= i < head
        implies #[trigger] gap[i].len() == 0 by {
            assert(gap.take_while(pred2)[i] == gap[i]);
            assert(pred2(gap.take_while(pred2)[i]));
        }
        assert forall |i: int| gap.len() - tail <= i < gap.len()
        implies #[trigger] gap[i].len() == 0 by {
            assert(gap.rtake_while(pred2)[i - (gap.len() - tail)] == gap[i]);
            assert(pred2(gap.rtake_while(pred2)[i - (gap.len() - tail)]));
        }
        assert(ret == join(seq.subrange(head, seq.len() - tail), gap.subrange(head, gap.len() - tail)));
        assert(gap[head].len() > 0) by {
            lemma_seq_count_while_upper_bound(gap, pred2, head);
        }
        assert(gap[gap.len() - tail - 1].len() > 0) by {
            lemma_seq_rcount_while_upper_bound(gap, pred2, gap.len() - tail - 1);
        }
        let left = seq.take(head).flatten();
        let mid_seq = seq.subrange(head, seq.len() - tail);
        let mid_gap = gap.subrange(head, gap.len() - tail);
        let right = seq.skip(seq.len() - tail).flatten();
        assert(s == left + ret + right) by {
            lemma_join_trim_decomposition(seq, gap, head, tail);
        }
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0])
        by {
            assert(seq[i] =~= seq![ch]);
        }
        assert forall |i: int| 0 <= i < seq.take(head).len()
        implies #[trigger] seq.take(head)[i].len() == 1 && pred(seq.take(head)[i][0])
        by {
            assert(seq.take(head)[i] == seq[i]);
            assert(seq[i].len() == 1 && pred(seq[i][0]));
        }
        assert forall |i: int| 0 <= i < seq.skip(seq.len() - tail).len()
        implies #[trigger] seq.skip(seq.len() - tail)[i].len() == 1
            && pred(seq.skip(seq.len() - tail)[i][0])
        by {
            assert(seq.skip(seq.len() - tail)[i] == seq[seq.len() - tail + i]);
            assert(seq[seq.len() - tail + i].len() == 1 && pred(seq[seq.len() - tail + i][0]));
        }
        lemma_flatten_singleton_pred(seq.take(head), pred);
        lemma_flatten_singleton_pred(seq.skip(seq.len() - tail), pred);
        assert(left.len() == head);
        assert(right.len() == tail);
        // #1
        assert(ret.is_subrange_of(s)) by {
            assert(s == left + ret + right);
            assert(s.subrange(left.len() as int, s.len() - right.len()) == ret);
            assert(left.len() == head);
            assert(right.len() == tail);
            assert(ret == s.subrange(head, s.len() - tail));
            lemma_seq_is_subrange_alt(s, ret);
        }
        // #2
        if ret.len() > 0 {
            assert(!gap[head].contains(ch));
            assert(!gap[gap.len() - tail - 1].contains(ch));
            assert(mid_gap.first() == gap[head]);
            assert(mid_gap.last() == gap[gap.len() - tail - 1]);
            lemma_join_boundary_gaps(mid_seq, mid_gap);
            assert(ret.first() != ch) by {
                assert(ret.first() == mid_gap.first()[0]);
            }
            assert(ret.last() != ch) by {
                assert(ret.last() == mid_gap.last().last());
            }
        }

        // #3
        if ret.len() > 0 {
            assert(!pred(ret.first()) && !pred(ret.last()));
            assert forall |i: int| 0 <= i < left.len()
            implies #[trigger] pred(left[i]) by {}
            assert forall |i: int| 0 <= i < right.len()
            implies #[trigger] pred(right[i]) by {}
            assert(ret == (left + ret + right).skip_while(pred).rskip_while(pred)) by {
                lemma_trimmed_concat_skip_rskip(left, ret, right, pred);
            }
        } else {
            assert(false) by {
                assert(ret == join(mid_seq, mid_gap));
                lemma_join_boundary_gaps(mid_seq, mid_gap);
            }
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_trim_matches_closure<F>(s: Seq<char>, f: F, ret: Seq<char>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_trim_matches_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret.is_subrange_of(s),
        ret.len() > 0 ==>
            call_ensures(f, (ret.first(),), false)
            && call_ensures(f, (ret.last(),), false),
        ret == s.skip_while(|c: char| call_ensures(f, (c,), true))
                .rskip_while(|c: char| call_ensures(f, (c,), true)),
{
    axiom_closure_matches_post(s, f);
    reveal(str_trim_matches_post);
    let (seq, gap) = spec_matches(s, f);
    let pred = |c: char| call_ensures(f, (c,), true);
    let gap_pred = |c: char| call_ensures(f, (c,), false);
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        lemma_join_empty_gap(seq, gap);
        assert(s == seq.flatten());
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0]) by {}
        lemma_flatten_singleton_pred(seq, pred);
        assert(seq.len() == s.len());
        assert forall |i: int| 0 <= i < s.len()
        implies #[trigger] pred(s[i]) by {
            assert(s[i] == seq.flatten()[i]);
            assert(pred(seq.flatten()[i]));
        }
        assert(s.skip_while(pred).len() == 0) by {
            lemma_seq_count_while_lower_bound(s, pred, s.len() as int);
        }
        assert(s.skip_while(pred).rskip_while(pred).len() == 0) by {
            lemma_seq_rskip_while_ensures(s.skip_while(pred), pred);
        }
        assert(ret.len() == 0);
        lemma_seq_is_subrange_alt(s, ret);
    } else {
        let pred2 = |ss: Seq<char>| ss.len() == 0;
        let head = gap.count_while(pred2) as int;
        let tail = gap.rcount_while(pred2) as int;
        lemma_seq_take_while_ensures(gap, pred2);
        lemma_seq_rtake_while_ensures(gap, pred2);
        assert(head + tail < gap.len()) by {
            let k = choose|i: int| 0 <= i < gap.len() && !(#[trigger] pred2(gap[i]));
            lemma_seq_count_while_upper_bound(gap, pred2, k);
            lemma_seq_rcount_while_upper_bound(gap, pred2, k);
        };

        assert forall |i: int| 0 <= i < head
        implies #[trigger] gap[i].len() == 0 by {
            assert(gap.take_while(pred2)[i] == gap[i]);
            assert(pred2(gap.take_while(pred2)[i]));
        }
        assert forall |i: int| gap.len() - tail <= i < gap.len()
        implies #[trigger] gap[i].len() == 0 by {
            assert(gap.rtake_while(pred2)[i - (gap.len() - tail)] == gap[i]);
            assert(pred2(gap.rtake_while(pred2)[i - (gap.len() - tail)]));
        }
        assert(ret == join(seq.subrange(head, seq.len() - tail), gap.subrange(head, gap.len() - tail)));
        assert(gap[head].len() > 0) by {
            lemma_seq_count_while_upper_bound(gap, pred2, head);
        }
        assert(gap[gap.len() - tail - 1].len() > 0) by {
            lemma_seq_rcount_while_upper_bound(gap, pred2, gap.len() - tail - 1);
        }
        let left = seq.take(head).flatten();
        let mid_seq = seq.subrange(head, seq.len() - tail);
        let mid_gap = gap.subrange(head, gap.len() - tail);
        let right = seq.skip(seq.len() - tail).flatten();
        assert(s == left + ret + right) by {
            lemma_join_trim_decomposition(seq, gap, head, tail);
        }
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0]) by {}
        assert forall |i: int| 0 <= i < seq.take(head).len()
        implies #[trigger] seq.take(head)[i].len() == 1 && pred(seq.take(head)[i][0])
        by {
            assert(seq.take(head)[i] == seq[i]);
            assert(seq[i].len() == 1 && pred(seq[i][0]));
        }
        assert forall |i: int| 0 <= i < seq.skip(seq.len() - tail).len()
        implies #[trigger] seq.skip(seq.len() - tail)[i].len() == 1
            && pred(seq.skip(seq.len() - tail)[i][0])
        by {
            assert(seq.skip(seq.len() - tail)[i] == seq[seq.len() - tail + i]);
            assert(seq[seq.len() - tail + i].len() == 1 && pred(seq[seq.len() - tail + i][0]));
        }
        lemma_flatten_singleton_pred(seq.take(head), pred);
        lemma_flatten_singleton_pred(seq.skip(seq.len() - tail), pred);
        assert(left.len() == head);
        assert(right.len() == tail);
        assert(ret.is_subrange_of(s)) by {
            assert(s == left + ret + right);
            assert(s.subrange(left.len() as int, s.len() - right.len()) == ret);
            assert(left.len() == head);
            assert(right.len() == tail);
            assert(ret == s.subrange(head, s.len() - tail));
            lemma_seq_is_subrange_alt(s, ret);
        }
        if ret.len() > 0 {
            assert(mid_gap.first() == gap[head]);
            assert(mid_gap.last() == gap[gap.len() - tail - 1]);
            lemma_join_boundary_gaps(mid_seq, mid_gap);
            assert(gap[head].all(gap_pred));
            assert(gap[gap.len() - tail - 1].all(gap_pred));
            assert(call_ensures(f, (ret.first(),), false)) by {
                assert(ret.first() == mid_gap.first()[0]);
                assert(gap[head][0] == mid_gap.first()[0]);
                assert(gap_pred(gap[head][0]));
            }
            assert(call_ensures(f, (ret.last(),), false)) by {
                assert(ret.last() == mid_gap.last().last());
                assert(gap_pred(gap[gap.len() - tail - 1].last()));
            }
        }

        if ret.len() > 0 {
            assert(!pred(ret.first()) && !pred(ret.last())) by {
                lemma_call_false_not_true(f, ret.first());
                lemma_call_false_not_true(f, ret.last());
            }
            assert forall |i: int| 0 <= i < left.len()
            implies #[trigger] pred(left[i]) by {}
            assert forall |i: int| 0 <= i < right.len()
            implies #[trigger] pred(right[i]) by {}
            assert(ret == (left + ret + right).skip_while(pred).rskip_while(pred)) by {
                lemma_trimmed_concat_skip_rskip(left, ret, right, pred);
            }
        } else {
            assert(false) by {
                assert(ret == join(mid_seq, mid_gap));
                lemma_join_boundary_gaps(mid_seq, mid_gap);
            }
        }
    }
}

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, chars@; ret)]
pub broadcast proof fn lemma_str_trim_matches_chars<'b>(s: Seq<char>, chars: &'b [char], ret: Seq<char>)
    requires
        #[trigger] str_trim_matches_post(s, chars, ret),
    ensures
        ret.is_subrange_of(s),
        ret.len() > 0 ==>
            !chars@.contains(ret.first()) && !chars@.contains(ret.last()),
        ret == s.skip_while(|c: char| chars@.contains(c))
                .rskip_while(|c: char| chars@.contains(c)),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_trim_matches_post);
    let (seq, gap) = spec_matches(s, chars);
    let pred = |c: char| chars@.contains(c);
    let gap_pred = |c: char| !chars@.contains(c);
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        lemma_join_empty_gap(seq, gap);
        assert(s == seq.flatten());
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0]) by {}
        lemma_flatten_singleton_pred(seq, pred);
        assert(seq.len() == s.len());
        assert forall |i: int| 0 <= i < s.len()
        implies #[trigger] pred(s[i]) by {
            assert(s[i] == seq.flatten()[i]);
            assert(pred(seq.flatten()[i]));
        }
        assert(s.skip_while(pred).len() == 0) by {
            lemma_seq_count_while_lower_bound(s, pred, s.len() as int);
        }
        assert(s.skip_while(pred).rskip_while(pred).len() == 0) by {
            lemma_seq_rskip_while_ensures(s.skip_while(pred), pred);
        }
        assert(ret.len() == 0);
        lemma_seq_is_subrange_alt(s, ret);
    } else {
        let pred2 = |ss: Seq<char>| ss.len() == 0;
        let head = gap.count_while(pred2) as int;
        let tail = gap.rcount_while(pred2) as int;
        lemma_seq_take_while_ensures(gap, pred2);
        lemma_seq_rtake_while_ensures(gap, pred2);
        assert(head + tail < gap.len()) by {
            let k = choose|i: int| 0 <= i < gap.len() && !(#[trigger] pred2(gap[i]));
            lemma_seq_count_while_upper_bound(gap, pred2, k);
            lemma_seq_rcount_while_upper_bound(gap, pred2, k);
        };

        assert forall |i: int| 0 <= i < head
        implies #[trigger] gap[i].len() == 0 by {
            assert(gap.take_while(pred2)[i] == gap[i]);
            assert(pred2(gap.take_while(pred2)[i]));
        }
        assert forall |i: int| gap.len() - tail <= i < gap.len()
        implies #[trigger] gap[i].len() == 0 by {
            assert(gap.rtake_while(pred2)[i - (gap.len() - tail)] == gap[i]);
            assert(pred2(gap.rtake_while(pred2)[i - (gap.len() - tail)]));
        }
        assert(ret == join(seq.subrange(head, seq.len() - tail), gap.subrange(head, gap.len() - tail)));
        assert(gap[head].len() > 0) by {
            lemma_seq_count_while_upper_bound(gap, pred2, head);
        }
        assert(gap[gap.len() - tail - 1].len() > 0) by {
            lemma_seq_rcount_while_upper_bound(gap, pred2, gap.len() - tail - 1);
        }
        let left = seq.take(head).flatten();
        let mid_seq = seq.subrange(head, seq.len() - tail);
        let mid_gap = gap.subrange(head, gap.len() - tail);
        let right = seq.skip(seq.len() - tail).flatten();
        assert(s == left + ret + right) by {
            lemma_join_trim_decomposition(seq, gap, head, tail);
        }
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0]) by {}
        assert forall |i: int| 0 <= i < seq.take(head).len()
        implies #[trigger] seq.take(head)[i].len() == 1 && pred(seq.take(head)[i][0])
        by {
            assert(seq.take(head)[i] == seq[i]);
            assert(seq[i].len() == 1 && pred(seq[i][0]));
        }
        assert forall |i: int| 0 <= i < seq.skip(seq.len() - tail).len()
        implies #[trigger] seq.skip(seq.len() - tail)[i].len() == 1
            && pred(seq.skip(seq.len() - tail)[i][0])
        by {
            assert(seq.skip(seq.len() - tail)[i] == seq[seq.len() - tail + i]);
            assert(seq[seq.len() - tail + i].len() == 1 && pred(seq[seq.len() - tail + i][0]));
        }
        lemma_flatten_singleton_pred(seq.take(head), pred);
        lemma_flatten_singleton_pred(seq.skip(seq.len() - tail), pred);
        assert(left.len() == head);
        assert(right.len() == tail);
        assert(ret.is_subrange_of(s)) by {
            assert(s == left + ret + right);
            assert(s.subrange(left.len() as int, s.len() - right.len()) == ret);
            assert(left.len() == head);
            assert(right.len() == tail);
            assert(ret == s.subrange(head, s.len() - tail));
            lemma_seq_is_subrange_alt(s, ret);
        }
        if ret.len() > 0 {
            assert(mid_gap.first() == gap[head]);
            assert(mid_gap.last() == gap[gap.len() - tail - 1]);
            lemma_join_boundary_gaps(mid_seq, mid_gap);
            assert(!chars@.contains(ret.first())) by {
                assert(gap[head].all(gap_pred));
                assert(ret.first() == mid_gap.first()[0]);
                assert(mid_gap.first()[0] == gap[head][0]);
                assert(gap_pred(gap[head][0]));
            }
            assert(!chars@.contains(ret.last())) by {
                let last_gap = gap[gap.len() - tail - 1];
                assert(last_gap.all(gap_pred));
                assert(ret.last() == mid_gap.last().last());
                assert(mid_gap.last().last() == last_gap.last());
                assert(gap_pred(last_gap.last()));
            }
        }

        if ret.len() > 0 {
            assert(!pred(ret.first()) && !pred(ret.last()));
            assert forall |i: int| 0 <= i < left.len()
            implies #[trigger] pred(left[i]) by {}
            assert forall |i: int| 0 <= i < right.len()
            implies #[trigger] pred(right[i]) by {}
            assert(ret == (left + ret + right).skip_while(pred).rskip_while(pred)) by {
                lemma_trimmed_concat_skip_rskip(left, ret, right, pred);
            }
        } else {
            assert(false) by {
                assert(ret == join(mid_seq, mid_gap));
                lemma_join_boundary_gaps(mid_seq, mid_gap);
            }
        }
    }
}

}
