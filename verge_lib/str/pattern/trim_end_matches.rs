// Internal proof module for `str::trim_end_matches` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, ch; ret)]
pub broadcast proof fn lemma_str_trim_end_matches_char(s: Seq<char>, ch: char, ret: Seq<char>)
    requires
        #[trigger] str_trim_end_matches_post(s, ch, ret),
    ensures
        ret.is_prefix_of(s),
        ret.len() > 0 ==> ret.last() != ch,
        forall|i: int| ret.len() <= i < s.len()
            ==> #[trigger] s[i] == ch,
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_trim_end_matches_post);
    let (seq, gap) = spec_rmatches(s, ch);
    let pred = |c: char| c == ch;
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        lemma_rjoin_empty_gap(seq, gap);
        assert(s == seq.reverse().flatten_alt());
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0])
        by { assert(seq[i] =~= seq![ch]); }
        let rseq = seq.reverse();
        assert forall |i: int| 0 <= i < rseq.len()
        implies #[trigger] rseq[i].len() == 1 && pred(rseq[i][0]) by {
            assert(rseq[i] == seq[seq.len() - 1 - i]);
        }
        lemma_flatten_alt_singleton_pred(rseq, pred);
        assert(seq.len() == s.len());
        assert forall |i: int| 0 <= i < s.len()
        implies #[trigger] s[i] == ch by {
            assert(s[i] == rseq.flatten_alt()[i]);
            assert(pred(rseq.flatten_alt()[i]));
            assert(pred(s[i]));
        }
        assert(ret.len() == 0);
        assert(ret.is_prefix_of(s));
    } else {
        let pred2 = |ss: Seq<char>| ss.len() == 0;
        let head = gap.count_while(pred2) as int;
        lemma_seq_take_while_ensures(gap, pred2);
        assert(head < gap.len()) by {
            let k = choose|i: int| 0 <= i < gap.len() && !(#[trigger] pred2(gap[i]));
            lemma_seq_count_while_upper_bound(gap, pred2, k);
        }
        assert forall |i: int| 0 <= i < head
        implies #[trigger] gap[i].len() == 0 by {
            assert(gap.take_while(pred2)[i] == gap[i]);
            assert(pred2(gap.take_while(pred2)[i]));
        }
        assert(ret == rjoin(seq.skip(head), gap.skip(head)));
        assert(gap[head].len() > 0) by {
            lemma_seq_count_while_upper_bound(gap, pred2, head);
        }
        let right = seq.take(head).map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().flatten_alt();
        assert(s == ret + right) by {
            lemma_rjoin_split_at(seq, gap, head);
            lemma_rjoin_empty_gap_prefix_parts(seq, gap, head);
        }
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0])
        by { assert(seq[i] =~= seq![ch]); }
        assert forall |i: int| 0 <= i < seq.take(head).len()
        implies #[trigger] seq.take(head)[i].len() == 1 && pred(seq.take(head)[i][0]) by {
            assert(seq.take(head)[i] == seq[i]);
        }
        lemma_flatten_alt_singleton_pred(seq.take(head), pred);
        lemma_rjoin_empty_gap_prefix_parts_pred(seq, gap, head, pred);
        assert(right.len() == head);
        assert(ret.is_prefix_of(s));
        if ret.len() > 0 {
            lemma_rjoin_last_first_gap(seq.skip(head), gap.skip(head));
            assert(!gap[head].contains(ch));
            assert(ret.last() == gap[head].last());
            assert(ret.last() != ch);
            assert(!pred(ret.last()));
            assert(ret == (ret + right).rskip_while(pred)) by {
                assert forall |i: int| 0 <= i < right.len()
                implies #[trigger] pred(right[i]) by {}
                lemma_trimmed_concat_rskip(ret, right, pred);
            }
        } else {
            assert(false) by {
                lemma_rjoin_uncons(seq.skip(head), gap.skip(head));
            }
        }
        assert forall |i: int| ret.len() <= i < s.len()
        implies #[trigger] s[i] == ch by {
            assert(s == ret + right);
            assert(i - ret.len() < right.len());
            assert(pred(right[i - ret.len()]));
            assert(s[i] == right[i - ret.len()]);
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_trim_end_matches_closure<F>(s: Seq<char>, f: F, ret: Seq<char>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_trim_end_matches_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret.is_prefix_of(s),
        ret.len() > 0 ==> call_ensures(f, (ret.last(),), false),
        forall|i: int| ret.len() <= i < s.len()
            ==> #[trigger] call_ensures(f, (s[i],), true),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_trim_end_matches_post);
    let (seq, gap) = spec_rmatches(s, f);
    let pred = |c: char| call_ensures(f, (c,), true);
    let gap_pred = |c: char| call_ensures(f, (c,), false);
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        lemma_rjoin_empty_gap(seq, gap);
        assert(s == seq.reverse().flatten_alt());
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0]) by {}
        let rseq = seq.reverse();
        assert forall |i: int| 0 <= i < rseq.len()
        implies #[trigger] rseq[i].len() == 1 && pred(rseq[i][0]) by {
            assert(rseq[i] == seq[seq.len() - 1 - i]);
        }
        lemma_flatten_alt_singleton_pred(rseq, pred);
        assert(seq.len() == s.len());
        assert forall |i: int| 0 <= i < s.len()
        implies #[trigger] pred(s[i]) by {
            assert(s[i] == rseq.flatten_alt()[i]);
            assert(pred(rseq.flatten_alt()[i]));
        }
        assert(ret.len() == 0);
        assert(ret.is_prefix_of(s));
        assert forall |i: int| ret.len() <= i < s.len()
        implies #[trigger] call_ensures(f, (s[i],), true) by {
            assert(pred(s[i]));
        }
    } else {
        let pred2 = |ss: Seq<char>| ss.len() == 0;
        let head = gap.count_while(pred2) as int;
        lemma_seq_take_while_ensures(gap, pred2);
        assert(head < gap.len()) by {
            let k = choose|i: int| 0 <= i < gap.len() && !(#[trigger] pred2(gap[i]));
            lemma_seq_count_while_upper_bound(gap, pred2, k);
        }
        assert forall |i: int| 0 <= i < head
        implies #[trigger] gap[i].len() == 0 by {
            assert(gap.take_while(pred2)[i] == gap[i]);
            assert(pred2(gap.take_while(pred2)[i]));
        }
        assert(ret == rjoin(seq.skip(head), gap.skip(head)));
        assert(gap[head].len() > 0) by {
            lemma_seq_count_while_upper_bound(gap, pred2, head);
        }
        let right = seq.take(head).map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().flatten_alt();
        assert(s == ret + right) by {
            lemma_rjoin_split_at(seq, gap, head);
            lemma_rjoin_empty_gap_prefix_parts(seq, gap, head);
        }
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0]) by {}
        assert forall |i: int| 0 <= i < seq.take(head).len()
        implies #[trigger] seq.take(head)[i].len() == 1 && pred(seq.take(head)[i][0]) by {
            assert(seq.take(head)[i] == seq[i]);
        }
        lemma_flatten_alt_singleton_pred(seq.take(head), pred);
        lemma_rjoin_empty_gap_prefix_parts_pred(seq, gap, head, pred);
        assert(right.len() == head);
        assert(s.len() == ret.len() + right.len());
        assert(s.len() - ret.len() == right.len());
        assert(ret.is_prefix_of(s));
        if ret.len() > 0 {
            lemma_rjoin_last_first_gap(seq.skip(head), gap.skip(head));
            assert(gap[head].all(gap_pred));
            assert(ret.last() == gap[head].last());
            assert(gap_pred(gap[head].last()));
            assert(call_ensures(f, (ret.last(),), false));
            assert(!pred(ret.last())) by { lemma_call_false_not_true(f, ret.last()); }
            assert(ret == (ret + right).rskip_while(pred)) by {
                assert forall |i: int| 0 <= i < right.len()
                implies #[trigger] pred(right[i]) by {}
                lemma_trimmed_concat_rskip(ret, right, pred);
            }
        } else {
            assert(false) by {
                lemma_rjoin_uncons(seq.skip(head), gap.skip(head));
            }
        }
        assert forall |i: int| ret.len() <= i < s.len()
        implies #[trigger] call_ensures(f, (s[i],), true) by {
            assert(s == ret + right);
            assert(i - ret.len() < right.len());
            assert(pred(right[i - ret.len()]));
            assert(s[i] == right[i - ret.len()]);
        }
    }
}

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, chars@; ret)]
pub broadcast proof fn lemma_str_trim_end_matches_chars<'b>(s: Seq<char>, chars: &'b [char], ret: Seq<char>)
    requires
        #[trigger] str_trim_end_matches_post(s, chars, ret),
    ensures
        ret.is_prefix_of(s),
        ret.len() > 0 ==> !chars@.contains(ret.last()),
        forall|i: int| ret.len() <= i < s.len()
            ==> #[trigger] chars@.contains(s[i]),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_trim_end_matches_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let pred = |c: char| chars@.contains(c);
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        lemma_rjoin_empty_gap(seq, gap);
        assert(s == seq.reverse().flatten_alt());
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0]) by {}
        let rseq = seq.reverse();
        assert forall |i: int| 0 <= i < rseq.len()
        implies #[trigger] rseq[i].len() == 1 && pred(rseq[i][0]) by {
            assert(rseq[i] == seq[seq.len() - 1 - i]);
        }
        lemma_flatten_alt_singleton_pred(rseq, pred);
        assert(seq.len() == s.len());
        assert forall |i: int| 0 <= i < s.len()
        implies #[trigger] pred(s[i]) by {
            assert(s[i] == rseq.flatten_alt()[i]);
            assert(pred(rseq.flatten_alt()[i]));
        }
        assert(ret.len() == 0);
        assert(ret.is_prefix_of(s));
        assert forall |i: int| ret.len() <= i < s.len()
        implies #[trigger] chars@.contains(s[i]) by {
            assert(pred(s[i]));
        }
    } else {
        let pred2 = |ss: Seq<char>| ss.len() == 0;
        let head = gap.count_while(pred2) as int;
        lemma_seq_take_while_ensures(gap, pred2);
        assert(head < gap.len()) by {
            let k = choose|i: int| 0 <= i < gap.len() && !(#[trigger] pred2(gap[i]));
            lemma_seq_count_while_upper_bound(gap, pred2, k);
        }
        assert forall |i: int| 0 <= i < head
        implies #[trigger] gap[i].len() == 0 by {
            assert(gap.take_while(pred2)[i] == gap[i]);
            assert(pred2(gap.take_while(pred2)[i]));
        }
        assert(ret == rjoin(seq.skip(head), gap.skip(head)));
        assert(gap[head].len() > 0) by {
            lemma_seq_count_while_upper_bound(gap, pred2, head);
        }
        let right = seq.take(head).map(|i: int, ss: Seq<char>| ss + gap[i]).reverse().flatten_alt();
        assert(s == ret + right) by {
            lemma_rjoin_split_at(seq, gap, head);
            lemma_rjoin_empty_gap_prefix_parts(seq, gap, head);
        }
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0]) by {}
        assert forall |i: int| 0 <= i < seq.take(head).len()
        implies #[trigger] seq.take(head)[i].len() == 1 && pred(seq.take(head)[i][0]) by {
            assert(seq.take(head)[i] == seq[i]);
        }
        lemma_flatten_alt_singleton_pred(seq.take(head), pred);
        lemma_rjoin_empty_gap_prefix_parts_pred(seq, gap, head, pred);
        assert(right.len() == head);
        assert(s.len() == ret.len() + right.len());
        assert(s.len() - ret.len() == right.len());
        assert(ret.is_prefix_of(s));
        if ret.len() > 0 {
            lemma_rjoin_last_first_gap(seq.skip(head), gap.skip(head));
            assert(ret.last() == gap[head].last());
            let gap_pred = |c: char| !chars@.contains(c);
            assert(gap[head].all(gap_pred));
            assert(gap_pred(gap[head].last()));
            assert(!chars@.contains(gap[head].last()));
            assert(!chars@.contains(ret.last()));
            assert(!pred(ret.last()));
            assert(ret == (ret + right).rskip_while(pred)) by {
                assert forall |i: int| 0 <= i < right.len()
                implies #[trigger] pred(right[i]) by {}
                lemma_trimmed_concat_rskip(ret, right, pred);
            }
        } else {
            assert(false) by {
                lemma_rjoin_uncons(seq.skip(head), gap.skip(head));
            }
        }
        assert forall |i: int| ret.len() <= i < s.len()
        implies #[trigger] chars@.contains(s[i]) by {
            assert(s == ret + right);
            assert(i - ret.len() < right.len());
            assert(pred(right[i - ret.len()]));
            assert(s[i] == right[i - ret.len()]);
        }
    }
}

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, pat@; ret)]
pub broadcast proof fn lemma_str_trim_end_matches_string<'b>(s: Seq<char>, pat: &'b str, ret: Seq<char>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_trim_end_matches_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_trim_end_matches_post(s, pat, ret),
    ensures
        ret.is_prefix_of(s),
        ret.len() > 0 ==> !pat@.is_suffix_of(ret),
        (s.len() - ret.len()) % pat@.len() as int == 0,
        forall|i: int| 0 <= i < s.len() - ret.len() && i % pat@.len() as int == 0
            ==> #[trigger] s.subrange(ret.len() + i, ret.len() + i + pat@.len()) == pat@,
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_trim_end_matches_post);
    let (seq, gap) = spec_rmatches(s, pat);
    let plen = pat@.len() as int;
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        lemma_rjoin_empty_gap(seq, gap);
        assert(s == seq.reverse().flatten_alt());
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i] =~= pat@ by {}
        assert forall |i: int| 0 <= i < seq.reverse().len()
        implies #[trigger] seq.reverse()[i] =~= pat@ by {
            assert(seq.reverse()[i] == seq[seq.len() - 1 - i]);
        }
        lemma_flatten_alt_same_seq(seq.reverse(), pat@);
        seq.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        assert(s.len() == seq.reverse().len() * pat@.len());
        assert(seq.reverse().len() == seq.len());
        assert(ret.len() == 0);
        assert(ret.is_prefix_of(s));
        assert((s.len() - ret.len()) % pat@.len() as int == 0) by {
            lemma_mod_multiples_basic(seq.len() as int, plen);
        }
        assert forall|i: int| 0 <= i < s.len() - ret.len() && i % pat@.len() as int == 0
        implies #[trigger] s.subrange(ret.len() + i, ret.len() + i + pat@.len()) == pat@ by {
            assert(ret.len() == 0);
            assert(s == seq.reverse().flatten());
            lemma_trim_string_flatten_block(s, seq.reverse(), pat@, i);
        }
    } else {
        let pred2 = |ss: Seq<char>| ss.len() == 0;
        let head = gap.count_while(pred2) as int;
        lemma_seq_take_while_ensures(gap, pred2);
        assert(head < gap.len()) by {
            let k = choose|i: int| 0 <= i < gap.len() && !(#[trigger] pred2(gap[i]));
            lemma_seq_count_while_upper_bound(gap, pred2, k);
        }
        assert forall |i: int| 0 <= i < head
        implies #[trigger] gap[i].len() == 0 by {
            assert(gap.take_while(pred2)[i] == gap[i]);
            assert(pred2(gap.take_while(pred2)[i]));
        }
        assert(ret == rjoin(seq.skip(head), gap.skip(head)));
        assert(gap[head].len() > 0) by {
            lemma_seq_count_while_upper_bound(gap, pred2, head);
        }
        let right = seq.take(head).reverse().flatten_alt();
        assert(s == ret + right) by {
            lemma_rjoin_split_at(seq, gap, head);
            lemma_rjoin_empty_gap_prefix_parts(seq, gap, head);
        }
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i] =~= pat@ by {}
        assert forall |i: int| 0 <= i < seq.take(head).reverse().len()
        implies #[trigger] seq.take(head).reverse()[i] =~= pat@ by {
            assert(seq.take(head).reverse()[i] == seq.take(head)[seq.take(head).len() - 1 - i]);
            assert(seq.take(head)[seq.take(head).len() - 1 - i] == seq[seq.take(head).len() - 1 - i]);
        }
        lemma_flatten_alt_same_seq(seq.take(head).reverse(), pat@);
        seq.take(head).reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        assert(right.len() == head * pat@.len());
        assert(ret.is_prefix_of(s));
        if ret.len() > 0 {
            lemma_rjoin_last_first_gap(seq.skip(head), gap.skip(head));
            assert(ret.last() == gap[head].last());
            assert(!pat@.is_suffix_of(ret)) by {
                assert(gap.skip(head).first() == gap[head]);
                assert(gap.skip(head).first().len() > 0);
                assert(ret.last() == gap.skip(head).first().last());
                if head < seq.len() {
                    assert(!pat@.is_suffix_of(pat@ + gap[head]));
                    assert(seq.skip(head)[0] == seq[head]);
                    assert(seq[head] =~= pat@);
                    lemma_rjoin_uncons(seq.skip(head), gap.skip(head));
                    lemma_string_rjoin_not_suffix(seq.skip(head), gap.skip(head), pat@);
                } else {
                    assert(head == seq.len());
                    assert(gap[head] == gap.last());
                    assert(!pat@.is_subrange_of(gap.last()));
                    lemma_seq_is_subrange_alt(gap[head], pat@);
                    assert(!pat@.is_suffix_of(gap[head]));
                    assert(seq.skip(head).len() == 0);
                    assert(gap.skip(head).len() == 1);
                    assert(ret == gap[head]);
                }
            }
        } else {
            assert(false) by {
                lemma_rjoin_uncons(seq.skip(head), gap.skip(head));
            }
        }
        assert((s.len() - ret.len()) % pat@.len() as int == 0) by {
            assert(s.len() == ret.len() + right.len());
            assert(s.len() - ret.len() == right.len());
            lemma_mod_multiples_basic(head, plen);
        }
        assert forall|i: int| 0 <= i < s.len() - ret.len() && i % pat@.len() as int == 0
        implies #[trigger] s.subrange(ret.len() + i, ret.len() + i + pat@.len()) == pat@ by {
            assert(right == seq.take(head).reverse().flatten());
            lemma_trim_string_flatten_block(right, seq.take(head).reverse(), pat@, i);
            lemma_concat_right_subrange(ret, right, i, i + pat@.len());
            assert(s.subrange(ret.len() + i, ret.len() + i + pat@.len()) == right.subrange(i, i + pat@.len()));
        }
    }
}

}
