// Internal proof module for `str::trim_start_matches` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, ch; ret)]
pub broadcast proof fn lemma_str_trim_start_matches_char(s: Seq<char>, ch: char, ret: Seq<char>)
    requires
        #[trigger] str_trim_start_matches_post(s, ch, ret),
    ensures
        ret.is_suffix_of(s),
        ret.len() > 0 ==> ret.first() != ch,
        forall|i: int| 0 <= i < s.len() - ret.len()
            ==> #[trigger] s[i] == ch,
{
    axiom_char_matches_post(s, ch);
    reveal(str_trim_start_matches_post);
    let (seq, gap) = spec_matches(s, ch);
    let pred = |c: char| c == ch;
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        lemma_join_empty_gap(seq, gap);
        assert(s == seq.flatten());
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i] == seq![ch] by { assert(seq[i] =~= seq![ch]) }
        lemma_seq_flatten_same_length(seq, 1);
        assert(seq.len() == s.len());
        assert forall |i: int| 0 <= i < s.len()
        implies #[trigger] s[i] == ch by {
            assert(s[i] == s.subrange(i * 1, (i + 1) * 1)[0]);
            assert(s.subrange(i * 1, (i + 1) * 1) == seq[i]);
        }
        assert(ret.len() == 0);
        assert(ret.is_suffix_of(s));
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
        assert(ret == join(seq.skip(head), gap.skip(head)));
        assert(gap[head].len() > 0) by {
            lemma_seq_count_while_upper_bound(gap, pred2, head);
        }
        let left = seq.take(head).flatten();
        assert(s == left + ret) by {
            lemma_join_split_at(seq, gap, head);
            lemma_join_empty_gap_prefix_parts(seq, gap, head);
        }
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0])
        by { assert(seq[i] =~= seq![ch]); }
        assert forall |i: int| 0 <= i < seq.take(head).len()
        implies #[trigger] seq.take(head)[i].len() == 1 && pred(seq.take(head)[i][0])
        by {
            assert(seq.take(head)[i] == seq[i]);
            assert(seq[i].len() == 1 && pred(seq[i][0]));
        }
        lemma_flatten_singleton_pred(seq.take(head), pred);
        assert(left.len() == head);
        assert(ret.is_suffix_of(s));
        if ret.len() > 0 {
            lemma_join_first_gap(seq.skip(head), gap.skip(head));
            assert(!gap[head].contains(ch));
            assert(ret.first() == gap[head][0]);
            assert(ret.first() != ch);
            assert(!pred(ret.first()));
            assert(ret == (left + ret).skip_while(pred)) by {
                assert forall |i: int| 0 <= i < left.len()
                implies #[trigger] pred(left[i]) by {}
                lemma_trimmed_concat_skip(left, ret, pred);
            }
        } else {
            assert(false) by {
                lemma_join_uncons(seq.skip(head), gap.skip(head));
            }
        }
        assert forall |i: int| 0 <= i < s.len() - ret.len()
        implies #[trigger] s[i] == ch by {
            assert(s == left + ret);
            assert(i < left.len());
            assert(pred(left[i]));
            assert(s[i] == left[i]);
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_trim_start_matches_closure<F>(s: Seq<char>, f: F, ret: Seq<char>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_trim_start_matches_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret.is_suffix_of(s),
        ret.len() > 0 ==> call_ensures(f, (ret.first(),), false),
        forall|i: int| 0 <= i < s.len() - ret.len()
            ==> #[trigger] call_ensures(f, (s[i],), true),
{
    axiom_closure_matches_post(s, f);
    reveal(str_trim_start_matches_post);
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
        assert(ret.len() == 0);
        assert(ret.is_suffix_of(s));
        assert forall |i: int| 0 <= i < s.len() - ret.len()
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
        assert(ret == join(seq.skip(head), gap.skip(head)));
        assert(gap[head].len() > 0) by {
            lemma_seq_count_while_upper_bound(gap, pred2, head);
        }
        let left = seq.take(head).flatten();
        assert(s == left + ret) by {
            lemma_join_split_at(seq, gap, head);
            lemma_join_empty_gap_prefix_parts(seq, gap, head);
        }
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0]) by {}
        assert forall |i: int| 0 <= i < seq.take(head).len()
        implies #[trigger] seq.take(head)[i].len() == 1 && pred(seq.take(head)[i][0])
        by {
            assert(seq.take(head)[i] == seq[i]);
            assert(seq[i].len() == 1 && pred(seq[i][0]));
        }
        lemma_flatten_singleton_pred(seq.take(head), pred);
        assert(left.len() == head);
        assert(s.len() == left.len() + ret.len());
        assert(s.len() - ret.len() == left.len());
        assert(ret.is_suffix_of(s));
        if ret.len() > 0 {
            lemma_join_first_gap(seq.skip(head), gap.skip(head));
            assert(gap[head].all(gap_pred));
            assert(ret.first() == gap[head][0]);
            assert(gap_pred(gap[head][0]));
            assert(call_ensures(f, (ret.first(),), false));
            assert(!pred(ret.first())) by { lemma_call_false_not_true(f, ret.first()); }
            assert(ret == (left + ret).skip_while(pred)) by {
                assert forall |i: int| 0 <= i < left.len()
                implies #[trigger] pred(left[i]) by {}
                lemma_trimmed_concat_skip(left, ret, pred);
            }
        } else {
            assert(false) by {
                lemma_join_uncons(seq.skip(head), gap.skip(head));
            }
        }
        assert forall |i: int| 0 <= i < s.len() - ret.len()
        implies #[trigger] call_ensures(f, (s[i],), true) by {
            assert(s == left + ret);
            assert(i < left.len());
            assert(pred(left[i]));
            assert(s[i] == left[i]);
        }
    }
}

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, chars@; ret)]
pub broadcast proof fn lemma_str_trim_start_matches_chars<'b>(s: Seq<char>, chars: &'b [char], ret: Seq<char>)
    requires
        #[trigger] str_trim_start_matches_post(s, chars, ret),
    ensures
        ret.is_suffix_of(s),
        ret.len() > 0 ==> !chars@.contains(ret.first()),
        forall|i: int| 0 <= i < s.len() - ret.len()
            ==> #[trigger] chars@.contains(s[i]),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_trim_start_matches_post);
    let (seq, gap) = spec_matches(s, chars);
    let pred = |c: char| chars@.contains(c);
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
        assert(ret.len() == 0);
        assert(ret.is_suffix_of(s));
        assert forall |i: int| 0 <= i < s.len() - ret.len()
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
        assert(ret == join(seq.skip(head), gap.skip(head)));
        assert(gap[head].len() > 0) by {
            lemma_seq_count_while_upper_bound(gap, pred2, head);
        }
        let left = seq.take(head).flatten();
        assert(s == left + ret) by {
            lemma_join_split_at(seq, gap, head);
            lemma_join_empty_gap_prefix_parts(seq, gap, head);
        }
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i].len() == 1 && pred(seq[i][0]) by {}
        assert forall |i: int| 0 <= i < seq.take(head).len()
        implies #[trigger] seq.take(head)[i].len() == 1 && pred(seq.take(head)[i][0])
        by {
            assert(seq.take(head)[i] == seq[i]);
            assert(seq[i].len() == 1 && pred(seq[i][0]));
        }
        lemma_flatten_singleton_pred(seq.take(head), pred);
        assert(left.len() == head);
        assert(s.len() == left.len() + ret.len());
        assert(s.len() - ret.len() == left.len());
        assert(ret.is_suffix_of(s));
        if ret.len() > 0 {
            lemma_join_first_gap(seq.skip(head), gap.skip(head));
            assert(ret.first() == gap[head][0]);
            let gap_pred = |c: char| !chars@.contains(c);
            assert(gap[head].all(gap_pred));
            assert(gap_pred(gap[head][0]));
            assert(!chars@.contains(gap[head][0]));
            assert(!chars@.contains(ret.first()));
            assert(!pred(ret.first()));
            assert(ret == (left + ret).skip_while(pred)) by {
                assert forall |i: int| 0 <= i < left.len()
                implies #[trigger] pred(left[i]) by {}
                lemma_trimmed_concat_skip(left, ret, pred);
            }
        } else {
            assert(false) by {
                lemma_join_uncons(seq.skip(head), gap.skip(head));
            }
        }
        assert forall |i: int| 0 <= i < s.len() - ret.len()
        implies #[trigger] chars@.contains(s[i]) by {
            assert(s == left + ret);
            assert(i < left.len());
            assert(pred(left[i]));
            assert(s[i] == left[i]);
        }
    }
}

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, pat@; ret)]
pub broadcast proof fn lemma_str_trim_start_matches_string<'b>(s: Seq<char>, pat: &'b str, ret: Seq<char>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_trim_start_matches_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_trim_start_matches_post(s, pat, ret),
    ensures
        ret.is_suffix_of(s),
        ret.len() > 0 ==> !pat@.is_prefix_of(ret),
        (s.len() - ret.len()) % pat@.len() as int == 0,
        forall|i: int| 0 <= i < s.len() - ret.len() && i % pat@.len() as int == 0
            ==> #[trigger] s.subrange(i, i + pat@.len()) == pat@,
{
    axiom_string_matches_post(s, pat);
    reveal(str_trim_start_matches_post);
    let (seq, gap) = spec_matches(s, pat);
    let plen = pat@.len() as int;
    if gap.all(|ss: Seq<char>| ss.len() == 0) {
        lemma_join_empty_gap(seq, gap);
        assert(s == seq.flatten());
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i] =~= pat@ by {}
        lemma_flatten_same_seq(seq, pat@);
        assert(s.len() == seq.len() * pat@.len());
        assert(ret.len() == 0);
        assert(ret.is_suffix_of(s));
        assert((s.len() - ret.len()) % pat@.len() as int == 0) by {
            lemma_mod_multiples_basic(seq.len() as int, plen);
        }
        assert forall|i: int| 0 <= i < s.len() - ret.len() && i % pat@.len() as int == 0
        implies #[trigger] s.subrange(i, i + pat@.len()) == pat@ by {
            let block = i / plen;
            lemma_trim_string_flatten_block(s, seq, pat@, i);
            lemma_trim_string_block_index(i, seq.len() as int, plen);
            assert(i == block * plen);
            assert(0 <= block < seq.len());
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
        assert(ret == join(seq.skip(head), gap.skip(head)));
        assert(gap[head].len() > 0) by {
            lemma_seq_count_while_upper_bound(gap, pred2, head);
        }
        let left = seq.take(head).flatten();
        assert(s == left + ret) by {
            lemma_join_split_at(seq, gap, head);
            lemma_join_empty_gap_prefix_parts(seq, gap, head);
        }
        assert forall |i: int| 0 <= i < seq.len()
        implies #[trigger] seq[i] =~= pat@ by {}
        assert forall |i: int| 0 <= i < seq.take(head).len()
        implies #[trigger] seq.take(head)[i] =~= pat@ by {
            assert(seq.take(head)[i] == seq[i]);
        }
        lemma_flatten_same_seq(seq.take(head), pat@);
        assert(left.len() == head * pat@.len());
        assert(ret.is_suffix_of(s));
        if ret.len() > 0 {
            lemma_join_first_gap(seq.skip(head), gap.skip(head));
            assert(ret.first() == gap[head][0]);
            assert(!pat@.is_prefix_of(ret)) by {
                assert(gap.skip(head).first() == gap[head]);
                assert(gap.skip(head).first().len() > 0);
                assert(ret.first() == gap.skip(head).first().first());
                if head < seq.len() {
                    assert(!pat@.is_prefix_of(gap[head] + pat@));
                    assert(seq.skip(head)[0] == seq[head]);
                    assert(seq[head] =~= pat@);
                    lemma_join_uncons(seq.skip(head), gap.skip(head));
                    lemma_string_join_not_prefix(seq.skip(head), gap.skip(head), pat@);
                } else {
                    assert(head == seq.len());
                    assert(gap[head] == gap.last());
                    assert(!pat@.is_subrange_of(gap.last()));
                    lemma_seq_is_subrange_alt(gap[head], pat@);
                    assert(!pat@.is_prefix_of(gap[head]));
                    assert(seq.skip(head).len() == 0);
                    assert(gap.skip(head).len() == 1);
                    assert(ret == gap[head]);
                }
            }
        } else {
            assert(false) by {
                lemma_join_uncons(seq.skip(head), gap.skip(head));
            }
        }
        assert((s.len() - ret.len()) % pat@.len() as int == 0) by {
            assert(s.len() == left.len() + ret.len());
            assert(s.len() - ret.len() == left.len());
            lemma_mod_multiples_basic(head, plen);
        }
        assert forall|i: int| 0 <= i < s.len() - ret.len() && i % pat@.len() as int == 0
        implies #[trigger] s.subrange(i, i + pat@.len()) == pat@ by {
            let block = i / plen;
            lemma_trim_string_flatten_block(left, seq.take(head), pat@, i);
            lemma_trim_string_block_index(i, head, plen);
            assert(i == block * plen);
            assert(0 <= block < head);
            lemma_concat_left_subrange(left, ret, i, i + pat@.len());
            assert(s.subrange(i, i + pat@.len()) == left.subrange(i, i + pat@.len()));
        }
    }
}

}
