// Internal proof module for `str::rmatches` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, ch; iter_seq.map_values(|s: &str| s@))]
pub broadcast proof fn lemma_str_rmatches_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rmatches_iter_post(s, ch, iter_seq),
    ensures
        // matches all match `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@ == seq![ch],
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| c == ch),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rmatches_iter_post);
    let (seq, gap) = spec_rmatches(s, ch);
    let pred = |c: char| c == ch;
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c)) by {
        assert forall |j: int| 0 <= j < gap[i].len()
            implies !pred(gap[i][j]) by {
            if pred(gap[i][j]) {
                assert(gap[i].contains(ch));
            }
        }
    }
    assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0]) by {
        assert(seq[i] =~= seq![ch]);
    }
    lemma_str_rmatches_count(seq, gap, pred);
}

//~doc-skip
pub broadcast proof fn lemma_str_rmatches_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rmatches_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // matches all match `f`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@.len() == 1
                && #[trigger] call_ensures(f, (iter_seq[i]@[0],), true),
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true)),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rmatches_iter_post);
    let (seq, gap) = spec_rmatches(s, f);
    let pred = |c: char| call_ensures(f, (c,), true);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c)) by {
        let neg_pred = |c: char| call_ensures(f, (c,), false);
        assert(gap[i].all(neg_pred));
        assert forall |j: int| 0 <= j < gap[i].len()
            implies !pred(gap[i][j]) by {
            assert(neg_pred(gap[i][j]));
            if pred(gap[i][j]) {
                assert(call_ensures(f, (gap[i][j],), false));
                assert(call_ensures(f, (gap[i][j],), true));
            }
        }
    }
    assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0]) by {
    }
    lemma_str_rmatches_count(seq, gap, pred);
}

//~doc-skip
pub broadcast proof fn lemma_str_rmatches_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rmatches_iter_post(s, chars, iter_seq),
    ensures
        // matches all match `chars`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@.len() == 1
                && #[trigger] chars@.contains(iter_seq[i]@[0]),
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| chars@.contains(c)),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rmatches_iter_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let pred = |c: char| chars@.contains(c);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c)) by {
        let neg_pred = |c: char| !chars@.contains(c);
        assert(gap[i].all(neg_pred));
        assert forall |j: int| 0 <= j < gap[i].len()
            implies !pred(gap[i][j]) by {
            assert(neg_pred(gap[i][j]));
        }
    }
    assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0]) by {
    }
    lemma_str_rmatches_count(seq, gap, pred);
}

//~doc-skip
pub broadcast proof fn lemma_str_rmatches_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_rmatches_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_rmatches_iter_post(s, pat, iter_seq),
    ensures
        // matches all match `pat`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@ == pat@,
        // matches are empty if none matches `pat`
        iter_seq.len() == 0 <==> !pat@.is_subrange_of(s),
        // delimiters and splits make up the original string
        exists |gap: Seq<Seq<char>>| {
            &&& #[trigger] gap.len() == iter_seq.len() + 1
            &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1
                    ==> gap[i].len() > 0
                        ==> (!pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i]))
            &&& !pat@.is_subrange_of(gap.last())
            &&& s == gap.last() + iter_seq.map(|i: int, ss: &'a str| ss@ + gap[i]).reverse().flatten()
        },
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rmatches_iter_post);
    let (seq, gap) = spec_rmatches(s, pat);
    // #1
    assert forall |i: int| 0 <= i < iter_seq.len()
    implies #[trigger] iter_seq[i]@ == pat@
    by {
        assert(iter_seq[i]@ == seq[i]);
        assert(seq[i] =~= pat@);
    }
    // #2
    assert(iter_seq.len() == 0 <==> !pat@.is_subrange_of(s)) by {
        assert(iter_seq.len() == seq.len());
        if iter_seq.len() == 0 {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(s == gap.last());
            assert(!pat@.is_subrange_of(gap.last()));
        }
        if !pat@.is_subrange_of(s) {
            assert_by_contradiction!(iter_seq.len() == 0, {
                assert(seq.len() > 0);
                assert(seq[0] == pat@);
                lemma_rjoin_uncons(seq, gap);
                let rest = rjoin(seq.skip(1), gap.skip(1));
                lemma_concat_associative(rest, seq[0], gap[0]);
                assert(s == rest + (seq[0] + gap[0]));
                assert(seq[0] =~= s.subrange(rest.len() as int, rest.len() + seq[0].len() as int));
                assert(seq[0].is_subrange_of(s)) by {
                    assert(exists |i: int| 0 <= i <= s.len() - seq[0].len()
                        && seq[0] =~= #[trigger] s.subrange(i, i + seq[0].len()));
                }
                assert(pat@.is_subrange_of(s));
            });
        }
    }
    // #3
    assert(gap.len() == iter_seq.len() + 1);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1 && gap[i].len() > 0
    implies !pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i])
    by {}
    assert(s == gap.last() + iter_seq.map(|i: int, ss: &'a str| ss@ + gap[i]).reverse().flatten()) by {
        lemma_rjoin_alt_for_matches(seq, gap);
        let s1 = iter_seq.map(|i: int, ss: &'a str| ss@ + gap[i]);
        let s2 = seq.map(|i: int, ss: Seq<char>| ss + gap[i]);
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i]@ == seq[i]);
            assert(seq[i] == pat@);
        });
        assert(s1.reverse() == s2.reverse());
        s1.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        assert(s2.reverse().flatten_alt() == s1.reverse().flatten());
    }
}

}
