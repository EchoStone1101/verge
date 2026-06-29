// Internal proof module for `str::matches` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
pub broadcast proof fn lemma_str_matches_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_matches_iter_post(s, ch, iter_seq),
    ensures
        // matches all match `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@ == seq![ch],
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| c == ch),
{
    axiom_char_matches_post(s, ch);
    reveal(str_matches_iter_post);
    let (seq, gap) = spec_matches(s, ch);
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
    lemma_str_matches_count(seq, gap, pred);
}

//~doc-skip
pub broadcast proof fn lemma_str_matches_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_matches_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // matches all match `f`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@.len() == 1
                && #[trigger] call_ensures(f, (iter_seq[i]@[0],), true),
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true)),
{
    axiom_closure_matches_post(s, f);
    reveal(str_matches_iter_post);
    let (seq, gap) = spec_matches(s, f);
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
    lemma_str_matches_count(seq, gap, pred);
}

//~doc-skip
pub broadcast proof fn lemma_str_matches_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_matches_iter_post(s, chars, iter_seq),
    ensures
        // matches all match `chars`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> #[trigger] iter_seq[i]@.len() == 1
                && #[trigger] chars@.contains(iter_seq[i]@[0]),
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| chars@.contains(c)),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_matches_iter_post);
    let (seq, gap) = spec_matches(s, chars);
    let pred = |c: char| chars@.contains(c);
    let gap_pred = |c: char| !chars@.contains(c);
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
    lemma_str_matches_count(seq, gap, pred);
}

//~doc-skip
pub broadcast proof fn lemma_str_matches_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_matches_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_matches_iter_post(s, pat, iter_seq),
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
                        ==> (!pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@))
            &&& !pat@.is_subrange_of(gap.last())
            &&& s == iter_seq.map(|i: int, ss: &'a str| gap[i] + ss@).flatten() + gap.last()
        },
{
    axiom_string_matches_post(s, pat);
    reveal(str_matches_iter_post);
    let (seq, gap) = spec_matches(s, pat);
    // #1
    assert forall |i: int| 0 <= i < iter_seq.len()
    implies #[trigger] iter_seq[i]@ == pat@
    by { assert(iter_seq[i]@ =~= pat@) }
    // #2
    assert(iter_seq.len() == 0 <==> !pat@.is_subrange_of(s)) by {
        assert(iter_seq.len() == seq.len());
        reveal(str_contains_post);
        lemma_str_contains_string(s, pat, seq.len() > 0);
    }
    // #3
    assert(gap.len() == iter_seq.len() + 1);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1 && gap[i].len() > 0
    implies !pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@)
    by {}
    assert(s == iter_seq.map(|i: int, ss: &'a str| gap[i] + ss@).flatten() + gap.last()) by {
        lemma_join_alt(seq, gap);
        let s1 = iter_seq.map(|i: int, ss: &'a str| gap[i] + ss@);
        let s2 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
        assert_seqs_equal!(s1 == s2);
    }
}

}
