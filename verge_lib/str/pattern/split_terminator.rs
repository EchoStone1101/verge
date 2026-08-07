// Internal proof module for `str::split_terminator` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, ch; iter_seq.map_values(|s: &str| s@))]
pub broadcast proof fn lemma_str_split_terminator_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_terminator_iter_post(s, ch, iter_seq),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // splits cannot contain `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> !(#[trigger] iter_seq[i]@.contains(ch)),
        // delimiters and splits make up the original string
        s.len() > 0 && s.last() == ch
            ==> s == iter_seq.map_values(|ss: &'a str| ss@.push(ch)).flatten(),
        s.len() > 0 && s.last() != ch
            ==> s == iter_seq.drop_last().map_values(|ss: &'a str| ss@.push(ch)).flatten() + iter_seq.last()@,
{
    axiom_char_matches_post(s, ch);
    reveal(str_split_terminator_iter_post);
    let (seq, gap) = spec_matches(s, ch);
    // #1
    if s.len() == 0 {
        lemma_join_alt(seq, gap);
        assert(gap.last().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            assert(seq[0] =~= seq![ch]);
            assert(s[gap.first().len() as int] == ch);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        assert(seq.len() == 0);
    }
    // #2
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < seq.len()
    implies !(#[trigger] iter_seq[i]@.contains(ch))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(!gap[i].contains(ch));
    }
    if iter_seq.len() == seq.len() + 1 {
        iter_seq.last()@ == gap.last();
        assert(!iter_seq.last()@.contains(ch));
    }
    // #3
    if s.len() == 0 { return }
    assert(s.last() == ch <==> gap.last().len() == 0) by {
        lemma_join_alt(seq, gap);
        if gap.last().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
            s1.lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.last() =~= seq![ch]);
            assert(s.last() == seq.last().last());
            assert(s.last() == ch);
        }
        if s.last() == ch {
            assert_by_contradiction!(gap.last().len() == 0, {
                assert(s.last() == gap.last().last());
                assert(!gap.last().contains(ch));
            });
        }
    }
    calc!{
        (==)
        s; {}
        join(seq, gap); { lemma_join_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
    if s.last() == ch {
        let s2 = iter_seq.map_values(|ss: &'a str| ss@.push(ch));
        assert(iter_seq.len() == seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            assert(seq[i] =~= seq![ch]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten();
        }
    } else {
        let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@.push(ch));
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last());
        assert_seqs_equal!(s1 == s2, i => {
            assert(seq[i] =~= seq![ch]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten() + iter_seq.last()@;
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_split_terminator_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_split_terminator_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // splits cannot match `f`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] call_ensures(f, (delim[i],), true)
            &&& s.len() > 0 && call_ensures(f, (s.last(),), true)
                    ==> {
                        &&& delim.len() == iter_seq.len()
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten()
                    }
            &&& s.len() > 0 && call_ensures(f, (s.last(),), false)
                    ==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten() + iter_seq.last()@
                    }
        },
{
    axiom_closure_matches_post(s, f);
    reveal(str_split_terminator_iter_post);
    let (seq, gap) = spec_matches(s, f);
    let gap_pred = |c: char| call_ensures(f, (c,), false);
    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);

    // #1
    if s.len() == 0 {
        lemma_join_alt(seq, gap);
        assert(gap.last().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            assert(seq[0].len() == 1 && call_ensures(f, (seq[0][0],), true));
            assert(s[gap.first().len() as int] == seq[0][0]);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        assert(seq.len() == 0);
    }
    // #2
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < seq.len()
    implies (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@ == gap.last());
        assert(iter_seq.last()@.all(|c: char| call_ensures(f, (c,), false)));
    }
    // #3
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] call_ensures(f, (delim[i],), true)
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
    }
    if s.len() == 0 { return }
    assert(call_ensures(f, (s.last(),), true) <==> gap.last().len() == 0) by {
        lemma_join_alt(seq, gap);
        if gap.last().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
            s1.lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.last().len() == 1 && call_ensures(f, (seq.last()[0],), true));
            assert(s.last() == seq.last()[0]);
            assert(call_ensures(f, (s.last(),), true));
        }
        if call_ensures(f, (s.last(),), true) {
            assert_by_contradiction!(gap.last().len() == 0, {
                assert(s.last() == gap.last().last());
                assert(gap.last().all(gap_pred));
                assert(gap_pred(gap.last()[gap.last().len() - 1]));
                assert(call_ensures(f, (gap.last()[gap.last().len() - 1],), false));
                gap.last().lemma_index_contains(gap.last().len() - 1);
                assert(gap.last().contains(gap.last().last()));
                assert(call_ensures(f, (gap.last().last(),), false));
                assert(call_ensures(f, (gap.last().last(),), true));
            });
        }
    }
    calc!{
        (==)
        s; {}
        join(seq, gap); { lemma_join_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
    if call_ensures(f, (s.last(),), true) {
        let s2 = iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(iter_seq.len() == seq.len());
        assert(delim.len() == iter_seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i].push(d) == gap[i] + seq![d]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten();
        }
    } else {
        let s2 = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last());
        assert(delim.len() == iter_seq.len() - 1);
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i].push(d) == gap[i] + seq![d]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten() + iter_seq.last()@;
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_split_terminator_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_terminator_iter_post(s, chars, iter_seq),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // splits cannot match `chars`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] chars@.contains(delim[i])
            &&& s.len() > 0 && chars@.contains(s.last())
                    ==> {
                        &&& delim.len() == iter_seq.len()
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten()
                    }
            &&& s.len() > 0 && !chars@.contains(s.last())
                    ==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i])).flatten() + iter_seq.last()@
                    }
        },
{
    axiom_chars_matches_post(s, chars);
    reveal(str_split_terminator_iter_post);
    let (seq, gap) = spec_matches(s, chars);
    let gap_pred = |c: char| !chars@.contains(c);
    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);

    // #1
    if s.len() == 0 {
        lemma_join_alt(seq, gap);
        assert(gap.last().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            assert(seq[0].len() == 1 && chars@.contains(seq[0][0]));
            assert(s[gap.first().len() as int] == seq[0][0]);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        assert(seq.len() == 0);
    }
    // #2
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < seq.len()
    implies (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@ == gap.last());
        assert(iter_seq.last()@.all(|c: char| !chars@.contains(c)));
    }
    // #3
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] chars@.contains(delim[i])
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
    }
    if s.len() == 0 { return }
    assert(chars@.contains(s.last()) <==> gap.last().len() == 0) by {
        lemma_join_alt(seq, gap);
        if gap.last().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
            s1.lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.last().len() == 1 && chars@.contains(seq.last()[0]));
            assert(s.last() == seq.last()[0]);
            assert(chars@.contains(s.last()));
        }
        if chars@.contains(s.last()) {
            assert_by_contradiction!(gap.last().len() == 0, {
                assert(s.last() == gap.last().last());
                assert(gap.last().all(gap_pred));
                assert(gap_pred(gap.last()[gap.last().len() - 1]));
                assert(!chars@.contains(gap.last()[gap.last().len() - 1]));
                gap.last().lemma_index_contains(gap.last().len() - 1);
                assert(gap.last().contains(gap.last().last()));
                assert(!chars@.contains(gap.last().last()));
                assert(chars@.contains(gap.last().last()));
            });
        }
    }
    calc!{
        (==)
        s; {}
        join(seq, gap); { lemma_join_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
    if chars@.contains(s.last()) {
        let s2 = iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(iter_seq.len() == seq.len());
        assert(delim.len() == iter_seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i].push(d) == gap[i] + seq![d]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten();
        }
    } else {
        let s2 = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last());
        assert(delim.len() == iter_seq.len() - 1);
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i].push(d) == gap[i] + seq![d]);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten() + iter_seq.last()@;
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_split_terminator_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_split_terminator_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_split_terminator_iter_post(s, pat, iter_seq),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@),
        // last split cannot have `pat` as a substring
        iter_seq.len() > 0 ==> !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        s.len() > 0 ==> {
            ||| s == iter_seq.map_values(|ss: &'a str| ss@ + pat@).flatten()
            ||| iter_seq.last()@.len() > 0 && s == iter_seq.drop_last().map_values(|ss: &'a str| ss@ + pat@).flatten() + iter_seq.last()@
        },
{
    axiom_string_matches_post(s, pat);
    reveal(str_split_terminator_iter_post);
    let (seq, gap) = spec_matches(s, pat);

    // #1
    if s.len() == 0 {
        assert_by_contradiction!(seq.len() == 0, {
            lemma_join_uncons(seq, gap);
            assert(seq[0] =~= pat@);
            assert(seq[0] == pat@);
            assert(s == gap[0] + seq[0] + join(seq.skip(1), gap.skip(1)));
            assert(s.len() >= pat@.len());
        });
        assert(gap.last().len() == 0);
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        assert(seq.len() == 0);
        lemma_join_alt(seq, gap);
        assert(s == gap.last());
        assert(gap.last().len() == 0);
        assert(s.len() == 0);
    }

    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);

    // #2
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@)
    by {
        assert(i < seq.len());
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].len() > 0 ==> !pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@));
    }
    if iter_seq.len() > 0 {
        if iter_seq.len() == seq.len() + 1 {
            assert(iter_seq.last()@ == gap.last());
            assert(!(pat@.is_subrange_of(gap.last())));
        } else {
            assert(iter_seq.len() == seq.len());
            assert(gap.last().len() == 0);
            assert(iter_seq.last()@ == gap[seq.len() - 1]);
            assert_by_contradiction!(!(pat@.is_subrange_of(iter_seq.last()@)), {
                let g = iter_seq.last()@;
                let k = choose |k: int| 0 <= k <= g.len() - pat@.len()
                    && pat@ =~= #[trigger] g.subrange(k, k + pat@.len());
                assert(g == gap[seq.len() - 1]);
                assert(g.len() > 0 || g.len() == 0);
                if k == 0 {
                    assert(pat@.is_prefix_of(g + pat@));
                } else {
                    assert(0 < k < (g + pat@).len() - pat@.len());
                    assert((g + pat@).subrange(k, k + pat@.len()) == g.subrange(k, k + pat@.len()));
                    assert(pat@ =~= (g + pat@).subrange(k, k + pat@.len()));
                    assert(pat@.is_infix_of(g + pat@));
                }
                assert(g.len() > 0 ==> !pat@.is_prefix_of(g + pat@) && !pat@.is_infix_of(g + pat@));
                if g.len() == 0 {
                    assert(false);
                }
            });
        }
    }

    // #3
    if s.len() == 0 { return }
    calc!{
        (==)
        s; {}
        join(seq, gap); { lemma_join_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
    if gap.last().len() == 0 {
        let s2 = iter_seq.map_values(|ss: &'a str| ss@ + pat@);
        assert(iter_seq.len() == seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i]@ == gap[i]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten();
        }
    } else {
        let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@ + pat@);
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.last()@ == gap.last());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i]@ == gap[i]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        calc!{
            (==)
            s; {}
            s2.flatten() + gap.last(); {}
            s2.flatten() + iter_seq.last()@;
        }
    }
}

}
