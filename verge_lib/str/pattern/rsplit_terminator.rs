// Internal proof module for `str::rsplit_terminator` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, ch; iter_seq.map_values(|s: &str| s@))]
pub broadcast proof fn lemma_str_rsplit_terminator_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplit_terminator_iter_post(s, ch, iter_seq),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // splits cannot contain `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> !(#[trigger] iter_seq[i]@.contains(ch)),
        // delimiters and splits make up the original string
        s.len() > 0 && s.last() == ch
            ==> s == iter_seq.map_values(|ss: &'a str| ss@.push(ch)).reverse().flatten(),
        s.len() > 0 && s.last() != ch
            ==> s == iter_seq.drop_first().map_values(|ss: &'a str| ss@.push(ch)).reverse().flatten() + iter_seq.first()@,
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rsplit_terminator_iter_post);
    let (seq, gap) = spec_rmatches(s, ch);

    // #1
    if s.len() == 0 {
        lemma_rjoin_alt(seq, gap);
        assert(gap.first().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            lemma_rjoin_uncons(seq, gap);
            assert(seq[0] =~= seq![ch]);
            assert(s.len() > 0);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        if gap.first().len() == 0 {
            assert(gap.len() == 1);
            assert(seq.len() == 0);
            assert(s == rjoin(seq, gap));
            assert(s == gap.first());
            assert(s.len() == 0);
        } else {
            assert(gap.len() > 0);
            assert(false);
        }
    }
    // #2
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < iter_seq.len()
    implies !(#[trigger] iter_seq[i]@.contains(ch))
    by {
        if gap.first().len() == 0 {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(!gap[i + 1].contains(ch));
        } else {
            assert(iter_seq[i]@ == gap[i]);
            assert(!gap[i].contains(ch));
        }
    }
    // #3
    if s.len() == 0 { return }
    assert(s.last() == ch <==> gap.first().len() == 0) by {
        lemma_rjoin_alt(seq, gap);
        if gap.first().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
            s1.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.first() =~= seq![ch]);
            assert(s.last() == seq.first().last());
            assert(s.last() == ch);
        }
        if s.last() == ch {
            assert_by_contradiction!(gap.first().len() == 0, {
                assert(s.last() == gap.first().last());
                assert(!gap.first().contains(ch));
            });
        }
    }
    calc!{
        (==)
        s; {}
        rjoin(seq, gap); { lemma_rjoin_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss).reverse().flatten_alt() + gap.first();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
    if s.last() == ch {
        let s2 = iter_seq.map_values(|ss: &'a str| ss@.push(ch));
        assert(gap.first().len() == 0);
        assert(iter_seq.len() == seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(seq[i] =~= seq![ch]);
            assert(seq[i] == seq![ch]);
            assert_seqs_equal!(gap[i + 1].push(ch) == gap[i + 1] + seq![ch]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten_alt(); {}
            s2.reverse().flatten();
        }
    } else {
        let s2 = iter_seq.drop_first().map_values(|ss: &'a str| ss@.push(ch));
        assert(gap.first().len() > 0);
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.first()@ == gap.first());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
            assert(iter_seq[i + 1]@ == gap[i + 1]);
            assert(seq[i] =~= seq![ch]);
            assert(seq[i] == seq![ch]);
            assert_seqs_equal!(gap[i + 1].push(ch) == gap[i + 1] + seq![ch]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten() + iter_seq.first()@;
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rsplit_terminator_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rsplit_terminator_iter_post(s, f, iter_seq),
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
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten()
                    }
            &&& s.len() > 0 && call_ensures(f, (s.last(),), false)
                    ==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten() + iter_seq.first()@
                    }
        },
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rsplit_terminator_iter_post);
    let (seq, gap) = spec_rmatches(s, f);
    let gap_pred = |c: char| call_ensures(f, (c,), false);
    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);

    if s.len() == 0 {
        lemma_rjoin_alt(seq, gap);
        assert(gap.first().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            lemma_rjoin_uncons(seq, gap);
            assert(seq[0].len() == 1 && call_ensures(f, (seq[0][0],), true));
            assert(s.len() > 0);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        if gap.first().len() == 0 {
            assert(gap.len() == 1);
            assert(seq.len() == 0);
            assert(s == rjoin(seq, gap));
            assert(s == gap.first());
            assert(s.len() == 0);
        } else {
            assert(gap.len() > 0);
            assert(false);
        }
    }
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < iter_seq.len()
    implies (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false))
    by {
        if gap.first().len() == 0 {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(gap[i + 1].all(gap_pred));
        } else {
            assert(iter_seq[i]@ == gap[i]);
            assert(gap[i].all(gap_pred));
        }
    }
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] call_ensures(f, (delim[i],), true)
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
    }
    if s.len() == 0 { return }
    assert(call_ensures(f, (s.last(),), true) <==> gap.first().len() == 0) by {
        lemma_rjoin_alt(seq, gap);
        if gap.first().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
            s1.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(s.last() == seq.first()[0]);
            assert(call_ensures(f, (s.last(),), true));
        }
        if call_ensures(f, (s.last(),), true) {
            assert_by_contradiction!(gap.first().len() == 0, {
                assert(s.last() == gap.first().last());
                assert(gap.first().all(gap_pred));
                assert(gap_pred(gap.first()[gap.first().len() - 1]));
                assert(call_ensures(f, (gap.first()[gap.first().len() - 1],), false));
                gap.first().lemma_index_contains(gap.first().len() - 1);
                assert(gap.first().contains(gap.first().last()));
                assert(call_ensures(f, (gap.first().last(),), false));
                assert(call_ensures(f, (gap.first().last(),), true));
            });
        }
    }
    calc!{
        (==)
        s; {}
        rjoin(seq, gap); { lemma_rjoin_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss).reverse().flatten_alt() + gap.first();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
    if call_ensures(f, (s.last(),), true) {
        let s2 = iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(gap.first().len() == 0);
        assert(iter_seq.len() == seq.len());
        assert(delim.len() == iter_seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i + 1].push(d) == gap[i + 1] + seq![d]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten_alt(); {}
            s2.reverse().flatten();
        }
    } else {
        let s2 = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(gap.first().len() > 0);
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.first()@ == gap.first());
        assert(delim.len() == iter_seq.len() - 1);
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
            assert(iter_seq[i + 1]@ == gap[i + 1]);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i + 1].push(d) == gap[i + 1] + seq![d]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten() + iter_seq.first()@;
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rsplit_terminator_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplit_terminator_iter_post(s, chars, iter_seq),
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
                        &&& s == iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten()
                    }
            &&& s.len() > 0 && !chars@.contains(s.last())
                    ==> {
                        &&& delim.len() == iter_seq.len() - 1
                        &&& s == iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i])).reverse().flatten() + iter_seq.first()@
                    }
        },
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rsplit_terminator_iter_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let gap_pred = |c: char| !chars@.contains(c);
    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);

    if s.len() == 0 {
        lemma_rjoin_alt(seq, gap);
        assert(gap.first().len() == 0);
        assert_by_contradiction!(seq.len() == 0, {
            lemma_rjoin_uncons(seq, gap);
            assert(seq[0].len() == 1 && chars@.contains(seq[0][0]));
            assert(s.len() > 0);
        });
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        if gap.first().len() == 0 {
            assert(gap.len() == 1);
            assert(seq.len() == 0);
            assert(s == rjoin(seq, gap));
            assert(s == gap.first());
            assert(s.len() == 0);
        } else {
            assert(gap.len() > 0);
            assert(false);
        }
    }
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| 0 <= i < iter_seq.len()
    implies (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c))
    by {
        if gap.first().len() == 0 {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(gap[i + 1].all(gap_pred));
        } else {
            assert(iter_seq[i]@ == gap[i]);
            assert(gap[i].all(gap_pred));
        }
    }
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] chars@.contains(delim[i])
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
    }
    if s.len() == 0 { return }
    assert(chars@.contains(s.last()) <==> gap.first().len() == 0) by {
        lemma_rjoin_alt(seq, gap);
        if gap.first().len() == 0 {
            let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
            s1.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(s.last() == seq.first()[0]);
            assert(chars@.contains(s.last()));
        }
        if chars@.contains(s.last()) {
            assert_by_contradiction!(gap.first().len() == 0, {
                assert(s.last() == gap.first().last());
                assert(gap.first().all(gap_pred));
                assert(gap_pred(gap.first()[gap.first().len() - 1]));
                assert(!chars@.contains(gap.first()[gap.first().len() - 1]));
                gap.first().lemma_index_contains(gap.first().len() - 1);
                assert(gap.first().contains(gap.first().last()));
                assert(!chars@.contains(gap.first().last()));
                assert(chars@.contains(gap.first().last()));
            });
        }
    }
    calc!{
        (==)
        s; {}
        rjoin(seq, gap); { lemma_rjoin_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss).reverse().flatten_alt() + gap.first();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
    if chars@.contains(s.last()) {
        let s2 = iter_seq.map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(gap.first().len() == 0);
        assert(iter_seq.len() == seq.len());
        assert(delim.len() == iter_seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i + 1].push(d) == gap[i + 1] + seq![d]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten_alt(); {}
            s2.reverse().flatten();
        }
    } else {
        let s2 = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert(gap.first().len() > 0);
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.first()@ == gap.first());
        assert(delim.len() == iter_seq.len() - 1);
        assert_seqs_equal!(s1 == s2, i => {
            let d = delim[i];
            assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
            assert(iter_seq[i + 1]@ == gap[i + 1]);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            assert_seqs_equal!(gap[i + 1].push(d) == gap[i + 1] + seq![d]);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten() + iter_seq.first()@;
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rsplit_terminator_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_rsplit_terminator_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_rsplit_terminator_iter_post(s, pat, iter_seq),
    ensures
        // splits are empty iff `s` is empty
        s.len() == 0 <==> iter_seq.len() == 0,
        // `pat + split` (apart from the last) cannot have `pat` as a suffix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@),
        // last split cannot have `pat` as a substring
        iter_seq.len() > 0 ==> !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        s.len() > 0 ==> {
            ||| s == iter_seq.map_values(|ss: &'a str| ss@ + pat@).reverse().flatten()
            ||| iter_seq.first()@.len() > 0 && s == iter_seq.drop_first().map_values(|ss: &'a str| ss@ + pat@).reverse().flatten() + iter_seq.first()@
        },
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rsplit_terminator_iter_post);
    let (seq, gap) = spec_rmatches(s, pat);

    if s.len() == 0 {
        assert_by_contradiction!(seq.len() == 0, {
            lemma_rjoin_uncons(seq, gap);
            assert(seq[0] =~= pat@);
            assert(seq[0] == pat@);
            assert(s.len() >= pat@.len());
        });
        assert(gap.first().len() == 0);
        assert(iter_seq.len() == 0);
    }
    if iter_seq.len() == 0 {
        if gap.first().len() == 0 {
            assert(gap.len() == 1);
            assert(seq.len() == 0);
            assert(s == rjoin(seq, gap));
            assert(s == gap.first());
            assert(s.len() == 0);
        } else {
            assert(gap.len() > 0);
            assert(false);
        }
    }
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@)
    by {
        if gap.first().len() == 0 {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(gap[i + 1].len() > 0 ==> !pat@.is_suffix_of(pat@ + gap[i + 1]) && !pat@.is_infix_of(pat@ + gap[i + 1]));
        } else {
            assert(iter_seq[i]@ == gap[i]);
            assert(gap[i].len() > 0 ==> !pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i]));
        }
    }
    if iter_seq.len() > 0 {
        if gap.first().len() == 0 {
            assert(iter_seq.last()@ == gap.last());
            assert(!(pat@.is_subrange_of(gap.last())));
        } else if iter_seq.len() == seq.len() + 1 {
            assert(iter_seq.last()@ == gap.last());
            assert(!(pat@.is_subrange_of(gap.last())));
        } else {
            assert(false);
        }
    }
    if s.len() == 0 { return }
    calc!{
        (==)
        s; {}
        rjoin(seq, gap); { lemma_rjoin_alt(seq, gap) }
        seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss).reverse().flatten_alt() + gap.first();
    }
    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i + 1] + ss);
    if gap.first().len() == 0 {
        let s2 = iter_seq.map_values(|ss: &'a str| ss@ + pat@);
        assert(iter_seq.len() == seq.len());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i]@ == gap[i + 1]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten_alt(); {}
            s2.reverse().flatten();
        }
    } else {
        let s2 = iter_seq.drop_first().map_values(|ss: &'a str| ss@ + pat@);
        assert(iter_seq.len() == seq.len() + 1 && iter_seq.first()@ == gap.first());
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
            assert(iter_seq[i + 1]@ == gap[i + 1]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        assert(s1.reverse() == s2.reverse());
        s2.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            s2.reverse().flatten_alt() + gap.first(); {}
            s2.reverse().flatten() + iter_seq.first()@;
        }
    }
}

}
