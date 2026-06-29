// Internal proof module for `str::rsplitn` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
pub broadcast proof fn lemma_str_rsplitn_iter_char<'a>(s: Seq<char>, n: usize, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplitn_iter_post(s, n, ch, iter_seq),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // splits (apart from the last) cannot contain `ch`
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> !(#[trigger] iter_seq[i]@.contains(ch)),
        // last split (if not the `n`th) cannot contain `ch` as well
        iter_seq.len() < n ==> !iter_seq.last()@.contains(ch),
        // delimiters and splits make up the original string
        n > 0 ==>
            s == iter_seq.last()@ + iter_seq.drop_last()
                    .map_values(|ss: &'a str| ss@.insert(0, ch))
                    .reverse().flatten(),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rsplitn_iter_post);
    let (seq, gap) = spec_rmatches(s, ch);
    let k = iter_seq.len() - 1;

    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
        implies !(#[trigger] iter_seq[i]@.contains(ch))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(!gap[i].contains(ch));
    }
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            rjoin(seq.skip(k), gap.skip(k)); {}
            rjoin(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            }
            gap.last();
        }
        assert(!gap.last().contains(ch));
    }
    if n > 0 {
        assert(0 <= k <= seq.len());
        lemma_rjoin_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
        let iter_parts = iter_seq.drop_last().map_values(|ss: &'a str| ss@.insert(0, ch));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            let g = gap[i];
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == g);
            assert(seq[i] =~= seq![ch]);
            assert(seq[i] == seq![ch]);
            g.insert_ensures(0, ch);
            assert_seqs_equal!(g.insert(0, ch) == seq![ch] + g);
        });
        assert(join_parts.reverse() == iter_parts.reverse());
        iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_at(seq, gap, k); }
            rjoin(seq.skip(k), gap.skip(k)) + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten();
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rsplitn_iter_closure<'a, F>(s: Seq<char>, n: usize, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rsplitn_iter_post(s, n, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // splits (apart from the last) cannot match `f`
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false)),
        // last split (if not the `n`th) cannot match `f` as well
        iter_seq.len() < n ==> iter_seq.last()@.all(|c: char| call_ensures(f, (c,), false)),
        // delimiters and splits make up the original string
        n > 0 ==> exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] call_ensures(f, (delim[i],), true)
            &&& s == iter_seq.last()@ + iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.insert(0, delim[i]))
                    .reverse().flatten()
        },
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rsplitn_iter_post);
    let (seq, gap) = spec_rmatches(s, f);
    let gap_pred = |c: char| call_ensures(f, (c,), false);
    let k = iter_seq.len() - 1;

    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
        implies (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            rjoin(seq.skip(k), gap.skip(k)); {}
            rjoin(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            }
            gap.last();
        }
        assert(gap.last().all(gap_pred));
    }
    if n > 0 {
        assert(0 <= k <= seq.len());
        let delim = Seq::<char>::new(k as nat, |i: int| seq[i][0]);
        assert(delim.len() == iter_seq.len() - 1);
        assert forall |i: int| 0 <= i < delim.len()
            implies #[trigger] call_ensures(f, (delim[i],), true)
        by {
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
        }

        lemma_rjoin_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.insert(0, delim[i]));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            let g = gap[i];
            let d = delim[i];
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == g);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            g.insert_ensures(0, d);
            assert_seqs_equal!(g.insert(0, d) == seq![d] + g);
        });
        assert(join_parts.reverse() == iter_parts.reverse());
        iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_at(seq, gap, k); }
            rjoin(seq.skip(k), gap.skip(k)) + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten();
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rsplitn_iter_chars<'a, 'b>(s: Seq<char>, n: usize, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplitn_iter_post(s, n, chars, iter_seq),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // splits (apart from the last) cannot match `chars`
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c)),
        // last split (if not the `n`th) cannot match `chars` as well
        iter_seq.len() < n ==> iter_seq.last()@.all(|c: char| !chars@.contains(c)),
        // delimiters and splits make up the original string
        n > 0 ==> exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] chars@.contains(delim[i])
            &&& s == iter_seq.last()@ + iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.insert(0, delim[i]))
                    .reverse().flatten()
        },
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rsplitn_iter_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let gap_pred = |c: char| !chars@.contains(c);
    let k = iter_seq.len() - 1;

    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
        implies (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            rjoin(seq.skip(k), gap.skip(k)); {}
            rjoin(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            }
            gap.last();
        }
        assert(gap.last().all(gap_pred));
    }
    if n > 0 {
        assert(0 <= k <= seq.len());
        let delim = Seq::<char>::new(k as nat, |i: int| seq[i][0]);
        assert(delim.len() == iter_seq.len() - 1);
        assert forall |i: int| 0 <= i < delim.len()
            implies #[trigger] chars@.contains(delim[i])
        by {
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
        }

        lemma_rjoin_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.insert(0, delim[i]));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            let g = gap[i];
            let d = delim[i];
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == g);
            assert(d == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![d]);
            g.insert_ensures(0, d);
            assert_seqs_equal!(g.insert(0, d) == seq![d] + g);
        });
        assert(join_parts.reverse() == iter_parts.reverse());
        iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_at(seq, gap, k); }
            rjoin(seq.skip(k), gap.skip(k)) + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten();
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rsplitn_iter_string<'a, 'b>(s: Seq<char>, n: usize, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_rsplitn_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_rsplitn_iter_post(s, n, pat, iter_seq),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // `pat + split` (apart from the last) cannot have `pat` as a suffix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@),
        // last split (if not the `n`th) cannot match `pat` as well
        iter_seq.len() < n ==> !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        n > 0 ==> s == iter_seq.last()@ + iter_seq.drop_last()
                        .map(|i: int, ss: &'a str| pat@ + ss@)
                        .reverse().flatten(),
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rsplitn_iter_post);
    let (seq, gap) = spec_rmatches(s, pat);
    let k = iter_seq.len() - 1;

    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@)
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].len() > 0 ==> !pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i]));
    }
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            rjoin(seq.skip(k), gap.skip(k)); {}
            rjoin(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            }
            gap.last();
        }
        assert(!(pat@.is_subrange_of(gap.last())));
    }
    if n > 0 {
        assert(0 <= k <= seq.len());
        lemma_rjoin_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| ss + gap[i]);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| pat@ + ss@);
        assert_seqs_equal!(join_parts == iter_parts, i => {
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == gap[i]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        assert(join_parts.reverse() == iter_parts.reverse());
        iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_at(seq, gap, k); }
            rjoin(seq.skip(k), gap.skip(k)) + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + join_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten_alt(); {}
            iter_seq.last()@ + iter_parts.reverse().flatten();
        }
    }
}

}
