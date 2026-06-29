// Internal proof module for `str::splitn` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
pub broadcast proof fn lemma_str_splitn_iter_char<'a>(s: Seq<char>, n: usize, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_splitn_iter_post(s, n, ch, iter_seq),
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
            s == iter_seq.drop_last()
                    .map_values(|ss: &'a str| ss@.push(ch))
                    .flatten() + iter_seq.last()@,
{
    axiom_char_matches_post(s, ch);
    reveal(str_splitn_iter_post);
    let (seq, gap) = spec_matches(s, ch);
    // #1
    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies !(#[trigger] iter_seq[i]@.contains(ch))
    by { assert(!gap[i].contains(ch)) }
    // #3
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            join(seq.skip(iter_seq.len() - 1), gap.skip(iter_seq.len() - 1)); {}
            join(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
            gap.last();
        }
        assert(!gap.last().contains(ch));
    }
    // #4
    if n > 0 {
        let k = iter_seq.len() - 1;
        assert(0 <= k <= seq.len());
        lemma_join_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss);
        let iter_parts = iter_seq.drop_last().map_values(|ss: &'a str| ss@.push(ch));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == gap[i]);
            assert(seq[i] =~= seq![ch]);
        });
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, k); }
            join_parts.flatten() + join(seq.skip(k), gap.skip(k)); {}
            iter_parts.flatten() + iter_seq.last()@;
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_splitn_iter_closure<'a, F>(s: Seq<char>, n: usize, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_splitn_iter_post(s, n, f, iter_seq),
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
            &&& s == iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.push(delim[i]))
                    .flatten() + iter_seq.last()@
        },
{
    axiom_closure_matches_post(s, f);
    reveal(str_splitn_iter_post);
    let (seq, gap) = spec_matches(s, f);
    let gap_pred = |c: char| call_ensures(f, (c,), false);
    // #1
    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    // #3
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            join(seq.skip(iter_seq.len() - 1), gap.skip(iter_seq.len() - 1)); {}
            join(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
            gap.last();
        }
        assert(gap.last().all(gap_pred));
    }
    // #4
    if n > 0 {
        let delim = Seq::<char>::new((iter_seq.len() - 1) as nat, |i: int| seq[i][0]);
        assert forall |i: int| 0 <= i < delim.len()
            implies #[trigger] call_ensures(f, (delim[i],), true)
        by {
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
        }
        let k = iter_seq.len() - 1;
        assert(0 <= k <= seq.len());
        lemma_join_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == gap[i]);
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![delim[i]]);
        });
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, k); }
            join_parts.flatten() + join(seq.skip(k), gap.skip(k)); {}
            iter_parts.flatten() + iter_seq.last()@;
        }
        assert(delim.len() == iter_seq.len() - 1);
        assert(exists |d: Seq<char>| {
            &&& #[trigger] d.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < d.len()
                    ==> #[trigger] call_ensures(f, (d[i],), true)
            &&& s == iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.push(d[i]))
                    .flatten() + iter_seq.last()@
        });
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_splitn_iter_chars<'a, 'b>(s: Seq<char>, n: usize, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_splitn_iter_post(s, n, chars, iter_seq),
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
            &&& s == iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.push(delim[i]))
                    .flatten() + iter_seq.last()@
        },
{
    axiom_chars_matches_post(s, chars);
    reveal(str_splitn_iter_post);
    let (seq, gap) = spec_matches(s, chars);
    let gap_pred = |c: char| !chars@.contains(c);
    // #1
    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(gap_pred));
    }
    // #3
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            join(seq.skip(iter_seq.len() - 1), gap.skip(iter_seq.len() - 1)); {}
            join(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
            gap.last();
        }
        assert(gap.last().all(gap_pred));
    }
    // #4
    if n > 0 {
        let delim = Seq::<char>::new((iter_seq.len() - 1) as nat, |i: int| seq[i][0]);
        assert forall |i: int| 0 <= i < delim.len()
            implies #[trigger] chars@.contains(delim[i])
        by {
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
        }
        let k = iter_seq.len() - 1;
        assert(0 <= k <= seq.len());
        lemma_join_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@.push(delim[i]));
        assert_seqs_equal!(join_parts == iter_parts, i => {
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == gap[i]);
            assert(delim[i] == seq[i][0]);
            assert(seq[i].len() == 1);
            assert_seqs_equal!(seq[i] == seq![delim[i]]);
        });
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, k); }
            join_parts.flatten() + join(seq.skip(k), gap.skip(k)); {}
            iter_parts.flatten() + iter_seq.last()@;
        }
        assert(delim.len() == iter_seq.len() - 1);
        assert(exists |d: Seq<char>| {
            &&& #[trigger] d.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < d.len()
                    ==> #[trigger] chars@.contains(d[i])
            &&& s == iter_seq.drop_last()
                    .map(|i: int, ss: &'a str| ss@.push(d[i]))
                    .flatten() + iter_seq.last()@
        });
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_splitn_iter_string<'a, 'b>(s: Seq<char>, n: usize, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_splitn_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_splitn_iter_post(s, n, pat, iter_seq),
    ensures
        // at most `n` items, at least one item (unless `n == 0`)
        iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0),
        // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@),
        // last split (if not the `n`th) cannot match `pat` as well
        iter_seq.len() < n ==> !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        n > 0 ==> s == iter_seq.drop_last().map(|i: int, ss: &'a str| ss@ + pat@).flatten() + iter_seq.last()@,
{
    axiom_string_matches_post(s, pat);
    reveal(str_splitn_iter_post);
    let (seq, gap) = spec_matches(s, pat);
    // #1
    assert(iter_seq.len() <= n && (n > 0 ==> iter_seq.len() > 0));
    // #2
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@)
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].len() > 0 ==> !pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@));
    }
    // #3
    if iter_seq.len() < n {
        assert(iter_seq.len() == gap.len());
        calc!{
            (==)
            iter_seq.last()@; {}
            join(seq.skip(iter_seq.len() - 1), gap.skip(iter_seq.len() - 1)); {}
            join(seq![], seq![gap.last()]); {
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
            gap.last();
        }
        assert(!(pat@.is_subrange_of(gap.last())));
    }
    // #4
    if n > 0 {
        let k = iter_seq.len() - 1;
        assert(0 <= k <= seq.len());
        lemma_join_split_at(seq, gap, k);
        let join_parts = seq.take(k).map(|i: int, ss: Seq<char>| gap[i] + ss);
        let iter_parts = iter_seq.drop_last().map(|i: int, ss: &'a str| ss@ + pat@);
        assert_seqs_equal!(join_parts == iter_parts, i => {
            assert(iter_seq.drop_last()[i]@ == iter_seq[i]@);
            assert(iter_seq[i]@ == gap[i]);
            assert(seq[i] =~= pat@);
            assert(seq[i] == pat@);
        });
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, k); }
            join_parts.flatten() + join(seq.skip(k), gap.skip(k)); {}
            iter_parts.flatten() + iter_seq.last()@;
        }
    }
}

}
