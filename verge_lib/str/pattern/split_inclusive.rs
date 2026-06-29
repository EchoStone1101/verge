// Internal proof module for `str::split_inclusive` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
pub broadcast proof fn lemma_str_split_inclusive_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_inclusive_iter_post(s, ch, iter_seq),
    ensures
        // splits are not empty and cannot contain `ch` except at the end
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len()
            ==> iter_seq[i]@.len() > 0
                && !iter_seq[i]@.drop_last().contains(ch),
        // splits except the last must end with `ch`
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> #[trigger] iter_seq[i]@.last() == ch,
        // splits make up the original string
        s == iter_seq.map_values(|ss: &'a str| ss@).flatten(),
{
    axiom_char_matches_post(s, ch);
    reveal(str_split_inclusive_iter_post);
    let (seq, gap) = spec_matches(s, ch);
    // #1
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| #![trigger iter_seq[i]@] 0 <= i < seq.len()
    implies iter_seq[i]@.len() > 0 && !iter_seq[i]@.drop_last().contains(ch)
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(iter_seq[i]@.len() > 0) by { assert(seq[i] =~= seq![ch]) }
        assert(!iter_seq[i]@.drop_last().contains(ch)) by {
            assert(!gap[i].contains(ch));
            assert(iter_seq[i]@.drop_last() == gap[i]);
        }
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@.len() > 0 && !iter_seq.last()@.drop_last().contains(ch)) by {
            assert(iter_seq.last()@ == gap.last());
            assert(!gap.last().drop_last().contains(ch)) by {
                assert(!gap.last().contains(ch));
            }
        }
    }
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies #[trigger] iter_seq[i]@.last() == ch
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(seq[i] =~= seq![ch]);
    }
    // #3
    assert(s == iter_seq.map_values(|ss: &'a str| ss@).flatten()) by {
        if iter_seq.len() == seq.len() {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    assert(gap.last().len() == 0);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        } else {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    let s1 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    s1.lemma_flatten_and_flatten_alt_are_equivalent();
                    assert(gap.last() == iter_seq.last()@);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten_alt() + iter_seq.last()@; {
                    reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                    assert_seqs_equal!(iter_seq.drop_last().map_values(|ss: &'a str| ss@) == iter_seq.map_values(|ss: &'a str| ss@).drop_last());
                    assert(iter_seq.map_values(|ss: &'a str| ss@).last() == iter_seq.last()@);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten_alt(); {
                    iter_seq.map_values(|ss: &'a str| ss@).lemma_flatten_and_flatten_alt_are_equivalent();
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_split_inclusive_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_split_inclusive_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // splits are not empty and cannot match `f` except at the end
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len()
            ==> iter_seq[i]@.len() > 0
                && iter_seq[i]@.drop_last().all(|c: char| call_ensures(f, (c,), false)),
        // splits except the last must match `f` at the end
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> #[trigger] call_ensures(f, (iter_seq[i]@.last(),), true),
        // splits make up the original string
        s == iter_seq.map_values(|ss: &'a str| ss@).flatten(),
{
    axiom_closure_matches_post(s, f);
    reveal(str_split_inclusive_iter_post);
    let (seq, gap) = spec_matches(s, f);
    // #1
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| #![trigger iter_seq[i]@] 0 <= i < seq.len()
    implies iter_seq[i]@.len() > 0 && iter_seq[i]@.drop_last().all(|c: char| call_ensures(f, (c,), false))
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(iter_seq[i]@.len() > 0) by { assert(seq[i].len() == 1) }
        assert(iter_seq[i]@.drop_last() == gap[i]) by {
            assert(seq[i].len() == 1);
        }
        assert(gap[i].all(|c: char| call_ensures(f, (c,), false)));
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@.len() > 0 && iter_seq.last()@.drop_last().all(|c: char| call_ensures(f, (c,), false))) by {
            assert(iter_seq.last()@ == gap.last());
            assert(gap.last().all(|c: char| call_ensures(f, (c,), false)));
            assert(iter_seq.last()@.drop_last().all(|c: char| call_ensures(f, (c,), false)));
        }
    }
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies #[trigger] call_ensures(f, (iter_seq[i]@.last(),), true)
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
        assert(iter_seq[i]@.last() == seq[i][0]);
    }
    // #3
    assert(s == iter_seq.map_values(|ss: &'a str| ss@).flatten()) by {
        if iter_seq.len() == seq.len() {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    assert(gap.last().len() == 0);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        } else {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    let s1 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    s1.lemma_flatten_and_flatten_alt_are_equivalent();
                    assert(gap.last() == iter_seq.last()@);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten_alt() + iter_seq.last()@; {
                    reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                    assert_seqs_equal!(iter_seq.drop_last().map_values(|ss: &'a str| ss@) == iter_seq.map_values(|ss: &'a str| ss@).drop_last());
                    assert(iter_seq.map_values(|ss: &'a str| ss@).last() == iter_seq.last()@);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten_alt(); {
                    iter_seq.map_values(|ss: &'a str| ss@).lemma_flatten_and_flatten_alt_are_equivalent();
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_split_inclusive_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_inclusive_iter_post(s, chars, iter_seq),
    ensures
        // splits are not empty and cannot match `chars` except at the end
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len()
            ==> iter_seq[i]@.len() > 0
                && iter_seq[i]@.drop_last().all(|c: char| !chars@.contains(c)),
        // splits except the last must match `chars` at the end
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> #[trigger] chars@.contains(iter_seq[i]@.last()),
        // splits make up the original string
        s == iter_seq.map_values(|ss: &'a str| ss@).flatten(),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_split_inclusive_iter_post);
    let (seq, gap) = spec_matches(s, chars);
    // #1
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| #![trigger iter_seq[i]@] 0 <= i < seq.len()
    implies iter_seq[i]@.len() > 0 && iter_seq[i]@.drop_last().all(|c: char| !chars@.contains(c))
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(iter_seq[i]@.len() > 0) by { assert(seq[i].len() == 1) }
        assert(iter_seq[i]@.drop_last() == gap[i]) by {
            assert(seq[i].len() == 1);
        }
        assert(gap[i].all(|c: char| !chars@.contains(c)));
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@.len() > 0 && iter_seq.last()@.drop_last().all(|c: char| !chars@.contains(c))) by {
            assert(iter_seq.last()@ == gap.last());
            assert(gap.last().all(|c: char| !chars@.contains(c)));
            assert(iter_seq.last()@.drop_last().all(|c: char| !chars@.contains(c)));
        }
    }
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies #[trigger] chars@.contains(iter_seq[i]@.last())
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
        assert(iter_seq[i]@.last() == seq[i][0]);
    }
    // #3
    assert(s == iter_seq.map_values(|ss: &'a str| ss@).flatten()) by {
        if iter_seq.len() == seq.len() {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    assert(gap.last().len() == 0);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        } else {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    let s1 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    s1.lemma_flatten_and_flatten_alt_are_equivalent();
                    assert(gap.last() == iter_seq.last()@);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten_alt() + iter_seq.last()@; {
                    reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                    assert_seqs_equal!(iter_seq.drop_last().map_values(|ss: &'a str| ss@) == iter_seq.map_values(|ss: &'a str| ss@).drop_last());
                    assert(iter_seq.map_values(|ss: &'a str| ss@).last() == iter_seq.last()@);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten_alt(); {
                    iter_seq.map_values(|ss: &'a str| ss@).lemma_flatten_and_flatten_alt_are_equivalent();
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        }
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_split_inclusive_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_split_inclusive_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_split_inclusive_iter_post(s, pat, iter_seq),
    ensures
        // splits are not empty and cannot match `pat` except at the end
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len()
            ==> iter_seq[i]@.len() > 0 && !pat@.is_subrange_of(iter_seq[i]@.drop_last()),
        // splits except the last must match `pat` at the end
        forall |i: int| 0 <= i < iter_seq.len() - 1
            ==> #[trigger] pat@.is_suffix_of(iter_seq[i]@),
        // splits make up the original string
        s == iter_seq.map_values(|ss: &'a str| ss@).flatten(),
{
    axiom_string_matches_post(s, pat);
    reveal(str_split_inclusive_iter_post);
    let (seq, gap) = spec_matches(s, pat);
    // #1
    assert(iter_seq.len() == seq.len() || iter_seq.len() == seq.len() + 1);
    assert forall |i: int| #![trigger iter_seq[i]@] 0 <= i < seq.len()
    implies iter_seq[i]@.len() > 0 && !pat@.is_subrange_of(iter_seq[i]@.drop_last())
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(seq[i] =~= pat@);
        assert(seq[i] == pat@);
        assert(iter_seq[i]@ == gap[i] + pat@);
        assert(iter_seq[i]@.len() > 0);
        if gap[i].len() == 0 {
            assert(iter_seq[i]@.drop_last().len() < pat@.len());
            assert(!pat@.is_subrange_of(iter_seq[i]@.drop_last()));
        } else {
            assert(gap[i].len() > 0 ==> !pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@));
            assert_by_contradiction!(!pat@.is_subrange_of(iter_seq[i]@.drop_last()), {
                let part = iter_seq[i]@;
                let dl = part.drop_last();
                let k = choose |k: int| 0 <= k <= dl.len() - pat@.len()
                    && pat@ =~= #[trigger] dl.subrange(k, k + pat@.len());
                assert(dl == part.subrange(0, part.len() - 1));
                assert(dl.subrange(k, k + pat@.len()) == part.subrange(k, k + pat@.len())) by {
                    part.lemma_slice_of_slice(0, part.len() - 1, k, k + pat@.len());
                }
                assert(pat@ =~= part.subrange(k, k + pat@.len()));
                assert(pat@.is_subrange_of(part));
                lemma_seq_is_subrange_alt(part, pat@);
                if k == 0 {
                    assert(pat@.is_prefix_of(part));
                } else {
                    assert(k < part.len() - pat@.len());
                    assert(pat@.is_infix_of(part));
                }
                assert(!pat@.is_prefix_of(part) && !pat@.is_infix_of(part));
            });
        }
    }
    if iter_seq.len() == seq.len() + 1 {
        assert(iter_seq.last()@.len() > 0 && !pat@.is_subrange_of(iter_seq.last()@.drop_last())) by {
            assert(iter_seq.last()@ == gap.last());
            assert(!(pat@.is_subrange_of(gap.last())));
            assert_by_contradiction!(!pat@.is_subrange_of(iter_seq.last()@.drop_last()), {
                let part = iter_seq.last()@;
                let dl = part.drop_last();
                let k = choose |k: int| 0 <= k <= dl.len() - pat@.len()
                    && pat@ =~= #[trigger] dl.subrange(k, k + pat@.len());
                assert(dl == part.subrange(0, part.len() - 1));
                assert(dl.subrange(k, k + pat@.len()) == part.subrange(k, k + pat@.len())) by {
                    part.lemma_slice_of_slice(0, part.len() - 1, k, k + pat@.len());
                }
                assert(pat@ =~= part.subrange(k, k + pat@.len()));
                assert(pat@.is_subrange_of(part));
            });
        }
    }
    // #2
    assert forall |i: int| 0 <= i < iter_seq.len() - 1
    implies #[trigger] pat@.is_suffix_of(iter_seq[i]@)
    by {
        assert(iter_seq[i]@ == gap[i] + seq[i]);
        assert(seq[i] =~= pat@);
        assert(seq[i] == pat@);
        assert(iter_seq[i]@ == gap[i] + pat@);
        assert(pat@.is_suffix_of(iter_seq[i]@));
    }
    // #3
    assert(s == iter_seq.map_values(|ss: &'a str| ss@).flatten()) by {
        if iter_seq.len() == seq.len() {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    assert(gap.last().len() == 0);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        } else {
            calc!{
                (==)
                s; { lemma_join_alt(seq, gap) }
                seq.map(|i: int, ss: Seq<char>| gap[i] + ss).flatten() + gap.last(); {
                    let s1 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
                    let s2 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    assert_seqs_equal!(s1 == s2);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten() + gap.last(); {
                    let s1 = iter_seq.drop_last().map_values(|ss: &'a str| ss@);
                    s1.lemma_flatten_and_flatten_alt_are_equivalent();
                    assert(gap.last() == iter_seq.last()@);
                }
                iter_seq.drop_last().map_values(|ss: &'a str| ss@).flatten_alt() + iter_seq.last()@; {
                    reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                    assert_seqs_equal!(iter_seq.drop_last().map_values(|ss: &'a str| ss@) == iter_seq.map_values(|ss: &'a str| ss@).drop_last());
                    assert(iter_seq.map_values(|ss: &'a str| ss@).last() == iter_seq.last()@);
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten_alt(); {
                    iter_seq.map_values(|ss: &'a str| ss@).lemma_flatten_and_flatten_alt_are_equivalent();
                }
                iter_seq.map_values(|ss: &'a str| ss@).flatten();
            };
        }
    }
}

}
