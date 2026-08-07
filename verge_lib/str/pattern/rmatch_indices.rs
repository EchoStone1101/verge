// Internal proof module for `str::rmatch_indices` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, ch; iter_seq.map_values(|item: (usize, &str)| (item.0, item.1@)))]
pub broadcast proof fn lemma_str_rmatch_indices_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<(usize, &'a str)>)
    requires
        #[trigger] str_rmatch_indices_iter_post(s, ch, iter_seq),
    ensures
        // matches all match `ch`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
                &&& ss@ == seq![ch]
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
                &&& ss@[0] == s[idx_ch]
            },
        // indices are non-overlapping
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i].0 > iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| c == ch),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rmatch_indices_iter_post);
    let (seq, gap) = spec_rmatches(s, ch);
    assert(iter_seq.len() == seq.len());
    // #1
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        &&& ss@ == seq![ch]
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
        &&& ss@[0] == s[idx_ch]
    } by {
        let (idx, ss) = iter_seq[i];
        assert(ss@ == seq[i]);
        assert(seq[i] =~= seq![ch]);
        assert(idx == rjoin(seq.skip(i + 1), gap.skip(i + 1)).as_bytes().len());
        let prefix = rjoin(seq.skip(i + 1), gap.skip(i + 1));
        let suffix = rjoin(seq.take(i), gap.take(i + 1));
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_match_at(seq, gap, i) }
            prefix + seq[i] + suffix;
        }
        assert(s.as_bytes() == prefix.as_bytes() + seq[i].as_bytes() + suffix.as_bytes()) by {
            lemma_str_concat_lower(prefix, seq[i]);
            lemma_str_concat_lower(prefix + seq[i], suffix);
        }
        assert(s.as_bytes().take(idx as int) == prefix.as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(prefix);
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + seq[i].as_bytes().len() <= s.as_bytes().len());
        assert(idx_ch == prefix.len()) by {
            lemma_str_lower_lift(prefix);
        }
        assert(s[idx_ch] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 > iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let prefix1 = rjoin(seq.skip(i+1), gap.skip(i+1));
        let prefix2 = rjoin(seq.skip(i+2), gap.skip(i+2));
        lemma_rjoin_uncons(seq.skip(i+1), gap.skip(i+1));
        assert(seq.skip(i+1)[0] == seq[i+1]);
        assert(gap.skip(i+1)[0] == gap[i+1]);
        assert(seq.skip(i+1).skip(1) == seq.skip(i+2));
        assert(gap.skip(i+1).skip(1) == gap.skip(i+2));
        assert(prefix1 == prefix2 + seq[i+1] + gap[i+1]);
        assert(idx1 == prefix1.as_bytes().len());
        assert(idx2 == prefix2.as_bytes().len());
        assert(prefix2.as_bytes() + seq[i+1].as_bytes() + gap[i+1].as_bytes() == prefix1.as_bytes()) by {
            lemma_str_concat_lower(prefix2, seq[i+1]);
            lemma_str_concat_lower(prefix2 + seq[i+1], gap[i+1]);
        }
        assert(seq[i+1] =~= seq![ch]);
        assert(seq[i+1].as_bytes().len() > 0);
    }
    // #3
    assert(iter_seq.len() == s.count(|c: char| c == ch)) by {
        let pred = |c: char| c == ch;
        assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c))
        by { assert(!gap[i].contains(ch)); }
        assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0])
        by { assert(seq[i] =~= seq![ch]) }
        lemma_str_rmatches_count(seq, gap, pred);
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rmatch_indices_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<(usize, &'a str)>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rmatch_indices_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // matches all match `f`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
                &&& ss@.len() == 1 && call_ensures(f, (ss@[0],), true)
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
                &&& ss@[0] == s[idx_ch]
            },
        // indices are non-overlapping
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i].0 > iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true)),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rmatch_indices_iter_post);
    let (seq, gap) = spec_rmatches(s, f);
    assert(iter_seq.len() == seq.len());
    // #1
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        &&& ss@.len() == 1 && call_ensures(f, (ss@[0],), true)
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
        &&& ss@[0] == s[idx_ch]
    } by {
        let (idx, ss) = iter_seq[i];
        assert(ss@ == seq[i]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
        assert(idx == rjoin(seq.skip(i + 1), gap.skip(i + 1)).as_bytes().len());
        let prefix = rjoin(seq.skip(i + 1), gap.skip(i + 1));
        let suffix = rjoin(seq.take(i), gap.take(i + 1));
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_match_at(seq, gap, i) }
            prefix + seq[i] + suffix;
        }
        assert(s.as_bytes() == prefix.as_bytes() + seq[i].as_bytes() + suffix.as_bytes()) by {
            lemma_str_concat_lower(prefix, seq[i]);
            lemma_str_concat_lower(prefix + seq[i], suffix);
        }
        assert(s.as_bytes().take(idx as int) == prefix.as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(prefix);
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + seq[i].as_bytes().len() <= s.as_bytes().len());
        assert(idx_ch == prefix.len()) by {
            lemma_str_lower_lift(prefix);
        }
        assert(s[idx_ch] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 > iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let prefix1 = rjoin(seq.skip(i+1), gap.skip(i+1));
        let prefix2 = rjoin(seq.skip(i+2), gap.skip(i+2));
        lemma_rjoin_uncons(seq.skip(i+1), gap.skip(i+1));
        assert(seq.skip(i+1)[0] == seq[i+1]);
        assert(gap.skip(i+1)[0] == gap[i+1]);
        assert(seq.skip(i+1).skip(1) == seq.skip(i+2));
        assert(gap.skip(i+1).skip(1) == gap.skip(i+2));
        assert(prefix1 == prefix2 + seq[i+1] + gap[i+1]);
        assert(idx1 == prefix1.as_bytes().len());
        assert(idx2 == prefix2.as_bytes().len());
        assert(prefix2.as_bytes() + seq[i+1].as_bytes() + gap[i+1].as_bytes() == prefix1.as_bytes()) by {
            lemma_str_concat_lower(prefix2, seq[i+1]);
            lemma_str_concat_lower(prefix2 + seq[i+1], gap[i+1]);
        }
        assert(seq[i+1].len() == 1);
        assert(seq[i+1].as_bytes().len() > 0);
    }
    // #3
    assert(iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true))) by {
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
        implies seq[i].len() == 1 && pred(seq[i][0]) by {}
        lemma_str_rmatches_count(seq, gap, pred);
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rmatch_indices_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<(usize, &'a str)>)
    requires
        #[trigger] str_rmatch_indices_iter_post(s, chars, iter_seq),
    ensures
        // matches all match `chars`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
                &&& ss@.len() == 1 && chars@.contains(ss@[0])
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
                &&& ss@[0] == s[idx_ch]
            },
        // indices are non-overlapping
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i].0 > iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| chars@.contains(c)),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rmatch_indices_iter_post);
    let (seq, gap) = spec_rmatches(s, chars);
    assert(iter_seq.len() == seq.len());
    // #1
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        &&& ss@.len() == 1 && chars@.contains(ss@[0])
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx < s.as_bytes().len()
        &&& ss@[0] == s[idx_ch]
    } by {
        let (idx, ss) = iter_seq[i];
        assert(ss@ == seq[i]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
        assert(idx == rjoin(seq.skip(i + 1), gap.skip(i + 1)).as_bytes().len());
        let prefix = rjoin(seq.skip(i + 1), gap.skip(i + 1));
        let suffix = rjoin(seq.take(i), gap.take(i + 1));
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_match_at(seq, gap, i) }
            prefix + seq[i] + suffix;
        }
        assert(s.as_bytes() == prefix.as_bytes() + seq[i].as_bytes() + suffix.as_bytes()) by {
            lemma_str_concat_lower(prefix, seq[i]);
            lemma_str_concat_lower(prefix + seq[i], suffix);
        }
        assert(s.as_bytes().take(idx as int) == prefix.as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(prefix);
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + seq[i].as_bytes().len() <= s.as_bytes().len());
        assert(idx_ch == prefix.len()) by {
            lemma_str_lower_lift(prefix);
        }
        assert(s[idx_ch] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 > iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let prefix1 = rjoin(seq.skip(i+1), gap.skip(i+1));
        let prefix2 = rjoin(seq.skip(i+2), gap.skip(i+2));
        lemma_rjoin_uncons(seq.skip(i+1), gap.skip(i+1));
        assert(seq.skip(i+1)[0] == seq[i+1]);
        assert(gap.skip(i+1)[0] == gap[i+1]);
        assert(seq.skip(i+1).skip(1) == seq.skip(i+2));
        assert(gap.skip(i+1).skip(1) == gap.skip(i+2));
        assert(prefix1 == prefix2 + seq[i+1] + gap[i+1]);
        assert(idx1 == prefix1.as_bytes().len());
        assert(idx2 == prefix2.as_bytes().len());
        assert(prefix2.as_bytes() + seq[i+1].as_bytes() + gap[i+1].as_bytes() == prefix1.as_bytes()) by {
            lemma_str_concat_lower(prefix2, seq[i+1]);
            lemma_str_concat_lower(prefix2 + seq[i+1], gap[i+1]);
        }
        assert(seq[i+1].len() == 1);
        assert(seq[i+1].as_bytes().len() > 0);
    }
    // #3
    assert(iter_seq.len() == s.count(|c: char| chars@.contains(c))) by {
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
        implies seq[i].len() == 1 && pred(seq[i][0]) by {}
        lemma_str_rmatches_count(seq, gap, pred);
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rmatch_indices_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<(usize, &'a str)>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_rmatch_indices_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_rmatch_indices_iter_post(s, pat, iter_seq),
    ensures
        // matches all match `pat`
        forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
            ==> {
                let (idx, ss) = iter_seq[i];
                &&& ss@ == pat@
                &&& is_char_boundary(s.as_bytes(), idx as int) && idx <= s.as_bytes().len() - pat@.as_bytes().len()
                &&& s.as_bytes().subrange(idx as int, idx + pat@.as_bytes().len() as int) == pat@.as_bytes()
            },
        // matches are empty if none matches `pat`
        iter_seq.len() == 0 <==> !pat@.is_subrange_of(s),
        // gaps and matches make up the original string
        exists |gap: Seq<Seq<char>>| {
            &&& #[trigger] gap.len() == iter_seq.len() + 1
            &&& forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1
                    ==> gap[i].len() > 0
                        ==> (!pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i]))
            &&& !pat@.is_subrange_of(gap.last())
            &&& s == gap.last() + iter_seq.map(|i: int, item: (usize, &'a str)| item.1@ + gap[i]).reverse().flatten()
            // ..and defines the indices
            &&& iter_seq.len() > 0 ==> iter_seq.last().0 == gap.last().as_bytes().len()
            &&& forall |i: int| #![trigger iter_seq[i].0] 0 <= i < iter_seq.len() - 1
                ==> iter_seq[i].0 == iter_seq[i+1].0 + pat@.as_bytes().len() + gap[i+1].as_bytes().len()
        },
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rmatch_indices_iter_post);
    let (seq, gap) = spec_rmatches(s, pat);
    assert(iter_seq.len() == seq.len());
    // #1: per-match postconditions
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len()
    implies {
        let (idx, ss) = iter_seq[i];
        &&& ss@ == pat@
        &&& is_char_boundary(s.as_bytes(), idx as int) && idx <= s.as_bytes().len() - pat@.as_bytes().len()
        &&& s.as_bytes().subrange(idx as int, idx + pat@.as_bytes().len() as int) == pat@.as_bytes()
    } by {
        let (idx, ss) = iter_seq[i];
        assert(ss@ == seq[i]);
        assert(seq[i] =~= pat@);
        assert(idx == rjoin(seq.skip(i + 1), gap.skip(i + 1)).as_bytes().len());
        let prefix = rjoin(seq.skip(i + 1), gap.skip(i + 1));
        let suffix = rjoin(seq.take(i), gap.take(i + 1));
        calc!{
            (==)
            s; {}
            rjoin(seq, gap); { lemma_rjoin_split_match_at(seq, gap, i) }
            prefix + seq[i] + suffix;
        }
        assert(s.as_bytes() == prefix.as_bytes() + seq[i].as_bytes() + suffix.as_bytes()) by {
            lemma_str_concat_lower(prefix, seq[i]);
            lemma_str_concat_lower(prefix + seq[i], suffix);
        }
        assert(s.as_bytes().take(idx as int) == prefix.as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(prefix);
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(seq[i].as_bytes() == pat@.as_bytes());
        assert(pat@.as_bytes().len() > 0);
        assert(idx + pat@.as_bytes().len() <= s.as_bytes().len());
        assert(s.as_bytes().subrange(idx as int, idx + pat@.as_bytes().len() as int) == pat@.as_bytes());
    }
    // #2: empty iff no subrange
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
    // #3: gap reconstruction
    assert(gap.len() == iter_seq.len() + 1);
    assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len() - 1 && gap[i].len() > 0
    implies !pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i])
    by {}
    assert(s == gap.last() + iter_seq.map(|i: int, item: (usize, &'a str)| item.1@ + gap[i]).reverse().flatten()) by {
        lemma_rjoin_alt_for_matches(seq, gap);
        let s1 = iter_seq.map(|i: int, item: (usize, &'a str)| item.1@ + gap[i]);
        let s2 = seq.map(|i: int, ss: Seq<char>| ss + gap[i]);
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i].1@ == seq[i]);
            assert(seq[i] == pat@);
        });
        assert(s1.reverse() == s2.reverse());
        s1.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
        assert(s2.reverse().flatten_alt() == s1.reverse().flatten());
    }
    // #4: index definitions
    assert(iter_seq.len() > 0 ==> iter_seq.last().0 == gap.last().as_bytes().len()) by {
        if iter_seq.len() > 0 {
            let i = iter_seq.len() - 1;
            assert(iter_seq.last() == iter_seq[i]);
            assert(iter_seq[i].0 == rjoin(seq.skip(i + 1), gap.skip(i + 1)).as_bytes().len());
            assert(seq.skip(i + 1).len() == 0);
            assert(gap.skip(i + 1).len() == 1);
            assert(rjoin(seq.skip(i + 1), gap.skip(i + 1)) == gap.last()) by {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            }
        }
    }
    assert forall |i: int| #![trigger iter_seq[i].0] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 == iter_seq[i+1].0 + pat@.as_bytes().len() + gap[i+1].as_bytes().len()
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let prefix1 = rjoin(seq.skip(i+1), gap.skip(i+1));
        let prefix2 = rjoin(seq.skip(i+2), gap.skip(i+2));
        lemma_rjoin_uncons(seq.skip(i+1), gap.skip(i+1));
        assert(seq.skip(i+1)[0] == seq[i+1]);
        assert(gap.skip(i+1)[0] == gap[i+1]);
        assert(seq.skip(i+1).skip(1) == seq.skip(i+2));
        assert(gap.skip(i+1).skip(1) == gap.skip(i+2));
        assert(prefix1 == prefix2 + seq[i+1] + gap[i+1]);
        assert(idx1 == prefix1.as_bytes().len());
        assert(idx2 == prefix2.as_bytes().len());
        assert(seq[i+1] == pat@);
        assert(prefix2.as_bytes() + seq[i+1].as_bytes() + gap[i+1].as_bytes() == prefix1.as_bytes()) by {
            lemma_str_concat_lower(prefix2, seq[i+1]);
            lemma_str_concat_lower(prefix2 + seq[i+1], gap[i+1]);
        }
    }
}

}
