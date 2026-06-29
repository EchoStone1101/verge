// Internal proof module for `str::match_indices` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
pub broadcast proof fn lemma_str_match_indices_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<(usize, &'a str)>)
    requires
        #[trigger] str_match_indices_iter_post(s, ch, iter_seq),
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
            ==> iter_seq[i].0 < iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| c == ch),
{
    axiom_char_matches_post(s, ch);
    reveal(str_match_indices_iter_post);
    let (seq, gap) = spec_matches(s, ch);
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
        // #1.1
        assert(ss@ == seq[i]);
        assert(seq[i] =~= seq![ch]);
        // #1.2 & 1.3
        assert(idx == join(seq.take(i), gap.take(i + 1)).as_bytes().len());
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        let tail = gap.skip(i).drop_first().map(|k: int, ss: Seq<char>| seq.skip(i)[k] + ss).flatten();
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, i) }
            seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss).flatten()
                + join(seq.skip(i), gap.skip(i));
                {
                    let s1 = seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss);
                    let s2 = seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss);
                    assert_seqs_equal!(s1 == s2);
                }
            seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss).flatten()
                + gap.skip(i).first() + tail;
                {
                    lemma_join_alt(seq.take(i), gap.take(i+1));
                    assert(gap.take(i+1).last() == gap.skip(i).first());
                }
            join(seq.take(i), gap.take(i+1)) + tail;
        }
        assert(s.as_bytes() == join(seq.take(i), gap.take(i + 1)).as_bytes() + tail.as_bytes()) by {
            lemma_str_concat_lower(join(seq.take(i), gap.take(i + 1)), tail);
        }
        assert(s.as_bytes().take(idx as int) == join(seq.take(i), gap.take(i + 1)).as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(join(seq.take(i), gap.take(i + 1)));
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + tail.as_bytes().len() == s.as_bytes().len());
        assert(idx_ch == join(seq.take(i), gap.take(i + 1)).len()) by {
            lemma_str_lower_lift(join(seq.take(i), gap.take(i + 1)));
        }
        assert(s[idx_ch] == tail[0]);
        assert(gap.skip(i).drop_first().len() > 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(seq.skip(i)[0] == seq[i]);
        assert(tail[0] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 < iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let s1 = join(seq.take(i), gap.take(i+1));
        let s2 = join(seq.take(i+1), gap.take(i+2));
        lemma_join_runcons(seq.take(i+1), gap.take(i+2));
        assert(seq.take(i+1).drop_last() == seq.take(i));
        assert(gap.take(i+2).drop_last() == gap.take(i+1));
        assert(idx1 == s1.as_bytes().len());
        assert(idx2 == s2.as_bytes().len());
        assert(s1.as_bytes() + seq.take(i+1).last().as_bytes() + gap.take(i+2).last().as_bytes() == s2.as_bytes()) by {
            lemma_str_concat_lower(s1, seq.take(i+1).last());
            lemma_str_concat_lower(s1 + seq.take(i+1).last(), gap.take(i+2).last());
        }
        assert(seq.take(i+1).last() =~= seq![ch]);
        assert(seq.take(i+1).last().as_bytes().len() > 0);
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
        lemma_str_matches_count(seq, gap, pred);
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_match_indices_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<(usize, &'a str)>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_match_indices_iter_post(s, f, iter_seq),
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
            ==> iter_seq[i].0 < iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true)),
{
    axiom_closure_matches_post(s, f);
    reveal(str_match_indices_iter_post);
    let (seq, gap) = spec_matches(s, f);
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
        // #1.1
        assert(ss@ == seq[i]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
        // #1.2 & 1.3
        assert(idx == join(seq.take(i), gap.take(i + 1)).as_bytes().len());
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        let tail = gap.skip(i).drop_first().map(|k: int, ss: Seq<char>| seq.skip(i)[k] + ss).flatten();
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, i) }
            seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss).flatten()
                + join(seq.skip(i), gap.skip(i));
                {
                    let s1 = seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss);
                    let s2 = seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss);
                    assert_seqs_equal!(s1 == s2);
                }
            seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss).flatten()
                + gap.skip(i).first() + tail;
                {
                    lemma_join_alt(seq.take(i), gap.take(i+1));
                    assert(gap.take(i+1).last() == gap.skip(i).first());
                }
            join(seq.take(i), gap.take(i+1)) + tail;
        }
        assert(s.as_bytes() == join(seq.take(i), gap.take(i + 1)).as_bytes() + tail.as_bytes()) by {
            lemma_str_concat_lower(join(seq.take(i), gap.take(i + 1)), tail);
        }
        assert(s.as_bytes().take(idx as int) == join(seq.take(i), gap.take(i + 1)).as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(join(seq.take(i), gap.take(i + 1)));
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + tail.as_bytes().len() == s.as_bytes().len());
        assert(idx_ch == join(seq.take(i), gap.take(i + 1)).len()) by {
            lemma_str_lower_lift(join(seq.take(i), gap.take(i + 1)));
        }
        assert(s[idx_ch] == tail[0]);
        assert(gap.skip(i).drop_first().len() > 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(seq.skip(i)[0] == seq[i]);
        assert(tail[0] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 < iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let s1 = join(seq.take(i), gap.take(i+1));
        let s2 = join(seq.take(i+1), gap.take(i+2));
        lemma_join_runcons(seq.take(i+1), gap.take(i+2));
        assert(seq.take(i+1).drop_last() == seq.take(i));
        assert(gap.take(i+2).drop_last() == gap.take(i+1));
        assert(idx1 == s1.as_bytes().len());
        assert(idx2 == s2.as_bytes().len());
        assert(s1.as_bytes() + seq.take(i+1).last().as_bytes() + gap.take(i+2).last().as_bytes() == s2.as_bytes()) by {
            lemma_str_concat_lower(s1, seq.take(i+1).last());
            lemma_str_concat_lower(s1 + seq.take(i+1).last(), gap.take(i+2).last());
        }
        assert(seq.take(i+1).last().len() == 1);
        assert(seq.take(i+1).last().as_bytes().len() > 0);
    }
    // #3
    assert(iter_seq.len() == s.count(|c: char| call_ensures(f, (c,), true))) by {
        let pred = |c: char| call_ensures(f, (c,), true);
        assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c))
        by {
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
        implies seq[i].len() == 1 && pred(seq[i][0])
        by {}
        lemma_str_matches_count(seq, gap, pred);
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_match_indices_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<(usize, &'a str)>)
    requires
        #[trigger] str_match_indices_iter_post(s, chars, iter_seq),
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
            ==> iter_seq[i].0 < iter_seq[i+1].0,
        // matches are exhaustive
        iter_seq.len() == s.count(|c: char| chars@.contains(c)),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_match_indices_iter_post);
    let (seq, gap) = spec_matches(s, chars);
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
        // #1.1
        assert(ss@ == seq[i]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
        // #1.2 & 1.3
        assert(idx == join(seq.take(i), gap.take(i + 1)).as_bytes().len());
        let idx_ch = decode_utf8(s.as_bytes().take(idx as int)).len() as int;
        let tail = gap.skip(i).drop_first().map(|k: int, ss: Seq<char>| seq.skip(i)[k] + ss).flatten();
        calc!{
            (==)
            s; {}
            join(seq, gap); { lemma_join_split_at(seq, gap, i) }
            seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss).flatten()
                + join(seq.skip(i), gap.skip(i));
                {
                    let s1 = seq.take(i).map(|k: int, ss: Seq<char>| gap[k] + ss);
                    let s2 = seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss);
                    assert_seqs_equal!(s1 == s2);
                }
            seq.take(i).map(|k: int, ss: Seq<char>| gap.take(i+1)[k] + ss).flatten()
                + gap.skip(i).first() + tail;
                {
                    lemma_join_alt(seq.take(i), gap.take(i+1));
                    assert(gap.take(i+1).last() == gap.skip(i).first());
                }
            join(seq.take(i), gap.take(i+1)) + tail;
        }
        assert(s.as_bytes() == join(seq.take(i), gap.take(i + 1)).as_bytes() + tail.as_bytes()) by {
            lemma_str_concat_lower(join(seq.take(i), gap.take(i + 1)), tail);
        }
        assert(s.as_bytes().take(idx as int) == join(seq.take(i), gap.take(i + 1)).as_bytes());
        assert(s.as_bytes().take(idx as int).is_utf8()) by {
            lemma_str_is_utf8(join(seq.take(i), gap.take(i + 1)));
        }
        lemma_str_is_utf8(s);
        lemma_char_boundary_iff_utf8(s.as_bytes(), idx as int);
        assert(idx + tail.as_bytes().len() == s.as_bytes().len());
        assert(idx_ch == join(seq.take(i), gap.take(i + 1)).len()) by {
            lemma_str_lower_lift(join(seq.take(i), gap.take(i + 1)));
        }
        assert(s[idx_ch] == tail[0]);
        assert(gap.skip(i).drop_first().len() > 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(seq.skip(i)[0] == seq[i]);
        assert(tail[0] == seq[i][0]);
    }
    // #2
    assert forall |i: int| #![trigger iter_seq[i]] 0 <= i < iter_seq.len() - 1
    implies iter_seq[i].0 < iter_seq[i+1].0
    by {
        let idx1 = iter_seq[i].0 as int;
        let idx2 = iter_seq[i+1].0 as int;
        let s1 = join(seq.take(i), gap.take(i+1));
        let s2 = join(seq.take(i+1), gap.take(i+2));
        lemma_join_runcons(seq.take(i+1), gap.take(i+2));
        assert(seq.take(i+1).drop_last() == seq.take(i));
        assert(gap.take(i+2).drop_last() == gap.take(i+1));
        assert(idx1 == s1.as_bytes().len());
        assert(idx2 == s2.as_bytes().len());
        assert(s1.as_bytes() + seq.take(i+1).last().as_bytes() + gap.take(i+2).last().as_bytes() == s2.as_bytes()) by {
            lemma_str_concat_lower(s1, seq.take(i+1).last());
            lemma_str_concat_lower(s1 + seq.take(i+1).last(), gap.take(i+2).last());
        }
        assert(seq.take(i+1).last().len() == 1);
        assert(seq.take(i+1).last().as_bytes().len() > 0);
    }
    // #3
    assert(iter_seq.len() == s.count(|c: char| chars@.contains(c))) by {
        let pred = |c: char| chars@.contains(c);
        assert forall |i: int| #![trigger gap[i]] 0 <= i < gap.len()
        implies gap[i].all(|c: char| !pred(c))
        by {
            let neg_pred = |c: char| !chars@.contains(c);
            assert(gap[i].all(neg_pred));
            assert forall |j: int| 0 <= j < gap[i].len()
                implies !pred(gap[i][j]) by {
                assert(neg_pred(gap[i][j]));
            }
        }
        assert forall |i: int| #![trigger seq[i]] 0 <= i < seq.len()
        implies seq[i].len() == 1 && pred(seq[i][0])
        by {}
        lemma_str_matches_count(seq, gap, pred);
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_match_indices_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<(usize, &'a str)>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_match_indices_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_match_indices_iter_post(s, pat, iter_seq),
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
                        ==> (!pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@))
            &&& !pat@.is_subrange_of(gap.last())
            &&& s == iter_seq.map(|i: int, item: (usize, &'a str)| gap[i] + item.1@).flatten() + gap.last()
            // ..and defines the indices
            &&& iter_seq.len() > 0 ==> iter_seq.first().0 == gap.first().as_bytes().len()
            &&& forall |i: int| #![trigger iter_seq[i].0] 1 <= i < iter_seq.len()
                ==> iter_seq[i].0 == iter_seq[i-1].0 + pat@.as_bytes().len() + gap[i].as_bytes().len()
        },
{
    axiom_string_matches_post(s, pat);
    reveal(str_match_indices_iter_post);
    let (seq, gap) = spec_matches(s, pat);
    assert(iter_seq.len() == seq.len());
    // #1
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
        assert(idx == join(seq.take(i), gap.take(i + 1)).as_bytes().len());
        let prefix = join(seq.take(i), gap.take(i + 1));
        let rest = join(seq.skip(i + 1), gap.skip(i + 1));
        lemma_join_split_match_at(seq, gap, i);
        assert(s == prefix + seq[i] + rest);
        assert(s.as_bytes() == prefix.as_bytes() + seq[i].as_bytes() + rest.as_bytes()) by {
            lemma_str_concat_lower(prefix, seq[i]);
            lemma_str_concat_lower(prefix + seq[i], rest);
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
    assert(s == iter_seq.map(|i: int, item: (usize, &'a str)| gap[i] + item.1@).flatten() + gap.last()) by {
        lemma_join_alt(seq, gap);
        let s1 = iter_seq.map(|i: int, item: (usize, &'a str)| gap[i] + item.1@);
        let s2 = seq.map(|i: int, ss: Seq<char>| gap[i] + ss);
        assert_seqs_equal!(s1 == s2, i => {
            assert(iter_seq[i].1@ == seq[i]);
        });
    }
    assert(iter_seq.len() > 0 ==> iter_seq.first().0 == gap.first().as_bytes().len()) by {
        if iter_seq.len() > 0 {
            assert(iter_seq.first() == iter_seq[0]);
            assert(iter_seq[0].0 == join(seq.take(0), gap.take(1)).as_bytes().len());
            assert(join(seq.take(0), gap.take(1)) == gap.first()) by {
                reveal_with_fuel(Seq::<_>::flatten, 2);
            }
        }
    }
    assert forall |i: int| #![trigger iter_seq[i].0] 1 <= i < iter_seq.len()
    implies iter_seq[i].0 == iter_seq[i-1].0 + pat@.as_bytes().len() + gap[i].as_bytes().len()
    by {
        let idx1 = iter_seq[i-1].0 as int;
        let idx2 = iter_seq[i].0 as int;
        let s1 = join(seq.take(i-1), gap.take(i));
        let s2 = join(seq.take(i), gap.take(i+1));
        lemma_join_runcons(seq.take(i), gap.take(i+1));
        assert(seq.take(i).drop_last() == seq.take(i-1));
        assert(gap.take(i+1).drop_last() == gap.take(i));
        assert(seq.take(i).last() == seq[i-1]);
        assert(gap.take(i+1).last() == gap[i]);
        assert(idx1 == s1.as_bytes().len());
        assert(idx2 == s2.as_bytes().len());
        assert(seq[i-1] == pat@);
        assert(s1.as_bytes() + seq[i-1].as_bytes() + gap[i].as_bytes() == s2.as_bytes()) by {
            lemma_str_concat_lower(s1, seq[i-1]);
            lemma_str_concat_lower(s1 + seq[i-1], gap[i]);
        }
    }
}

}
