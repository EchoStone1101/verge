// Internal proof module for `str::strip_suffix` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
pub broadcast proof fn lemma_str_strip_suffix_char<'a>(s: Seq<char>, ch: char, ret: Option<&'a str>)
    requires
        #[trigger] str_strip_suffix_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && s.last() != ch),
                Some(o) => {
                    &&& s.len() > 0
                    &&& s.last() == ch
                    &&& o@ == s.drop_last()
                },
            }
        }),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_strip_suffix_post);
    let (seq, gap) = spec_rmatches(s, ch);
    match ret {
        None => {
            if s.len() > 0 && s.last() == ch {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                assert_by_contradiction!(seq.len() > 0, {
                    assert(gap.len() == 1);
                    assert(gap.first() == s);
                    assert(gap.first().last() == ch);
                    assert(!gap.first().contains(ch));
                });
                assert_by_contradiction!(gap.first().len() == 0, {
                    assert(s.last() == gap.first().last());
                    assert(gap.first().last() == ch);
                    assert(!gap.first().contains(ch));
                });
            }
        },
        Some(o) => {
            assert(seq.first() == seq![ch] && gap.first().len() == 0);
            let rest = rjoin(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten_alt, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
            assert(parts.len() > 0);
            assert(parts.first() == gap[1] + seq[0]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
            assert(parts.reverse().last() == parts.first());
            assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
            assert(s == parts.reverse().flatten_alt() + gap[0]);
            lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
            assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
            assert(s == rest + seq[0] + gap[0]);
            assert(gap[0] == Seq::<char>::empty());
            assert(seq[0] == seq![ch]);
            assert(s == rest + seq![ch]);
            assert(s.last() == ch);
            assert((rest + seq![ch]).drop_last() == rest);
            assert(o@ == s.drop_last());
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_strip_suffix_closure<'a, F>(s: Seq<char>, f: F, ret: Option<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_strip_suffix_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && call_ensures(f, (s.last(),), false)),
                Some(o) => {
                    &&& s.len() > 0
                    &&& call_ensures(f, (s.last(),), true)
                    &&& o@ == s.drop_last()
                },
            }
        }),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_strip_suffix_post);
    let (seq, gap) = spec_rmatches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);
    match ret {
        None => {
            if s.len() > 0 {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                if seq.len() == 0 {
                    assert(gap.len() == 1);
                    assert(gap.first() == s);
                    assert(gap.first().last() == s.last());
                    assert(gap.first().all(pred));
                    assert(pred(gap.first().last()));
                    assert(call_ensures(f, (gap.first().last(),), false));
                } else {
                    assert(gap.first().len() > 0);
                    assert(s.last() == gap.first().last());
                    assert(gap.first().all(pred));
                    assert(pred(gap.first().last()));
                    assert(call_ensures(f, (gap.first().last(),), false));
                }
            }
        },
        Some(o) => {
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(gap.first().len() == 0);
            let rest = rjoin(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten_alt, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
            assert(parts.len() > 0);
            assert(parts.first() == gap[1] + seq[0]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
            assert(parts.reverse().last() == parts.first());
            assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
            assert(s == parts.reverse().flatten_alt() + gap[0]);
            lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
            assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
            assert(s == rest + seq[0] + gap[0]);
            assert(gap[0] == Seq::<char>::empty());
            let last_ch = seq[0][0];
            assert_seqs_equal!(seq[0] == seq![last_ch]);
            assert(s == rest + seq![last_ch]);
            assert(s.last() == last_ch);
            assert(call_ensures(f, (s.last(),), true));
            assert((rest + seq![last_ch]).drop_last() == rest);
            assert(o@ == s.drop_last());
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_strip_suffix_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], ret: Option<&'a str>)
    requires
        #[trigger] str_strip_suffix_post(s, chars, ret),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && !chars@.contains(s.last())),
                Some(o) => {
                    &&& s.len() > 0
                    &&& chars@.contains(s.last())
                    &&& o@ == s.drop_last()
                },
            }
        }),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_strip_suffix_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let pred = |c: char| !chars@.contains(c);
    match ret {
        None => {
            if s.len() > 0 && chars@.contains(s.last()) {
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                assert_by_contradiction!(seq.len() > 0, {
                    assert(gap.len() == 1);
                    assert(gap.first() == s);
                    assert(gap.first().last() == s.last());
                    assert(gap.first().all(pred));
                    assert(pred(gap.first().last()));
                    assert(!chars@.contains(gap.first().last()));
                });
                assert_by_contradiction!(gap.first().len() == 0, {
                    assert(s.last() == gap.first().last());
                    assert(gap.first().all(pred));
                    assert(pred(gap.first().last()));
                    assert(!chars@.contains(gap.first().last()));
                });
            }
        },
        Some(o) => {
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(gap.first().len() == 0);
            let rest = rjoin(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten_alt, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
            assert(parts.len() > 0);
            assert(parts.first() == gap[1] + seq[0]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
            assert(parts.reverse().last() == parts.first());
            assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
            assert(s == parts.reverse().flatten_alt() + gap[0]);
            lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
            assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
            assert(s == rest + seq[0] + gap[0]);
            assert(gap[0] == Seq::<char>::empty());
            let last_ch = seq[0][0];
            assert_seqs_equal!(seq[0] == seq![last_ch]);
            assert(s == rest + seq![last_ch]);
            assert(s.last() == last_ch);
            assert(chars@.contains(s.last()));
            assert((rest + seq![last_ch]).drop_last() == rest);
            assert(o@ == s.drop_last());
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_strip_suffix_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<&'a str>)
    requires
        #[trigger] str_strip_suffix_post(s, pat, ret),
    ensures
        ({
            match ret {
                None => !pat@.is_suffix_of(s),
                Some(o) => {
                    &&& pat@.is_suffix_of(s)
                    &&& o@ == s.take(s.len() - pat@.len())
                },
            }
        }),
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_strip_suffix_post);
    let (seq, gap) = spec_rmatches(s, pat);
    match ret {
        None => {
            if pat@.is_suffix_of(s) {
                if pat@.len() == 0 {
                    assert(seq.len() == s.len() + 1);
                    assert(gap.first().len() == 0);
                } else {
                    reveal_with_fuel(Seq::<_>::flatten_alt, 4);
                    assert_by_contradiction!(seq.len() > 0, {
                        assert(gap.len() == 1);
                        assert(gap.last() == s);
                        assert(!pat@.is_subrange_of(gap.last()));
                        lemma_seq_is_subrange_alt(gap.last(), pat@);
                    });
                    assert_by_contradiction!(gap.first().len() == 0, {
                        assert(seq.first() == pat@);
                        assert(gap.first().len() > 0);
                        assert(gap.len() > 1);
                        assert(gap.first().len() > 0 ==> !pat@.is_suffix_of(pat@ + gap.first()) && !pat@.is_infix_of(pat@ + gap.first()));
                        let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
                        assert(parts.len() > 0);
                        assert(parts.first() == gap[1] + seq[0]);
                        assert(parts.reverse().last() == parts.first());
                        assert(parts.reverse().flatten_alt() == parts.reverse().drop_last().flatten_alt() + parts.reverse().last());
                        assert(s == parts.reverse().flatten_alt() + gap[0]);
                        lemma_concat_associative(parts.reverse().drop_last().flatten_alt(), gap[1], seq[0]);
                        assert(s == (parts.reverse().drop_last().flatten_alt() + gap[1]) + pat@ + gap[0]);
                        assert((pat@ + gap[0]).is_suffix_of(s));
                        assert(pat@.is_suffix_of(pat@ + gap[0]));
                        assert(!pat@.is_suffix_of(pat@ + gap[0]));
                    });
                }
            }
        },
        Some(o) => {
            if pat@.len() == 0 {
                assert_seqs_equal!(seq[0] == pat@);
            } else {
                assert(seq.first() == pat@);
            }
            assert(gap.first().len() == 0);
            let rest = rjoin(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten_alt, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| ss + seq.skip(1)[i]);
            assert(parts.len() > 0);
            assert(parts.first() == gap[1] + seq[0]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert_seqs_equal!(parts.reverse().drop_last() == rest_parts.reverse());
            assert(parts.reverse().last() == parts.first());
            assert(parts.reverse().flatten_alt() == rest_parts.reverse().flatten_alt() + (gap[1] + seq[0]));
            assert(s == parts.reverse().flatten_alt() + gap[0]);
            lemma_concat_associative(rest_parts.reverse().flatten_alt(), gap[1], seq[0]);
            assert(rest == rest_parts.reverse().flatten_alt() + gap[1]);
            assert(s == rest + seq[0] + gap[0]);
            assert(gap[0] == Seq::<char>::empty());
            assert(seq[0] == pat@);
            assert(s == rest + pat@);
            assert(pat@.is_suffix_of(s));
            assert(s.len() == rest.len() + pat@.len());
            assert(s.len() - pat@.len() == rest.len());
            assert((rest + pat@).take(rest.len() as int) == rest);
            assert(o@ == s.take(s.len() - pat@.len()));
        },
    }
}

}
