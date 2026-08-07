// Internal proof module for `str::strip_prefix` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, ch; (ret is Some, if ret is Some { ret->0@ } else { Seq::<char>::empty() }))]
pub broadcast proof fn lemma_str_strip_prefix_char<'a>(s: Seq<char>, ch: char, ret: Option<&'a str>)
    requires
        #[trigger] str_strip_prefix_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && s.first() != ch),
                Some(o) => {
                    &&& s.len() > 0
                    &&& s.first() == ch
                    &&& o@ == s.drop_first()
                },
            }
        }),
{
    axiom_char_matches_post(s, ch);
    reveal(str_strip_prefix_post);
    let (seq, gap) = spec_matches(s, ch);
    match ret {
        None => {
            if s.len() > 0 && s.first() == ch {
                reveal_with_fuel(Seq::<_>::flatten, 2);
                assert_by_contradiction!(seq.len() > 0, {
                    assert(gap.len() == 1);
                    assert(gap.first() == s);
                    assert(gap.first()[0] == ch);
                    assert(!gap.first().contains(ch));
                });
                assert_by_contradiction!(gap.first().len() == 0, {
                    assert(s.first() == gap.first()[0]);
                    assert(gap.first()[0] == ch);
                    assert(!gap.first().contains(ch));
                });
            }
        },
        Some(o) => {
            assert(seq.first() == seq![ch] && gap.first().len() == 0);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s[0] == seq.first()[0]);
            assert(s.len() > 0);
            let rest = join(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == parts.flatten());
            assert(s == seq[0] + rest);
            assert(s == seq![ch] + rest);
            assert((seq![ch] + rest).drop_first() == rest);
            assert(o@ == s.drop_first());
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_strip_prefix_closure<'a, F>(s: Seq<char>, f: F, ret: Option<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_strip_prefix_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && call_ensures(f, (s.first(),), false)),
                Some(o) => {
                    &&& s.len() > 0
                    &&& call_ensures(f, (s.first(),), true)
                    &&& o@ == s.drop_first()
                },
            }
        }),
{
    axiom_closure_matches_post(s, f);
    reveal(str_strip_prefix_post);
    let (seq, gap) = spec_matches(s, f);
    match ret {
        None => {
            if s.len() > 0 {
                reveal_with_fuel(Seq::<_>::flatten, 2);
                let pred = |c: char| call_ensures(f, (c,), false);
                if seq.len() == 0 {
                    assert(gap.len() == 1);
                    assert(gap.first() == s);
                    assert(gap.first()[0] == s.first());
                    assert(pred(gap.first()[0]));
                    assert(call_ensures(f, (gap.first()[0],), false));
                } else {
                    assert(gap.first().len() > 0);
                    assert(s.first() == gap.first()[0]);
                    assert(pred(gap.first()[0]));
                    assert(call_ensures(f, (gap.first()[0],), false));
                }
            }
        },
        Some(o) => {
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(gap.first().len() == 0);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s[0] == seq.first()[0]);
            assert(s.len() > 0);
            let rest = join(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == parts.flatten());
            assert(s == seq[0] + rest);
            assert((seq[0] + rest).drop_first() == rest);
            assert(o@ == s.drop_first());
        },
    }
}

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, chars@; (ret is Some, if ret is Some { ret->0@ } else { Seq::<char>::empty() }))]
pub broadcast proof fn lemma_str_strip_prefix_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], ret: Option<&'a str>)
    requires
        #[trigger] str_strip_prefix_post(s, chars, ret),
    ensures
        ({
            match ret {
                None => s.len() == 0 || (s.len() > 0 && !chars@.contains(s.first())),
                Some(o) => {
                    &&& s.len() > 0
                    &&& chars@.contains(s.first())
                    &&& o@ == s.drop_first()
                },
            }
        }),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_strip_prefix_post);
    let (seq, gap) = spec_matches(s, chars);
    match ret {
        None => {
            if s.len() > 0 && chars@.contains(s.first()) {
                reveal_with_fuel(Seq::<_>::flatten, 2);
                let pred = |c: char| !chars@.contains(c);
                assert_by_contradiction!(seq.len() > 0, {
                    assert(gap.len() == 1);
                    assert(gap.first() == s);
                    assert(gap.first()[0] == s.first());
                    assert(pred(gap.first()[0]));
                    assert(!chars@.contains(gap.first()[0]));
                });
                assert_by_contradiction!(gap.first().len() == 0, {
                    assert(s.first() == gap.first()[0]);
                    assert(pred(gap.first()[0]));
                    assert(!chars@.contains(gap.first()[0]));
                });
            }
        },
        Some(o) => {
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(gap.first().len() == 0);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s[0] == seq.first()[0]);
            assert(s.len() > 0);
            let rest = join(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == parts.flatten());
            assert(s == seq[0] + rest);
            assert((seq[0] + rest).drop_first() == rest);
            assert(o@ == s.drop_first());
        },
    }
}

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, pat@; (ret is Some, if ret is Some { ret->0@ } else { Seq::<char>::empty() }))]
pub broadcast proof fn lemma_str_strip_prefix_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<&'a str>)
    requires
        #[trigger] str_strip_prefix_post(s, pat, ret),
    ensures
        ({
            match ret {
                None => !pat@.is_prefix_of(s),
                Some(o) => {
                    &&& pat@.is_prefix_of(s)
                    &&& o@ == s.skip(pat@.len() as int)
                },
            }
        }),
{
    axiom_string_matches_post(s, pat);
    reveal(str_strip_prefix_post);
    let (seq, gap) = spec_matches(s, pat);
    match ret {
        None => {
            if pat@.is_prefix_of(s) {
                if pat@.len() == 0 {
                    assert(seq.len() == s.len() + 1);
                    assert(gap.first().len() == 0);
                } else {
                    reveal_with_fuel(Seq::<_>::flatten, 4);
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
                        assert(gap.first().len() > 0 ==> !pat@.is_prefix_of(gap.first() + pat@) && !pat@.is_infix_of(gap.first() + pat@));
                        let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
                        assert(parts.len() > 0);
                        assert(parts.first() == seq[0] + gap[1]);
                        assert(s == gap[0] + parts.flatten());
                        lemma_concat_associative(gap[0], seq[0], gap[1]);
                        assert(s == (gap[0] + pat@ + gap[1]) + parts.drop_first().flatten());
                        assert((gap[0] + pat@).is_prefix_of(s));
                        assert(pat@.is_prefix_of(gap[0] + pat@));
                        assert(!pat@.is_prefix_of(gap[0] + pat@));
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
            let rest = join(seq.skip(1), gap.skip(1));
            assert(o@ == rest);
            reveal_with_fuel(Seq::<_>::flatten, 4);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == gap[0] + parts.flatten());
            assert(gap[0] == Seq::<char>::empty());
            assert(seq[0] == pat@);
            assert(s == pat@ + rest);
            assert(pat@.is_prefix_of(s));
            assert((pat@ + rest).skip(pat@.len() as int) == rest);
            assert(o@ == s.skip(pat@.len() as int));
        },
    }
}

}
