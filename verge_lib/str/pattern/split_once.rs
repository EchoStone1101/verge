// Internal proof module for `str::split_once` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
pub broadcast proof fn lemma_str_split_once_char<'a>(s: Seq<char>, ch: char, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_split_once_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => !s.contains(ch),
                Some((head, tail)) => {
                    // `head` does not contain `ch`
                    &&& !head@.contains(ch)
                    // `head` and `tail` make up the original string
                    &&& s == head@.push(ch) + tail@
                },
            }
        }),
{
    axiom_char_matches_post(s, ch);
    reveal(str_split_once_post);
    let (seq, gap) = spec_matches(s, ch);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(!s.contains(ch));
        },
        Some((head, tail)) => {
            assert(head@ == gap.first());
            assert(!head@.contains(ch));
            assert(seq.first() == seq![ch]);
            assert(tail@ == join(seq.skip(1), gap.skip(1)));
            let rest = join(seq.skip(1), gap.skip(1));
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == gap.first() + parts.flatten());
            assert(s == gap.first() + seq[0] + rest);
            assert_seqs_equal!(head@.push(ch) == gap.first() + seq![ch]);
            assert(s == head@.push(ch) + tail@);
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_split_once_closure<'a, F>(s: Seq<char>, f: F, ret: Option<(&'a str, &'a str)>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_split_once_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ({
            match ret {
                None => forall|i: int| 0 <= i < s.len() ==> #[trigger] call_ensures(f, (s[i],), false),
                Some((head, tail)) => {
                    // `head` does not match `f`
                    &&& forall|i: int| 0 <= i < head@.len() ==> #[trigger] call_ensures(f, (head@[i],), false)
                    // `head` and `tail` make up the original string
                    &&& head@.is_prefix_of(s)
                    &&& tail@.is_suffix_of(s)
                    &&& head@.len() + tail@.len() == s.len() - 1
                    &&& call_ensures(f, (s[head@.len() as int],), true)
                },
            }
        }),
{
    axiom_closure_matches_post(s, f);
    reveal(str_split_once_post);
    let (seq, gap) = spec_matches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < s.len()
                implies #[trigger] call_ensures(f, (s[i],), false)
            by {
                assert(s[i] == gap.first()[i]);
                assert(pred(gap.first()[i]));
            }
        },
        Some((head, tail)) => {
            assert(head@ == gap.first());
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < head@.len()
                implies #[trigger] call_ensures(f, (head@[i],), false)
            by {
                assert(pred(gap.first()[i]));
            }
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(tail@ == join(seq.skip(1), gap.skip(1)));
            let rest = join(seq.skip(1), gap.skip(1));
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == gap.first() + parts.flatten());
            assert(s == head@ + seq[0] + tail@);
            let d = seq[0][0];
            assert_seqs_equal!(seq[0] == seq![d]);
            assert(s == head@ + seq![d] + tail@);
            assert(head@.is_prefix_of(s));
            assert(tail@.is_suffix_of(s));
            assert(head@.len() + tail@.len() == s.len() - 1);
            assert(s[head@.len() as int] == d);
            assert(call_ensures(f, (s[head@.len() as int],), true));
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_split_once_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_split_once_post(s, chars, ret),
    ensures
        ({
            match ret {
                None => forall|i: int| 0 <= i < s.len() ==> !(#[trigger] chars@.contains(s[i])),
                Some((head, tail)) => {
                    // `head` does not match `chars`
                    &&& forall|i: int| 0 <= i < head@.len() ==> !(#[trigger] chars@.contains(head@[i]))
                    // `head` and `tail` make up the original string
                    &&& head@.is_prefix_of(s)
                    &&& tail@.is_suffix_of(s)
                    &&& head@.len() + tail@.len() == s.len() - 1
                    &&& chars@.contains(s[head@.len() as int])
                },
            }
        }),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_split_once_post);
    let (seq, gap) = spec_matches(s, chars);
    let pred = |c: char| !chars@.contains(c);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < s.len()
                implies !(#[trigger] chars@.contains(s[i]))
            by {
                assert(s[i] == gap.first()[i]);
                assert(pred(gap.first()[i]));
            }
        },
        Some((head, tail)) => {
            assert(head@ == gap.first());
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < head@.len()
                implies !(#[trigger] chars@.contains(head@[i]))
            by {
                assert(pred(gap.first()[i]));
            }
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(tail@ == join(seq.skip(1), gap.skip(1)));
            let rest = join(seq.skip(1), gap.skip(1));
            reveal_with_fuel(Seq::<_>::flatten, 3);
            let parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
            let rest_parts = gap.skip(1).drop_first().map(|i: int, ss: Seq<char>| seq.skip(1)[i] + ss);
            assert(parts.len() > 0);
            assert(parts.first() == seq[0] + gap[1]);
            assert_seqs_equal!(parts.drop_first() == rest_parts);
            assert(rest == gap[1] + rest_parts.flatten());
            lemma_concat_associative(seq[0], gap[1], rest_parts.flatten());
            assert(parts.flatten() == seq[0] + rest);
            assert(s == gap.first() + parts.flatten());
            assert(s == head@ + seq[0] + tail@);
            let d = seq[0][0];
            assert_seqs_equal!(seq[0] == seq![d]);
            assert(s == head@ + seq![d] + tail@);
            assert(head@.is_prefix_of(s));
            assert(tail@.is_suffix_of(s));
            assert(head@.len() + tail@.len() == s.len() - 1);
            assert(s[head@.len() as int] == d);
            assert(chars@.contains(s[head@.len() as int]));
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_split_once_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_split_once_post(s, pat, ret),
    ensures
        ({
            match (ret, pat@.len() > 0) {
                (None, _) => !pat@.is_subrange_of(s),
                (Some((head, tail)), false) => head@.len() == 0 && tail@ == s,
                (Some((head, tail)), true) => {
                    // `head + pat` does not match `pat` except at the end
                    &&& head@.len() > 0 ==>
                            !pat@.is_prefix_of(head@ + pat@) && !pat@.is_infix_of(head@ + pat@)
                    // `head` and `tail` make up the original string
                    &&& s == head@ + pat@ + tail@
                },
            }
        }),
{
    axiom_string_matches_post(s, pat);
    reveal(str_split_once_post);
    let (seq, gap) = spec_matches(s, pat);
    match (ret, pat@.len() > 0) {
        (None, _) => {
            assert_by_contradiction!(!pat@.is_subrange_of(s), {
                reveal_with_fuel(Seq::<_>::flatten, 2);
                assert(s == gap.last());
                assert(!pat@.is_subrange_of(gap.last()));
            });
        },
        (Some((head, tail)), pat_empty) => {
            assert(head@ == gap.first());
            assert(head@.len() > 0 ==> !pat@.is_prefix_of(head@ + pat@) && !pat@.is_infix_of(head@ + pat@));
            calc!{
                (==)
                s; {}
                join(seq, gap); {
                    lemma_join_uncons(seq, gap);
                    assert(gap[0] == head@);
                    assert(seq[0] =~= pat@);
                }
                head@ + pat@ + join(seq.skip(1), gap.skip(1)); {}
                head@ + pat@ + tail@;
            }
            if pat_empty {
                assert(head@.len() > 0 ==> !pat@.is_prefix_of(head@ + pat@) && !pat@.is_infix_of(head@ + pat@));
            } else {
                assert(head@.len() == 0);
                assert(tail@ == s);
            }
        },
    }
}

}
