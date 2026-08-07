// Internal proof module for `str::rsplit_once` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, ch; (ret is Some, if ret is Some { ((ret->0).0@, (ret->0).1@) } else { (Seq::<char>::empty(), Seq::<char>::empty()) }))]
pub broadcast proof fn lemma_str_rsplit_once_char<'a>(s: Seq<char>, ch: char, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_rsplit_once_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => !s.contains(ch),
                Some((head, tail)) => {
                    // `tail` does not contain `ch`
                    &&& !tail@.contains(ch)
                    // `head` and `tail` make up the original string
                    &&& s == head@.push(ch) + tail@
                },
            }
        }),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rsplit_once_post);
    let (seq, gap) = spec_rmatches(s, ch);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(gap.first() == s);
            assert(!s.contains(ch));
        },
        Some((head, tail)) => {
            assert(tail@ == gap.first());
            assert(!tail@.contains(ch));
            assert(seq.first() == seq![ch]);
            assert(head@ == rjoin(seq.skip(1), gap.skip(1)));
            lemma_rjoin_uncons(seq, gap);
            assert(s == head@ + seq[0] + tail@);
            assert_seqs_equal!(head@.push(ch) == head@ + seq![ch]);
            assert(s == head@.push(ch) + tail@);
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rsplit_once_closure<'a, F>(s: Seq<char>, f: F, ret: Option<(&'a str, &'a str)>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rsplit_once_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ({
            match ret {
                None => forall|i: int| 0 <= i < s.len() ==> #[trigger] call_ensures(f, (s[i],), false),
                Some((head, tail)) => {
                    // `tail` does not match `f`
                    &&& forall|i: int| 0 <= i < tail@.len() ==> #[trigger] call_ensures(f, (tail@[i],), false)
                    // `head` and `tail` make up the original string
                    &&& head@.is_prefix_of(s)
                    &&& tail@.is_suffix_of(s)
                    &&& head@.len() + tail@.len() == s.len() - 1
                    &&& call_ensures(f, (s[head@.len() as int],), true)
                },
            }
        }),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rsplit_once_post);
    let (seq, gap) = spec_rmatches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
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
            assert(tail@ == gap.first());
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < tail@.len()
                implies #[trigger] call_ensures(f, (tail@[i],), false)
            by {
                assert(pred(gap.first()[i]));
            }
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(head@ == rjoin(seq.skip(1), gap.skip(1)));
            lemma_rjoin_uncons(seq, gap);
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
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, chars@; (ret is Some, if ret is Some { ((ret->0).0@, (ret->0).1@) } else { (Seq::<char>::empty(), Seq::<char>::empty()) }))]
pub broadcast proof fn lemma_str_rsplit_once_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_rsplit_once_post(s, chars, ret),
    ensures
        ({
            match ret {
                None => forall|i: int| 0 <= i < s.len() ==> !(#[trigger] chars@.contains(s[i])),
                Some((head, tail)) => {
                    // `tail` does not match `chars`
                    &&& forall|i: int| 0 <= i < tail@.len() ==> !(#[trigger] chars@.contains(tail@[i]))
                    // `head` and `tail` make up the original string
                    &&& head@.is_prefix_of(s)
                    &&& tail@.is_suffix_of(s)
                    &&& head@.len() + tail@.len() == s.len() - 1
                    &&& chars@.contains(s[head@.len() as int])
                },
            }
        }),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rsplit_once_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let pred = |c: char| !chars@.contains(c);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
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
            assert(tail@ == gap.first());
            assert(gap.first().all(pred));
            assert forall|i: int| 0 <= i < tail@.len()
                implies !(#[trigger] chars@.contains(tail@[i]))
            by {
                assert(pred(gap.first()[i]));
            }
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(head@ == rjoin(seq.skip(1), gap.skip(1)));
            lemma_rjoin_uncons(seq, gap);
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
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, pat@; (ret is Some, if ret is Some { ((ret->0).0@, (ret->0).1@) } else { (Seq::<char>::empty(), Seq::<char>::empty()) }))]
pub broadcast proof fn lemma_str_rsplit_once_string<'a, 'b>(s: Seq<char>, pat: &'b str, ret: Option<(&'a str, &'a str)>)
    requires
        #[trigger] str_rsplit_once_post(s, pat, ret),
    ensures
        ({
            match (ret, pat@.len() > 0) {
                (None, _) => !pat@.is_subrange_of(s),
                (Some((head, tail)), false) => tail@.len() == 0 && head@ == s,
                (Some((head, tail)), true) => {
                    // `pat + tail` does not match `pat` except at the front
                    &&& tail@.len() > 0 ==>
                            !pat@.is_suffix_of(pat@ + tail@) && !pat@.is_infix_of(pat@ + tail@)
                    // `head` and `tail` make up the original string
                    &&& s == head@ + pat@ + tail@
                },
            }
        }),
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rsplit_once_post);
    let (seq, gap) = spec_rmatches(s, pat);
    match ret {
        None => {
            if pat@.len() == 0 {
                assert(seq.len() == s.len() + 1);
                assert(false);
            } else {
                assert(gap.len() == 1);
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                assert(gap.first() == s);
                assert(gap.last() == s);
                assert(!pat@.is_subrange_of(gap.last()));
                assert(!pat@.is_subrange_of(s));
            }
        },
        Some((head, tail)) => {
            assert(tail@ == gap.first());
            assert(head@ == rjoin(seq.skip(1), gap.skip(1)));
            lemma_rjoin_uncons(seq, gap);
            assert(s == head@ + seq[0] + tail@);
            if pat@.len() == 0 {
                assert(seq[0].len() == 0);
                assert(gap.first().len() == 0);
                assert_seqs_equal!(seq[0] == pat@);
                assert_seqs_equal!(gap[0] == Seq::<char>::empty());
                assert(tail@.len() == 0);
                assert(s == head@ + Seq::<char>::empty() + Seq::<char>::empty());
                assert(head@ == s);
            } else {
                assert(seq[0] == pat@);
                assert(s == head@ + pat@ + tail@);
                assert(tail@.len() > 0 ==> !pat@.is_suffix_of(pat@ + tail@) && !pat@.is_infix_of(pat@ + tail@));
            }
        },
    }
}

}
