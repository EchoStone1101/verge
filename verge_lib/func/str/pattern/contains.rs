//! Function-contract lemmas for `str::contains` pattern linking lemmas.

use crate::str::pattern::*;
use vstd::assert_by_contradiction;
use vstd::prelude::*;

verus! {

pub proof fn lemma_str_contains_char_surjective(s: Seq<char>, ch: char, ret: bool)
    requires
        ret <==> s.contains(ch),
    ensures
        str_contains_post(s, ch, ret),
{
    axiom_char_matches_post(s, ch);
    reveal(str_contains_post);
    let (seq, gap) = spec_matches(s, ch);

    assert(seq.len() > 0 ==> s.contains(ch)) by {
        if seq.len() > 0 {
            assert(seq.first() == seq![ch]);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s[gap.first().len() as int] == ch);
        }
    }

    assert(s.contains(ch) ==> seq.len() > 0) by {
        if s.contains(ch) {
            assert_by_contradiction!(seq.len() > 0, {
                assert(gap.len() == 1);
                reveal_with_fuel(Seq::<_>::flatten, 2);
                assert(gap.first() == s);
                assert(gap.first().contains(ch));
            });
        }
    }

    assert(ret == (seq.len() > 0));
}

pub proof fn lemma_str_contains_char_injective_by(
    s1: Seq<char>,
    ch1: char,
    ret1: bool,
    s2: Seq<char>,
    ch2: char,
    ret2: bool,
)
    requires
        str_contains_post(s1, ch1, ret1),
        ret1 <==> s1.contains(ch1),
        str_contains_post(s2, ch2, ret2),
        ret2 <==> s2.contains(ch2),
        s1 == s2,
        ch1 == ch2,
    ensures
        ret1 == ret2,
{
    assert(ret1 <==> ret2);
}

} // verus!
