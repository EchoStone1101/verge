// Internal proof module for `str::contains` pattern linking lemmas.

use super::internal::*;
use super::*;

verus! {

#[crate::func::assert_surjective(
    crate::func::str::pattern::contains::lemma_str_contains_char_surjective
)]
#[crate::func::assert_injective_by(
    crate::func::str::pattern::contains::lemma_str_contains_char_injective_by(s, ch; ret)
)]
//~doc-skip
pub broadcast proof fn lemma_str_contains_char(s: Seq<char>, ch: char, ret: bool)
    requires
        #[trigger] str_contains_post(s, ch, ret),
    ensures
        ret <==> s.contains(ch),
{
    axiom_char_matches_post(s, ch);
    reveal(str_contains_post);
    let (seq, gap) = spec_matches(s, ch);
    if ret {
        assert(seq.first() == seq![ch]);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[gap.first().len() as int] == ch);
    }
    if s.contains(ch) {
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(gap.first().contains(ch));
        });
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_contains_closure<F>(s: Seq<char>, f: F, ret: bool)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_contains_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret <==> exists|i: int| 0 <= i < s.len() && #[trigger] call_ensures(f, (s[i],), true),
{
    axiom_closure_matches_post(s, f);
    reveal(str_contains_post);
    let (seq, gap) = spec_matches(s, f);
    if ret {
        assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[gap.first().len() as int] == seq.first()[0]);
    }
    if exists|i: int| 0 <= i < s.len() && #[trigger] call_ensures(f, (s[i],), true) {
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(
                exists |i: int| 0 <= i < gap.first().len()
                    && #[trigger] call_ensures(f, (gap.first()[i],), true)
            );
            let k = choose |i: int| 0 <= i < gap.first().len()
                && #[trigger] call_ensures(f, (gap.first()[i],), true);
            let pred = |c: char| call_ensures(f, (c,), false);
            assert(
                forall |i: int| 0 <= i < gap.first().len()
                    ==> #[trigger] pred(gap.first()[i])
            );
            assert(pred(gap.first()[k]));
            assert(call_ensures(f, (gap.first()[k],), false));
            assert(call_ensures(f, (gap.first()[k],), true));
        });
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_contains_chars<'b>(s: Seq<char>, chars: &'b [char], ret: bool)
    requires
        #[trigger] str_contains_post(s, chars, ret),
    ensures
        ret <==> exists|i: int| 0 <= i < s.len() && #[trigger] chars@.contains(s[i]),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_contains_post);
    let (seq, gap) = spec_matches(s, chars);
    if ret {
        assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[gap.first().len() as int] == seq.first()[0]);
    }
    if exists|i: int| 0 <= i < s.len() && #[trigger] chars@.contains(s[i]) {
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(
                exists |i: int| 0 <= i < gap.first().len()
                    && #[trigger] chars@.contains(gap.first()[i])
            );
            let k = choose |i: int| 0 <= i < gap.first().len()
                && #[trigger] chars@.contains(gap.first()[i]);
            let pred = |c: char| !chars@.contains(c);
            assert(
                forall |i: int| 0 <= i < gap.first().len()
                    ==> #[trigger] pred(gap.first()[i])
            );
            assert(pred(gap.first()[k]));
        });
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_contains_string<'b>(s: Seq<char>, pat: &'b str, ret: bool)
    requires
        #[trigger] str_contains_post(s, pat, ret),
    ensures
        ret <==> pat@.is_subrange_of(s),
{
    axiom_string_matches_post(s, pat);
    reveal(str_contains_post);
    let (seq, gap) = spec_matches(s, pat);
    if ret {
        assert(seq.first() == pat@);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(
            s.subrange(gap.first().len() as int, gap.first().len() + seq.first().len() as int)
                == seq.first()
        );
    }
    if pat@.is_subrange_of(s) {
        if pat@.len() == 0 {
            assert(seq.len() > 0);
        } else {
            assert_by_contradiction!(seq.len() > 0, {
                assert(gap.len() == 1);
                reveal_with_fuel(Seq::<_>::flatten, 2);
                assert(gap.last() == s);
                assert(!pat@.is_subrange_of(gap.last()));
            });
        }
    }
}

}
