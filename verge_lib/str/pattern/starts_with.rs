// Internal proof module for `str::starts_with` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, ch; ret)]
pub broadcast proof fn lemma_str_starts_with_char(s: Seq<char>, ch: char, ret: bool)
    requires
        #[trigger] str_starts_with_post(s, ch, ret),
    ensures
        ret <==> s.len() > 0 && s.first() == ch,
{
    axiom_char_matches_post(s, ch);
    reveal(str_starts_with_post);
    let (seq, gap) = spec_matches(s, ch);
    if ret {
        assert(seq.first() == seq![ch] && gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[0] == seq.first()[0]);
    }
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
}

//~doc-skip
pub broadcast proof fn lemma_str_starts_with_closure<F>(s: Seq<char>, f: F, ret: bool)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_starts_with_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret <==> s.len() > 0 && call_ensures(f, (s.first(),), true),
{
    axiom_closure_matches_post(s, f);
    reveal(str_starts_with_post);
    let (seq, gap) = spec_matches(s, f);
    if ret {
        assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
        assert(gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[0] == seq.first()[0]);
    }
    if s.len() > 0 && call_ensures(f, (s.first(),), true) {
        reveal_with_fuel(Seq::<_>::flatten, 2);
        let pred = |c: char| call_ensures(f, (c,), false);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.first() == s);
            assert(gap.first()[0] == s.first());
            assert(pred(gap.first()[0]));
            assert(call_ensures(f, (gap.first()[0],), false));
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            assert(s.first() == gap.first()[0]);
            assert(pred(gap.first()[0]));
            assert(call_ensures(f, (gap.first()[0],), false));
        });
    }
}

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, chars@; ret)]
pub broadcast proof fn lemma_str_starts_with_chars<'b>(s: Seq<char>, chars: &'b [char], ret: bool)
    requires
        #[trigger] str_starts_with_post(s, chars, ret),
    ensures
        ret <==> s.len() > 0 && chars@.contains(s.first()),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_starts_with_post);
    let (seq, gap) = spec_matches(s, chars);
    if ret {
        assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
        assert(gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert(s[0] == seq.first()[0]);
    }
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
}

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, pat@; ret)]
pub broadcast proof fn lemma_str_starts_with_string<'b>(s: Seq<char>, pat: &'b str, ret: bool)
    requires
        #[trigger] str_starts_with_post(s, pat, ret),
    ensures
        ret <==> pat@.is_prefix_of(s),
{
    axiom_string_matches_post(s, pat);
    reveal(str_starts_with_post);
    let (seq, gap) = spec_matches(s, pat);
    if ret {
        if pat@.len() == 0 {
            assert(pat@.is_prefix_of(s));
        } else {
            assert(seq.first() == pat@);
            assert(gap.first().len() == 0);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(pat@.is_prefix_of(s));
        }
    }
    if pat@.is_prefix_of(s) {
        if pat@.len() == 0 {
            assert(seq.len() > 0 || gap.first().len() == 0);
            return;
        }
        reveal_with_fuel(Seq::<_>::flatten, 2);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.last() == s);
            assert(!pat@.is_subrange_of(gap.last()));
            lemma_seq_is_subrange_alt(gap.last(), pat@);
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(seq.first() == pat@);
            assert((gap[0] + pat@ + gap[1]).is_prefix_of(s));
            assert(pat@.is_prefix_of(gap[0] + pat@));
            assert(!pat@.is_prefix_of(gap[0] + pat@));
        });
    }
}

}
