// Internal proof module for `str::ends_with` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
pub broadcast proof fn lemma_str_ends_with_char(s: Seq<char>, ch: char, ret: bool)
    requires
        #[trigger] str_ends_with_post(s, ch, ret),
    ensures
        ret <==> s.len() > 0 && s.last() == ch,
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_ends_with_post);
    let (seq, gap) = spec_rmatches(s, ch);
    if ret {
        assert(seq.first() == seq![ch] && gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        assert(s.last() == seq.first()[0]);
    }
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
}

//~doc-skip
pub broadcast proof fn lemma_str_ends_with_closure<F>(s: Seq<char>, f: F, ret: bool)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_ends_with_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ret <==> s.len() > 0 && call_ensures(f, (s.last(),), true),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_ends_with_post);
    let (seq, gap) = spec_rmatches(s, f);
    if ret {
        assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
        assert(gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        assert(s.last() == seq.first()[0]);
        assert(call_ensures(f, (s.last(),), true));
    }
    if s.len() > 0 && call_ensures(f, (s.last(),), true) {
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        let pred = |c: char| call_ensures(f, (c,), false);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.first() == s);
            assert(gap.first().last() == s.last());
            assert(pred(gap.first().last()));
            assert(call_ensures(f, (gap.first().last(),), false));
            assert(call_ensures(f, (gap.first().last(),), true));
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            assert(s.last() == gap.first().last());
            assert(pred(gap.first().last()));
            assert(call_ensures(f, (gap.first().last(),), false));
            assert(call_ensures(f, (gap.first().last(),), true));
        });
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_ends_with_chars<'b>(s: Seq<char>, chars: &'b [char], ret: bool)
    requires
        #[trigger] str_ends_with_post(s, chars, ret),
    ensures
        ret <==> s.len() > 0 && chars@.contains(s.last()),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_ends_with_post);
    let (seq, gap) = spec_rmatches(s, chars);
    if ret {
        assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
        assert(gap.first().len() == 0);
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        assert(s.last() == seq.first()[0]);
        assert(chars@.contains(s.last()));
    }
    if s.len() > 0 && chars@.contains(s.last()) {
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        let pred = |c: char| !chars@.contains(c);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.first() == s);
            assert(gap.first().last() == s.last());
            assert(pred(gap.first().last()));
            assert(!chars@.contains(gap.first().last()));
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            assert(s.last() == gap.first().last());
            assert(pred(gap.first().last()));
            assert(!chars@.contains(gap.first().last()));
        });
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_ends_with_string<'b>(s: Seq<char>, pat: &'b str, ret: bool)
    requires
        #[trigger] str_ends_with_post(s, pat, ret),
    ensures
        ret <==> pat@.is_suffix_of(s),
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_ends_with_post);
    let (seq, gap) = spec_rmatches(s, pat);
    if ret {
        if pat@.len() == 0 {
            assert(pat@.is_suffix_of(s));
        } else {
            assert(seq.first() == pat@);
            assert(gap.first().len() == 0);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(pat@.is_suffix_of(s));
        }
    }
    if pat@.is_suffix_of(s) {
        if pat@.len() == 0 {
            assert(seq.len() > 0 || gap.first().len() == 0);
            return;
        }
        reveal_with_fuel(Seq::<_>::flatten_alt, 2);
        assert_by_contradiction!(seq.len() > 0, {
            assert(gap.len() == 1);
            assert(gap.last() == s);
            assert(!pat@.is_subrange_of(gap.last()));
            lemma_seq_is_subrange_alt(gap.last(), pat@);
        });
        assert_by_contradiction!(gap.first().len() == 0, {
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(seq.first() == pat@);
            assert((gap[1] + pat@ + gap[0]).is_suffix_of(s));
            assert(pat@.is_suffix_of(pat@ + gap[0]));
            assert(!pat@.is_suffix_of(pat@ + gap[0]));
        });
    }
}

}
