// Internal proof module for `str::find` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
pub broadcast proof fn lemma_str_find_char(s: Seq<char>, ch: char, ret: Option<usize>)
    requires
        #[trigger] str_find_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => !s.contains(ch),
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch < s.len()
                    &&& s[k_ch] == ch
                    &&& forall |i: int| 0 <= i < k_ch ==> #[trigger] s[i] != ch
                },
            }
        }),
{
    axiom_char_matches_post(s, ch);
    reveal(str_find_post);
    let (seq, gap) = spec_matches(s, ch);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(!s.contains(ch));
        },
        Some(k) => {
            let tail = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss).flatten();
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s == gap.first() + tail);
            lemma_str_concat_lower(gap.first(), tail);
            assert(s.as_bytes().take(k as int) == gap.first().as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(gap.first());
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(gap.first());
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == gap.first().len());
            assert(seq.first() == seq![ch]);
            assert(s[k_ch] == seq.first()[0]);
            assert forall |i: int| 0 <= i < k_ch implies #[trigger] s[i] != ch by {
                assert(s[i] == gap.first()[i]);
                assert_by_contradiction!(s[i] != ch, {
                    assert(gap.first()[i] == ch);
                    assert(gap.first().contains(ch));
                });
            }
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_find_closure<F>(s: Seq<char>, f: F, ret: Option<usize>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_find_post(s, f, ret),
        is_deterministic(f) && is_total(f),
    ensures
        ({
            match ret {
                None => {
                    forall |i: int| 0 <= i < s.len()
                        ==> #[trigger] call_ensures(f, (s[i],), false)
                },
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch < s.len()
                    &&& call_ensures(f, (s[k_ch],), true)
                    &&& forall |i: int| 0 <= i < k_ch
                            ==> #[trigger] call_ensures(f, (s[i],), false)
                },
            }
        }),
{
    axiom_closure_matches_post(s, f);
    reveal(str_find_post);
    let (seq, gap) = spec_matches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < s.len()
                implies #[trigger] call_ensures(f, (s[i],), false) by {
                assert(pred(gap.first()[i]));
                assert(call_ensures(f, (gap.first()[i],), false));
            }
        },
        Some(k) => {
            let tail = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss).flatten();
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s == gap.first() + tail);
            lemma_str_concat_lower(gap.first(), tail);
            assert(s.as_bytes().take(k as int) == gap.first().as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(gap.first());
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(gap.first());
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == gap.first().len());
            assert(seq.first().len() == 1 && call_ensures(f, (seq.first()[0],), true));
            assert(s[k_ch] == seq.first()[0]);
            assert(call_ensures(f, (s[k_ch],), true));
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < k_ch
                implies #[trigger] call_ensures(f, (s[i],), false) by {
                assert(s[i] == gap.first()[i]);
                assert(pred(gap.first()[i]));
                assert(call_ensures(f, (gap.first()[i],), false));
            }
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_find_chars<'b>(s: Seq<char>, chars: &'b [char], ret: Option<usize>)
    requires
        #[trigger] str_find_post(s, chars, ret),
    ensures
        ({
            match ret {
                None => {
                    forall |i: int| 0 <= i < s.len()
                        ==> !(#[trigger] chars@.contains(s[i]))
                },
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch < s.len()
                    &&& chars@.contains(s[k_ch])
                    &&& forall |i: int| 0 <= i < k_ch
                            ==> !(#[trigger] chars@.contains(s[i]))
                },
            }
        }),
{
    axiom_chars_matches_post(s, chars);
    reveal(str_find_post);
    let (seq, gap) = spec_matches(s, chars);
    let pred = |c: char| !chars@.contains(c);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < s.len()
                implies !(#[trigger] chars@.contains(s[i])) by {
                assert(pred(gap.first()[i]));
                assert(!chars@.contains(gap.first()[i]));
            }
        },
        Some(k) => {
            let tail = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss).flatten();
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s == gap.first() + tail);
            lemma_str_concat_lower(gap.first(), tail);
            assert(s.as_bytes().take(k as int) == gap.first().as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(gap.first());
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(gap.first());
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == gap.first().len());
            assert(seq.first().len() == 1 && chars@.contains(seq.first()[0]));
            assert(s[k_ch] == seq.first()[0]);
            assert(chars@.contains(s[k_ch]));
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < k_ch
                implies !(#[trigger] chars@.contains(s[i])) by {
                assert(s[i] == gap.first()[i]);
                assert(pred(gap.first()[i]));
                assert(!chars@.contains(gap.first()[i]));
            }
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_find_string<'b>(s: Seq<char>, pat: &'b str, ret: Option<usize>)
    requires
        #[trigger] str_find_post(s, pat, ret),
    ensures
        ({
            match ret {
                None => !pat@.is_subrange_of(s),
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch <= s.len() - pat@.len()
                    &&& pat@ == s.subrange(k_ch, k_ch + pat@.len())
                    &&& forall |i: int| 0 <= i < k_ch
                            ==> pat@ != #[trigger] s.subrange(i, i + pat@.len())
                },
            }
        }),
{
    axiom_string_matches_post(s, pat);
    reveal(str_find_post);
    let (seq, gap) = spec_matches(s, pat);
    match ret {
        None => {
            if pat@.len() == 0 {
                assert(seq.len() == s.len() + 1);
            } else {
                assert(gap.len() == 1);
                reveal_with_fuel(Seq::<_>::flatten, 2);
                assert(gap.last() == s);
                assert(!pat@.is_subrange_of(s));
            }
        },
        Some(k) => {
            let tail = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss).flatten();
            reveal_with_fuel(Seq::<_>::flatten, 2);
            assert(s == gap.first() + tail);
            lemma_str_concat_lower(gap.first(), tail);
            assert(s.as_bytes().take(k as int) == gap.first().as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(gap.first());
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(gap.first());
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == gap.first().len());
            if pat@.len() == 0 {
                assert(gap.first().len() == 0);
                assert(pat@ == s.subrange(0, 0));
            } else {
                assert(seq.first() == pat@);
                assert(s.subrange(k_ch, k_ch + pat@.len()) == pat@);
                assert(k_ch <= s.len() - pat@.len());
                assert forall |i: int| 0 <= i < k_ch
                    implies pat@ != #[trigger] s.subrange(i, i + pat@.len()) by {
                    assert_by_contradiction!(pat@ != s.subrange(i, i + pat@.len()), {
                        assert(s.subrange(i, i + pat@.len())
                            == (gap.first() + pat@).subrange(i, i + pat@.len()));
                        assert(pat@.is_subrange_of(gap.first() + pat@));
                        lemma_seq_is_subrange_alt(gap.first() + pat@, pat@);
                        if i == 0 {
                            assert(pat@.is_prefix_of(gap.first() + pat@));
                        } else {
                            assert(pat@.is_infix_of(gap.first() + pat@));
                        }
                    });
                }
            }
        },
    }
}

}
