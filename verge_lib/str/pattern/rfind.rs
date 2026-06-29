// Internal proof module for `str::rfind` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
pub broadcast proof fn lemma_str_rfind_char(s: Seq<char>, ch: char, ret: Option<usize>)
    requires
        #[trigger] str_rfind_post(s, ch, ret),
    ensures
        ({
            match ret {
                None => !s.contains(ch),
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch < s.len()
                    &&& s[k_ch] == ch
                    &&& forall |i: int| k_ch < i < s.len() ==> #[trigger] s[i] != ch
                },
            }
        }),
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rfind_post);
    let (seq, gap) = spec_rmatches(s, ch);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(gap.first() == s);
            assert(!s.contains(ch));
        },
        Some(k) => {
            let rest = rjoin(seq.skip(1), gap.skip(1));
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
            assert(seq[0] == seq![ch]);
            lemma_concat_associative(rest, seq[0], gap[0]);
            assert(s == rest + (seq[0] + gap[0]));
            lemma_str_concat_lower(seq[0], gap[0]);
            lemma_str_concat_lower(rest, seq[0] + gap[0]);
            assert(s.as_bytes() == rest.as_bytes() + seq[0].as_bytes() + gap[0].as_bytes());
            assert(k as int == rest.as_bytes().len());
            assert(s.as_bytes().take(k as int) == rest.as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(rest);
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(rest);
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == rest.len());
            assert(s[k_ch] == seq[0][0]);
            assert(s[k_ch] == ch);
            assert forall |i: int| k_ch < i < s.len() implies #[trigger] s[i] != ch by {
                assert(seq[0].len() == 1);
                assert(k_ch + 1 <= i);
                assert(s[i] == gap[0][i - k_ch - 1]);
                assert(!gap[0].contains(ch));
                assert_by_contradiction!(s[i] != ch, {
                    assert(gap[0][i - k_ch - 1] == ch);
                    assert(gap[0].contains(ch));
                });
            }
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rfind_closure<F>(s: Seq<char>, f: F, ret: Option<usize>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rfind_post(s, f, ret),
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
                    &&& forall |i: int| k_ch < i < s.len()
                            ==> #[trigger] call_ensures(f, (s[i],), false)
                },
            }
        }),
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rfind_post);
    let (seq, gap) = spec_rmatches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < s.len()
                implies #[trigger] call_ensures(f, (s[i],), false) by {
                assert(pred(gap.first()[i]));
                assert(call_ensures(f, (gap.first()[i],), false));
            }
        },
        Some(k) => {
            let rest = rjoin(seq.skip(1), gap.skip(1));
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
            assert(seq[0].len() == 1 && call_ensures(f, (seq[0][0],), true));
            lemma_concat_associative(rest, seq[0], gap[0]);
            assert(s == rest + (seq[0] + gap[0]));
            lemma_str_concat_lower(seq[0], gap[0]);
            lemma_str_concat_lower(rest, seq[0] + gap[0]);
            assert(s.as_bytes() == rest.as_bytes() + seq[0].as_bytes() + gap[0].as_bytes());
            assert(k as int == rest.as_bytes().len());
            assert(s.as_bytes().take(k as int) == rest.as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(rest);
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(rest);
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == rest.len());
            assert(s[k_ch] == seq[0][0]);
            assert(call_ensures(f, (s[k_ch],), true));
            assert(gap[0].all(pred));
            assert forall |i: int| k_ch < i < s.len()
                implies #[trigger] call_ensures(f, (s[i],), false) by {
                assert(seq[0].len() == 1);
                assert(k_ch + 1 <= i);
                assert(s[i] == gap[0][i - k_ch - 1]);
                assert(pred(gap[0][i - k_ch - 1]));
                assert(call_ensures(f, (gap[0][i - k_ch - 1],), false));
            }
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rfind_chars<'b>(s: Seq<char>, chars: &'b [char], ret: Option<usize>)
    requires
        #[trigger] str_rfind_post(s, chars, ret),
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
                    &&& forall |i: int| k_ch < i < s.len()
                            ==> !(#[trigger] chars@.contains(s[i]))
                },
            }
        }),
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rfind_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let pred = |c: char| !chars@.contains(c);
    match ret {
        None => {
            assert(gap.len() == 1);
            reveal_with_fuel(Seq::<_>::flatten_alt, 2);
            assert(gap.first() == s);
            assert(gap.first().all(pred));
            assert forall |i: int| 0 <= i < s.len()
                implies !(#[trigger] chars@.contains(s[i])) by {
                assert(pred(gap.first()[i]));
                assert(!chars@.contains(gap.first()[i]));
            }
        },
        Some(k) => {
            let rest = rjoin(seq.skip(1), gap.skip(1));
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
            assert(seq[0].len() == 1 && chars@.contains(seq[0][0]));
            lemma_concat_associative(rest, seq[0], gap[0]);
            assert(s == rest + (seq[0] + gap[0]));
            lemma_str_concat_lower(seq[0], gap[0]);
            lemma_str_concat_lower(rest, seq[0] + gap[0]);
            assert(s.as_bytes() == rest.as_bytes() + seq[0].as_bytes() + gap[0].as_bytes());
            assert(k as int == rest.as_bytes().len());
            assert(s.as_bytes().take(k as int) == rest.as_bytes());
            lemma_str_is_utf8(s);
            lemma_str_is_utf8(rest);
            lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
            lemma_str_lower_lift(rest);
            let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
            assert(k_ch == rest.len());
            assert(s[k_ch] == seq[0][0]);
            assert(chars@.contains(s[k_ch]));
            assert(gap[0].all(pred));
            assert forall |i: int| k_ch < i < s.len()
                implies !(#[trigger] chars@.contains(s[i])) by {
                assert(seq[0].len() == 1);
                assert(k_ch + 1 <= i);
                assert(s[i] == gap[0][i - k_ch - 1]);
                assert(pred(gap[0][i - k_ch - 1]));
                assert(!chars@.contains(gap[0][i - k_ch - 1]));
            }
        },
    }
}

//~doc-skip
pub broadcast proof fn lemma_str_rfind_string<'b>(s: Seq<char>, pat: &'b str, ret: Option<usize>)
    requires
        #[trigger] str_rfind_post(s, pat, ret),
    ensures
        ({
            match ret {
                None => !pat@.is_subrange_of(s),
                Some(k) => {
                    let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                    &&& is_char_boundary(s.as_bytes(), k as int) && k_ch <= s.len() - pat@.len()
                    &&& pat@ == s.subrange(k_ch, k_ch + pat@.len())
                    &&& forall |i: int| k_ch < i <= s.len() - pat@.len()
                            ==> pat@ != #[trigger] s.subrange(i, i + pat@.len())
                },
            }
        }),
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rfind_post);
    let (seq, gap) = spec_rmatches(s, pat);
    match ret {
        None => {
            if pat@.len() == 0 {
                assert(seq.len() == s.len() + 1);
                assert(false);
            } else {
                assert(gap.len() == 1);
                reveal_with_fuel(Seq::<_>::flatten_alt, 2);
                assert(gap.last() == s);
                assert(!pat@.is_subrange_of(s));
            }
        },
        Some(k) => {
            if pat@.len() == 0 {
                assert_seqs_equal!(seq[0] == pat@);
                assert(gap.first().len() == 0);
                assert(gap.first().as_bytes().len() == 0);
                assert(seq.first().as_bytes().len() == 0);
                assert(k as int == s.as_bytes().len());
                assert(s.as_bytes().take(k as int) == s.as_bytes());
                lemma_str_is_utf8(s);
                lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
                lemma_str_lower_lift(s);
                let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                assert(k_ch == s.len());
                assert(k_ch <= s.len() - pat@.len());
                assert(pat@ == s.subrange(k_ch, k_ch + pat@.len()));
                assert forall |i: int| k_ch < i <= s.len() - pat@.len()
                    implies pat@ != #[trigger] s.subrange(i, i + pat@.len()) by {
                    assert(false);
                }
            } else {
                let rest = rjoin(seq.skip(1), gap.skip(1));
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
                assert(seq[0] == pat@);
                lemma_concat_associative(rest, seq[0], gap[0]);
                assert(s == rest + (seq[0] + gap[0]));
                lemma_str_concat_lower(seq[0], gap[0]);
                lemma_str_concat_lower(rest, seq[0] + gap[0]);
                assert(s.as_bytes() == rest.as_bytes() + seq[0].as_bytes() + gap[0].as_bytes());
                assert(k as int == rest.as_bytes().len());
                assert(s.as_bytes().take(k as int) == rest.as_bytes());
                lemma_str_is_utf8(s);
                lemma_str_is_utf8(rest);
                lemma_char_boundary_iff_utf8(s.as_bytes(), k as int);
                lemma_str_lower_lift(rest);
                let k_ch = decode_utf8(s.as_bytes().take(k as int)).len() as int;
                assert(k_ch == rest.len());
                assert(s.subrange(k_ch, k_ch + pat@.len()) == pat@);
                assert(k_ch <= s.len() - pat@.len());
                assert forall |i: int| k_ch < i <= s.len() - pat@.len()
                    implies pat@ != #[trigger] s.subrange(i, i + pat@.len()) by {
                    let j = i - k_ch;
                    assert(0 < j <= gap[0].len());
                    assert(gap[0].len() > 0);
                    assert(s.subrange(i, i + pat@.len())
                        == (pat@ + gap[0]).subrange(j, j + pat@.len()));
                    assert_by_contradiction!(pat@ != s.subrange(i, i + pat@.len()), {
                        assert(pat@.is_subrange_of(pat@ + gap[0]));
                        lemma_seq_is_subrange_alt(pat@ + gap[0], pat@);
                        if j == gap[0].len() {
                            assert(pat@.is_suffix_of(pat@ + gap[0]));
                        } else {
                            assert(j < gap[0].len());
                            assert(pat@.is_infix_of(pat@ + gap[0]));
                        }
                        assert(gap[0].len() > 0 ==> !pat@.is_suffix_of(pat@ + gap[0]) && !pat@.is_infix_of(pat@ + gap[0]));
                    });
                }
            }
        },
    }
}

}
