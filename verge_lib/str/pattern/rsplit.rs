// Internal proof module for `str::rsplit` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
pub broadcast proof fn lemma_str_rsplit_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplit_iter_post(s, ch, iter_seq),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // splits cannot contain `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> !(#[trigger] iter_seq[i]@.contains(ch)),
        // delimiters and splits make up the original string
        s == iter_seq.drop_first().map_values(|ss: &'a str| ss@.push(ch))
                .reverse().flatten() + iter_seq.first()@,
{
    axiom_char_rmatches_post(s, ch);
    reveal(str_rsplit_iter_post);
    let (seq, gap) = spec_rmatches(s, ch);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| 0 <= i < iter_seq.len()
        implies !(#[trigger] iter_seq[i]@.contains(ch))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(!gap[i].contains(ch));
    }

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let iter_parts = iter_seq.drop_first().map_values(|ss: &'a str| ss@.push(ch));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(seq[i] =~= seq![ch]);
        assert(seq[i] == seq![ch]);
        assert_seqs_equal!(g.push(ch) == g + seq![ch]);
    });
    assert(s == join_parts.reverse().flatten_alt() + gap.first());
    assert(join_parts.reverse() == iter_parts.reverse());
    iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
    assert(iter_parts.reverse().flatten() == iter_parts.reverse().flatten_alt());
    assert(iter_seq.first()@ == gap.first());
}

//~doc-skip
pub broadcast proof fn lemma_str_rsplit_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_rsplit_iter_post(s, f, iter_seq),
        is_deterministic(f) && is_total(f),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // splits cannot match `f`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] call_ensures(f, (delim[i],), true)
            &&& s == iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]))
                        .reverse().flatten() + iter_seq.first()@
        },
{
    axiom_closure_rmatches_post(s, f);
    reveal(str_rsplit_iter_post);
    let (seq, gap) = spec_rmatches(s, f);
    let pred = |c: char| call_ensures(f, (c,), false);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| 0 <= i < iter_seq.len()
        implies (#[trigger] iter_seq[i]@).all(|c: char| call_ensures(f, (c,), false))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(pred));
    }

    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);
    assert(delim.len() == iter_seq.len() - 1);
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] call_ensures(f, (delim[i],), true)
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && call_ensures(f, (seq[i][0],), true));
    }

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let iter_parts = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        let d = delim[i];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(d == seq[i][0]);
        assert(seq[i].len() == 1);
        assert_seqs_equal!(seq[i] == seq![d]);
        assert_seqs_equal!(g.push(d) == g + seq![d]);
    });
    assert(s == join_parts.reverse().flatten_alt() + gap.first());
    assert(join_parts.reverse() == iter_parts.reverse());
    iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
    assert(iter_parts.reverse().flatten() == iter_parts.reverse().flatten_alt());
    assert(iter_seq.first()@ == gap.first());
}

//~doc-skip
pub broadcast proof fn lemma_str_rsplit_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_rsplit_iter_post(s, chars, iter_seq),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // splits cannot match `chars`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c)),
        // delimiters and splits make up the original string
        exists |delim: Seq<char>| {
            &&& #[trigger] delim.len() == iter_seq.len() - 1
            &&& forall |i: int| 0 <= i < delim.len()
                    ==> #[trigger] chars@.contains(delim[i])
            &&& s == iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]))
                        .reverse().flatten() + iter_seq.first()@
        },
{
    axiom_chars_rmatches_post(s, chars);
    reveal(str_rsplit_iter_post);
    let (seq, gap) = spec_rmatches(s, chars);
    let pred = |c: char| !chars@.contains(c);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| 0 <= i < iter_seq.len()
        implies (#[trigger] iter_seq[i]@).all(|c: char| !chars@.contains(c))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].all(pred));
    }

    let delim = Seq::<char>::new(seq.len(), |i: int| seq[i][0]);
    assert(delim.len() == iter_seq.len() - 1);
    assert forall |i: int| 0 <= i < delim.len()
        implies #[trigger] chars@.contains(delim[i])
    by {
        assert(delim[i] == seq[i][0]);
        assert(seq[i].len() == 1 && chars@.contains(seq[i][0]));
    }

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let iter_parts = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.push(delim[i]));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        let d = delim[i];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(d == seq[i][0]);
        assert(seq[i].len() == 1);
        assert_seqs_equal!(seq[i] == seq![d]);
        assert_seqs_equal!(g.push(d) == g + seq![d]);
    });
    assert(s == join_parts.reverse().flatten_alt() + gap.first());
    assert(join_parts.reverse() == iter_parts.reverse());
    iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
    assert(iter_parts.reverse().flatten() == iter_parts.reverse().flatten_alt());
    assert(iter_seq.first()@ == gap.first());
}

//~doc-skip
pub broadcast proof fn lemma_str_rsplit_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_rsplit_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_rsplit_iter_post(s, pat, iter_seq),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // `pat + split` (apart from the last) cannot have `pat` as a suffix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@),
        // last split cannot have `pat` as a substring
        !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        s == iter_seq.drop_first().map_values(|ss: &'a str| ss@ + pat@)
                .reverse().flatten() + iter_seq.first()@,
{
    axiom_string_rmatches_post(s, pat);
    reveal(str_rsplit_iter_post);
    let (seq, gap) = spec_rmatches(s, pat);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_suffix_of(pat@ + iter_seq[i]@) && !pat@.is_infix_of(pat@ + iter_seq[i]@)
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].len() > 0 ==> !pat@.is_suffix_of(pat@ + gap[i]) && !pat@.is_infix_of(pat@ + gap[i]));
    }
    assert(iter_seq.last()@ == gap.last());
    assert(!(pat@.is_subrange_of(gap.last())));

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| ss + seq[i]);
    let iter_parts = iter_seq.drop_first().map_values(|ss: &'a str| ss@ + pat@);
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(seq[i] =~= pat@);
        assert(seq[i] == pat@);
    });
    assert(s == join_parts.reverse().flatten_alt() + gap.first());
    assert(join_parts.reverse() == iter_parts.reverse());
    iter_parts.reverse().lemma_flatten_and_flatten_alt_are_equivalent();
    assert(iter_parts.reverse().flatten() == iter_parts.reverse().flatten_alt());
    assert(iter_seq.first()@ == gap.first());
}

}
