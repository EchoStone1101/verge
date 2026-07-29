// Internal proof module for `str::split` pattern linking lemmas.

use super::*;
use super::internal::*;

verus! {

//~doc-skip
#[crate::func::assume_surjective]
#[crate::func::assume_injective_by(s, ch; iter_seq.map_values(|s: &str| s@))]
pub broadcast proof fn lemma_str_split_iter_char<'a>(s: Seq<char>, ch: char, iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_iter_post(s, ch, iter_seq),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // splits cannot contain `ch`
        forall |i: int| 0 <= i < iter_seq.len()
            ==> !(#[trigger] iter_seq[i]@.contains(ch)),
        // delimiters and splits make up the original string
        s == iter_seq.first()@ + iter_seq.drop_first()
            .map_values(|ss: &'a str| ss@.insert(0, ch))
            .flatten()
{
    axiom_char_matches_post(s, ch);
    reveal(str_split_iter_post);
    let (seq, gap) = spec_matches(s, ch);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| 0 <= i < iter_seq.len()
        implies !(#[trigger] iter_seq[i]@.contains(ch))
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(!gap[i].contains(ch));
    }

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
    let iter_parts = iter_seq.drop_first().map_values(|ss: &'a str| ss@.insert(0, ch));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(seq[i] =~= seq![ch]);
        assert(seq[i] == seq![ch]);
        g.insert_ensures(0, ch);
        assert_seqs_equal!(g.insert(0, ch) == seq![ch] + g);
    });
    reveal_with_fuel(Seq::<_>::flatten, 2);
    assert(s == gap.first() + join_parts.flatten());
    assert(iter_seq.first()@ == gap.first());
}

//~doc-skip
pub broadcast proof fn lemma_str_split_iter_closure<'a, F>(s: Seq<char>, f: F, iter_seq: Seq<&'a str>)
    where
        F: FnMut(char) -> bool,
    requires
        #[trigger] str_split_iter_post(s, f, iter_seq),
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
            &&& s == iter_seq.first()@ + iter_seq.drop_first()
                    .map(|i: int, ss: &'a str| ss@.insert(0, delim[i]))
                    .flatten()
        },
{
    axiom_closure_matches_post(s, f);
    reveal(str_split_iter_post);
    let (seq, gap) = spec_matches(s, f);
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

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
    let iter_parts = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.insert(0, delim[i]));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        let d = delim[i];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(d == seq[i][0]);
        assert(seq[i].len() == 1);
        assert_seqs_equal!(seq[i] == seq![d]);
        g.insert_ensures(0, d);
        assert_seqs_equal!(g.insert(0, d) == seq![d] + g);
    });
    reveal_with_fuel(Seq::<_>::flatten, 2);
    assert(s == gap.first() + join_parts.flatten());
    assert(iter_seq.first()@ == gap.first());
}

//~doc-skip
pub broadcast proof fn lemma_str_split_iter_chars<'a, 'b>(s: Seq<char>, chars: &'b [char], iter_seq: Seq<&'a str>)
    requires
        #[trigger] str_split_iter_post(s, chars, iter_seq),
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
            &&& s == iter_seq.first()@ + iter_seq.drop_first()
                    .map(|i: int, ss: &'a str| ss@.insert(0, delim[i]))
                    .flatten()
        },
{
    axiom_chars_matches_post(s, chars);
    reveal(str_split_iter_post);
    let (seq, gap) = spec_matches(s, chars);
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

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
    let iter_parts = iter_seq.drop_first().map(|i: int, ss: &'a str| ss@.insert(0, delim[i]));
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        let d = delim[i];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(d == seq[i][0]);
        assert(seq[i].len() == 1);
        assert_seqs_equal!(seq[i] == seq![d]);
        g.insert_ensures(0, d);
        assert_seqs_equal!(g.insert(0, d) == seq![d] + g);
    });
    reveal_with_fuel(Seq::<_>::flatten, 2);
    assert(s == gap.first() + join_parts.flatten());
    assert(iter_seq.first()@ == gap.first());
}

//~doc-skip
pub broadcast proof fn lemma_str_split_iter_string<'a, 'b>(s: Seq<char>, pat: &'b str, iter_seq: Seq<&'a str>)
    requires
        #![verifier::proof_note(
            "This lemma requires `pat@.len() > 0` to simplify specs; \
            to prove post-conditions when `pat@.len() == 0`, manually reveal `str_split_iter_post`."
        )]
        pat@.len() > 0,
        #[trigger] str_split_iter_post(s, pat, iter_seq),
    ensures
        // at least one split exists
        iter_seq.len() > 0,
        // `split + pat` (apart from the last) cannot have `pat` as a prefix or infix
        forall |i: int| #![trigger iter_seq[i]@] 0 <= i < iter_seq.len() - 1
            ==> iter_seq[i]@.len() > 0
                ==> !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@),
        // last split cannot have `pat` as a substring
        !(pat@.is_subrange_of(iter_seq.last()@)),
        // delimiters and splits make up the original string
        s == iter_seq.first()@ + iter_seq.drop_first()
                .map_values(|ss: &'a str| pat@ + ss@)
                .flatten(),
{
    axiom_string_matches_post(s, pat);
    reveal(str_split_iter_post);
    let (seq, gap) = spec_matches(s, pat);

    assert(iter_seq.len() == gap.len());
    assert(gap.len() > 0);
    assert forall |i: int| #![trigger iter_seq[i]@]
        0 <= i < iter_seq.len() - 1 && iter_seq[i]@.len() > 0
        implies !pat@.is_prefix_of(iter_seq[i]@ + pat@) && !pat@.is_infix_of(iter_seq[i]@ + pat@)
    by {
        assert(iter_seq[i]@ == gap[i]);
        assert(gap[i].len() > 0 ==> !pat@.is_prefix_of(gap[i] + pat@) && !pat@.is_infix_of(gap[i] + pat@));
    }
    assert(iter_seq.last()@ == gap.last());
    assert(!(pat@.is_subrange_of(gap.last())));

    let join_parts = gap.drop_first().map(|i: int, ss: Seq<char>| seq[i] + ss);
    let iter_parts = iter_seq.drop_first().map_values(|ss: &'a str| pat@ + ss@);
    assert_seqs_equal!(join_parts == iter_parts, i => {
        let g = gap[i + 1];
        assert(gap.drop_first()[i] == g);
        assert(iter_seq.drop_first()[i]@ == iter_seq[i + 1]@);
        assert(iter_seq[i + 1]@ == g);
        assert(seq[i] =~= pat@);
        assert(seq[i] == pat@);
    });
    reveal_with_fuel(Seq::<_>::flatten, 2);
    assert(s == gap.first() + join_parts.flatten());
    assert(iter_seq.first()@ == gap.first());
}

}
