//! Private proof helpers for `cmp`.

use super::*;
use vstd::assert_seqs_equal;
use vstd::math::min;

verus! {

//~doc-skip
pub(super) proof fn lemma_lexico_cons_equal(s: Seq<Option<Ordering>>)
    ensures
        lexico_is_less(seq![Some(Ordering::Equal)] + s) <==> lexico_is_less(s),
        lexico_is_greater(seq![Some(Ordering::Equal)] + s) <==> lexico_is_greater(s),
        lexico_is_incomparable(seq![Some(Ordering::Equal)] + s) <==> lexico_is_incomparable(s),
        lexico_is_equal(seq![Some(Ordering::Equal)] + s) <==> lexico_is_equal(s),
{
    let prefixed = seq![Some(Ordering::Equal)] + s;
    assert(lexico_is_less(prefixed) ==> lexico_is_less(s)) by {
        if lexico_is_less(prefixed) {
            let i = choose|i: int| 0 <= i < prefixed.len()
                && prefixed[i] == Some(Ordering::Less)
                && forall|j: int| 0 <= j < i ==> prefixed[j] == Some(Ordering::Equal);
            assert(i > 0);
            assert(s[i - 1] == Some(Ordering::Less));
            assert forall|j: int| 0 <= j < i - 1 implies s[j] == Some(Ordering::Equal) by {
                assert(prefixed[j + 1] == s[j]);
            }
        }
    };
    assert(lexico_is_less(s) ==> lexico_is_less(prefixed)) by {
        if lexico_is_less(s) {
            let i = choose|i: int| 0 <= i < s.len()
                && s[i] == Some(Ordering::Less)
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
            assert(prefixed[i + 1] == Some(Ordering::Less));
            assert forall|j: int| 0 <= j < i + 1 implies prefixed[j] == Some(Ordering::Equal) by {
                if j > 0 {
                    assert(prefixed[j] == s[j - 1]);
                }
            }
        }
    };
    assert(lexico_is_greater(prefixed) ==> lexico_is_greater(s)) by {
        if lexico_is_greater(prefixed) {
            let i = choose|i: int| 0 <= i < prefixed.len()
                && prefixed[i] == Some(Ordering::Greater)
                && forall|j: int| 0 <= j < i ==> prefixed[j] == Some(Ordering::Equal);
            assert(i > 0);
            assert(s[i - 1] == Some(Ordering::Greater));
            assert forall|j: int| 0 <= j < i - 1 implies s[j] == Some(Ordering::Equal) by {
                assert(prefixed[j + 1] == s[j]);
            }
        }
    };
    assert(lexico_is_greater(s) ==> lexico_is_greater(prefixed)) by {
        if lexico_is_greater(s) {
            let i = choose|i: int| 0 <= i < s.len()
                && s[i] == Some(Ordering::Greater)
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
            assert(prefixed[i + 1] == Some(Ordering::Greater));
            assert forall|j: int| 0 <= j < i + 1 implies prefixed[j] == Some(Ordering::Equal) by {
                if j > 0 {
                    assert(prefixed[j] == s[j - 1]);
                }
            }
        }
    };
    assert(lexico_is_incomparable(prefixed) ==> lexico_is_incomparable(s)) by {
        if lexico_is_incomparable(prefixed) {
            let i = choose|i: int| 0 <= i < prefixed.len()
                && prefixed[i] == None
                && forall|j: int| 0 <= j < i ==> prefixed[j] == Some(Ordering::Equal);
            assert(i > 0);
            assert(s[i - 1] == None);
            assert forall|j: int| 0 <= j < i - 1 implies s[j] == Some(Ordering::Equal) by {
                assert(prefixed[j + 1] == s[j]);
            }
        }
    };
    assert(lexico_is_incomparable(s) ==> lexico_is_incomparable(prefixed)) by {
        if lexico_is_incomparable(s) {
            let i = choose|i: int| 0 <= i < s.len()
                && s[i] == None
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
            assert(prefixed[i + 1] == None);
            assert forall|j: int| 0 <= j < i + 1 implies prefixed[j] == Some(Ordering::Equal) by {
                if j > 0 {
                    assert(prefixed[j] == s[j - 1]);
                }
            }
        }
    };
    assert(lexico_is_equal(prefixed) ==> lexico_is_equal(s)) by {
        if lexico_is_equal(prefixed) {
            assert forall|i: int| 0 <= i < s.len() implies s[i] == Some(Ordering::Equal) by {
                assert(prefixed[i + 1] == s[i]);
            }
        }
    };
    assert(lexico_is_equal(s) ==> lexico_is_equal(prefixed)) by {
        if lexico_is_equal(s) {
            assert forall|i: int| 0 <= i < prefixed.len() implies prefixed[i] == Some(Ordering::Equal) by {
                if i > 0 {
                    assert(prefixed[i] == s[i - 1]);
                }
            }
        }
    };
}

//~doc-skip
pub(super) proof fn lemma_lexico_cmp_by_prefix_empty<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() == 0 || s2.len() == 0,
    ensures
        lexico_cmp(s1, s2) == lexico_cmp_by_prefix(s1, s2),
{
    let head = Seq::<Option<Ordering>>::new(
        min(s1.len() as int, s2.len() as int) as nat,
        |i: int| PartialOrdSpec::partial_cmp_spec(&s1[i], &s2[i])
    );
    assert(head.len() == 0);
    assert(lexico_is_equal(head));
    lemma_lexico_cmp_tetrachotomy(head);
}

//~doc-skip
pub(super) proof fn lemma_lexico_cmp_by_prefix_equal_head<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() > 0,
        s2.len() > 0,
        PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Equal),
    ensures
        lexico_cmp_by_prefix(s1, s2) == lexico_cmp_by_prefix(s1.drop_first(), s2.drop_first()),
{
    let rest1 = s1.drop_first();
    let rest2 = s2.drop_first();
    let head = Seq::<Option<Ordering>>::new(
        min(s1.len() as int, s2.len() as int) as nat,
        |i: int| PartialOrdSpec::partial_cmp_spec(&s1[i], &s2[i])
    );
    let rest_head = Seq::<Option<Ordering>>::new(
        min(rest1.len() as int, rest2.len() as int) as nat,
        |i: int| PartialOrdSpec::partial_cmp_spec(&rest1[i], &rest2[i])
    );
    assert_seqs_equal!(head == seq![Some(Ordering::Equal)] + rest_head, i => {
        if i > 0 {
            assert(rest1[i - 1] == s1[i]);
            assert(rest2[i - 1] == s2[i]);
        }
    });
    lemma_lexico_cons_equal(rest_head);
    lemma_lexico_cmp_tetrachotomy(rest_head);
}

//~doc-skip
pub(super) proof fn lemma_lexico_cmp_by_prefix_less_head<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() > 0,
        s2.len() > 0,
        PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Less),
    ensures
        lexico_cmp(s1, s2) == lexico_cmp_by_prefix(s1, s2),
{
    let head = Seq::<Option<Ordering>>::new(
        min(s1.len() as int, s2.len() as int) as nat,
        |i: int| PartialOrdSpec::partial_cmp_spec(&s1[i], &s2[i])
    );
    assert(lexico_is_less(head)) by {
        assert(head[0] == Some(Ordering::Less));
    }
}

//~doc-skip
pub(super) proof fn lemma_lexico_cmp_by_prefix_greater_head<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() > 0,
        s2.len() > 0,
        PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Greater),
    ensures
        lexico_cmp(s1, s2) == lexico_cmp_by_prefix(s1, s2),
{
    let head = Seq::<Option<Ordering>>::new(
        min(s1.len() as int, s2.len() as int) as nat,
        |i: int| PartialOrdSpec::partial_cmp_spec(&s1[i], &s2[i])
    );
    assert(lexico_is_greater(head)) by {
        assert(head[0] == Some(Ordering::Greater));
    }
}

//~doc-skip
pub(super) proof fn lemma_lexico_cmp_by_prefix_none_head<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() > 0,
        s2.len() > 0,
        PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == None,
    ensures
        lexico_cmp(s1, s2) == lexico_cmp_by_prefix(s1, s2),
{
    let head = Seq::<Option<Ordering>>::new(
        min(s1.len() as int, s2.len() as int) as nat,
        |i: int| PartialOrdSpec::partial_cmp_spec(&s1[i], &s2[i])
    );
    assert(lexico_is_incomparable(head)) by {
        assert(head[0] == None);
    }
}

//~doc-skip
pub(super) proof fn lemma_cmp_eq_substitute_right<T: PartialOrdVerified>(a: &T, b: &T, c: &T)
    requires
        b.partial_cmp_spec(c) == Some(Ordering::Equal),
    ensures
        a.partial_cmp_spec(b) == a.partial_cmp_spec(c),
{
    <T as PartialOrdVerified>::lemma_cmp_dual(a, b);
    <T as PartialOrdVerified>::lemma_cmp_dual(a, c);
    <T as PartialOrdVerified>::lemma_cmp_eq_consistent(b, c);
}

//~doc-skip
pub(super) proof fn lemma_cmp_three_transitive<T: PartialOrdVerified>(a: &T, b: &T, c: &T, ord: Ordering)
    requires
        ord == Ordering::Less || ord == Ordering::Greater,
        a.partial_cmp_spec(b) == Some(ord),
        b.partial_cmp_spec(c) == Some(ord),
    ensures
        a.partial_cmp_spec(c) == Some(ord),
{
    <T as PartialOrdVerified>::lemma_cmp_transitive(a, b, c);
}

// Helper: given any non-Equal position, there exists a first one with all-Equal prefix.
//~doc-skip
pub(super) proof fn lemma_lexico_first_non_equal(s: Seq<Option<Ordering>>, witness: int)
    requires
        0 <= witness < s.len(),
        s[witness] != Some(Ordering::Equal),
    ensures
        exists|i: int| 0 <= i < s.len()
            && s[i] != Some(Ordering::Equal)
            && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal),
    decreases witness,
{
    if witness == 0 || s[witness - 1] != Some(Ordering::Equal) {
        if witness == 0 {
            assert(forall|j: int| 0 <= j < 0int ==> s[j] == Some(Ordering::Equal));
        } else {
            lemma_lexico_first_non_equal(s, witness - 1);
        }
    } else {
        // s[witness-1] == Some(Equal), recurse not needed; witness itself works if prefix is all-Equal
        // Check: does there exist a smaller non-Equal?
        if forall|j: int| 0 <= j < witness ==> s[j] == Some(Ordering::Equal) {
            // witness is the first
        } else {
            let smaller = choose|j: int| 0 <= j < witness && s[j] != Some(Ordering::Equal);
            lemma_lexico_first_non_equal(s, smaller);
        }
    }
}

} // verus!
