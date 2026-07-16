//! Generic lexicographic comparison specs and lemmas.

use super::*;
use vstd::assert_by_contradiction;
use vstd::math::min;

verus! {

// --- Lexicographic ordering on sequences ---

/// This function encodes lexicographic equality over two sequences.
pub open spec fn lexico_eq<T: PartialEq>(s1: Seq<T>, s2: Seq<T>) -> bool
    decreases s1.len(),
{
    if s1.len() == 0 || s2.len() == 0 {
        s1.len() == 0 && s2.len() == 0
    } else {
        s1[0].eq_spec(&s2[0]) && lexico_eq(s1.drop_first(), s2.drop_first())
    }
}

/// This function compares two sequences in the lexicographic order.
pub open spec fn lexico_cmp<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>) -> Option<Ordering>
    decreases s1.len(),
{
    if s1.len() == 0 && s2.len() == 0 {
        Some(Ordering::Equal)
    } else if s1.len() == 0 {
        Some(Ordering::Less)
    } else if s2.len() == 0 {
        Some(Ordering::Greater)
    } else {
        match PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) {
            Some(Ordering::Equal) => lexico_cmp(s1.drop_first(), s2.drop_first()),
            cmp => cmp,
        }
    }
}

/// Proof that `lexico_eq` is symmetric for `PartialEqVerified` elements.
pub proof fn lemma_lexico_eq_symmetric<T: PartialEqVerified>(s1: Seq<T>, s2: Seq<T>)
    ensures
        lexico_eq(s1, s2) <==> lexico_eq(s2, s1),
    decreases s1.len() + s2.len(),
{
    if s1.len() == 0 || s2.len() == 0 {
    } else {
        <T as PartialEqVerified>::lemma_eq_symmetric(&s1[0], &s2[0]);
        lemma_lexico_eq_symmetric(s1.drop_first(), s2.drop_first());
    }
}

/// Proof that `lexico_eq` is transitive for `PartialEqVerified` elements.
pub proof fn lemma_lexico_eq_transitive<T: PartialEqVerified>(
    s1: Seq<T>,
    s2: Seq<T>,
    s3: Seq<T>,
)
    requires
        lexico_eq(s1, s2),
        lexico_eq(s2, s3),
    ensures
        lexico_eq(s1, s3),
    decreases s1.len() + s2.len() + s3.len(),
{
    if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
    } else {
        <T as PartialEqVerified>::lemma_eq_transitive(&s1[0], &s2[0], &s3[0]);
        lemma_lexico_eq_transitive(s1.drop_first(), s2.drop_first(), s3.drop_first());
    }
}

/// Proof that `lexico_eq` is reflexive for `EqVerified` elements.
pub proof fn lemma_lexico_eq_reflexive<T: EqVerified>(s: Seq<T>)
    ensures
        lexico_eq(s, s),
    decreases s.len(),
{
    if s.len() > 0 {
        <T as EqVerified>::lemma_eq_reflexive(&s[0]);
        lemma_lexico_eq_reflexive(s.drop_first());
    }
}

/// This function compares two sequences in lexicographic order using the
/// first non-`Equal` comparison in the common prefix.
pub open spec fn lexico_cmp_by_prefix<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>) -> Option<Ordering> {
    let head = Seq::<Option<Ordering>>::new(
        min(s1.len() as int, s2.len() as int) as nat,
        |i: int| PartialOrdSpec::partial_cmp_spec(&s1[i], &s2[i])
    );
    if lexico_is_less(head) {
        Some(Ordering::Less)
    } else if lexico_is_greater(head) {
        Some(Ordering::Greater)
    } else if lexico_is_incomparable(head) {
        None
    } else {
        if s1.len() < s2.len() {
            Some(Ordering::Less)
        } else if s1.len() > s2.len() {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

/// This function encodes the lexicographic Less: the first non-Equal entry is Less.
pub open spec fn lexico_is_less(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
        && s[i] == Some(Ordering::Less)
        && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
}

/// This function encodes the lexicographic Greater: the first non-Equal entry is Greater.
pub open spec fn lexico_is_greater(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
        && s[i] == Some(Ordering::Greater)
        && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
}

/// This function encodes the lexicographic Incomparable: the first non-Equal entry is None.
pub open spec fn lexico_is_incomparable(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
        && s[i] == None
        && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
}

/// This function encodes the lexicographic Equal: all entries are Equal.
pub open spec fn lexico_is_equal(s: Seq<Option<Ordering>>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == Some(Ordering::Equal)
}

/// Proof that exactly one of `lexico_is_less(s)`, `lexico_is_greater(s)`,
/// `lexico_is_incomparable(s)`, and `lexico_is_equal(s)` holds.
pub proof fn lemma_lexico_cmp_tetrachotomy(s: Seq<Option<Ordering>>)
    ensures
        ({
            match (
                lexico_is_less(s),
                lexico_is_greater(s),
                lexico_is_incomparable(s),
                lexico_is_equal(s),
            ) {
                (true, false, false, false)
                | (false, true, false, false)
                | (false, false, true, false)
                | (false, false, false, true)
                    => true,
                _ 
                    => false,
            }
        }),
{
    let n = s.len() as int;
    if lexico_is_equal(s) {
        assert_by_contradiction!(!lexico_is_less(s), {
            let i = choose|i: int| 0 <= i < n
                && s[i] == Some(Ordering::Less)
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        });
        assert_by_contradiction!(!lexico_is_greater(s), {
            let i = choose|i: int| 0 <= i < n
                && s[i] == Some(Ordering::Greater)
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        });
        assert_by_contradiction!(!lexico_is_incomparable(s), {
            let i = choose|i: int| 0 <= i < n
                && s[i] == None
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        });
    } else {
        let w = choose|i: int| 0 <= i < n && s[i] != Some(Ordering::Equal);
        super::internal::lemma_lexico_first_non_equal(s, w);
        let first = choose|i: int| 0 <= i < n
            && s[i] != Some(Ordering::Equal)
            && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        assert(
            s[first] == Some(Ordering::Less) 
            || s[first] == Some(Ordering::Greater)
            || s[first] == None
        );
        assert(lexico_is_less(s) || lexico_is_greater(s) || lexico_is_incomparable(s));

        assert_by_contradiction!(!(lexico_is_less(s) && lexico_is_greater(s)), {
            let i1 = choose|i: int| 0 <= i < n
                && s[i] == Some(Ordering::Less)
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
            let i2 = choose|i: int| 0 <= i < n
                && s[i] == Some(Ordering::Greater)
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        });
        assert_by_contradiction!(!(lexico_is_less(s) && lexico_is_incomparable(s)), {
            let i1 = choose|i: int| 0 <= i < n
                && s[i] == Some(Ordering::Less)
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
            let i2 = choose|i: int| 0 <= i < n
                && s[i] == None
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        });
        assert_by_contradiction!(!(lexico_is_greater(s) && lexico_is_incomparable(s)), {
            let i1 = choose|i: int| 0 <= i < n
                && s[i] == Some(Ordering::Greater)
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
            let i2 = choose|i: int| 0 <= i < n
                && s[i] == None
                && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal);
        });
    }
}

/// Proof that the recursive `lexico_cmp` agrees with the equivalent
/// first-non-`Equal` formulation.
pub proof fn lemma_lexico_cmp_by_prefix<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    ensures
        lexico_cmp(s1, s2) == lexico_cmp_by_prefix(s1, s2),
    decreases s1.len(),
{
    if s1.len() == 0 || s2.len() == 0 {
        super::internal::lemma_lexico_cmp_by_prefix_empty(s1, s2);
    } else if PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Equal) {
        lemma_lexico_cmp_by_prefix(s1.drop_first(), s2.drop_first());
        super::internal::lemma_lexico_cmp_by_prefix_equal_head(s1, s2);
    } else if PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Less) {
        super::internal::lemma_lexico_cmp_by_prefix_less_head(s1, s2);
    } else if PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Greater) {
        super::internal::lemma_lexico_cmp_by_prefix_greater_head(s1, s2);
    } else {
        assert(PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == None);
        super::internal::lemma_lexico_cmp_by_prefix_none_head(s1, s2);
    }
}

/// Proof that `lexico_cmp` returning `Equal` is consistent with `lexico_eq`,
/// and that equal prefixes are substitutable on the left of a comparison.
pub proof fn lemma_lexico_cmp_eq_consistent<T: PartialOrdVerified>(s1: Seq<T>, s2: Seq<T>)
    ensures
        lexico_cmp(s1, s2) == Some(Ordering::Equal) <==> lexico_eq(s1, s2),
        lexico_cmp(s1, s2) == Some(Ordering::Equal) ==>
            forall|s3: Seq<T>| lexico_cmp(s1, s3) == lexico_cmp(s2, s3),
    decreases s1.len(),
{
    if s1.len() == 0 || s2.len() == 0 {
    } else {
        <T as PartialOrdVerified>::lemma_cmp_eq_consistent(&s1[0], &s2[0]);
        if PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Equal) {
            lemma_lexico_cmp_eq_consistent(s1.drop_first(), s2.drop_first());
            assert(lexico_cmp(s1, s2) == Some(Ordering::Equal) <==> lexico_eq(s1, s2));
            if lexico_cmp(s1, s2) == Some(Ordering::Equal) {
                assert(lexico_cmp(s1.drop_first(), s2.drop_first()) == Some(Ordering::Equal));
                assert forall|s3: Seq<T>| lexico_cmp(s1, s3) == lexico_cmp(s2, s3) by {
                    if s3.len() == 0 {
                    } else {
                        assert(PartialOrdSpec::partial_cmp_spec(&s1[0], &s3[0])
                            == PartialOrdSpec::partial_cmp_spec(&s2[0], &s3[0]));
                        if PartialOrdSpec::partial_cmp_spec(&s1[0], &s3[0]) == Some(Ordering::Equal) {
                            assert(lexico_cmp(s1.drop_first(), s3.drop_first())
                                == lexico_cmp(s2.drop_first(), s3.drop_first()));
                        }
                    }
                };
            }
        } else {
            assert(PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) != Some(Ordering::Equal));
            assert(!s1[0].eq_spec(&s2[0]));
        }
    }
}

/// Proof that `lexico_cmp` upholds duality.
pub proof fn lemma_lexico_cmp_dual<T: PartialOrdVerified>(
    s1: Seq<T>,
    s2: Seq<T>,
)
    ensures
        ({
            match lexico_cmp(s1, s2) {
                Some(Ordering::Equal) => lexico_cmp(s2, s1) == Some(Ordering::Equal),
                Some(Ordering::Less) => lexico_cmp(s2, s1) == Some(Ordering::Greater),
                Some(Ordering::Greater) => lexico_cmp(s2, s1) == Some(Ordering::Less),
                None => lexico_cmp(s2, s1) == None,
            }
        }),
    decreases s1.len() + s2.len(),
{
    if s1.len() == 0 || s2.len() == 0 {
    } else {
        <T as PartialOrdVerified>::lemma_cmp_dual(&s1[0], &s2[0]);
        if PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Equal) {
            lemma_lexico_cmp_dual(s1.drop_first(), s2.drop_first());
        }
    }
}

/// Proof that `lexico_cmp` is total for `OrdVerified` elements.
pub proof fn lemma_lexico_cmp_total<T: OrdVerified>(s1: Seq<T>, s2: Seq<T>)
    ensures
        lexico_cmp(s1, s2) is Some,
    decreases s1.len(),
{
    if s1.len() == 0 || s2.len() == 0 {
    } else {
        <T as OrdVerified>::lemma_cmp_consistent(&s1[0], &s2[0]);
        if PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Equal) {
            lemma_lexico_cmp_total(s1.drop_first(), s2.drop_first());
        }
    }
}

/// Proof that `lexico_cmp` upholds transitivity for `PartialOrdVerified` elements.
pub proof fn lemma_lexico_cmp_transitive<T: PartialOrdVerified>(
    s1: Seq<T>,
    s2: Seq<T>,
    s3: Seq<T>,
)
    requires
        lexico_cmp(s1, s2) == lexico_cmp(s2, s3),
        lexico_cmp(s1, s2) == Some(Ordering::Less)
            || lexico_cmp(s1, s2) == Some(Ordering::Greater),
    ensures
        lexico_cmp(s1, s3) == lexico_cmp(s1, s2),
    decreases s1.len() + s2.len() + s3.len(),
{
    let ord = lexico_cmp(s1, s2)->0;
    if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
    } else {
        let ab = PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]);
        let bc = PartialOrdSpec::partial_cmp_spec(&s2[0], &s3[0]);
        if ab == Some(Ordering::Equal) {
            <T as PartialOrdVerified>::lemma_cmp_eq_consistent(&s1[0], &s2[0]);
            if bc == Some(Ordering::Equal) {
                lemma_lexico_cmp_transitive(s1.drop_first(), s2.drop_first(), s3.drop_first());
            } else {
                assert(PartialOrdSpec::partial_cmp_spec(&s1[0], &s3[0]) == bc);
            }
        } else {
            if bc == Some(Ordering::Equal) {
                super::internal::lemma_cmp_eq_substitute_right(&s1[0], &s2[0], &s3[0]);
            } else {
                assert(ab == Some(ord));
                assert(bc == Some(ord));
                super::internal::lemma_cmp_three_transitive(&s1[0], &s2[0], &s3[0], ord);
            }
        }
    }
}


} // verus!
