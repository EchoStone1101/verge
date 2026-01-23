//! Definitions and lemmas for `Set::fold` in Verus, extending `vstd::set::fold`.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set::fold::*;
use vstd::{assert_by_contradiction, assert_sets_equal, assert_multisets_equal, calc};
use vstd::relations::*;

verus! {

/// Proof that folding over two disjoint sets is equivalent to folding over their union set.
pub proof fn lemma_fold_disjoint_union<A, B>(s1: Set<A>, s2: Set<A>, z: B, f: spec_fn(B, A) -> B)
    requires
        s1.finite() && s2.finite(),
        s1.disjoint(s2),
        is_fun_commutative(f),
    ensures
        (s1 + s2).fold(z, f) == s2.fold(s1.fold(z, f), f),
    decreases s2.len(),
{
    if s2.is_empty() {
        // ..base
        calc!{
            (==)
            (s1 + s2).fold(z, f); { assert(s1 + s2 == s1); }
            s1.fold(z, f); { lemma_fold_empty(s1.fold(z, f), f); }
            s2.fold(s1.fold(z, f), f);
        }
    } else {
        // ..induct
        let a = s2.choose();
        calc!{
            (==)
            (s1 + s2).fold(z, f); { lemma_fold_insert((s1 + s2).remove(a), z, f, a); }
            f((s1 + s2).remove(a).fold(z, f), a); { assert((s1 + s2).remove(a) == s1 + s2.remove(a)); }
            f((s1 + s2.remove(a)).fold(z, f), a); { lemma_fold_disjoint_union(s1, s2.remove(a), z, f); }
            f(s2.remove(a).fold(s1.fold(z, f), f), a); { lemma_fold_insert(s2.remove(a), s1.fold(z, f), f, a); }
            s2.fold(s1.fold(z, f), f);
        }
    }
}

/// Proof that folding over a set is equivalent to folding along its sequence version, 
/// if the fold function is commutative.
pub proof fn lemma_fold_set_seq_eq<A, B>(set: Set<A>, seq: Seq<A>, z: B, f: spec_fn(B, A) -> B)
    requires
        set.finite(),
        seq.no_duplicates() && seq.to_set() == set,
        is_fun_commutative(f),
    ensures
        set.fold(z, f) == seq.fold_left(z, f),
    decreases
        set.len(),
{
    seq.unique_seq_to_set();
    if set.is_empty() {
        // ..base
        assert(set.fold(z, f) == z) by { lemma_fold_empty(z, f); }
        assert(seq.fold_left(z, f) == z);
    } else {
        // ..induct
        let a = seq.last();
        calc!{
            (==)
            seq.fold_left(z, f); {}
            f(seq.drop_last().fold_left(z, f), a); {
                assert_sets_equal!(seq.drop_last().to_set() == set.remove(a), elem => {
                    calc!{
                        (<==>)
                        seq.drop_last().to_set().contains(elem); {}
                        seq.drop_last().contains(elem); {
                            if seq.contains(elem) && elem != a {
                                let i = seq.index_of(elem);
                                assert_by_contradiction!(i != seq.len() - 1, {
                                    assert(seq[i] == a);
                                });
                                assert(seq.drop_last()[i] == seq[i]);
                            }
                        }
                        seq.contains(elem) && elem != a; {}
                        set.contains(elem) && elem != a; {}
                        set.remove(a).contains(elem);
                    }
                });
                lemma_fold_set_seq_eq(set.remove(a), seq.drop_last(), z, f);
            }
            f(set.remove(a).fold(z, f), a); { lemma_fold_insert(set.remove(a), z, f, a); }
            set.fold(z, f); 
        }
    }
}

/// Proof that folding over set `s` with `f1` and `f2` is equivalent if `f1` and `f2` are equivalent 
/// over domain `s`.
pub proof fn lemma_fold_fn_eq<A, B>(s: Set<A>, z: B, f1: spec_fn(B, A) -> B, f2: spec_fn(B, A) -> B)
    requires
        s.finite(),
        is_fun_commutative(f1) && is_fun_commutative(f2),
        forall|b: B, a: A| s.contains(a) ==> #[trigger] f1(b, a) == f2(b, a),
    ensures
        s.fold(z, f1) == s.fold(z, f2),
    decreases s.len(),
{
    if s.is_empty() {
        // ..base
        assert(s.fold(z, f1) == z) by { lemma_fold_empty(z, f1); }
        assert(s.fold(z, f2) == z) by { lemma_fold_empty(z, f2); }
    } else {
        // ..induct
        let a = s.choose();
        calc!{
            (==)
            s.fold(z, f1); { lemma_fold_insert(s.remove(a), z, f1, a); }
            f1(s.remove(a).fold(z, f1), a); {}
            f2(s.remove(a).fold(z, f1), a); { lemma_fold_fn_eq(s.remove(a), z, f1, f2); }
            f2(s.remove(a).fold(z, f2), a); { lemma_fold_insert(s.remove(a), z, f2, a); }
            s.fold(z, f2);
        }
    }
}

} // verus!