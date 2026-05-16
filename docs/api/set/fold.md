# `verge::set::fold`

Definitions and lemmas for `Set::fold` in Verus, extending `vstd::set::fold`.


## Functions


### `lemma_fold_disjoint_union`

Proof that folding over two disjoint sets is equivalent to folding over their union set.

```rust
pub proof fn lemma_fold_disjoint_union<A, B>(s1: Set<A>, s2: Set<A>, z: B, f: spec_fn(B, A) -> B)
    requires
        s1.finite() && s2.finite(),
        s1.disjoint(s2),
        is_fun_commutative(f),
    ensures
        (s1 + s2).fold(z, f) == s2.fold(s1.fold(z, f), f),
    decreases s2.len(),
```


### `lemma_fold_set_seq_eq`

Proof that folding over a set is equivalent to folding along its sequence version,
if the fold function is commutative.

```rust
pub proof fn lemma_fold_set_seq_eq<A, B>(set: Set<A>, seq: Seq<A>, z: B, f: spec_fn(B, A) -> B)
    requires
        set.finite(),
        seq.no_duplicates() && seq.to_set() == set,
        is_fun_commutative(f),
    ensures
        set.fold(z, f) == seq.fold_left(z, f),
    decreases
        set.len(),
```


### `lemma_fold_fn_eq`

Proof that folding over set `s` with `f1` and `f2` is equivalent if `f1` and `f2` are equivalent
over domain `s`.

```rust
pub proof fn lemma_fold_fn_eq<A, B>(s: Set<A>, z: B, f1: spec_fn(B, A) -> B, f2: spec_fn(B, A) -> B)
    requires
        s.finite(),
        is_fun_commutative(f1) && is_fun_commutative(f2),
        forall|b: B, a: A| s.contains(a) ==> #[trigger] f1(b, a) == f2(b, a),
    ensures
        s.fold(z, f1) == s.fold(z, f2),
    decreases s.len(),
```
