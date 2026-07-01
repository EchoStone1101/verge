# `verge::cmp::internal`

Private proof helpers for `cmp`.


## Functions


### `lemma_lexico_cons_equal`

```rust
pub(super) proof fn lemma_lexico_cons_equal(s: Seq<Option<Ordering>>)
    ensures
        lexico_less(seq![Some(Ordering::Equal)] + s) <==> lexico_less(s),
        lexico_greater(seq![Some(Ordering::Equal)] + s) <==> lexico_greater(s),
        lexico_incomparable(seq![Some(Ordering::Equal)] + s) <==> lexico_incomparable(s),
        lexico_equal(seq![Some(Ordering::Equal)] + s) <==> lexico_equal(s),
```


### `lemma_lexico_cmp_by_prefix_empty`

```rust
pub(super) proof fn lemma_lexico_cmp_by_prefix_empty<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() == 0 || s2.len() == 0,
    ensures
        lexico_cmp(s1, s2) == lexico_cmp_by_prefix(s1, s2),
```


### `lemma_lexico_cmp_by_prefix_equal_head`

```rust
pub(super) proof fn lemma_lexico_cmp_by_prefix_equal_head<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() > 0,
        s2.len() > 0,
        PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Equal),
    ensures
        lexico_cmp_by_prefix(s1, s2) == lexico_cmp_by_prefix(s1.drop_first(), s2.drop_first()),
```


### `lemma_lexico_cmp_by_prefix_less_head`

```rust
pub(super) proof fn lemma_lexico_cmp_by_prefix_less_head<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() > 0,
        s2.len() > 0,
        PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Less),
    ensures
        lexico_cmp(s1, s2) == lexico_cmp_by_prefix(s1, s2),
```


### `lemma_lexico_cmp_by_prefix_greater_head`

```rust
pub(super) proof fn lemma_lexico_cmp_by_prefix_greater_head<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() > 0,
        s2.len() > 0,
        PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == Some(Ordering::Greater),
    ensures
        lexico_cmp(s1, s2) == lexico_cmp_by_prefix(s1, s2),
```


### `lemma_lexico_cmp_by_prefix_none_head`

```rust
pub(super) proof fn lemma_lexico_cmp_by_prefix_none_head<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() > 0,
        s2.len() > 0,
        PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) == None,
    ensures
        lexico_cmp(s1, s2) == lexico_cmp_by_prefix(s1, s2),
```


### `lemma_cmp_eq_substitute_right`

```rust
pub(super) proof fn lemma_cmp_eq_substitute_right<T: PartialOrdVerified>(a: &T, b: &T, c: &T)
    requires
        b.partial_cmp_spec(c) == Some(Ordering::Equal),
    ensures
        a.partial_cmp_spec(b) == a.partial_cmp_spec(c),
```


### `lemma_cmp_three_transitive`

```rust
pub(super) proof fn lemma_cmp_three_transitive<T: PartialOrdVerified>(a: &T, b: &T, c: &T, ord: Ordering)
    requires
        ord == Ordering::Less || ord == Ordering::Greater,
        a.partial_cmp_spec(b) == Some(ord),
        b.partial_cmp_spec(c) == Some(ord),
    ensures
        a.partial_cmp_spec(c) == Some(ord),
```


### `lemma_lexico_first_non_equal`

```rust
pub(super) proof fn lemma_lexico_first_non_equal(s: Seq<Option<Ordering>>, witness: int)
    requires
        0 <= witness < s.len(),
        s[witness] != Some(Ordering::Equal),
    ensures
        exists|i: int| 0 <= i < s.len()
            && s[i] != Some(Ordering::Equal)
            && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal),
    decreases witness,
```
