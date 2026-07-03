# `verge::cmp::slice`

Specifications and verified comparison impls for slices.

The Rust slice comparison traits are external to Verge, so this module links
their vstd spec methods to Verge's lexicographic sequence specs by broadcast
axioms and then proves the local `*Verified` traits from those links.


## Functions


### `<[T] as PartialEq<[U]>>::eq`

Enable slice equality.

```rust
pub assume_specification<T: PartialEq<U>, U>[ <[T] as PartialEq<[U]>>::eq ](
    a: &[T],
    b: &[U],
    ) -> bool;
```


### `<[T] as PartialOrd>::partial_cmp`

Enable slice partial comparison.

```rust
pub assume_specification<T: PartialOrd>[ <[T] as PartialOrd>::partial_cmp ](
    a: &[T],
    b: &[T],
    ) -> Option<Ordering>;
```


### `<[T] as Ord>::cmp`

Enable slice total comparison.

```rust
pub assume_specification<T: Ord>[ <[T] as Ord>::cmp ](a: &[T], b: &[T]) -> Ordering;
```


### `lemma_slice_obeys_eq_spec`

Proof that asserts slice equality obeys the element equality spec.

```rust
pub broadcast axiom fn lemma_slice_obeys_eq_spec<T: PartialEq>()
    ensures
        #[trigger] <[T] as PartialEqSpec>::obeys_eq_spec() == T::obeys_eq_spec();
```


### `lemma_slice_eq_spec`

Proof that links slice `eq_spec` with lexicographic equality.

```rust
pub broadcast axiom fn lemma_slice_eq_spec<T: PartialEq>(a: &[T], b: &[T])
    ensures
        #![trigger <[T] as PartialEqSpec>::eq_spec(a, b)]
        <[T] as PartialEqSpec>::eq_spec(a, b) == crate::cmp::lexico_eq(a@, b@);
```


### `lemma_slice_obeys_partial_cmp_spec`

Proof that asserts slice partial comparison obeys the element partial comparison spec.

```rust
pub broadcast axiom fn lemma_slice_obeys_partial_cmp_spec<T: PartialOrd>()
    ensures
        #[trigger] <[T] as PartialOrdSpec>::obeys_partial_cmp_spec()
            == T::obeys_partial_cmp_spec();
```


### `lemma_slice_lexico_partial_cmp_spec`

Proof that links slice `partial_cmp_spec` with lexicographic comparison.

```rust
pub broadcast axiom fn lemma_slice_lexico_partial_cmp_spec<T: PartialOrd>(a: &[T], b: &[T])
    ensures
        #![trigger <[T] as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <[T] as PartialOrdSpec>::partial_cmp_spec(a, b) == crate::cmp::lexico_cmp(a@, b@);
```


### `lemma_slice_obeys_cmp_spec`

Proof that asserts slice total comparison obeys the element total comparison spec.

```rust
pub broadcast axiom fn lemma_slice_obeys_cmp_spec<T: Ord>()
    ensures
        #[trigger] <[T] as OrdSpec>::obeys_cmp_spec() == T::obeys_cmp_spec();
```


### `lemma_slice_lexico_cmp_spec`

Proof that links slice `cmp_spec` with lexicographic comparison.

```rust
pub broadcast axiom fn lemma_slice_lexico_cmp_spec<T: Ord>(a: &[T], b: &[T])
    ensures
        #![trigger <[T] as OrdSpec>::cmp_spec(a, b)]
        Some(<[T] as OrdSpec>::cmp_spec(a, b)) == crate::cmp::lexico_cmp(a@, b@);
```
