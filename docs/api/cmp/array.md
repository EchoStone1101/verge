# `verge::cmp::array`

Specifications and verified comparison impls for arrays.


## Functions


### `<[T; N] as PartialEq<[U; N]>>::eq`

Enable array equality.

```rust
pub assume_specification<T: PartialEq<U>, U, const N: usize>[ <[T; N] as PartialEq<[U; N]>>::eq ](
    a: &[T; N],
    b: &[U; N],
    ) -> bool;
```


### `<[T; N] as PartialOrd>::partial_cmp`

Enable array partial comparison.

```rust
pub assume_specification<T: PartialOrd, const N: usize>[ <[T; N] as PartialOrd>::partial_cmp ](
    a: &[T; N],
    b: &[T; N],
    ) -> Option<Ordering>;
```


### `<[T; N] as Ord>::cmp`

Enable array total comparison.

```rust
pub assume_specification<T: Ord, const N: usize>[ <[T; N] as Ord>::cmp ](
    a: &[T; N],
    b: &[T; N],
    ) -> Ordering;
```


### `lemma_array_obeys_eq_spec`

Proof that asserts array equality obeys the element equality spec.

```rust
pub broadcast axiom fn lemma_array_obeys_eq_spec<T: PartialEq, const N: usize>()
    ensures
        #[trigger] <[T; N] as PartialEqSpec>::obeys_eq_spec() == T::obeys_eq_spec();
```


### `lemma_array_eq_spec`

Proof that links array `eq_spec` with lexicographic equality.

```rust
pub broadcast axiom fn lemma_array_eq_spec<T: PartialEq, const N: usize>(a: &[T; N], b: &[T; N])
    ensures
        #![trigger <[T; N] as PartialEqSpec>::eq_spec(a, b)]
        <[T; N] as PartialEqSpec>::eq_spec(a, b) == crate::cmp::lexico_eq(a@, b@);
```


### `lemma_array_obeys_partial_cmp_spec`

Proof that asserts array partial comparison obeys the element partial comparison spec.

```rust
pub broadcast axiom fn lemma_array_obeys_partial_cmp_spec<T: PartialOrd, const N: usize>()
    ensures
        #[trigger] <[T; N] as PartialOrdSpec>::obeys_partial_cmp_spec()
            == T::obeys_partial_cmp_spec();
```


### `lemma_array_lexico_partial_cmp_spec`

Proof that links array `partial_cmp_spec` with lexicographic comparison.

```rust
pub broadcast axiom fn lemma_array_lexico_partial_cmp_spec<T: PartialOrd, const N: usize>(
    a: &[T; N],
    b: &[T; N],
    )
    ensures
        #![trigger <[T; N] as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <[T; N] as PartialOrdSpec>::partial_cmp_spec(a, b) == crate::cmp::lexico_cmp(a@, b@);
```


### `lemma_array_obeys_cmp_spec`

Proof that asserts array total comparison obeys the element total comparison spec.

```rust
pub broadcast axiom fn lemma_array_obeys_cmp_spec<T: Ord, const N: usize>()
    ensures
        #[trigger] <[T; N] as OrdSpec>::obeys_cmp_spec() == T::obeys_cmp_spec();
```


### `lemma_array_lexico_cmp_spec`

Proof that links array `cmp_spec` with lexicographic comparison.

```rust
pub broadcast axiom fn lemma_array_lexico_cmp_spec<T: Ord, const N: usize>(a: &[T; N], b: &[T; N])
    ensures
        #![trigger <[T; N] as OrdSpec>::cmp_spec(a, b)]
        Some(<[T; N] as OrdSpec>::cmp_spec(a, b)) == crate::cmp::lexico_cmp(a@, b@);
```
