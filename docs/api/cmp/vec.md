# `verge::cmp::vec`

Specifications and verified comparison impls for `Vec<T>`.


## Functions


### `<Vec<T, A1> as PartialEq<Vec<U, A2>>>::ne`

Enable `Vec::ne`.

```rust
pub assume_specification<T: PartialEq<U>, U, A1: Allocator, A2: Allocator>[ <Vec<T, A1> as PartialEq<Vec<U, A2>>>::ne ](
    a: &Vec<T, A1>,
    b: &Vec<U, A2>,
    ) -> bool;
```


### `<Vec<T, A1> as PartialOrd<Vec<T, A2>>>::partial_cmp`

Enable `Vec::partial_cmp`.

```rust
pub assume_specification<T: PartialOrd, A1: Allocator, A2: Allocator>[ <Vec<T, A1> as PartialOrd<Vec<T, A2>>>::partial_cmp ](
    a: &Vec<T, A1>,
    b: &Vec<T, A2>,
    ) -> Option<Ordering>;
```


### `<Vec<T, A> as Ord>::cmp`

Enable `Vec::cmp`.

```rust
pub assume_specification<T: Ord, A: Allocator>[ <Vec<T, A> as Ord>::cmp ](
    a: &Vec<T, A>,
    b: &Vec<T, A>,
    ) -> Ordering;
```


### `lemma_vec_eq_spec`

Proof that links vstd's vector `eq_spec` with lexicographic equality.

```rust
pub broadcast axiom fn lemma_vec_eq_spec<T: PartialEq>(a: &Vec<T>, b: &Vec<T>)
    ensures
        #![trigger <Vec<T> as PartialEqSpec>::eq_spec(a, b)]
        <Vec<T> as PartialEqSpec>::eq_spec(a, b) == crate::cmp::lexico_eq(a@, b@);
```


### `lemma_vec_obeys_partial_cmp_spec`

Proof that asserts vector partial comparison obeys the element partial comparison spec.

```rust
pub broadcast axiom fn lemma_vec_obeys_partial_cmp_spec<T: PartialOrd>()
    ensures
        #[trigger] <Vec<T> as PartialOrdSpec>::obeys_partial_cmp_spec()
            == T::obeys_partial_cmp_spec();
```


### `lemma_vec_lexico_partial_cmp_spec`

Proof that links vector `partial_cmp_spec` with lexicographic comparison.

```rust
pub broadcast axiom fn lemma_vec_lexico_partial_cmp_spec<T: PartialOrd>(a: &Vec<T>, b: &Vec<T>)
    ensures
        #![trigger <Vec<T> as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <Vec<T> as PartialOrdSpec>::partial_cmp_spec(a, b) == crate::cmp::lexico_cmp(a@, b@);
```


### `lemma_vec_obeys_cmp_spec`

Proof that asserts vector total comparison obeys the element total comparison spec.

```rust
pub broadcast axiom fn lemma_vec_obeys_cmp_spec<T: Ord>()
    ensures
        #[trigger] <Vec<T> as OrdSpec>::obeys_cmp_spec() == T::obeys_cmp_spec();
```


### `lemma_vec_lexico_cmp_spec`

Proof that links vector `cmp_spec` with lexicographic comparison.

```rust
pub broadcast axiom fn lemma_vec_lexico_cmp_spec<T: Ord>(a: &Vec<T>, b: &Vec<T>)
    ensures
        #![trigger <Vec<T> as OrdSpec>::cmp_spec(a, b)]
        Some(<Vec<T> as OrdSpec>::cmp_spec(a, b)) == crate::cmp::lexico_cmp(a@, b@);
```
