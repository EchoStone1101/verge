# `verge::cmp::vec_deque`

Specifications and verified comparison impls for `VecDeque<T>`.


## Functions


### `<VecDeque<T, A> as PartialEq>::eq`

Enable `VecDeque::eq`.

```rust
pub assume_specification<T: PartialEq, A: Allocator>[ <VecDeque<T, A> as PartialEq>::eq ](
    a: &VecDeque<T, A>,
    b: &VecDeque<T, A>,
    ) -> bool;
```


### `<VecDeque<T, A> as PartialOrd>::partial_cmp`

Enable `VecDeque::partial_cmp`.

```rust
pub assume_specification<T: PartialOrd, A: Allocator>[ <VecDeque<T, A> as PartialOrd>::partial_cmp ](
    a: &VecDeque<T, A>,
    b: &VecDeque<T, A>,
    ) -> Option<Ordering>;
```


### `<VecDeque<T, A> as Ord>::cmp`

Enable `VecDeque::cmp`.

```rust
pub assume_specification<T: Ord, A: Allocator>[ <VecDeque<T, A> as Ord>::cmp ](
    a: &VecDeque<T, A>,
    b: &VecDeque<T, A>,
    ) -> Ordering;
```


### `lemma_vec_deque_obeys_eq_spec`

Proof that asserts vector deque equality obeys the element equality spec.

```rust
pub broadcast axiom fn lemma_vec_deque_obeys_eq_spec<T: PartialEq>()
    ensures
        #[trigger] <VecDeque<T> as PartialEqSpec>::obeys_eq_spec() == T::obeys_eq_spec();
```


### `lemma_vec_deque_eq_spec`

Proof that links vector deque `eq_spec` with lexicographic equality.

```rust
pub broadcast axiom fn lemma_vec_deque_eq_spec<T: PartialEq>(a: &VecDeque<T>, b: &VecDeque<T>)
    ensures
        #![trigger <VecDeque<T> as PartialEqSpec>::eq_spec(a, b)]
        <VecDeque<T> as PartialEqSpec>::eq_spec(a, b) == crate::cmp::lexico_eq(a@, b@);
```


### `lemma_vec_deque_obeys_partial_cmp_spec`

Proof that asserts vector deque partial comparison obeys the element partial comparison spec.

```rust
pub broadcast axiom fn lemma_vec_deque_obeys_partial_cmp_spec<T: PartialOrd>()
    ensures
        #[trigger] <VecDeque<T> as PartialOrdSpec>::obeys_partial_cmp_spec()
            == T::obeys_partial_cmp_spec();
```


### `lemma_vec_deque_lexico_partial_cmp_spec`

Proof that links vector deque `partial_cmp_spec` with lexicographic comparison.

```rust
pub broadcast axiom fn lemma_vec_deque_lexico_partial_cmp_spec<T: PartialOrd>(
    a: &VecDeque<T>,
    b: &VecDeque<T>,
    )
    ensures
        #![trigger <VecDeque<T> as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <VecDeque<T> as PartialOrdSpec>::partial_cmp_spec(a, b) == crate::cmp::lexico_cmp(a@, b@);
```


### `lemma_vec_deque_obeys_cmp_spec`

Proof that asserts vector deque total comparison obeys the element total comparison spec.

```rust
pub broadcast axiom fn lemma_vec_deque_obeys_cmp_spec<T: Ord>()
    ensures
        #[trigger] <VecDeque<T> as OrdSpec>::obeys_cmp_spec() == T::obeys_cmp_spec();
```


### `lemma_vec_deque_lexico_cmp_spec`

Proof that links vector deque `cmp_spec` with lexicographic comparison.

```rust
pub broadcast axiom fn lemma_vec_deque_lexico_cmp_spec<T: Ord>(a: &VecDeque<T>, b: &VecDeque<T>)
    ensures
        #![trigger <VecDeque<T> as OrdSpec>::cmp_spec(a, b)]
        Some(<VecDeque<T> as OrdSpec>::cmp_spec(a, b)) == crate::cmp::lexico_cmp(a@, b@);
```
