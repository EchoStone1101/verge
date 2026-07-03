# `verge::cmp::result`

Verified comparison impls for `Result<T, E>`.


## Functions


### `lemma_result_obeys_eq_spec`

Proof that asserts `Result<T, E>` obeys `PartialEq` when its contents do.

```rust
pub broadcast axiom fn lemma_result_obeys_eq_spec<T: PartialEqSpec, E: PartialEqSpec>()
    ensures
        T::obeys_eq_spec() && E::obeys_eq_spec() ==>
            #[trigger] <Result<T, E> as PartialEqSpec>::obeys_eq_spec();
```


### `lemma_result_eq_spec`

Proof that links `PartialEqSpec::eq_spec` for `Result<T, E>` with Rust's variant-wise equality.

```rust
pub broadcast axiom fn lemma_result_eq_spec<T: PartialEqSpec, E: PartialEqSpec>(a: &Result<T, E>, b: &Result<T, E>)
    ensures
        #![trigger <Result<T, E> as PartialEqSpec>::eq_spec(a, b)]
        <Result<T, E> as PartialEqSpec>::eq_spec(a, b) == match (a, b) {
            (Ok(x), Ok(y)) => x.eq_spec(y),
            (Err(x), Err(y)) => x.eq_spec(y),
            _ => false,
        };
```


### `<Result<T, E> as PartialEq>::eq`

Enable `Result::eq`.

```rust
pub assume_specification<T: PartialEq, E: PartialEq>[ <Result<T, E> as PartialEq>::eq ](
    x: &Result<T, E>,
    y: &Result<T, E>,
    ) -> bool;
```


### `lemma_result_obeys_partial_cmp_spec`

Proof that asserts `Result<T, E>` obeys `PartialOrd` when its contents do.

```rust
pub broadcast axiom fn lemma_result_obeys_partial_cmp_spec<T: PartialOrdSpec, E: PartialOrdSpec>()
    ensures
        T::obeys_partial_cmp_spec() && E::obeys_partial_cmp_spec() ==>
            #[trigger] <Result<T, E> as PartialOrdSpec>::obeys_partial_cmp_spec();
```


### `lemma_result_partial_cmp_spec`

Proof that links `PartialOrdSpec::partial_cmp_spec` for `Result<T, E>` with Rust's ordering.

```rust
pub broadcast axiom fn lemma_result_partial_cmp_spec<T: PartialOrdSpec, E: PartialOrdSpec>(a: &Result<T, E>, b: &Result<T, E>)
    ensures
        #![trigger <Result<T, E> as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <Result<T, E> as PartialOrdSpec>::partial_cmp_spec(a, b) == match (a, b) {
            (Ok(x), Ok(y)) => x.partial_cmp_spec(y),
            (Ok(_), Err(_)) => Some(Ordering::Greater),
            (Err(_), Ok(_)) => Some(Ordering::Less),
            (Err(x), Err(y)) => x.partial_cmp_spec(y),
        };
```


### `<Result<T, E> as PartialOrd>::partial_cmp`

Enable `Result::partial_cmp`.

```rust
pub assume_specification<T: PartialOrd, E: PartialOrd>[ <Result<T, E> as PartialOrd>::partial_cmp ](
    x: &Result<T, E>,
    y: &Result<T, E>,
    ) -> Option<Ordering>;
```


### `lemma_result_obeys_cmp_spec`

Proof that asserts `Result<T, E>` obeys `Ord` when its contents do.

```rust
pub broadcast axiom fn lemma_result_obeys_cmp_spec<T: OrdSpec, E: OrdSpec>()
    ensures
        T::obeys_cmp_spec() && E::obeys_cmp_spec() ==>
            #[trigger] <Result<T, E> as OrdSpec>::obeys_cmp_spec();
```


### `lemma_result_cmp_spec`

Proof that links `OrdSpec::cmp_spec` for `Result<T, E>` with Rust's ordering.

```rust
pub broadcast axiom fn lemma_result_cmp_spec<T: OrdSpec, E: OrdSpec>(a: &Result<T, E>, b: &Result<T, E>)
    ensures
        #![trigger <Result<T, E> as OrdSpec>::cmp_spec(a, b)]
        <Result<T, E> as OrdSpec>::cmp_spec(a, b) == match (a, b) {
            (Ok(x), Ok(y)) => x.cmp_spec(y),
            (Ok(_), Err(_)) => Ordering::Greater,
            (Err(_), Ok(_)) => Ordering::Less,
            (Err(x), Err(y)) => x.cmp_spec(y),
        };
```


### `<Result<T, E> as Ord>::cmp`

Enable `Result::cmp`.

```rust
pub assume_specification<T: Ord, E: Ord>[ <Result<T, E> as Ord>::cmp ](
    x: &Result<T, E>,
    y: &Result<T, E>,
    ) -> Ordering;
```
