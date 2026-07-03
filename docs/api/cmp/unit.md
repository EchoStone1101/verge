# `verge::cmp::unit`

Verified comparison impls for unit.


## Functions


### `<() as PartialEq>::eq`

Enable unit equality.

```rust
pub assume_specification[ <() as PartialEq>::eq ](a: &(), b: &()) -> bool;
```


### `<() as PartialEq>::ne`

Enable unit inequality.

```rust
pub assume_specification[ <() as PartialEq>::ne ](a: &(), b: &()) -> bool;
```


### `<() as PartialOrd>::partial_cmp`

Enable unit partial comparison.

```rust
pub assume_specification[ <() as PartialOrd>::partial_cmp ](a: &(), b: &()) -> Option<Ordering>;
```


### `<() as Ord>::cmp`

Enable unit total comparison.

```rust
pub assume_specification[ <() as Ord>::cmp ](a: &(), b: &()) -> Ordering;
```


### `lemma_unit_obeys_eq_spec`

Proof that asserts unit obeys `PartialEq`.

```rust
pub broadcast axiom fn lemma_unit_obeys_eq_spec()
    ensures
        #[trigger] <() as PartialEqSpec>::obeys_eq_spec();
```


### `lemma_unit_eq_spec`

Proof that unit equality is always true.

```rust
pub broadcast axiom fn lemma_unit_eq_spec(a: &(), b: &())
    ensures
        #![trigger <() as PartialEqSpec>::eq_spec(a, b)]
        <() as PartialEqSpec>::eq_spec(a, b);
```


### `lemma_unit_obeys_partial_cmp_spec`

Proof that asserts unit obeys `PartialOrd`.

```rust
pub broadcast axiom fn lemma_unit_obeys_partial_cmp_spec()
    ensures
        #[trigger] <() as PartialOrdSpec>::obeys_partial_cmp_spec();
```


### `lemma_unit_partial_cmp_spec`

Proof that unit partial comparison is always equal.

```rust
pub broadcast axiom fn lemma_unit_partial_cmp_spec(a: &(), b: &())
    ensures
        #![trigger <() as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <() as PartialOrdSpec>::partial_cmp_spec(a, b) == Some(Ordering::Equal);
```


### `lemma_unit_obeys_cmp_spec`

Proof that asserts unit obeys `Ord`.

```rust
pub broadcast axiom fn lemma_unit_obeys_cmp_spec()
    ensures
        #[trigger] <() as OrdSpec>::obeys_cmp_spec();
```


### `lemma_unit_cmp_spec`

Proof that unit total comparison is always equal.

```rust
pub broadcast axiom fn lemma_unit_cmp_spec(a: &(), b: &())
    ensures
        #![trigger <() as OrdSpec>::cmp_spec(a, b)]
        <() as OrdSpec>::cmp_spec(a, b) == Ordering::Equal;
```
