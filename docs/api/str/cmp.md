# `verge::str::cmp`

Specifications and lemmas for string comparison.

## Specification Methodology
`vstd` provides the `PartialEqSpec`, `PartialOrdSpec`, and `OrdSpec` traits as
the standard way to build comparison specs. However, the orphan rule blocks
Verge from implementing the traits directly on `str` and `String`. As a
workaround, we introduce broadcast lemmas that link the `vstd` spec methods
with actual spec clauses.


## Traits


### `StringSpecOrd`

Allows for `spec`-mode comparisons on strings.

```rust
pub trait StringSpecOrd
```


#### `spec_lt`

```rust
spec fn spec_lt(self, rhs: Self) -> bool;
```


#### `spec_le`

```rust
spec fn spec_le(self, rhs: Self) -> bool;
```


#### `spec_gt`

```rust
spec fn spec_gt(self, rhs: Self) -> bool;
```


#### `spec_ge`

```rust
spec fn spec_ge(self, rhs: Self) -> bool;
```


## Functions


### `<str as PartialEq>::eq`

Enable `str` equality.

```rust
pub assume_specification[ <str as PartialEq>::eq ](s: &str, other: &str) -> (res: bool)
    ensures
        res == crate::cmp::lexico_eq(s@.as_bytes(), other@.as_bytes()),
        ;
```


### `lemma_str_obeys_eq_spec`

Proof that asserts `str` obeys `PartialEq`.

```rust
pub broadcast axiom fn lemma_str_obeys_eq_spec()
    ensures
        #[trigger] <str as PartialEqSpec>::obeys_eq_spec();
```


### `lemma_string_obeys_eq_spec`

Proof that asserts `String` obeys `PartialEq`.

```rust
pub broadcast axiom fn lemma_string_obeys_eq_spec()
    ensures
        #[trigger] <String as PartialEqSpec>::obeys_eq_spec();
```


### `lemma_str_eq_spec`

Proof that links `PartialEqSpec::eq_spec` for `str` with byte-wise string equality.

```rust
pub broadcast axiom fn lemma_str_eq_spec(a: &str, b: &str)
    ensures
        #![trigger <str as PartialEqSpec>::eq_spec(a, b)]
        <str as PartialEqSpec>::eq_spec(a, b) ==
            crate::cmp::lexico_eq(a@.as_bytes(), b@.as_bytes());
```


### `lemma_string_eq_spec`

Proof that links `PartialEqSpec::eq_spec` for `String` with byte-wise string equality.

```rust
pub broadcast axiom fn lemma_string_eq_spec(a: &String, b: &String)
    ensures
        #![trigger <String as PartialEqSpec>::eq_spec(a, b)]
        <String as PartialEqSpec>::eq_spec(a, b) ==
            crate::cmp::lexico_eq(a@.as_bytes(), b@.as_bytes());
```


### `lemma_str_obeys_partial_cmp_spec`

Proof that asserts `str` obeys `PartialOrd`.

```rust
pub broadcast axiom fn lemma_str_obeys_partial_cmp_spec()
    ensures
        #[trigger] <str as PartialOrdSpec>::obeys_partial_cmp_spec();
```


### `lemma_string_obeys_partial_cmp_spec`

Proof that asserts `String` obeys `PartialOrd`.

```rust
pub broadcast axiom fn lemma_string_obeys_partial_cmp_spec()
    ensures
        #[trigger] <String as PartialOrdSpec>::obeys_partial_cmp_spec();
```


### `lemma_str_lexico_partial_cmp_spec`

Proof that links `PartialOrdSpec::partial_cmp_spec` for `str` with actual specs.

```rust
pub broadcast axiom fn lemma_str_lexico_partial_cmp_spec(a: &str, b: &str)
    ensures
        #![trigger <str as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <str as PartialOrdSpec>::partial_cmp_spec(a, b) ==
            crate::cmp::lexico_cmp(a@.as_bytes(), b@.as_bytes());
```


### `lemma_string_lexico_partial_cmp_spec`

Proof that links `PartialOrdSpec::partial_cmp_spec` for `String` with actual specs.

```rust
pub broadcast axiom fn lemma_string_lexico_partial_cmp_spec(a: &String, b: &String)
    ensures
        #![trigger <String as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <String as PartialOrdSpec>::partial_cmp_spec(a, b) ==
            crate::cmp::lexico_cmp(a@.as_bytes(), b@.as_bytes());
```


### `lemma_str_obeys_cmp_spec`

Proof that asserts `str` obeys `Ord`.

```rust
pub broadcast axiom fn lemma_str_obeys_cmp_spec()
    ensures
        #[trigger] <str as OrdSpec>::obeys_cmp_spec();
```


### `lemma_string_obeys_cmp_spec`

Proof that asserts `String` obeys `Ord`.

```rust
pub broadcast axiom fn lemma_string_obeys_cmp_spec()
    ensures
        #[trigger] <String as OrdSpec>::obeys_cmp_spec();
```


### `lemma_str_lexico_cmp_spec`

Proof that links `OrdSpec::cmp_spec` for `str` with actual specs.

```rust
pub broadcast axiom fn lemma_str_lexico_cmp_spec(a: &str, b: &str)
    ensures
        #![trigger <str as OrdSpec>::cmp_spec(a, b)]
        <str as OrdSpec>::cmp_spec(a, b) ==
            crate::cmp::lexico_cmp(a@.as_bytes(), b@.as_bytes())->0;
```


### `lemma_string_lexico_cmp_spec`

Proof that links `OrdSpec::cmp_spec` for `String` with actual specs.

```rust
pub broadcast axiom fn lemma_string_lexico_cmp_spec(a: &String, b: &String)
    ensures
        #![trigger <String as OrdSpec>::cmp_spec(a, b)]
        <String as OrdSpec>::cmp_spec(a, b) ==
            crate::cmp::lexico_cmp(a@.as_bytes(), b@.as_bytes())->0;
```
