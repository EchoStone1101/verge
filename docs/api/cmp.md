# `verge::cmp`

Verified trait invariants for comparison traits.

## Trait-Level Invariants
Rust's comparison traits (`PartialEq`, `Eq`, `PartialOrd`, `Ord`) carry implicit
invariants that the compiler does not enforce. For example, `PartialEq` should be
symmetric and transitive, and `Eq` should additionally be reflexive. `vstd` provides
the spec scaffolding (`eq_spec`, `obeys_eq_spec`, etc.) but does not mandate that
these invariants are proven for user-defined types.

Verge addresses this with "verified" sub-traits (e.g., `PartialEqVerified`) that
require the user to provide proofs of the relevant invariants as trait methods.
Implementing these traits is the recommended way to establish trait correctness
for custom types in verified Rust code.


## Traits


### `PartialEqVerified`

A verified `PartialEq` that requires proofs of symmetry and transitivity
for the type's `eq_spec`.

Implementing this trait certifies that the type's `PartialEq` implementation satisfies
the expected mathematical properties.

# Usage

```ignore
impl PartialEqVerified for MyType {
    proof fn lemma_eq_symmetric(a: &Self, b: &Self) {
        // prove a.eq_spec(b) <==> b.eq_spec(a)
    }
    proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {
        // prove a.eq_spec(b) && b.eq_spec(c) ==> a.eq_spec(c)
    }
}
```

```rust
pub trait PartialEqVerified: PartialEq
```


#### `lemma_obeys_eq_spec`

Proof obligation that the type's `obeys_eq_spec()` holds unconditionally.

```rust
proof fn lemma_obeys_eq_spec()
    ensures
        Self::obeys_eq_spec();
```


#### `lemma_eq_symmetric`

Proof that `eq_spec` is symmetric.

```rust
proof fn lemma_eq_symmetric(a: &Self, b: &Self)
    ensures
        a.eq_spec(b) <==> b.eq_spec(a);
```


#### `lemma_eq_transitive`

Proof that `eq_spec` is transitive.

```rust
proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self)
    requires
        a.eq_spec(b),
        b.eq_spec(c),
    ensures
        a.eq_spec(c);
```


### `EqVerified`

A verified `Eq` that additionally requires a proof of reflexivity for `eq_spec`.

```rust
pub trait EqVerified: Eq + PartialEqVerified
```


#### `lemma_eq_reflexive`

Proof that `eq_spec` is reflexive.

```rust
proof fn lemma_eq_reflexive(a: &Self)
    ensures a.eq_spec(a);
```


### `PartialOrdVerified`

A verified `PartialOrd` that requires proofs of the ordering invariants for
`partial_cmp_spec`.

The proof obligations correspond to `vstd::laws_cmp::obeys_partial_cmp_spec_properties`:
- Consistency with `eq_spec` (including substitutivity of Equal)
- Duality between all ordering results
- Transitivity of `Less`
- Transitivity of `Greater`

```rust
pub trait PartialOrdVerified: PartialOrd + PartialEqVerified
```


#### `lemma_obeys_partial_cmp_spec`

Proof obligation that the type's `obeys_partial_cmp_spec()` holds unconditionally.

```rust
proof fn lemma_obeys_partial_cmp_spec()
    ensures
        Self::obeys_partial_cmp_spec();
```


#### `lemma_cmp_eq_consistent`

Proof that `partial_cmp_spec` returning `Equal` asserts equivalence, which means two things:
- (1) `Some(Equal)` is equivalent to `PartialEq::eq`
- (2) two equal values are equivalent when compared with another value

```rust
proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self)
    ensures
        a.partial_cmp_spec(b) == Some(Ordering::Equal) <==> a.eq_spec(b),
        a.partial_cmp_spec(b) == Some(Ordering::Equal) ==>
            forall|c: &Self| a.partial_cmp_spec(c) == b.partial_cmp_spec(c);
```


#### `lemma_cmp_dual`

Proof that `partial_cmp_spec` upholds duality.

```rust
proof fn lemma_cmp_dual(a: &Self, b: &Self)
    ensures
        a.partial_cmp_spec(b) == Some(Ordering::Less)
            <==> b.partial_cmp_spec(a) == Some(Ordering::Greater),
        a.partial_cmp_spec(b) == Some(Ordering::Greater)
            <==> b.partial_cmp_spec(a) == Some(Ordering::Less),
        a.partial_cmp_spec(b) == Some(Ordering::Equal)
            <==> b.partial_cmp_spec(a) == Some(Ordering::Equal),
        a.partial_cmp_spec(b) == None <==> b.partial_cmp_spec(a) == None;
```


#### `lemma_cmp_transitive`

Proof that `Less` and `Greater` are each transitive.

```rust
proof fn lemma_cmp_transitive(a: &Self, b: &Self, c: &Self)
    requires
        a.partial_cmp_spec(b) == b.partial_cmp_spec(c),
        a.partial_cmp_spec(b) == Some(Ordering::Less)
            || a.partial_cmp_spec(b) == Some(Ordering::Greater),
    ensures
        a.partial_cmp_spec(c) == a.partial_cmp_spec(b);
```


### `OrdVerified`

A verified `Ord` that requires a proof that `cmp_spec` is consistent with
`partial_cmp_spec` (and therefore total).

```rust
pub trait OrdVerified: Ord + EqVerified + PartialOrdVerified
```


#### `lemma_obeys_cmp_spec`

Proof obligation that the type's `obeys_cmp_spec()` holds unconditionally.

```rust
proof fn lemma_obeys_cmp_spec()
    ensures
        Self::obeys_cmp_spec();
```


#### `lemma_cmp_consistent`

Proof that `partial_cmp_spec` always equals `Some(cmp_spec(...))`.

```rust
proof fn lemma_cmp_consistent(a: &Self, b: &Self)
    ensures
        a.partial_cmp_spec(b) == Some(a.cmp_spec(b));
```


## Functions


### `lemma_ordering_obeys_eq_spec`

Proof that `Ordering` obeys its `PartialEqSpec` contract.

```rust
pub broadcast axiom fn lemma_ordering_obeys_eq_spec()
    ensures
        #[trigger] <Ordering as PartialEqSpec>::obeys_eq_spec();
```


### `lemma_ordering_eq_spec`

Link `Ordering::eq_spec` to concrete equality between `Ordering` variants.

```rust
pub broadcast axiom fn lemma_ordering_eq_spec(a: &Ordering, b: &Ordering)
    ensures
        #![trigger <Ordering as PartialEqSpec>::eq_spec(a, b)]
        <Ordering as PartialEqSpec>::eq_spec(a, b) == (*a == *b);
```


### `<Ordering as PartialEq<Ordering>>::eq`

Enable direct `Ordering` equality calls in verified code.

```rust
pub assume_specification[ <Ordering as PartialEq<Ordering>>::eq ](
    a: &Ordering,
    b: &Ordering,
    ) -> bool;
```


### `lemma_partial_eq_verified`

For any type implementing `PartialEqVerified`, the full `laws_eq::obeys_eq_spec`
predicate holds.

```rust
pub proof fn lemma_partial_eq_verified<T: PartialEqVerified>()
    ensures laws_eq::obeys_eq::<T>(),
```


### `lemma_partial_ord_verified`

For any type implementing `PartialOrdVerified`, the
`laws_cmp::obeys_partial_cmp_spec_properties` predicate holds.

```rust
pub proof fn lemma_partial_ord_verified<T: PartialOrdVerified>()
    ensures
        laws_cmp::obeys_partial_cmp_spec_properties::<T>(),
```


### `lemma_ord_verified`

For any type implementing `OrdVerified`, the full `laws_cmp::obeys_cmp_spec`
predicate holds.

```rust
pub proof fn lemma_ord_verified<T: OrdVerified>()
    ensures
        laws_cmp::obeys_cmp::<T>(),
```
