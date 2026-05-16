# `verge::clone`

Verified trait invariants for `Clone`.

## Inter-Trait Invariants
`Clone` alone carries no invariant. However, when combined with other traits,
Rust language design does have further specifications:
- `PartialEq`: `x == x ==> x.clone() == x`.
- `Copy`: `x.clone()` is a *bit-wise* copy.
Traits in this module each carries a proof of these cross-trait invariants.

## Clone Ban
The `CloneImpl` trait and sealed helpers allow macros to statically prevent
a type from implementing `Clone`.  A blanket impl sets `Impl = Yes` for all
`Clone` types; emitting `impl CloneImpl for T { type Impl = No; }` makes any
future `Clone` impl a coherence error.


## Structs


### `CloneYes`

Marker: type implements `Clone`.

```rust
pub struct CloneYes;
```


### `CloneNo`

Marker: type must *not* implement `Clone`.

```rust
pub struct CloneNo;
```


## Traits


### `CloneImpl`

Blanket-impl side of the Clone ban trick.
All `Clone` types get `Impl = CloneYes`.
Macros can emit `impl CloneImpl for T { type Impl = CloneNo; }`
to make `Clone` for `T` a coherence error.

```rust
pub trait CloneImpl { type Impl: _clone_sealed::Sealed; }
```


### `ClonePartialEq`

A verified `Clone + PartialEq` that requires a proof that cloning preserves
equality: if `a.eq_spec(a)`, then `clone(a).eq_spec(a)`.

For `EqVerified` types (where reflexivity holds), this simplifies to:
cloning always produces an `eq_spec`-equal value.

```rust
pub trait ClonePartialEq: Clone + PartialEqVerified
```


#### `lemma_clone_preserves_eq`

Proof that cloning preserves `eq_spec`.

```rust
proof fn lemma_clone_preserves_eq(a: &Self)
    requires
        Self::obeys_eq_spec(),
        a.eq_spec(a),
    ensures
        forall|ret: Self|
            #[trigger] strictly_cloned(*a, ret) ==> a.eq_spec(&ret);
```


### `CopyVerified`

A verified `Copy` that requires a proof that cloning produces a spec-equal value.

For `Copy` types, Rust requires that `clone()` is equivalent to a bit-wise copy.
This trait approximates that requirement using Verus's ghost-mode `==`.

**Gap:** Ghost-mode `==` is not strictly bit-wise equality. For immutable references
(`&T`), spec `==` compares the pointed-to values rather than the pointer addresses.
In practice this distinction rarely matters for correctness of collections or
algorithms, but it means `CopyVerified` is slightly weaker than true bit-wise
identity for reference types.

```rust
pub trait CopyVerified: Copy
```


#### `lemma_clone_identical`

Proof that cloning a `Copy` type produces a spec-equal (ghost `==`) value.

```rust
proof fn lemma_clone_identical(a: &Self)
    ensures
        forall|ret: Self|
            #[trigger] strictly_cloned(*a, ret) ==> ret == *a;
```
