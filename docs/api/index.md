# `verge::`

The Verge library for [Verus](https://github.com/verus-lang/verus).
Contains extensions of the `vstd` standard library in various domains.

# Unix-Only Support
Because of the semantic difference in APIs across various targets, supporting multiple
targets burdens specification. Verge is currently a Unix-only crate.

# `std` Specification
A core part of Verge is exposing much more of the Rust standard library API
to Verus than supported in `vstd`. This process is deliberately kept minimal:
Verge adds only *specification*, not *implementation*.

# Tests as Examples
Verge specifications come with integration tests in the `verge_tests` crate, in the form of
private `exec fn`s that use the public Verge APIs to specify and prove properties
(automatically checked by Verus). These tests also double as examples, showing how the Verge
APIs can be used from a downstream crate.


## Traits


### `Sealed`

Shared marker trait used to seal internal traits.

```rust
pub(crate) trait Sealed {}
```


### `ExAsRef`

Enable the `AsRef` trait.

```rust
pub trait ExAsRef<T: std::marker::PointeeSized>: std::marker::PointeeSized
```


### `ExAsMut`

Enable the `AsMut` trait.

```rust
pub trait ExAsMut<T: std::marker::PointeeSized>: std::marker::PointeeSized
```


### `VergeView`

The `VergeView` trait adds the `view` method to a type that otherwise
does not implement `vstd::View`.
Semantically it is equivalent to implement `view` as part of the type's `impl` block,
but `VergeView` has the advantage of working as a trait bound.

```rust
pub trait VergeView
```


#### `V`

```rust
type V;
```


#### `view`

```rust
spec fn view(&self) -> Self::V;
```


## Functions


### `is_deterministic`

Encodes whether an exec-mode function is deterministic in spec mode.

```rust
pub open spec fn is_deterministic<F, Args: Tuple>(f: F) -> bool
    where
    F: FnMut<Args>,
    Args: Tuple,
{
        forall |args: Args, o1: <F as FnOnce<Args>>::Output, o2: <F as FnOnce<Args>>::Output|
            #![trigger call_ensures(f, args, o1), call_ensures(f, args, o2)]
            call_requires(f, args) && call_ensures(f, args, o1) && call_ensures(f, args, o2) ==> o1 == o2
}
```


### `is_total`

Encodes whether an exec-mode function is total.

```rust
pub open spec fn is_total<F, Args: Tuple>(f: F) -> bool
    where
    F: FnMut<Args>,
    Args: Tuple,
{
        forall |args: Args| #[trigger] call_requires(f, args)
}
```


### `dummy`

A one-term trigger helper.

```rust
pub uninterp spec fn dummy<A>(a: A) -> ();
```


### `dummy2`

A two-term trigger helper.

```rust
pub uninterp spec fn dummy2<A, B>(a: A, b: B) -> ();
```
