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
Verge specifications come with unit tests (`mod tests`), in the form of private `exec fn`s
that use the Verge specs to specify and prove properties (automatically checked by Verus).
These tests also double as examples, showing how the Verge APIs can be used.


## Traits


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


## Functions


### `dummy`

Used for a dummy one-term trigger.

```rust
pub uninterp spec fn dummy<A>(a: A) -> ();
```


### `dummy2`

Used for a dummy two-term trigger.

```rust
pub uninterp spec fn dummy2<A, B>(a: A, b: B) -> ();
```


### `box_as_ref`

Enables `Box::<T>::as_ref`.

```rust
pub uninterp spec fn box_as_ref<T: ?Sized, A: Allocator>(ptr: &Box<T, A>) -> &T;
```


### `Box::<T, A>::as_ref`

```rust
pub assume_specification<T: ?Sized, A: Allocator>[ Box::<T, A>::as_ref ](this: &Box<T, A>) -> (ret: &T)
    ensures
        this == ret,
    no_unwind
        ;
```


### `rc_as_ref`

Enables `Rc::<T>::as_ref`.

```rust
pub uninterp spec fn rc_as_ref<T: ?Sized, A: Allocator>(ptr: &Rc<T, A>) -> &T;
```


### `Rc::<T, A>::as_ref`

```rust
pub assume_specification<T: ?Sized, A: Allocator>[ Rc::<T, A>::as_ref ](this: &Rc<T, A>) -> (ret: &T)
    ensures
        this == ret,
    no_unwind
        ;
```
