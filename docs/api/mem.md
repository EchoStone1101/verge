# `verge::mem`

Specifications and lemmas for memory-related operations.


## Functions


### `core::mem::forget::<T>`

Enable `core::mem::forget`.

```rust
pub assume_specification<T> [core::mem::forget::<T>] (t: T)
    opens_invariants none
    no_unwind;
```


### `core::mem::replace::<T>`

Enable `core::mem::replace`.

```rust
pub assume_specification<T> [core::mem::replace::<T>] (dest: &mut T, src: T) -> (ret: T)
    ensures
        *final(dest) == src,
        ret == *old(dest),
    opens_invariants none
    no_unwind;
```
