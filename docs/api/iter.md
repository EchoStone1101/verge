# `verge::iter`

Specifications and lemmas for the `Iterator` trait.

This module includes a template specification for various implementations
of the `core::iter::Iterator` trait and its `next` method.


## Traits


### `IteratorView`

This trait adds the `view()` method for any iterator.

```rust
pub trait IteratorView
```


#### `Item`

```rust
type Item;
```


#### `view`

```rust
spec fn view(&self) -> (int, Seq<Self::Item>);
```
