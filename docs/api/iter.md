# `verge::iter`

Specifications and lemmas for `Iterator` types.

## Specification Methodology
This module includes a template specification for various implementations
of the `Iterator` trait, built upon `vstd`'s `IteratorSpec` encoding.
In time, these specifications should be upstreamed by `vstd` itself.
However, as it is, Rust's orphan rules forbid implementing `IteratorSpec`
on the actual types. Thus, wrapper types are introduced, and the
constructor methods for the iterators are added by extension traits
with a uniform naming convention:
- `str::char_indices() -> CharIndices` into `str::char_indices_iter() -> VergeCharIndices`;
- `path::iter() -> path::Iter` into `path::iterate() -> path::VergeIter`;
This workaround does not affect downstream crates. Users of Verge should
simply make use of the `IteratorSpec` trait.


## Traits


### `IteratorImpl`

```rust
pub(crate) trait IteratorImpl: Iterator
```


#### `next_impl`

```rust
fn next_impl(&mut self) -> Option<<Self as Iterator>::Item>;
```


### `DoubleEndedIteratorImpl`

```rust
pub(crate) trait DoubleEndedIteratorImpl: DoubleEndedIterator
```


#### `next_back_impl`

```rust
fn next_back_impl(&mut self) -> Option<<Self as Iterator>::Item>;
```


### `VergeIteratorSpec`

This trait is used for specifying `(DoubleEnded)Iterator` types by adding the index and
the full sequence as `spec` functions.

```rust
pub trait VergeIteratorSpec: Sized + crate::Sealed
```


#### `Item`

```rust
type Item;
```


#### `seq`

```rust
spec fn seq(&self) -> Seq<Self::Item>;
```


#### `idx`

```rust
spec fn idx(&self) -> int;
```


#### `ridx`

```rust
spec fn ridx(&self) -> int;
```


#### `new_dummy`

Creates a fresh iterator-typed value with the given `seq` view.

This function enables the creation of iterators (which are typically meant for `exec`-mode usage)
in `proof`-mode. It is sound because `VergeIteratorSpec` is a sealed trait and is
only implemented on iterator types with no inherent type invariants, nor additional proof properties.
The sole point of this function is to allow for reasoning about Verge iterators in proofs.

```rust
proof fn new_dummy(seq: Seq<Self::Item>) -> (ret: Self)
    ensures
        ret.idx() == 0,
        ret.ridx() == seq.len(),
        ret.seq() == seq,
```


## Functions


### `iter_count`

Enables `Iterator::count`, which consumes the iterator.

```rust
pub fn iter_count<I: Iterator>(iter: I) -> (ret: usize)
    requires
        iter.obeys_prophetic_iter_laws() && iter.will_return_none(),
    ensures
        ret == iter.remaining().len(),
        { iter.count() }
```
