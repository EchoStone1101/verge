# `verge::str`

Specifications and lemmas for strings, extending `vstd`'s support.

### Bytes or Chars
There are two typical ways to view a Rust string (`&str` or `String`): as bytes (`u8`), or as `char`s.
Each string is in fact stored as a raw `&[u8]`, so the byte representation is more true to the
memory layout.
However, Rust strings are by construction valid UTF-8, and not all byte sequences satisfy this.
Given that this invariant is rooted in Rust by the type safety of `char` and `str`, Verus
views strings as `Seq<char>`, and this module follows that paradigm. Generally, any added
specification for string operations should be based on the `char` level.

Conversion between the byte- and char-views is done via `vstd::utf8` methods, particularly
`encode_utf8()` (`Seq<char>` to `Seq<u8>`) and `decode_utf8()` (`Seq<u8>` to `Seq<char>`).
However, directly using these as `open` specs can slow verification; hence they are wrapped
in `as_bytes()` and `as_str()` with `#[verifier::opaque]`. Use lemmas provided by Verge for
lightweight common-case reasoning, or `reveal` and use `vstd::utf8` if needed.

### `Deref` Methods
In native Rust, `String` inherits all `&self` methods from `str` because it implements `Deref<Target=str>`.
However, `Deref` coercion is not automatically done in Verus, so an explicit `as_str()` is needed
to call these methods (e.g., `s.as_str().is_char_boundary()`).

Note that some methods exists natively for both types, such as `str::len()` and `String::len()`;
in this case they are covered by `assume_specification`.

### Mid-String Mutation
Because of the UTF-8 nature of Rust strings, mid-string mutation (e.g., updating a character in the middle of
a string) is already awkward. In Verge, such APIs are generally not exposed on purpose.
This essentially forces strings to be grow-only containers, which is the typical use case anyway.


## Traits


### `StrView`

This trait allows viewing a type as a string (sequence of `char`s).

```rust
pub trait StrView
```


#### `as_str`

Casts `self` as a `char` sequence.

```rust
spec fn as_str(self) -> Seq<char>
    recommends self.is_utf8(),
        ;
```


#### `is_utf8`

Predicate for asserting `self` can be viewed as a valid UTF-8 string.

```rust
spec fn is_utf8(self) -> bool;
```


#### `is_ascii`

Predicate for asserting `self` can be viewed as a valid ASCII string.

```rust
spec fn is_ascii(self) -> bool;
```


### `BytesView`

This trait allows viewing a type as a byte sequence.

```rust
pub trait BytesView
```


#### `as_bytes`

Casts `self` as a `u8` sequence.

```rust
spec fn as_bytes(self) -> Seq<u8>;
```


#### `is_ascii`

Predicate for asserting `self` can be viewed as a valid sequence of ASCII bytes.

```rust
spec fn is_ascii(self) -> bool;
```


## Functions


### `lemma_subrange_self`

```rust
pub broadcast proof fn lemma_subrange_self<T>(s: Seq<T>)
    ensures (#[trigger] s.subrange(0, s.len() as int)) =~= s {}
```
