# `verge::env`

Specifications for `std::env`, the program's environment.


## Structs


### `ExArgs`

Enables `std::env::Args` (iterator struct).

```rust
pub struct ExArgs(Args);
```


### `ExVars`

Enables `std::env::Vars` (iterator struct).

```rust
pub struct ExVars(Vars);
```


### `Env`

Specification for `env::Args` and `env::Vars`.

```rust
pub struct Env;
```


## Functions


### `impl_iterator_default!(std)`

Enables `Args` as an iterator.

```rust
impl_iterator_default!(
    Args [] where Item = String
    [ std::env::args ] () -> |seq| {
    Env::args() =~~= seq.map(|i: int, arg: String| arg@)
    }
    );
```


### `impl_iterator_default!(std)`

Enables `Vars` as an iterator.

```rust
impl_iterator_default!(
    Vars [] where Item = (String, String)
    [ std::env::vars ] () -> |seq| {
    Env::vars().kv_pairs().to_seq() =~~= seq.map(|i: int, var: (String, String)| (var.0@, var.1@))
    }
    );
```


### `var`

Enables `std::env::var`.

```rust
pub fn var(key: &str) -> (ret: Option<String>)
    ensures
        ret.deep_view() == Env::vars().get(key@),
```


## Implementations


### `impl Env`

```rust
impl Env
```


#### `args`

This function encodes program arguments as a sequence of strings.

```rust
pub uninterp spec fn args() -> Seq<Seq<char>>;
```


#### `vars`

This function encodes environment variables as a map from strings to strings.

```rust
pub uninterp spec fn vars() -> Map<Seq<char>, Seq<char>>;
```
