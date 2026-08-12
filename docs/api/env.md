# `verge::env`

Specifications for `std::env`, the program's environment.


## Structs


### `Env`

Specification for `env::Args` and `env::Vars`.

```rust
pub struct Env;
```


## Functions


### `impl_iterator!`

Specifies the iterator `VergeArgs` which wraps `Args`,
contructed via `args_iter()`.

```rust
impl_iterator!(
    Args<> as VergeArgs<> :: Item = String
    ;

    args_iter via args
    () -> (iter: VergeArgs)
    ensures {
            Env::args() =~~= iter.seq().map(|i: int, arg: String| arg@)
        }
        ;
        );
```


### `impl_double_ended_iterator!`

Specifies the iterator `VergeArgs` as a double-ended iterator.

```rust
impl_double_ended_iterator!(
    Args as VergeArgs [] :: Item = String
    );
```


### `impl_iterator!`

Specifies the iterator `VergeVars` which wraps `Vars`,
contructed via `vars_iter()`.

```rust
impl_iterator!(
    Vars<> as VergeVars<> :: Item = (String, String)
    ;

    vars_iter via vars
    () -> (iter: VergeVars)
    ensures {
            Env::vars().kv_pairs().to_seq() =~~= iter.seq().map(|i: int, var: (String, String)| (var.0@, var.1@))
        }
        ;
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
