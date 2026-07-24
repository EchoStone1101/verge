# `verge::func`

Specifications and lemmas for functions.

## Macros
The `assume_surjective` and `assume_injective_by` proc-macros derive admitted
proof lemmas from an existing `proof fn` or `exec fn` contract. They are gated
by the `func_assume_lemmas` feature because the generated lemmas are trusted.
The `assert_surjective` and `assert_injective_by` variants instead generate
private sanity-check lemmas that call a separately written proof function.
Dedicated submodules under `func` hold proof functions for other Verge modules'
function-contract sanity checks.


## Functions


### `is_deterministic`

This function encodes whether an `exec`-mode function `f` is deterministic.

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

This function encodes whether an `exec`-mode function `f` is total.

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

Used for a dummy one-term trigger.

```rust
pub uninterp spec fn dummy<A>(a: A) -> ();
```


### `dummy2`

Used for a dummy two-term trigger.

```rust
pub uninterp spec fn dummy2<A, B>(a: A, b: B) -> ();
```
