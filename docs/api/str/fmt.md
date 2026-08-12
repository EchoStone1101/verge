# `verge::str::fmt`

Specifications and lemmas for formatting types into strings.

## `Display` and `Debug` support
Currently, Verge provides support for a selection of primitive `Display` types by further specifying
their `to_string()` method. However, the `format!` macro and formatters remain external.
To implement formatting for types beyond the primitive ones, implement `ToString` manually.
The `Debug` trait is also exposed, but the specification is left deliberately uninterpreted
because of its volatile nature. The same is true for other `Display` types that aren't included
below.

That is, Verge allows for:
- using `#[derive(Debug)]` to introduce new `Debug` types
- formatting `Debug` types (via the `debug_format()` function in Verge), where the result
  is left uninterpreted
- implementing `ToString` for custom types
- formatting `Display` types (by calling `to_string()`), where the result
  is fully interpreted for a selection of types (via `to_string_from_display_ensures()`);
  `Display` types not in that list can still be formatted, but the result
  (`to_string_from_display_ensures`) is left uninterpreted


## Traits


### `ExToString`

Specification extension for `ToString` implementations.

Implement `ToStringSpecImpl` for custom `ToString` types to define the
postcondition of `to_string()`. This complements vstd's blanket
`Display`-based spec and supports manual `ToString` impls that do not go
through `Display`.

```rust
pub trait ExToString
```


#### `to_string_ensures`

```rust
spec fn to_string_ensures(&self, s: String) -> bool;
```


#### `to_string`

```rust
fn to_string(&self) -> (s: String)
    ensures
        self.to_string_ensures(s),
        ;
```


### `AsInt`

Helper trait for integer types that can be casted into `int` via `as`.

```rust
pub trait AsInt: vstd::prelude::Integer + std::fmt::Display
```


#### `as_int`

```rust
spec fn as_int(&self) -> int;
```


## Functions


### `lemma_bool_to_string`

This lemma fully interprets `<bool as ToString>::to_string`.

```rust
pub broadcast axiom fn lemma_bool_to_string(b: &bool, s: String)
    ensures
        #[trigger] to_string_from_display_ensures(b, s) == {
            &&& *b <==> s@ == seq!['t', 'r', 'u', 'e']
            &&& !*b <==> s@ == seq!['f', 'a', 'l', 's', 'e']
        },
        ;
```


### `lemma_char_to_string`

This lemma fully interprets `<char as ToString>::to_string`.

```rust
pub broadcast axiom fn lemma_char_to_string(c: &char, s: String)
    ensures
        #[trigger] to_string_from_display_ensures(c, s) == {
            s@ == seq![*c]
        },
        ;
```


### `lemma_int_to_string`

This lemma fully interprets `<iN|uN as ToString>::to_string`.

```rust
pub broadcast axiom fn lemma_int_to_string<I: AsInt>(n: &I, s: String)
    ensures
        #[trigger] to_string_from_display_ensures(n, s) == {
            s@ == spec_int_to_str(n.as_int())
        },
        ;
```


### `lemma_string_to_string`

This lemma fully interprets `<String as ToString>::to_string`.

```rust
pub broadcast axiom fn lemma_string_to_string(this: &String, s: String)
    ensures
        #[trigger] to_string_from_display_ensures(this, s) == {
            this@ == s@
        },
        ;
```


### `lemma_ref_to_string`

This lemma fully interprets `<&T as ToString>::to_string`, where `T: Display + ?Sized`
(blanket impl from `std`).

```rust
pub broadcast axiom fn lemma_ref_to_string<T: Display + ?Sized>(t: &&T, s: String)
    ensures
        #[trigger] to_string_from_display_ensures::<&T>(t, s) == to_string_from_display_ensures::<T>(&**t, s)
        ;
```


### `lemma_mut_ref_to_string`

This lemma fully interprets `<&mut T as ToString>::to_string`, where `T: Display + ?Sized`
(blanket impl from `std`).

```rust
pub broadcast axiom fn lemma_mut_ref_to_string<T: Display + ?Sized>(t: &&mut T, s: String)
    ensures
        &*final(*t) == &*old(*t),
        #[trigger] to_string_from_display_ensures::<&mut T>(t, s) == to_string_from_display_ensures::<T>(&*final(*t), s)
        ;
```


### `lemma_box_to_string`

This lemma fully interprets `<Box<T> as ToString>::to_string`, where `T: Display + ?Sized`
(blanket impl from `std`).

```rust
pub broadcast axiom fn lemma_box_to_string<T: Display + ?Sized>(t: &Box<T>, s: String)
    ensures
        #[trigger] to_string_from_display_ensures::<Box<T>>(t, s) == to_string_from_display_ensures::<T>(&*t, s)
        ;
```


### `lemma_rc_to_string`

This lemma fully interprets `<Rc<T> as ToString>::to_string`, where `T: Display + ?Sized`
(blanket impl from `std`).

```rust
pub broadcast axiom fn lemma_rc_to_string<T: Display + ?Sized>(t: &Rc<T>, s: String)
    ensures
        #[trigger] to_string_from_display_ensures::<Rc<T>>(t, s) == to_string_from_display_ensures::<T>(&*t, s)
        ;
```


### `spec_int_to_str`

This function encodes displaying an (arbitrarily large) decimal `int` into a string.

```rust
pub open spec fn spec_int_to_str(n: int) -> Seq<char> {
    if n == 0 {
    seq!['0']
    } else if n > 0 {
    spec_int_to_str_rec(n as nat)
    } else {
    seq!['-'] + spec_int_to_str_rec((-n) as nat)
    }
    }
```


### `spec_int_to_str_rec`

Recursive expansion for `spec_int_to_str`.

```rust
pub open spec fn spec_int_to_str_rec(n: nat) -> Seq<char>
    decreases n,
        {
        if n == 0 {
        seq![]
        } else {
        use vstd::arithmetic::div_mod::lemma_div_decreases;
        proof { lemma_div_decreases(n as int, 10) } // proof for `decreases`
        spec_int_to_str_rec(n / 10).push((n % 10 + CHAR_ZERO) as char)
        }
        }
```


### `debug_format`

Enables formatting the value `t` as `Debug`.

```rust
pub fn debug_format<T: Debug + ?Sized>(t: &T) -> (s: String)
    ensures
        debug_format_ensures::<T>(t, s),
```


### `debug_format_ensures`

This function represents the result of formatting `T` as `Debug`.

However, the exact formatting is undefined, and this function always uninterpreted.

```rust
pub uninterp spec fn debug_format_ensures<T: Debug + ?Sized>(
    t: &T,
    s: String,
    ) -> bool;
```
