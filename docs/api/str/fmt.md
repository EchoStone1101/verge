# `verge::str::fmt`

Specifications and lemmas for formatting types into strings.

Currently, Verge provides support for a selection of primitive `Display` types by further specifying
their `to_string()` method. The `format!` macro and formatters remain external.
The `Debug` trait is also exposed, but the specification is left deliberately uninterpreted
because of its volatile nature.


## Functions


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

```rust
pub open spec fn spec_int_to_str_rec(n: nat) -> Seq<char>
    decreases n,
        {
        if n == 0 {
        seq![]
        } else {
        use vstd::arithmetic::div_mod::lemma_div_decreases;
        proof { lemma_div_decreases(n as int, 10) } // proof for `decreases`
        seq![(n % 10 + 0x30) as char] + spec_int_to_str_rec(n / 10)
        }
        }
```


### `lemma_ref_to_string`

Specifies `<&T as ToString>::to_string`, where `T: Display + ?Sized`.

```rust
pub axiom fn lemma_ref_to_string<T: Display + ?Sized>(t: &&T, s: String)
    ensures
        to_string_from_display_ensures::<&T>(t, s) == to_string_from_display_ensures::<T>(*t, s)
        ;
```


### `lemma_box_to_string`

Specifies `<Box<T> as ToString>::to_string`, where `T: Display + ?Sized`.

```rust
pub axiom fn lemma_box_to_string<T: Display + ?Sized>(t: &Box<T>, s: String)
    ensures
        to_string_from_display_ensures::<Box<T>>(t, s) == to_string_from_display_ensures::<T>(&*t, s)
        ;
```


### `lemma_rc_to_string`

Specifies `<Rc<T> as ToString>::to_string`, where `T: Display + ?Sized`.

```rust
pub axiom fn lemma_rc_to_string<T: Display + ?Sized>(t: &Rc<T>, s: String)
    ensures
        to_string_from_display_ensures::<Rc<T>>(t, s) == to_string_from_display_ensures::<T>(&*t, s)
        ;
```


### `debug_format`

Enables printing the value `t` as `Debug`.

```rust
pub fn debug_format<T: Debug + ?Sized>(t: &T) -> (s: String)
    ensures
        debug_format_ensures::<T>(t, s),
```


### `debug_format_ensures`

This function defines the result of printing `T` as `Debug`. It is always uninterpreted.

```rust
pub uninterp spec fn debug_format_ensures<T: Debug + ?Sized>(
    t: &T,
    s: String,
    ) -> bool;
```
