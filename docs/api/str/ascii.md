# `verge::str::ascii`

ASCII-related string specifications.


## Functions


### `u8_to_ascii_lowercase`

Enables `u8::to_ascii_lowercase`.

```rust
pub open spec fn u8_to_ascii_lowercase(this: &u8) -> u8
    { if this.is_ascii_uppercase() { (*this + 0x20) as u8 } else { *this } }
```


### `u8::to_ascii_lowercase`

```rust
pub assume_specification [ u8::to_ascii_lowercase ](this: &u8) -> (ret: u8)
    returns
        if this.is_ascii_uppercase() { (*this + 0x20) as u8 } else { *this }
    no_unwind
        ;
```


### `char_to_ascii_lowercase`

Enables `char::to_ascii_lowercase`.

```rust
pub open spec fn char_to_ascii_lowercase(this: &char) -> char
    { if this.is_ascii_uppercase() { (*this as u8 + 0x20) as char } else { *this } }
```


### `char::to_ascii_lowercase`

```rust
pub assume_specification [ char::to_ascii_lowercase ](this: &char) -> (ret: char)
    returns
        if this.is_ascii_uppercase() { (*this as u8 + 0x20) as char } else { *this }
    no_unwind
        ;
```


### `u8_to_ascii_uppercase`

Enables `u8::to_ascii_uppercase`.

```rust
pub open spec fn u8_to_ascii_uppercase(this: &u8) -> u8
    { if this.is_ascii_lowercase() { (*this - 0x20) as u8 } else { *this } }
```


### `u8::to_ascii_uppercase`

```rust
pub assume_specification [ u8::to_ascii_uppercase ](this: &u8) -> (ret: u8)
    returns
        if this.is_ascii_lowercase() { (*this - 0x20) as u8 } else { *this }
    no_unwind
        ;
```


### `char_to_ascii_uppercase`

Enables `char::to_ascii_uppercase`.

```rust
pub open spec fn char_to_ascii_uppercase(this: &char) -> char
    { if this.is_ascii_lowercase() { (*this as u8 - 0x20) as char } else { *this } }
```


### `char::to_ascii_uppercase`

```rust
pub assume_specification [ char::to_ascii_uppercase ](this: &char) -> (ret: char)
    returns
        if this.is_ascii_lowercase() { (*this as u8 - 0x20) as char } else { *this }
    no_unwind
        ;
```
