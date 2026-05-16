# `verge::str::parse`

Specifications and lemmas for parsing values from a string.

To avoid name conflicts with existing `vstd` functionality, the `FromStr` trait is
not directly specified.


## Structs


### `ExParseBoolError`

```rust
pub struct ExParseBoolError(ParseBoolError);
```


### `ExParseIntError`

```rust
pub struct ExParseIntError(ParseIntError);
```


### `ExIntErrorKind`

```rust
pub struct ExIntErrorKind(IntErrorKind);
```


## Functions


### `spec_from_str`

This function defines the result of parsing a `T` from the string `s`, with the potential
error type `E`.
It is left uninterpreted by default; implementations can add further specifications
as is appropriate, by introducing axioms with `define_spec_from_str!`.

```rust
pub uninterp spec fn spec_from_str<T, E>(s: Seq<char>) -> Result<T, E>;
```


### `bool::from_str`

Enable `bool::from_str`.

```rust
pub assume_specification [ bool::from_str ] (s: &str) -> (ret: Result<bool, ParseBoolError>)
    returns
        spec_from_str::<bool, ParseBoolError>(s@),
    no_unwind
        ;
```


### `spec_int_error_kind`

```rust
pub uninterp spec fn spec_int_error_kind(e: &ParseIntError) -> &IntErrorKind;
```


### `ParseIntError::kind`

```rust
pub assume_specification[ParseIntError::kind](e: &ParseIntError) -> (kind: &IntErrorKind)
    ensures
        spec_int_error_kind(e) == kind,
        ;
```


### `spec_int_from_str`

This function encodes parsing an (arbitrarily large) decimal `int` from a string.

```rust
pub open spec fn spec_int_from_str(s: Seq<char>) -> int
    recommends
        str_is_valid_int(s),
        {
        if s.first() == '+' {
        spec_int_from_str_rec(s.drop_first(), 0)
        } else if s.first() == '-' {
        -spec_int_from_str_rec(s.drop_first(), 0)
        } else {
        spec_int_from_str_rec(s, 0)
        }
        }
```


### `spec_int_from_str_rec`

```rust
pub open spec fn spec_int_from_str_rec(s: Seq<char>, n: int) -> int
    recommends
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].is_ascii_digit(),
    decreases
        s.len(),
        {
        if s.len() == 0 {
        n
        } else {
        spec_int_from_str_rec(s.drop_first(), 10 * n + (s.first() as u8 - 0x30u8))
        }
        }
```


### `str_is_valid_int`

This function encodes whether a string can be parsed as a decimal `int`.

```rust
pub open spec fn str_is_valid_int(s: Seq<char>) -> bool {
    &&& s.len() > 0
    &&& forall|i: int| 1 <= i < s.len()
    ==> #[trigger] s[i].is_ascii_digit()
    &&& s.first().is_ascii_digit()
    || ((s.first() == '+' || s.first() == '-') && s.len() > 1)
    }
```


### `spec_int_from_str_hex`

This function encodes parsing an (arbitrarily large) hexadecimal `int` from a string.

```rust
pub open spec fn spec_int_from_str_hex(s: Seq<char>) -> int
    recommends
        str_is_valid_int_hex(s),
        {
        if s.first() == '+' {
        spec_int_from_str_hex_rec(s.drop_first(), 0)
        } else if s.first() == '-' {
        -spec_int_from_str_hex_rec(s.drop_first(), 0)
        } else {
        spec_int_from_str_hex_rec(s, 0)
        }
        }
```


### `spec_int_from_str_hex_rec`

```rust
pub open spec fn spec_int_from_str_hex_rec(s: Seq<char>, n: int) -> int
    recommends
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i].is_ascii_hexdigit(),
    decreases
        s.len(),
        {
        if s.len() == 0 {
        n
        } else if s.first().is_ascii_digit() {
        spec_int_from_str_rec(s.drop_first(), 16 * n + (s.first() as u8 - 0x30u8))
        } else if s.first().is_ascii_lowercase() {
        spec_int_from_str_rec(s.drop_first(), 16 * n + (s.first() as u8 - 0x61u8 + 10u8))
        } else {
        spec_int_from_str_rec(s.drop_first(), 16 * n + (s.first() as u8 - 0x41u8 + 10u8))
        }
        }
```


### `str_is_valid_int_hex`

This function encodes whether a string can be parsed as a hexadecimal `int`.

```rust
pub open spec fn str_is_valid_int_hex(s: Seq<char>) -> bool {
    &&& s.len() > 0
    &&& forall|i: int| 1 <= i < s.len()
    ==> #[trigger] s[i].is_ascii_hexdigit()
    &&& s.first().is_ascii_hexdigit()
    || ((s.first() == '+' || s.first() == '-') && s.len() > 1)
    }
```


### `spec_signed_int_from_str`

Common specification for `iN::from_str()`.

```rust
pub open spec fn spec_signed_int_from_str<T: Ord + Integer + Debug>(
    s: Seq<char>, res: Result<T, ParseIntError>, min: T, max: T,
    ) -> bool {
    &&& res.is_ok() && spec_unwrap(res) as int == spec_int_from_str(s)
    <==> str_is_valid_int(s) && (min as int) <= spec_int_from_str(s) <= (max as int)
    &&& res.is_err() ==> spec_unwrap_err(res).is_str_parse_error()
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::Empty
    <==> s.len() == 0
    // caveat: i8::from_str("128n") might be `Err(PosOverflow)`
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::InvalidDigit
    ==> s.len() > 0 && !str_is_valid_int(s)
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::PosOverflow
    <== str_is_valid_int(s) && spec_int_from_str(s) > (max as int)
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::NegOverflow
    <== str_is_valid_int(s) && spec_int_from_str(s) < (min as int)
    &&& res.is_err() ==> spec_unwrap_err(res).kind() != &IntErrorKind::Zero
    }

    /// Common specification for `iN::from_str_radix(_, 16)`.
    pub open spec fn spec_signed_int_from_str_hex<T: Ord + Integer + Debug>(
    s: Seq<char>, res: Result<T, ParseIntError>, min: T, max: T,
    ) -> bool {
    &&& res.is_ok() && spec_unwrap(res) as int == spec_int_from_str_hex(s)
    <==> str_is_valid_int_hex(s) && (min as int) <= spec_int_from_str_hex(s) <= (max as int)
    &&& res.is_err() ==> spec_unwrap_err(res).is_str_parse_error()
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::Empty
    <==> s.len() == 0
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::InvalidDigit
    ==> s.len() > 0 && !str_is_valid_int_hex(s)
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::PosOverflow
    <== str_is_valid_int_hex(s) && spec_int_from_str_hex(s) > (max as int)
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::NegOverflow
    <== str_is_valid_int_hex(s) && spec_int_from_str_hex(s) < (min as int)
    &&& res.is_err() ==> spec_unwrap_err(res).kind() != &IntErrorKind::Zero
    }

    /// Common specification for `uN::from_str()`.
    pub open spec fn spec_unsigned_int_from_str<T: Ord + Integer + Debug>(
    s: Seq<char>, res: Result<T, ParseIntError>, max: T,
    ) -> bool {
    &&& res.is_ok() && spec_unwrap(res) as int == spec_int_from_str(s)
    <==> str_is_valid_int(s) && s.first() != '-' && 0int <= spec_int_from_str(s) <= (max as int)
    &&& res.is_err() ==> spec_unwrap_err(res).is_str_parse_error()
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::Empty
    <==> s.len() == 0
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::InvalidDigit
    ==> s.len() > 0 && (!str_is_valid_int(s) || s.first() == '-')
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::PosOverflow
    <== str_is_valid_int(s) && s.first() != '-' && spec_int_from_str(s) > (max as int)
    &&& res.is_err() ==> spec_unwrap_err(res).kind() != &IntErrorKind::NegOverflow
    &&& res.is_err() ==> spec_unwrap_err(res).kind() != &IntErrorKind::Zero
    }

    /// Common specification for `uN::from_str_radix(_, 16)`.
    pub open spec fn spec_unsigned_int_from_str_hex<T: Ord + Integer + Debug>(
    s: Seq<char>, res: Result<T, ParseIntError>, max: T,
    ) -> bool {
    &&& res.is_ok() && spec_unwrap(res) as int == spec_int_from_str_hex(s)
    <==> str_is_valid_int_hex(s) && s.first() != '-' && 0int <= spec_int_from_str_hex(s) <= (max as int)
    &&& res.is_err() ==> spec_unwrap_err(res).is_str_parse_error()
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::Empty
    <==> s.len() == 0
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::InvalidDigit
    ==> s.len() > 0 && (!str_is_valid_int_hex(s) || s.first() == '-')
    &&& res.is_err() && spec_unwrap_err(res).kind() == &IntErrorKind::PosOverflow
    <== str_is_valid_int_hex(s) && s.first() != '-' && spec_int_from_str_hex(s) > (max as int)
    &&& res.is_err() ==> spec_unwrap_err(res).kind() != &IntErrorKind::NegOverflow
    &&& res.is_err() ==> spec_unwrap_err(res).kind() != &IntErrorKind::Zero
    }

    /// Enable `i8::from_str`.
    pub assume_specification [ i8::from_str ] (s: &str) -> (ret: Result<i8, ParseIntError>)
    returns
        spec_from_str::<i8, ParseIntError>(s@),
    no_unwind
        ;
```


### `i8::from_str_radix`

Enable `i8::from_str_radix` (hex-only).

```rust
pub assume_specification [ i8::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<i8, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_signed_int_from_str_hex::<i8>(s@, ret, i8::MIN, i8::MAX),
    no_unwind
        ;
```


### `i16::from_str`

Enable `i16::from_str`.

```rust
pub assume_specification [ i16::from_str ] (s: &str) -> (ret: Result<i16, ParseIntError>)
    returns
        spec_from_str::<i16, ParseIntError>(s@),
    no_unwind
        ;
```


### `i16::from_str_radix`

Enable `i16::from_str_radix` (hex-only).

```rust
pub assume_specification [ i16::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<i16, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_signed_int_from_str_hex::<i16>(s@, ret, i16::MIN, i16::MAX),
    no_unwind
        ;
```


### `i32::from_str`

Enable `i32::from_str`.

```rust
pub assume_specification [ i32::from_str ] (s: &str) -> (ret: Result<i32, ParseIntError>)
    returns
        spec_from_str::<i32, ParseIntError>(s@),
    no_unwind
        ;
```


### `i32::from_str_radix`

Enable `i32::from_str_radix` (hex-only).

```rust
pub assume_specification [ i32::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<i32, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_signed_int_from_str_hex::<i32>(s@, ret, i32::MIN, i32::MAX),
    no_unwind
        ;
```


### `i64::from_str`

Enable `i64::from_str`.

```rust
pub assume_specification [ i64::from_str ] (s: &str) -> (ret: Result<i64, ParseIntError>)
    returns
        spec_from_str::<i64, ParseIntError>(s@),
    no_unwind
        ;
```


### `i64::from_str_radix`

Enable `i64::from_str_radix` (hex-only).

```rust
pub assume_specification [ i64::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<i64, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_signed_int_from_str_hex::<i64>(s@, ret, i64::MIN, i64::MAX),
    no_unwind
        ;
```


### `i128::from_str`

Enable `i128::from_str`.

```rust
pub assume_specification [ i128::from_str ] (s: &str) -> (ret: Result<i128, ParseIntError>)
    returns
        spec_from_str::<i128, ParseIntError>(s@),
    no_unwind
        ;
```


### `i128::from_str_radix`

Enable `i128::from_str_radix` (hex-only).

```rust
pub assume_specification [ i128::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<i128, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_signed_int_from_str_hex::<i128>(s@, ret, i128::MIN, i128::MAX),
    no_unwind
        ;
```


### `isize::from_str`

Enable `isize::from_str`.

```rust
pub assume_specification [ isize::from_str ] (s: &str) -> (ret: Result<isize, ParseIntError>)
    returns
        spec_from_str::<isize, ParseIntError>(s@),
    no_unwind
        ;
```


### `isize::from_str_radix`

Enable `isize::from_str_radix` (hex-only).

```rust
pub assume_specification [ isize::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<isize, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_signed_int_from_str_hex::<isize>(s@, ret, isize::MIN, isize::MAX),
    no_unwind
        ;
```


### `u8::from_str`

Enable `u8::from_str`.

```rust
pub assume_specification [ u8::from_str ] (s: &str) -> (ret: Result<u8, ParseIntError>)
    returns
        spec_from_str::<u8, ParseIntError>(s@),
    no_unwind
        ;
```


### `u8::from_str_radix`

Enable `u8::from_str_radix` (hex-only).

```rust
pub assume_specification [ u8::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<u8, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_unsigned_int_from_str_hex::<u8>(s@, ret, u8::MAX),
    no_unwind
        ;
```


### `u16::from_str`

Enable `u16::from_str`.

```rust
pub assume_specification [ u16::from_str ] (s: &str) -> (ret: Result<u16, ParseIntError>)
    returns
        spec_from_str::<u16, ParseIntError>(s@),
    no_unwind
        ;
```


### `u16::from_str_radix`

Enable `u16::from_str_radix` (hex-only).

```rust
pub assume_specification [ u16::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<u16, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_unsigned_int_from_str_hex::<u16>(s@, ret, u16::MAX),
    no_unwind
        ;
```


### `u32::from_str`

Enable `u32::from_str`.

```rust
pub assume_specification [ u32::from_str ] (s: &str) -> (ret: Result<u32, ParseIntError>)
    returns
        spec_from_str::<u32, ParseIntError>(s@),
    no_unwind
        ;
```


### `u32::from_str_radix`

Enable `u32::from_str_radix` (hex-only).

```rust
pub assume_specification [ u32::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<u32, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_unsigned_int_from_str_hex::<u32>(s@, ret, u32::MAX),
    no_unwind
        ;
```


### `u64::from_str`

Enable `u64::from_str`.

```rust
pub assume_specification [ u64::from_str ] (s: &str) -> (ret: Result<u64, ParseIntError>)
    returns
        spec_from_str::<u64, ParseIntError>(s@),
    no_unwind
        ;
```


### `u64::from_str_radix`

Enable `u64::from_str_radix` (hex-only).

```rust
pub assume_specification [ u64::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<u64, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_unsigned_int_from_str_hex::<u64>(s@, ret, u64::MAX),
    no_unwind
        ;
```


### `u128::from_str`

Enable `u128::from_str`.

```rust
pub assume_specification [ u128::from_str ] (s: &str) -> (ret: Result<u128, ParseIntError>)
    returns
        spec_from_str::<u128, ParseIntError>(s@),
    no_unwind
        ;
```


### `u128::from_str_radix`

Enable `u128::from_str_radix` (hex-only).

```rust
pub assume_specification [ u128::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<u128, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_unsigned_int_from_str_hex::<u128>(s@, ret, u128::MAX),
    no_unwind
        ;
```


### `usize::from_str`

Enable `usize::from_str`.

```rust
pub assume_specification [ usize::from_str ] (s: &str) -> (ret: Result<usize, ParseIntError>)
    returns
        spec_from_str::<usize, ParseIntError>(s@),
    no_unwind
        ;
```


### `usize::from_str_radix`

Enable `usize::from_str_radix` (hex-only).

```rust
pub assume_specification [ usize::from_str_radix ] (s: &str, radix: u32) -> (ret: Result<usize, ParseIntError>)
    requires
        radix == 16,
    ensures
        spec_unsigned_int_from_str_hex::<usize>(s@, ret, usize::MAX),
    no_unwind
        ;
```
