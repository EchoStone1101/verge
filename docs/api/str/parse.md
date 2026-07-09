# `verge::str::parse`

Specifications and lemmas for parsing values from a string.

This module specifies `std::str::FromStr` directly via `FromStrSpec`.
Implement `FromStrSpecImpl` for custom `FromStr` types to define the
validity predicate and value/error postconditions of `from_str()`.


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


## Traits


### `ExFromStr`

Specification extension for `FromStr` implementations.

`from_str_recommends(s)` is the complete validity predicate for parsing
`s`; successful parses imply it, and failed parses imply its negation.
`from_str_ok_ensures` should fully characterize the parsed value. Error
postconditions may be intentionally looser, because parse error kinds often
expose only partial information about the failed input.

```rust
pub trait ExFromStr: Sized
```


#### `Err`

```rust
type Err;
```


#### `from_str_recommends`

```rust
spec fn from_str_recommends(s: Seq<char>) -> bool;
```


#### `from_str_ok_ensures`

```rust
spec fn from_str_ok_ensures(s: Seq<char>, value: Self) -> bool
    recommends
        Self::from_str_recommends(s),
        ;
```


#### `from_str_err_ensures`

```rust
spec fn from_str_err_ensures(s: Seq<char>, err: Self::Err) -> bool
    recommends
        !Self::from_str_recommends(s),
        ;
```


#### `from_str`

```rust
fn from_str(s: &str) -> (res: Result<Self, Self::Err>)
    ensures
        res.is_ok() ==> Self::from_str_recommends(s@) && Self::from_str_ok_ensures(s@, res->Ok_0),
        res.is_err() ==> !Self::from_str_recommends(s@) && Self::from_str_err_ensures(s@, res->Err_0),
        ;
```


## Functions


### `<bool as FromStr>::from_str`

Enable `<bool as FromStr>::from_str`.

```rust
pub assume_specification [ <bool as FromStr>::from_str ] (s: &str) -> (res: Result<bool, ParseBoolError>)
    ensures
        res.is_ok() ==> (s@ == seq!['t', 'r', 'u', 'e'] || s@ == seq!['f', 'a', 'l', 's', 'e'])
            && (res->Ok_0 <==> s@ == seq!['t', 'r', 'u', 'e']),
        res.is_err() ==> !(s@ == seq!['t', 'r', 'u', 'e'] || s@ == seq!['f', 'a', 'l', 's', 'e'])
            && res->Err_0.is_str_parse_error(),
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


### `spec_char_digit_value`

Encodes the numeric value of an ASCII radix digit.

Non-digits map to `-1`; use `char_is_digit_radix` when checking validity.

```rust
pub open spec fn spec_char_digit_value(c: char) -> int {
    if (CHAR_ZERO as int) <= (c as u32) < (CHAR_NINE as int) + 1 {
    (c as u32) as int - (CHAR_ZERO as int)
    } else if (CHAR_LOWER_A as int) <= (c as u32) < (CHAR_LOWER_Z as int) + 1 {
    (c as u32) as int - (CHAR_LOWER_A as int) + 10
    } else if (CHAR_UPPER_A as int) <= (c as u32) < (CHAR_UPPER_Z as int) + 1 {
    (c as u32) as int - (CHAR_UPPER_A as int) + 10
    } else {
    -1
    }
    }
```


### `char_is_digit_radix`

Encodes whether `c` is an ASCII digit in the supplied radix.

```rust
pub open spec fn char_is_digit_radix(c: char, radix: int) -> bool
    recommends
        2 <= radix,
        {
        0 <= spec_char_digit_value(c) < radix
        }
```


### `spec_int_from_str_radix_rec`

This function encodes parsing an unsigned digit sequence as an arbitrarily
large `int` in the supplied radix.

```rust
pub open spec fn spec_int_from_str_radix_rec(s: Seq<char>, n: int, radix: int) -> int
    recommends
        2 <= radix,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] char_is_digit_radix(s[i], radix),
    decreases
        s.len(),
        {
        if s.len() == 0 {
        n
        } else {
        spec_int_from_str_radix_rec(
            s.drop_first(),
            radix * n + spec_char_digit_value(s.first()),
            radix,
        )
        }
        }
```


### `spec_int_from_str_radix`

This function encodes parsing an arbitrarily large `int` from a string in
the supplied radix. A leading `+` or `-` sign is handled separately from the
digit sequence.

```rust
pub open spec fn spec_int_from_str_radix(s: Seq<char>, radix: int) -> int
    recommends
        2 <= radix,
        str_is_valid_int_radix(s, radix),
        {
        if s.first() == '+' {
        spec_int_from_str_radix_rec(s.drop_first(), 0, radix)
        } else if s.first() == '-' {
        -spec_int_from_str_radix_rec(s.drop_first(), 0, radix)
        } else {
        spec_int_from_str_radix_rec(s, 0, radix)
        }
        }
```


### `str_is_valid_int_radix`

This function encodes whether a string can be parsed as an arbitrarily large
signed `int` in the supplied radix, ignoring machine-integer bounds.

```rust
pub open spec fn str_is_valid_int_radix(s: Seq<char>, radix: int) -> bool
    recommends
        2 <= radix,
        {
        &&& s.len() > 0
        &&& if s.first() == '+' || s.first() == '-' {
        &&& s.len() > 1
        &&& forall|i: int| 1 <= i < s.len() ==> #[trigger] char_is_digit_radix(s[i], radix)
        } else {
        forall|i: int| 0 <= i < s.len() ==> #[trigger] char_is_digit_radix(s[i], radix)
        }
        }
```


### `spec_int_from_str`

This function encodes parsing an (arbitrarily large) decimal `int` from a string.

```rust
pub open spec fn spec_int_from_str(s: Seq<char>) -> int
    recommends
        str_is_valid_int(s),
        {
        spec_int_from_str_radix(s, 10)
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
        spec_int_from_str_radix_rec(s, n, 10)
        }
```


### `str_is_valid_int`

This function encodes whether a string can be parsed as a decimal `int`.

```rust
pub open spec fn str_is_valid_int(s: Seq<char>) -> bool {
    str_is_valid_int_radix(s, 10)
    }
```


### `spec_int_from_str_hex`

This function encodes parsing an (arbitrarily large) hexadecimal `int` from a string.

```rust
pub open spec fn spec_int_from_str_hex(s: Seq<char>) -> int
    recommends
        str_is_valid_int_hex(s),
        {
        spec_int_from_str_radix(s, 16)
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
        spec_int_from_str_radix_rec(s, n, 16)
        }
```


### `str_is_valid_int_hex`

This function encodes whether a string can be parsed as a hexadecimal `int`.

```rust
pub open spec fn str_is_valid_int_hex(s: Seq<char>) -> bool {
    str_is_valid_int_radix(s, 16)
    }
```


### `spec_signed_int_from_str_radix_recommends`

Validity predicate for signed machine-integer parsing in an arbitrary radix.

```rust
pub open spec fn spec_signed_int_from_str_radix_recommends<T: Ord + Integer + Debug>(
    s: Seq<char>, radix: int, min: T, max: T,
    ) -> bool
    recommends
        2 <= radix <= 36,
        {
        &&& str_is_valid_int_radix(s, radix)
        &&& (min as int) <= spec_int_from_str_radix(s, radix) <= (max as int)
        }
```


### `spec_signed_int_from_str_radix_ok_ensures`

Successful-value postcondition for signed machine-integer parsing in an arbitrary radix.

```rust
pub open spec fn spec_signed_int_from_str_radix_ok_ensures<T: Ord + Integer + Debug>(
    s: Seq<char>, radix: int, value: T, min: T, max: T,
    ) -> bool
    recommends
        spec_signed_int_from_str_radix_recommends(s, radix, min, max),
        {
        value as int == spec_int_from_str_radix(s, radix)
        }
```


### `spec_signed_int_from_str_radix_err_ensures`

Error postcondition for signed machine-integer parsing in an arbitrary radix.

```rust
pub open spec fn spec_signed_int_from_str_radix_err_ensures<T: Ord + Integer + Debug>(
    s: Seq<char>, radix: int, err: ParseIntError, min: T, max: T,
    ) -> bool
    recommends
        2 <= radix <= 36,
        !spec_signed_int_from_str_radix_recommends(s, radix, min, max),
        {
        &&& err.is_str_parse_error()
        &&& (err.kind() == &IntErrorKind::Empty <==> s.len() == 0)
        // caveat: i8::from_str("128n") may be `Err(PosOverflow)`.
        &&& (err.kind() == &IntErrorKind::InvalidDigit ==> s.len() > 0 && !str_is_valid_int_radix(s, radix))
        &&& (str_is_valid_int_radix(s, radix) && spec_int_from_str_radix(s, radix) > (max as int)
        ==> err.kind() == &IntErrorKind::PosOverflow)
        &&& (str_is_valid_int_radix(s, radix) && spec_int_from_str_radix(s, radix) < (min as int)
        ==> err.kind() == &IntErrorKind::NegOverflow)
        &&& err.kind() != &IntErrorKind::Zero
        }
```


### `spec_signed_int_from_str_radix`

Common specification for `iN::from_str_radix`.

```rust
pub open spec fn spec_signed_int_from_str_radix<T: Ord + Integer + Debug>(
    s: Seq<char>, radix: int, res: Result<T, ParseIntError>, min: T, max: T,
    ) -> bool
    recommends
        2 <= radix <= 36,
        {
        &&& (res.is_ok() ==> spec_signed_int_from_str_radix_recommends(s, radix, min, max)
        && spec_signed_int_from_str_radix_ok_ensures(s, radix, spec_unwrap(res), min, max))
        &&& (res.is_err() ==> !spec_signed_int_from_str_radix_recommends(s, radix, min, max)
        && spec_signed_int_from_str_radix_err_ensures(s, radix, spec_unwrap_err(res), min, max))
        }
```


### `spec_signed_int_from_str`

Common specification for `iN::from_str()`.

```rust
pub open spec fn spec_signed_int_from_str<T: Ord + Integer + Debug>(
    s: Seq<char>, res: Result<T, ParseIntError>, min: T, max: T,
    ) -> bool {
    spec_signed_int_from_str_radix(s, 10, res, min, max)
    }

    /// Common specification for `iN::from_str_radix(_, 16)`.
    pub open spec fn spec_signed_int_from_str_hex<T: Ord + Integer + Debug>(
    s: Seq<char>, res: Result<T, ParseIntError>, min: T, max: T,
    ) -> bool {
    spec_signed_int_from_str_radix(s, 16, res, min, max)
    }

    /// Validity predicate for unsigned machine-integer parsing in an arbitrary radix.
    pub open spec fn spec_unsigned_int_from_str_radix_recommends<T: Ord + Integer + Debug>(
    s: Seq<char>, radix: int, max: T,
    ) -> bool
    recommends
        2 <= radix <= 36,
        {
        &&& str_is_valid_int_radix(s, radix)
        &&& s.first() != '-'
        &&& 0int <= spec_int_from_str_radix(s, radix) <= (max as int)
        }
```


### `spec_unsigned_int_from_str_radix_ok_ensures`

Successful-value postcondition for unsigned machine-integer parsing in an arbitrary radix.

```rust
pub open spec fn spec_unsigned_int_from_str_radix_ok_ensures<T: Ord + Integer + Debug>(
    s: Seq<char>, radix: int, value: T, max: T,
    ) -> bool
    recommends
        spec_unsigned_int_from_str_radix_recommends(s, radix, max),
        {
        value as int == spec_int_from_str_radix(s, radix)
        }
```


### `spec_unsigned_int_from_str_radix_err_ensures`

Error postcondition for unsigned machine-integer parsing in an arbitrary radix.

```rust
pub open spec fn spec_unsigned_int_from_str_radix_err_ensures<T: Ord + Integer + Debug>(
    s: Seq<char>, radix: int, err: ParseIntError, max: T,
    ) -> bool
    recommends
        2 <= radix <= 36,
        !spec_unsigned_int_from_str_radix_recommends(s, radix, max),
        {
        &&& err.is_str_parse_error()
        &&& (err.kind() == &IntErrorKind::Empty <==> s.len() == 0)
        &&& (err.kind() == &IntErrorKind::InvalidDigit
        ==> s.len() > 0 && (!str_is_valid_int_radix(s, radix) || s.first() == '-'))
        &&& (str_is_valid_int_radix(s, radix) && s.first() != '-' && spec_int_from_str_radix(s, radix) > (max as int)
        ==> err.kind() == &IntErrorKind::PosOverflow)
        &&& err.kind() != &IntErrorKind::NegOverflow
        &&& err.kind() != &IntErrorKind::Zero
        }
```


### `spec_unsigned_int_from_str_radix`

Common specification for `uN::from_str_radix`.

```rust
pub open spec fn spec_unsigned_int_from_str_radix<T: Ord + Integer + Debug>(
    s: Seq<char>, radix: int, res: Result<T, ParseIntError>, max: T,
    ) -> bool
    recommends
        2 <= radix <= 36,
        {
        &&& (res.is_ok() ==> spec_unsigned_int_from_str_radix_recommends(s, radix, max)
        && spec_unsigned_int_from_str_radix_ok_ensures(s, radix, spec_unwrap(res), max))
        &&& (res.is_err() ==> !spec_unsigned_int_from_str_radix_recommends(s, radix, max)
        && spec_unsigned_int_from_str_radix_err_ensures(s, radix, spec_unwrap_err(res), max))
        }
```


### `spec_unsigned_int_from_str`

Common specification for `uN::from_str()`.

```rust
pub open spec fn spec_unsigned_int_from_str<T: Ord + Integer + Debug>(
    s: Seq<char>, res: Result<T, ParseIntError>, max: T,
    ) -> bool {
    spec_unsigned_int_from_str_radix(s, 10, res, max)
    }

    /// Common specification for `uN::from_str_radix(_, 16)`.
    pub open spec fn spec_unsigned_int_from_str_hex<T: Ord + Integer + Debug>(
    s: Seq<char>, res: Result<T, ParseIntError>, max: T,
    ) -> bool {
    spec_unsigned_int_from_str_radix(s, 16, res, max)
    }

    } // verus!

    macro_rules! impl_from_str_spec_signed_int {
    ($($ty:ident),+) => {
    verus! {
    $(
    impl FromStrSpecImpl for $ty {
    open spec fn from_str_recommends(s: Seq<char>) -> bool {
    spec_signed_int_from_str_radix_recommends::<$ty>(s, 10, $ty::MIN, $ty::MAX)
    }

    open spec fn from_str_ok_ensures(s: Seq<char>, value: $ty) -> bool {
    spec_signed_int_from_str_radix_ok_ensures::<$ty>(s, 10, value, $ty::MIN, $ty::MAX)
    }

    open spec fn from_str_err_ensures(s: Seq<char>, err: Self::Err) -> bool {
    spec_signed_int_from_str_radix_err_ensures::<$ty>(s, 10, err, $ty::MIN, $ty::MAX)
    }
    }
    )+
    }
    }
```
