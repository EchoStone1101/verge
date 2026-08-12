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


### `ExParseCharError`

```rust
pub struct ExParseCharError(ParseCharError);
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

Specification for the `FromStr` trait.

Note that in general, the `from_str` method is not always `no_unwind` (for example, when creating `Self` involves
heap allocation). `from_str_no_unwind()` explicitly models this.

```rust
pub trait ExFromStr: Sized
```


#### `Err`

```rust
type Err;
```


#### `from_str_ok_ensures`

```rust
spec fn from_str_ok_ensures(s: Seq<char>, value: Self) -> bool;
```


#### `from_str_err_ensures`

```rust
spec fn from_str_err_ensures(s: Seq<char>, err: Self::Err) -> bool;
```


#### `from_str_no_unwind`

```rust
spec fn from_str_no_unwind() -> bool;
```


#### `from_str`

```rust
fn from_str(s: &str) -> (res: Result<Self, Self::Err>)
    ensures
        res.is_ok() ==> Self::from_str_ok_ensures(s@, res->Ok_0),
        res.is_err() ==>
            Self::from_str_err_ensures(s@, res->Err_0)
            && !exists|v: Self| Self::from_str_ok_ensures(s@, v),
    no_unwind when Self::from_str_no_unwind()
        ;
```


### `FromToStr`

This trait specifies round-tripping between `ToString` and `FromStr` - implementing
this trait for type `T` certifies that `T::from_str(t.to_string())` produces `t` itself.

Note that this definition uses strict `spec`-mode equality. As a result, it is
generally only applicable to simple `Copy` types. For instance, `String` is not `FromToStr`
because the round-trip creates a new `String` which is not `spec`-mode equal to the old `String`.

```rust
pub trait FromToStr: ToString + FromStr
```


#### `lemma_round_tripping`

```rust
proof fn lemma_round_tripping(t: Self)
    ensures
        ({
            forall|s: String| #[trigger] t.to_string_ensures(s)
                ==> Self::from_str_ok_ensures(s@, t)
        }),
        ;
```


## Functions


### `<bool as FromStr>::from_str`

Enable `<bool as FromStr>::from_str`.

```rust
pub assume_specification [ <bool as FromStr>::from_str ] (s: &str) -> Result<bool, ParseBoolError>;
```


### `<char as FromStr>::from_str`

Enable `<char as FromStr>::from_str`.

```rust
pub assume_specification [ <char as FromStr>::from_str ] (s: &str) -> Result<char, <char as FromStr>::Err>;
```


### `spec_int_error_kind`

```rust
pub uninterp spec fn spec_int_error_kind(e: &ParseIntError) -> &IntErrorKind;
```


### `ParseIntError::kind`

Enable `ParseIntError::kind`.

```rust
pub assume_specification[ ParseIntError::kind ](e: &ParseIntError) -> (kind: &IntErrorKind)
    ensures
        spec_int_error_kind(e) == kind,
        ;
```


### `str_is_valid_int_radix`

This function encodes whether a string can be parsed as an arbitrarily large `int` in
the supplied radix, ignoring machine-integer bounds.

```rust
pub open spec fn str_is_valid_int_radix(s: Seq<char>, radix: int, signed: bool) -> bool
    recommends
        2 <= radix,
        {
        &&& s.len() > 0
        &&& if s.first() == '+' || (signed && s.first() == '-') {
        &&& s.len() > 1
        &&& forall|i: int| 1 <= i < s.len() ==> #[trigger] char_is_digit_radix(s[i], radix)
        } else {
        forall|i: int| 0 <= i < s.len() ==> #[trigger] char_is_digit_radix(s[i], radix)
        }
        }
```


### `spec_int_from_str_radix`

This function encodes parsing an arbitrarily large `int` from a string in the supplied radix.

```rust
pub open spec fn spec_int_from_str_radix(s: Seq<char>, radix: int) -> int
    recommends
        2 <= radix,
        str_is_valid_int_radix(s, radix, true),
        {
        if s.first() == '+' {
        spec_int_from_str_radix_rec(s.drop_first(), radix)
        } else if s.first() == '-' {
        -spec_int_from_str_radix_rec(s.drop_first(), radix)
        } else {
        spec_int_from_str_radix_rec(s, radix)
        }
        }
```


### `spec_int_from_str_radix_rec`

This function encodes parsing an unsigned digit sequence as an arbitrarily large `int`,
recursively, in the supplied radix.

Invalid sequences map to arbitrary values.

```rust
pub open spec fn spec_int_from_str_radix_rec(s: Seq<char>, radix: int) -> int
    recommends
        2 <= radix,
        forall|i: int| 0 <= i < s.len() ==> #[trigger] char_is_digit_radix(s[i], radix),
    decreases
        s.len(),
        {
        if s.len() == 0 {
        0
        } else if char_is_digit_radix(s.last(), radix) {
        radix
        * spec_int_from_str_radix_rec(s.drop_last(), radix)
        + char_digit_value(s.last())
        } else {
        arbitrary::<int>()
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
        0 <= char_digit_value(c) < radix
        }
```


### `char_digit_value`

Encodes the numeric value of an ASCII radix digit.

Non-digits map to an arbitrary negative value; use `char_is_digit_radix` when checking validity.

```rust
pub open spec fn char_digit_value(c: char) -> int {
    if (CHAR_ZERO as int) <= (c as u32) <= (CHAR_NINE as int) {
    (c as u32) as int - (CHAR_ZERO as int)
    } else if (CHAR_LOWER_A as int) <= (c as u32) <= (CHAR_LOWER_Z as int) {
    (c as u32) as int - (CHAR_LOWER_A as int) + 10
    } else if (CHAR_UPPER_A as int) <= (c as u32) <= (CHAR_UPPER_Z as int) {
    (c as u32) as int - (CHAR_UPPER_A as int) + 10
    } else {
    // this makes sure the value is definitely not a valid digit
    -(arbitrary::<nat>() as int + 1)
    }
    }
```


### `lemma_parse_bool_error_obeys_eq_spec`

Proof that asserts `ParseBoolError` obeys `PartialEq`.

```rust
pub broadcast axiom fn lemma_parse_bool_error_obeys_eq_spec()
    ensures
        #[trigger] <ParseBoolError as PartialEqSpec>::obeys_eq_spec();
```


### `lemma_parse_bool_error_eq_spec`

Proof that interprets `ParseBoolError::eq_spec`.

```rust
pub broadcast axiom fn lemma_parse_bool_error_eq_spec(a: &ParseBoolError, b: &ParseBoolError)
    ensures
        #![trigger <ParseBoolError as PartialEqSpec>::eq_spec(a, b)]
        <ParseBoolError as PartialEqSpec>::eq_spec(a, b) == true;
```


### `<ParseBoolError as PartialEq>::eq`

Enable `ParseBoolError::eq`.

```rust
pub assume_specification[ <ParseBoolError as PartialEq>::eq ](
    x: &ParseBoolError,
    y: &ParseBoolError,
    ) -> bool;
```


### `lemma_parse_char_error_obeys_eq_spec`

Proof that asserts `ParseCharError` obeys `PartialEq`.

```rust
pub broadcast axiom fn lemma_parse_char_error_obeys_eq_spec()
    ensures
        #[trigger] <ParseCharError as PartialEqSpec>::obeys_eq_spec();
```


### `<ParseCharError as PartialEq>::eq`

Enable `ParseCharError::eq`.

```rust
pub assume_specification[ <ParseCharError as PartialEq>::eq ](
    x: &ParseCharError,
    y: &ParseCharError,
    ) -> bool;
```


### `lemma_parse_int_error_obeys_eq_spec`

Proof that asserts `ParseIntError` obeys `PartialEq`.

```rust
pub broadcast axiom fn lemma_parse_int_error_obeys_eq_spec()
    ensures
        #[trigger] <ParseIntError as PartialEqSpec>::obeys_eq_spec();
```


### `lemma_parse_int_error_eq_spec`

Proof that interprets `ParseIntError::eq_spec`.

```rust
pub broadcast axiom fn lemma_parse_int_error_eq_spec(a: &ParseIntError, b: &ParseIntError)
    ensures
        #![trigger <ParseIntError as PartialEqSpec>::eq_spec(a, b)]
        <ParseIntError as PartialEqSpec>::eq_spec(a, b) == (a.kind() == b.kind());
```


### `<ParseIntError as PartialEq>::eq`

Enable `ParseIntError::eq`.

```rust
pub assume_specification[ <ParseIntError as PartialEq>::eq ](
    x: &ParseIntError,
    y: &ParseIntError,
    ) -> bool;
```


### `lemma_int_error_kind_obeys_eq_spec`

Proof that asserts `IntErrorKind` obeys `PartialEq`.

```rust
pub broadcast axiom fn lemma_int_error_kind_obeys_eq_spec()
    ensures
        #[trigger] <IntErrorKind as PartialEqSpec>::obeys_eq_spec();
```


### `lemma_int_error_kind_eq_spec`

Proof that interprets `IntErrorKind::eq_spec`.

```rust
pub broadcast axiom fn lemma_int_error_kind_eq_spec(a: &IntErrorKind, b: &IntErrorKind)
    ensures
        #![trigger <IntErrorKind as PartialEqSpec>::eq_spec(a, b)]
        <IntErrorKind as PartialEqSpec>::eq_spec(a, b) == (a == b);
```


### `<IntErrorKind as PartialEq>::eq`

Enable `IntErrorKind::eq`.

```rust
pub assume_specification[ <IntErrorKind as PartialEq>::eq ](
    x: &IntErrorKind,
    y: &IntErrorKind,
    ) -> bool;
```
