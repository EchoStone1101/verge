# `verge::str::string`

Specifications and lemmas for `std::String`.


## Structs


### `ExFromUtf8Error`

```rust
pub struct ExFromUtf8Error(FromUtf8Error);
```


## Traits


### `StringExecFromUtf8Fns`

```rust
pub trait StringExecFromUtf8Fns
```


#### `from_utf8_checked`

```rust
fn from_utf8_checked(vec: Vec<u8>) -> (res: Result<String, FromUtf8Error>)
    ensures
        vec@.is_utf8() <==> res.is_ok(),
    no_unwind
        ;
```


#### `from_utf8_verified`

```rust
fn from_utf8_verified(vec: Vec<u8>) -> String
    requires
        vec@.is_utf8(),
    no_unwind
        ;
```


## Functions


### `String::as_bytes`

Enable `String::as_bytes`.

```rust
pub assume_specification [ String::as_bytes ] (s: &String) -> (bytes: &[u8])
    ensures
        bytes@ =~= s@.as_bytes(),
    no_unwind
        ;
```


### `String::len`

Enable `String::len`. Note that this returns length in bytes.

```rust
pub assume_specification [ String::len ] (s: &String) -> (ret: usize)
    ensures
        ret == s@.as_bytes().len(),
    no_unwind
        ;
```


### `String::with_capacity`

Enable `String::with_capacity`.

```rust
pub assume_specification [ String::with_capacity ] (cap: usize) -> (s: String)
    ensures
        s@ =~= Seq::<char>::empty(),
        ;
```


### `String::into_bytes`

Enable `String::into_bytes`.

```rust
pub assume_specification [ String::into_bytes ] (s: String) -> (bytes: Vec<u8>)
    ensures
        bytes@ =~= s@.as_bytes(),
    no_unwind
        ;
```


### `String::clear`

Enable `String::clear`.

```rust
pub assume_specification [ String::clear ] (s: &mut String)
    ensures
        s@ =~= Seq::<char>::empty(),
    no_unwind
        ;
```


### `String::push`

Enable `String::push`.

```rust
pub assume_specification [ String::push ] (s: &mut String, ch: char)
    ensures
        s@ =~= old(s)@.push(ch),
        ;
```


### `String::pop`

Enable `String::pop`.

```rust
pub assume_specification [ String::pop ] (s: &mut String) -> (ch: Option<char>)
    ensures
        old(s)@.len() > 0 ==> s@ =~= old(s)@.drop_last() && ch == Some(old(s)@.last()),
        old(s)@.len() == 0 ==> s@ =~= old(s)@ && ch.is_none(),
    no_unwind
        ;
```


### `String::reserve`

Enable `String::reserve`.

```rust
pub assume_specification [ String::reserve ] (s: &mut String, _amt: usize)
    ensures
        s@ =~= old(s)@,
        ;
```


### `String::reserve_exact`

Enable `String::reserve_exact`.

```rust
pub assume_specification [ String::reserve_exact ] (s: &mut String, _amt: usize)
    ensures
        s@ =~= old(s)@,
        ;
```


### `String::insert`

Enable `String::insert`.

Note that this function no longer panics, but requires proving that `idx`
falls between code points.

```rust
pub assume_specification [ String::insert ] (s: &mut String, idx: usize, ch: char)
    requires
        idx <= old(s)@.as_bytes().len(),
        old(s)@.as_bytes().take(idx as int).is_utf8(),
        old(s)@.as_bytes().skip(idx as int).is_utf8(),
    ensures
        s@.as_bytes() =~= old(s)@.as_bytes().take(idx as int) + seq![ch].as_bytes() + old(s)@.as_bytes().skip(idx as int),
        ;
```


### `String::insert_str`

Enable `String::insert_str`.

Note that this function no longer panics, but requires proving that `idx`
falls between code points.

```rust
pub assume_specification [ String::insert_str ] (s: &mut String, idx: usize, string: &str)
    requires
        idx <= old(s)@.as_bytes().len(),
        old(s)@.as_bytes().take(idx as int).is_utf8(),
        old(s)@.as_bytes().skip(idx as int).is_utf8(),
    ensures
        s@.as_bytes() =~= old(s)@.as_bytes().take(idx as int) + string@.as_bytes() + old(s)@.as_bytes().skip(idx as int),
        ;
```


### `String::split_off`

Enable `String::split_off`.

Note that this function no longer panics, but requires proving that `at`
falls between code points.

```rust
pub assume_specification [ String::split_off ] (s: &mut String, at: usize) -> (rem: String)
    requires
        at <= old(s)@.as_bytes().len(),
        old(s)@.as_bytes().take(at as int).is_utf8(),
        old(s)@.as_bytes().skip(at as int).is_utf8(),
    ensures
        s@.as_bytes() =~= old(s)@.as_bytes().take(at as int),
        rem@.as_bytes() =~= old(s)@.as_bytes().skip(at as int),
        ;
```


### `String::truncate`

Enable `String::truncate`.

Note that this function no longer panics, but requires proving that `new_len`
falls between code points.

```rust
pub assume_specification [ String::truncate ] (s: &mut String, new_len: usize)
    requires
        new_len <= old(s)@.as_bytes().len(),
        old(s)@.as_bytes().take(new_len as int).is_utf8(),
    ensures
        s@.as_bytes() =~= old(s)@.as_bytes().take(new_len as int),
    no_unwind
        ;
```
