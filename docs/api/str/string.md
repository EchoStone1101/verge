# `verge::str::string`

Specifications and lemmas for `std::String`.


## Structs


### `ExFromUtf8Error`

```rust
pub struct ExFromUtf8Error(FromUtf8Error);
```


## Traits


### `StringAdditionalFns`

Additional methods on `String`.

```rust
pub trait StringAdditionalFns: Sized
```


#### `from_utf8_verified`

```rust
fn from_utf8_verified(vec: Vec<u8>) -> Self
    requires
        vec@.is_utf8(),
    no_unwind;
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


### `String::is_empty`

Enable `String::is_empty`.

```rust
pub assume_specification [ String::is_empty ] (s: &String) -> (ret: bool)
    returns
        s@.len() == 0,
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


### `String::from_utf8`

Enable `String::from_utf8`.

```rust
pub assume_specification [ String::from_utf8 ] (vec: Vec<u8>) -> (ret: Result<String, FromUtf8Error>)
    ensures
        ({
            match ret {
                Ok(s) => vec@.is_utf8() && s@ =~= vec@.as_str(),
                Err(e) => !vec@.is_utf8() && e.is_str_utf8_error(),
            }
        }),
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


### `String::as_mut_str`

Enable `String::as_mut_str`.

```rust
pub assume_specification [ String::as_mut_str ] (s: &mut String) -> (ret: &mut str)
    ensures
        ret@ =~= old(s)@,
        final(ret)@ =~= final(s)@,
    no_unwind
        ;
```


### `String::clear`

Enable `String::clear`.

```rust
pub assume_specification [ String::clear ] (s: &mut String)
    ensures
        final(s)@ =~= Seq::<char>::empty(),
    no_unwind
        ;
```


### `String::push`

Enable `String::push`.

```rust
pub assume_specification [ String::push ] (s: &mut String, ch: char)
    ensures
        final(s)@ =~= old(s)@.push(ch),
        ;
```


### `String::push_str`

Enable `String::push_str`.

```rust
pub assume_specification [ String::push_str ] (s: &mut String, string: &str)
    ensures
        final(s)@ =~= old(s)@ + string@,
        ;
```


### `String::pop`

Enable `String::pop`.

```rust
pub assume_specification [ String::pop ] (s: &mut String) -> (ch: Option<char>)
    ensures
        old(s)@.len() > 0 ==> final(s)@ =~= old(s)@.drop_last() && ch == Some(old(s)@.last()),
        old(s)@.len() == 0 ==> final(s)@ =~= old(s)@ && ch.is_none(),
    no_unwind
        ;
```


### `String::reserve`

Enable `String::reserve`.

```rust
pub assume_specification [ String::reserve ] (s: &mut String, _amt: usize)
    ensures
        final(s)@ =~= old(s)@,
        ;
```


### `String::reserve_exact`

Enable `String::reserve_exact`.

```rust
pub assume_specification [ String::reserve_exact ] (s: &mut String, _amt: usize)
    ensures
        final(s)@ =~= old(s)@,
        ;
```


### `String::insert`

Enable `String::insert`.

Note that this function no longer panics, but requires proving that `idx`
falls between code points.

```rust
pub assume_specification [ String::insert ] (s: &mut String, idx: usize, ch: char)
    requires
        is_char_boundary(s@.as_bytes(), idx as int),
    ensures
        final(s)@.as_bytes() =~= old(s)@.as_bytes().take(idx as int) + seq![ch].as_bytes() + old(s)@.as_bytes().skip(idx as int),
        ;
```


### `String::insert_str`

Enable `String::insert_str`.

Note that this function no longer panics, but requires proving that `idx`
falls between code points.

```rust
pub assume_specification [ String::insert_str ] (s: &mut String, idx: usize, string: &str)
    requires
        is_char_boundary(s@.as_bytes(), idx as int),
    ensures
        final(s)@.as_bytes() =~= old(s)@.as_bytes().take(idx as int) + string@.as_bytes() + old(s)@.as_bytes().skip(idx as int),
        ;
```


### `String::remove`

Enable `String::remove`.

Note that this function no longer panics, but requires proving that `idx` is valid.

```rust
pub assume_specification [ String::remove ] (s: &mut String, idx: usize) -> (ret: char)
    requires
        is_char_boundary(s@.as_bytes(), idx as int),
        idx < s@.as_bytes().len(),
    ensures
        ret as u32 == decode_first_scalar(old(s)@.as_bytes().skip(idx as int)),
        final(s)@.as_bytes() =~=
            old(s)@.as_bytes().take(idx as int) + pop_first_scalar(old(s)@.as_bytes().skip(idx as int)),
        ;
```


### `String::retain`

Enable `String::retain`.

```rust
pub assume_specification<F> [ String::retain ] (s: &mut String, f: F)
    where
    F: FnMut(char) -> bool,
    ensures
        final(s)@ =~= old(s)@.filter(|c: char| call_ensures(f, (c,), true)),
        ;
```


### `String::split_off`

Enable `String::split_off`.

Note that this function no longer panics, but requires proving that `at`
falls between code points.

```rust
pub assume_specification [ String::split_off ] (s: &mut String, at: usize) -> (rem: String)
    requires
        is_char_boundary(s@.as_bytes(), at as int),
    ensures
        final(s)@.as_bytes() =~= old(s)@.as_bytes().take(at as int),
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
        is_char_boundary(s@.as_bytes(), new_len as int),
    ensures
        final(s)@.as_bytes() =~= old(s)@.as_bytes().take(new_len as int),
    no_unwind
        ;
```
