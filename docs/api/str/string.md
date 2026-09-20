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
pub trait StringAdditionalFns: Sized + View<V = Seq<char>>
```


#### `from_utf8_verified`

```rust
fn from_utf8_verified(vec: Vec<u8>) -> (ret: Self)
    requires
        vec@.is_utf8(),
    ensures
        ret@ =~= vec@.as_str(),
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

Enable `String::len`.

Note that this returns length in bytes.

```rust
pub assume_specification [ String::len ] (s: &String) -> (ret: usize)
    returns
        s@.as_bytes().len() as usize,
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
either falls between code points or is past the end of the string.

```rust
pub assume_specification [ String::truncate ] (s: &mut String, new_len: usize)
    requires
        new_len > s@.as_bytes().len() || is_char_boundary(s@.as_bytes(), new_len as int),
    ensures
        new_len <= old(s)@.as_bytes().len() ==> final(s)@.as_bytes() =~= old(s)@.as_bytes().take(new_len as int),
        new_len > old(s)@.as_bytes().len() ==> final(s)@.as_bytes() =~= old(s)@.as_bytes(),
    no_unwind
        ;
```
