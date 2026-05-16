# `verge::io`

Specifications and lemmas for `std`-based I/O functionality.

The `verge::io` module lays down the general abstraction for inputting
and outputting data from various sources. The overall API design mimicks
`std::io` (https://doc.rust-lang.org/std/io/index.html).

The core of this module includes the `ReadSpec` and `WriteSpec` traits, as well as
the access to `stdin`, `stdout`, and `stderr`.


## Structs


### `ExError`

```rust
pub struct ExError(Error);
```


### `ExErrorKind`

```rust
pub struct ExErrorKind(ErrorKind);
```


### `ExIntoInnerError`

```rust
pub struct ExIntoInnerError<W>(IntoInnerError<W>);
```


### `ExEmpty`

Enables `std::io::Empty`.

```rust
pub struct ExEmpty(Empty);
```


### `ExRepeat`

Enables `std::io::Repeat`.

```rust
pub struct ExRepeat(Repeat);
```


### `ExBufReader`

Enables `std::io::BufReader`.

```rust
pub struct ExBufReader<R: ?Sized>(BufReader<R>);
```


### `ExBufWriter`

Enables `std::io::BufWriter`.

### `Drop` and Flushing
In native Rust, the buffer of a `BufWriter` is flushed whenever the writer itself goes out of scope,
using a custom `Drop::drop` implementation, which Verus does not yet support.
While this does potentially create a discrepancy between specification and actual program states,
it will only matter when those inner sink states are part of the spec. And when they are, `Write`'s
specification will in fact not derive anything specific about the inner sink (e.g., how much bytes are
truly written) without inspecting or flushing the buffer in `exec` code; thus there is no real soundness issue here.

```rust
pub struct ExBufWriter<W: ?Sized + std::io::Write>(BufWriter<W>);
```


### `ExLineWriter`

Enables `std::io::LineWriter`.

### `Drop` and Flushing
See the comments on `BufWriter` for the issue on `LineWriter`'s drop specification.

```rust
pub struct ExLineWriter<W: ?Sized + std::io::Write>(LineWriter<W>);
```


### `ExCursor`

Enables `std::io::Cursor`.

```rust
pub struct ExCursor<T>(Cursor<T>);
```


## Traits


### `ReadBuf`

The `ReadBuf` trait defines types that can be used as the destination buffer for `Read::read`.

It is essentially `AsMut<[u8]>` with a `View` bound. This has to be external due to Verus's
limited support of `&mut`. See comments on `Read` for more information.

```rust
pub trait ReadBuf: View<V = Seq<u8>>
```


#### `as_mut`

```rust
fn as_mut(&mut self, range: Option<Range<usize>>) -> &mut [u8];
```


### `ExReadBuf`

```rust
pub trait ExReadBuf: View<V = Seq<u8>>
```


### `ExRead`

```rust
pub trait ExRead
```


### `ExBufRead`

```rust
pub trait ExBufRead: std::io::Read
```


### `ExWrite`

```rust
pub trait ExWrite
```


### `Read`

The `Read` trait allows for reading bytes from a source.

### Notes on the interface
`Read::read()`'s interface is different from `std::io::Read::read()`, in that the buffer is `&mut B where B: ReadBuf`
instead of `&mut [u8]`, and it also accepts an extra argument `range: Option<Range>` for writing to a
subrange of the read buffer.

This is entirely a workaround for Verus's limited support of `&mut`. In native Rust, the caller
can produce an `&mut` subrange from various actual buffers like `[u8; N]` or `Vec<u8>`.
However, `&mut` at the return position is currently forbidden in Verus, making such an interface
essentially unusable.

We solve this with the `ReadBuf` trait and the separate `range` argument. Implementors of `ReadBuf`
bypass the `&mut` issue by using external operations.

```rust
pub trait Read: ReadSpec
```


#### `read`

Pull some bytes from this source into the specified buffer, returning how many bytes were read.

```rust
fn read<B: ReadBuf + ?Sized>(&mut self, buf: &mut B, range: Option<Range<usize>>) -> (res: Result<usize>)
    requires
        old(self).read_inv(),
        match range {
            Some(range) => 0 <= range.start <= range.end <= old(buf)@.len(),
            _ => true,
        },
    ensures
        self.read_inv(),
        ({
            let (start, end) = match range {
                Some(range) => (range.start as int, range.end as int),
                _ => (0int, buf@.len() as int),
            };
            match res {
                Ok(nread) => {
                    &&& nread <= old(self).bytes().len() && nread <= end - start
                    &&& buf@ =~=
                        old(buf)@.take(start)
                        + old(self).bytes().take(nread as int)
                        + old(buf)@.skip(start + nread as int)
                    &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                    // ^ basic read semantics
                    &&& Self::read_ok(old(self), self)
                    &&& end - start > 0 && nread == 0 ==> self.read_eof()
                },
                Err(e) => {
                    &&& self.bytes() =~= old(self).bytes()
                    &&& buf@ =~= old(buf)@
                    &&& e.kind() == ErrorKind::Interrupted ==> Self::read_ok(old(self), self)
                    // ^ basic error semantics
                    &&& Self::read_err(e, old(self), self)
                }
            }
        }),
        ;
```


#### `read_to_end`

Reads all bytes until EOF in this source, appending them to `buf`.

```rust
fn read_to_end(&mut self, buf: &mut Vec<u8>) -> (res: Result<usize>)
    requires
        old(self).read_inv(),
        old(self).bytes().len() <= isize::MAX,
    ensures
        self.read_inv(),
        ({
            match res {
                Ok(nread) => {
                    &&& self.read_eof()
                    &&& nread <= old(self).bytes().len() && buf@.len() == old(buf)@.len() + nread
                    &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread as int)
                    &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                    &&& Self::read_ok(old(self), self)
                },
                Err(e) => {
                    let nread = old(self).bytes().len() - self.bytes().len();
                    &&& nread >= 0
                    &&& self.bytes() =~= old(self).bytes().skip(nread)
                    &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread)
                    //  ^ bytes already read are in `buf`
                    &&& e.kind() != ErrorKind::Interrupted // interrupts are retried
                    &&& Self::read_err(e, old(self), self)
                },
            }
        }),
        ;
```


#### `read_to_string`

Reads all bytes until EOF in this source, appending them to `buf`.

If the data in this stream is not valid UTF-8 then an error is returned and `buf` is unchanged.

```rust
fn read_to_string(&mut self, buf: &mut String) -> (res: Result<(usize)>)
    requires
        old(self).read_inv(),
        old(self).bytes().len() <= isize::MAX,
    ensures
        self.read_inv(),
        ({
            match res {
                Ok(nread) => {
                    &&& self.read_eof()
                    &&& nread <= old(self).bytes().len()
                    &&& old(self).bytes().take(nread as int).is_utf8()
                    &&& buf@.as_bytes() =~= old(buf)@.as_bytes() + old(self).bytes().take(nread as int)
                    &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                    &&& Self::read_ok(old(self), self)
                },
                Err(e) => {
                    let nread = old(self).bytes().len() - self.bytes().len();
                    &&& nread >= 0
                    &&& self.bytes() =~= old(self).bytes().skip(nread)
                    &&& buf@ =~= old(buf)@
                    //  ^ bytes already read are *not* in `buf`
                    &&& e.kind() == ErrorKind::InvalidData ==>
                            !old(self).bytes().take(nread).is_utf8()
                    &&& e.kind() != ErrorKind::Interrupted // interrupts are retried
                    &&& Self::read_err(e, old(self), self)
                },
            }
        }),
        ;
```


#### `read_exact`

Reads the exact number of bytes required to fill `buf`.

```rust
fn read_exact<B: ReadBuf>(&mut self, buf: &mut B) -> (res: Result<()>)
    requires
        old(self).read_inv(),
    ensures
        self.read_inv(),
        ({
            match res {
                Ok(_) => {
                    &&& old(buf)@.len() <= old(self).bytes().len()
                    &&& buf@ =~= old(self).bytes().take(old(buf)@.len() as int)
                    &&& self.bytes() =~= old(self).bytes().skip(old(buf)@.len() as int)
                    &&& Self::read_ok(old(self), self)
                },
                Err(e) => {
                    &&& e.kind() != ErrorKind::Interrupted // interrupts are retried
                    &&& e.kind() == ErrorKind::UnexpectedEof ==> self.read_eof()
                    &&& Self::read_err(e, old(self), self)
                },
            }
        }),
        ;
```


### `ReadSpec`

The `ReadSpec` trait specifies `std::io::Read` by describing the behavior of
reading bytes from a source.

This trait should be implemented by types that also implement `std::io::Read`.
Implementors should customize the following basic functions for instance-specific semantics:

* `bytes()`: the remaining bytes that can be read from this source;

* `read_inv()`: invariants of this instance;

* `read_ok()`: extra *composable* post-conditions for a successful read;

* `read_err()`: post-conditions for an erroneous read; can be `false` if `read()` cannot fail;

* `read_eof()`: post-conditions after an EOF read;

### Understanding EOF
`ReadSpec::read_eof()` is intended to *not* be a terminal state (i.e., `old(self).read_eof()` does not
necessarily imply `self.read_eof()`; although for specific implemenatation it does, for example
when `read_eof() <==> self.bytes().len() == 0`).
In fact, `ReadSpec::read_eof()` doesn't even guarantee that the next `read()` will return 0 bytes;
its whole purpose is to expose some extra post-conditions to the caller of `read()`.

```rust
pub trait ReadSpec
```


#### `bytes`

```rust
spec fn bytes(&self) -> Seq<u8>;
```


#### `read_inv`

```rust
open spec fn read_inv(&self) -> bool { true }
```


#### `read_ok`

```rust
spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool;
```


#### `read_err`

```rust
spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool;
```


#### `read_eof`

```rust
spec fn read_eof(&self) -> bool;
```


#### `read_ok_extra_ensures`

```rust
open spec fn read_ok_extra_ensures(
    pre_self: &Self, post_self: &Self,
    pre_buf: Seq<u8>, post_buf: Seq<u8>,
    range: Option<Range<usize>>, res: Result<usize>,
    ) -> bool { true }

    proof fn read_ok_is_reflexive(inst: &Self)
    requires
        inst.read_inv(),
    ensures
        Self::read_ok(inst, inst),
        ;
```


#### `read_ok_is_composable`

```rust
proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self)
    requires
        pre_self.read_inv() && mid_self.read_inv() && post_self.read_inv(),
        Self::read_ok(pre_self, mid_self),
        Self::read_ok(mid_self, post_self),
    ensures
        Self::read_ok(pre_self, post_self),
        ;
```


#### `read_ok_err_are_composable`

```rust
proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error)
    requires
        pre_self.read_inv() && mid_self.read_inv() && post_self.read_inv(),
        Self::read_ok(pre_self, mid_self),
        Self::read_err(error, mid_self, post_self),
    ensures
        Self::read_err(error, pre_self, post_self),
        ;
```


### `BufRead`

A `BufRead` is a type of reader which has an internal buffer, allowing it to perform extra ways of reading.

```rust
pub trait BufRead: Read + BufReadSpec
```


#### `fill_buf`

Returns the contents of the internal buffer, filling it with more data,
via `Read` methods, if empty.

```rust
fn fill_buf(&mut self) -> (res: Result<&[u8]>)
    requires
        old(self).read_inv(),
    ensures
        self.read_inv(),
        self.bytes() =~= old(self).bytes(),
        match res {
            Ok(buf) => ({
                let buflen = buf@.len();
                &&& buf@ =~= self.buffer()
                &&& buflen <= old(self).bytes().len()
                &&& self.buffer() =~= old(self).bytes().take(buflen as int)
                &&& Self::read_ok(old(self), self)
                &&& buflen == 0 ==> self.read_eof()
            }),
            Err(e) => ({
                // effectively one failed `read`
                &&& old(self).buffer().len() == 0 && self.buffer().len() == 0
                &&& self.buffer() =~= old(self).buffer()
                &&& e.kind() == ErrorKind::Interrupted ==> Self::read_ok(old(self), self)
                &&& Self::read_err(e, old(self), self)
            })
        },
        ;
```


#### `consume`

Marks the given amount of additional bytes from the internal buffer as having been read.
Subsequent calls to `read` only return bytes that have not been marked as read.

```rust
fn consume(&mut self, amount: usize)
    requires
        old(self).read_inv(),
        amount <= old(self).buffer().len(),
    ensures
        self.read_inv(),
        self.buffer() =~= old(self).buffer().skip(amount as int),
        self.bytes() =~= old(self).bytes().skip(amount as int),
        Self::read_ok(old(self), self),
        Self::read_eof(old(self)) ==> self.read_eof(),
        ;
```


#### `read_until`

Reads all bytes into `buf` until the delimiter `byte` or EOF is reached.

This function will read bytes from the underlying stream until the delimiter or EOF is found.
Once found, all bytes up to, and including, the delimiter (if found) will be appended to `buf`.
If successful, this function will return the total number of bytes read.

```rust
fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> (res: Result<usize>)
    requires
        old(self).read_inv(),
        old(self).bytes().len() <= isize::MAX,
    ensures
        self.read_inv(),
        ({
            match res {
                Ok(nread) => ({
                    &&& nread <= old(self).bytes().len()
                    &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread as int)
                    &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                    &&& forall|i: int| #![auto] old(buf)@.len() <= i < buf@.len() - 1 ==> buf[i] != byte
                    &&& (nread == 0 || buf@.last() != byte) ==> self.read_eof()
                    &&& Self::read_ok(old(self), self)
                }),
                Err(e) => ({
                    let nread = old(self).bytes().len() - self.bytes().len();
                    &&& nread >= 0
                    &&& self.bytes() =~= old(self).bytes().skip(nread)
                    &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread)
                    &&& forall|i: int| #![auto] old(buf)@.len() <= i < buf@.len() ==> buf[i] != byte
                    //  ^ bytes already read are in `buf`
                    &&& e.kind() != ErrorKind::Interrupted // interrupts are retried
                    &&& Self::read_err(e, old(self), self)
                }),
            }
        }),
        ;
```


#### `skip_until`

Skips all bytes until the delimiter `byte` or EOF is reached.

This function will read (and discard) bytes from the underlying stream until the delimiter or EOF is found.
If successful, this function will return the total number of bytes read, including the delimiter byte if found.

```rust
fn skip_until(&mut self, byte: u8) -> (res: Result<usize>)
    requires
        old(self).read_inv(),
        old(self).bytes().len() <= isize::MAX,
    ensures
        self.read_inv(),
        ({
            match res {
                Ok(nread) => ({
                    &&& nread <= old(self).bytes().len()
                    &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                    &&& forall|i: int| #![auto] 0 <= i < nread as int - 1 ==> old(self).bytes()[i] != byte
                    &&& (nread == 0 || old(self).bytes()[nread as int - 1] != byte) ==> self.read_eof()
                    &&& Self::read_ok(old(self), self)
                }),
                Err(e) => ({
                    let nread = old(self).bytes().len() - self.bytes().len();
                    &&& nread >= 0
                    &&& self.bytes() =~= old(self).bytes().skip(nread)
                    &&& forall|i: int| #![auto] 0 <= i < nread ==> old(self).bytes()[i] != byte
                    &&& e.kind() != ErrorKind::Interrupted // interrupts are retried
                    &&& Self::read_err(e, old(self), self)
                }),
            }
        }),
        ;
```


#### `read_line`

Reads all bytes until a newline (the `0xA` byte) is reached, and append them to the provided `String` buffer.

This function will read bytes from the underlying stream until the newline delimiter (the 0xA byte) or EOF is found.
Once found, all bytes up to, and including, the delimiter (if found) will be appended to buf.
If successful, this function will return the total number of bytes read.

```rust
fn read_line(&mut self, buf: &mut String) -> (res: Result<usize>)
    requires
        old(self).read_inv(),
        old(self).bytes().len() <= isize::MAX,
    ensures
        ({
            match res {
                Ok(nread) => ({
                    &&& nread <= old(self).bytes().len()
                    &&& old(self).bytes().take(nread as int).is_utf8()
                    &&& buf@.as_bytes() =~= old(buf)@.as_bytes() + old(self).bytes().take(nread as int)
                    &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                    &&& forall|i: int| old(buf)@.len() <= i < buf@.len() - 1 ==> #[trigger] buf@[i] != 0xA
                    &&& (nread == 0 || buf@.last() != 0xA) ==> self.read_eof()
                    &&& Self::read_ok(old(self), self)
                }),
                Err(e) => ({
                    let nread = old(self).bytes().len() - self.bytes().len();
                    &&& nread >= 0
                    &&& self.bytes() =~= old(self).bytes().skip(nread)
                    &&& buf@ =~= old(buf)@
                    //  ^ bytes already read are *not* in `buf`
                    &&& e.kind() == ErrorKind::InvalidData ==>
                            !old(self).bytes().take(nread).is_utf8()
                    &&& e.kind() != ErrorKind::Interrupted // interrupts are retried
                    &&& Self::read_err(e, old(self), self)
                }),
            }
        }),
        ;
```


### `BufReadSpec`

The `BufReadSpec` trait specifies `std::io::BufRead` by describing the behavior of
buffered reading.

The specification is based on `Read` and `Read::bytes()`, with the addition of the
`buffer()` spec function to represent buffering semantics.

```rust
pub trait BufReadSpec: ReadSpec
```


#### `buffer`

```rust
spec fn buffer(&self) -> Seq<u8>;
```


#### `consume_extra_ensures`

```rust
open spec fn consume_extra_ensures(
    pre_self: &Self, post_self: &Self, amt: usize
    ) -> bool { true }

    proof fn buffer_is_prefix_of_bytes(inst: &Self)
    requires
        inst.read_inv(),
    ensures
        inst.buffer().is_prefix_of(inst.bytes()),
        ;
```


### `Write`

The `Write` trait is for objects which are byte-oriented sinks.

```rust
pub trait Write: WriteSpec + Sized
```


#### `write`

Writes a buffer into this writer, returning how many bytes were written.

```rust
fn write(&mut self, buf: &[u8]) -> (res: Result<usize>)
    requires
        old(self).write_inv(),
    ensures
        self.write_inv(),
        ({
            match res {
                Ok(nwritten) => {
                    &&& nwritten <= buf@.len()
                    &&& self.bytes() =~= old(self).bytes() + buf@.take(nwritten as int)
                    // ^ basic write semantics
                    &&& Self::write_ok(old(self), self)
                    &&& buf@.len() > 0 && nwritten == 0 ==> self.write_eof()
                },
                Err(e) => {
                    &&& self.bytes() =~= old(self).bytes()
                    &&& e.kind() == ErrorKind::Interrupted ==> Self::write_ok(old(self), self)
                    // ^ basic error semantics
                    &&& Self::write_err(e, old(self), self)
                }
            }
        }),
        ;
```


#### `flush`

Flushes this output stream, ensuring that all intermediately buffered contents reach their destination.

It is considered an error if not all bytes could be written due to I/O errors or EOF being reached.

```rust
fn flush(&mut self) -> (res: Result<()>)
    requires
        old(self).write_inv(),
    ensures
        self.write_inv(),
        self.bytes() =~= old(self).bytes(),
        ({
            match res {
                Ok(_) => {
                    &&& self.buffer().len() == 0
                    &&& Self::write_ok(old(self), self)
                },
                Err(e) => {
                    &&& self.buffer().len() <= old(self).buffer().len()
                    &&& Self::write_err(e, old(self), self)
                    &&& e.kind() != ErrorKind::Interrupted
                    &&& e.kind() == ErrorKind::WriteZero
                        ==> self.write_eof()
                }
            }
        }),
        ;
```


#### `write_all`

Attempts to write an entire buffer into this writer.

If the buffer contains no data, this will never call write.

```rust
fn write_all(&mut self, buf: &[u8]) -> (res: Result<()>)
    requires
        old(self).write_inv(),
    ensures
        self.write_inv(),
        ({
            match res {
                Ok(_) => {
                    let nwritten = buf@.len();
                    &&& self.bytes() =~= old(self).bytes() + buf@
                    &&& Self::write_ok(old(self), self)
                    &&& buf@.len() > 0 && nwritten == 0 ==> self.write_eof()
                    &&& buf@.len() == 0 ==> *self == *old(self)
                },
                Err(e) => {
                    let nwritten = self.bytes().len() - old(self).bytes().len();
                    &&& 0 <= nwritten < buf@.len()
                    &&& self.bytes() =~= old(self).bytes() + buf@.take(nwritten)
                    //  ^ bytes already written are in the sink
                    &&& e.kind() != ErrorKind::Interrupted // interrupts are retried
                    &&& Self::write_err(e, old(self), self)
                    &&& e.kind() == ErrorKind::WriteZero
                        ==> self.write_eof()
                }
            }
        }),
        ;
```


### `WriteSpec`

The `WriteSpec` trait specifies `std::io::Write` by describing the behavior of
writing bytes to a (potentially buffered) sink.

This trait should be implemented by types that also implement `std::io::Write`.
Implementors should customize the following basic functions for instance-specific semantics:

* `bytes()`: the bytes currently in the sink.

* `buffer()`: the bytes in the buffer (also considered "in the sink").

* `write_inv()`: invariants of this instance;

* `write_ok()`: extra *composable* post-conditions for a successful write;

* `write_err()`: post-conditions for an erroneous write; can be `false` if `write()` cannot fail;

* `write_eof()`: post-conditions after an EOF write;

### `flush()` and Buffering
`Write` is more like `BufRead` (compared to `Read`) in the sense that it assumes buffering
capabilities of a sink. If a sink is buffered, then asserting that `Write::bytes()` contains
some sequence of bytes (i.e., the sequence is "in the sink") does not prove that the sequence
is truly "written" - you must also prove that the sequence is not in the buffer, which is
only possible by calling the `flush()` method on buffered sinks. Meanwhile, unbuffered sinks
should be specified in a way where `Write::buffer()` is always empty.

```rust
pub trait WriteSpec
```


#### `bytes`

```rust
spec fn bytes(&self) -> Seq<u8>;
```


#### `buffer`

```rust
spec fn buffer(&self) -> Seq<u8>;
```


#### `write_inv`

```rust
open spec fn write_inv(&self) -> bool { true }
```


#### `write_ok`

```rust
spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool;
```


#### `write_err`

```rust
spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool;
```


#### `write_eof`

```rust
spec fn write_eof(&self) -> bool;
```


#### `write_ok_extra_ensures`

```rust
open spec fn write_ok_extra_ensures(pre_self: &Self, post_self: &Self, buf: Seq<u8>, res: Result<usize>) -> bool
    { true }
```


#### `flush_extra_ensures`

```rust
open spec fn flush_extra_ensures(pre_self: &Self, post_self: &Self, res: Result<()>) -> bool
    { true }
```


#### `buffer_is_suffix_of_bytes`

```rust
proof fn buffer_is_suffix_of_bytes(inst: &Self)
    requires
        inst.write_inv(),
    ensures
        inst.buffer().is_suffix_of(inst.bytes()),
        ;
```


#### `write_ok_is_reflexive`

```rust
proof fn write_ok_is_reflexive(inst: &Self)
    requires
        inst.write_inv(),
    ensures
        Self::write_ok(inst, inst),
        ;
```


#### `write_ok_is_composable`

```rust
proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self)
    requires
        pre_self.write_inv() && mid_self.write_inv() && post_self.write_inv(),
        Self::write_ok(pre_self, mid_self),
        Self::write_ok(mid_self, post_self),
    ensures
        Self::write_ok(pre_self, post_self),
        ;
```


#### `write_ok_err_are_composable`

```rust
proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error)
    requires
        pre_self.write_inv() && mid_self.write_inv() && post_self.write_inv(),
        Self::write_ok(pre_self, mid_self),
        Self::write_err(error, mid_self, post_self),
    ensures
        Self::write_err(error, pre_self, post_self),
        ;
```


### `RepeatSpec`

```rust
pub trait RepeatSpec
```


#### `byte`

```rust
spec fn byte(&self) -> u8;
```


### `BufReaderSpec`

```rust
pub trait BufReaderSpec<R: ?Sized>
```


#### `inv`

Invariant of `BufReader`.

```rust
open spec fn inv(&self) -> bool {
    &&& 0 <= self.pos() <= self.filled() <= spec_slice_len(self.buf())
    &&& spec_slice_len(self.buf()) > 0
    }
```


#### `valid_buf`

In-use region of the internal buffer.

```rust
open spec fn valid_buf(&self) -> Seq<u8> {
    self.buf()@.subrange(self.pos(), self.filled())
    }
```


#### `buf`

The full internal buffer.

```rust
spec fn buf(&self) -> &[u8];
```


#### `pos`

Start offset of the in-use buffer range.

```rust
spec fn pos(&self) -> int;
```


#### `filled`

End offset of the in-use buffer range.

```rust
spec fn filled(&self) -> int;
```


#### `inner`

Underlying reader instance.

```rust
spec fn inner(&self) -> &R;
```


### `BufReaderIntoInnerFns`

```rust
pub trait BufReaderIntoInnerFns<R: Read + Sized>
```


#### `into_inner`

```rust
fn into_inner(self) -> R;
```


### `BufWriterSpec`

```rust
pub trait BufWriterSpec<W: ?Sized>
```


#### `inv`

Invariant of `BufWriter`.

```rust
open spec fn inv(&self) -> bool {
    &&& 0 <= self.pos() <= spec_slice_len(self.buf())
    &&& spec_slice_len(self.buf()) > 0
    }
```


#### `valid_buf`

In-use region of the internal buffer.

```rust
open spec fn valid_buf(&self) -> Seq<u8> {
    self.buf()@.take(self.pos())
    }
```


#### `buf`

The full internal buffer.

```rust
spec fn buf(&self) -> &[u8];
```


#### `pos`

End offset of the in-use buffer range.

```rust
spec fn pos(&self) -> int;
```


#### `inner`

Underlying writer instance.

```rust
spec fn inner(&self) -> &W;
```


### `BufWriterIntoInnerFns`

```rust
pub trait BufWriterIntoInnerFns<W: Write + std::io::Write>
```


#### `into_inner`

```rust
fn into_inner(self) -> std::result::Result<W, IntoInnerError<BufWriter<W>>>;
```


### `LineWriterSpec`

```rust
pub trait LineWriterSpec<W: ?Sized>
```


#### `inv`

Invariant of `LineWriter`.

```rust
open spec fn inv(&self) -> bool {
    &&& 0 <= self.pos() <= spec_slice_len(self.buf())
    &&& spec_slice_len(self.buf()) > 0
    &&& !self.valid_buf().contains(0xA)
    }
```


#### `valid_buf`

In-use region of the internal buffer.

```rust
open spec fn valid_buf(&self) -> Seq<u8> {
    self.buf()@.take(self.pos())
    }
```


#### `buf`

The full internal buffer.

```rust
spec fn buf(&self) -> &[u8];
```


#### `pos`

End offset of the in-use buffer range.

```rust
spec fn pos(&self) -> int;
```


#### `inner`

Underlying writer instance.

```rust
spec fn inner(&self) -> &W;
```


### `LineWriterIntoInnerFns`

```rust
pub trait LineWriterIntoInnerFns<W: Write + std::io::Write>
```


#### `into_inner`

```rust
fn into_inner(self) -> std::result::Result<W, IntoInnerError<LineWriter<W>>>;
```


### `CursorSpec`

```rust
pub trait CursorSpec<T>
```


#### `inv`

Invariant of `Cursor`.

NOTE: Verge restricts the cursor to always fit within `usize`, not `u64`.

```rust
open spec fn inv(&self) -> bool {
    self.pos() <= usize::MAX
    }
```


#### `pos`

The current cursor position of the in-memory buffer.

```rust
spec fn pos(&self) -> nat;
```


#### `inner`

Underlying buffer instance.

```rust
spec fn inner(&self) -> &T;
```


## Functions


### `spec_error_kind`

```rust
pub uninterp spec fn spec_error_kind(e: &Error) -> ErrorKind;
```


### `Error::kind`

```rust
pub assume_specification[Error::kind](e: &Error) -> (kind: ErrorKind)
    ensures
        spec_error_kind(e) == kind,
        ;
```


### `spec_err_into_error`

```rust
pub uninterp spec fn spec_err_into_error<W>(e: IntoInnerError<W>) -> Error;
```


### `IntoInnerError::into_error`

```rust
pub assume_specification<W>[IntoInnerError::into_error](e: IntoInnerError<W>) -> (err: Error)
    ensures
        spec_err_into_error(e) == err,
        ;
```


### `IntoInnerError::error`

```rust
pub assume_specification<W>[IntoInnerError::error](e: &IntoInnerError<W>) -> (err: &Error)
    ensures
        spec_err_into_error(*e) == *err,
        ;
```


### `spec_err_into_inner`

```rust
pub uninterp spec fn spec_err_into_inner<W>(e: IntoInnerError<W>) -> W;
```


### `IntoInnerError::into_inner`

```rust
pub assume_specification<W>[IntoInnerError::into_inner](e: IntoInnerError<W>) -> (ret: W)
    ensures
        spec_err_into_inner(e) == ret,
        ;
```


### `std::io::empty`

```rust
pub assume_specification[ std::io::empty ]() -> Empty
    no_unwind
        ;
```


### `std::io::repeat`

```rust
pub assume_specification[ std::io::repeat ](b: u8) -> (ret: Repeat)
    ensures ret.byte() == b,
    no_unwind
        ;
```


### `BufReader::new`

Enables `BufReader::new`.

```rust
pub assume_specification<R: std::io::Read>[ BufReader::new ](inner: R) -> (ret: BufReader<R>)
    ensures
        ret.inv(),
        ret.pos() == 0,
        ret.filled() == 0,
        *ret.inner() == inner,
        ;
```


### `BufReader::with_capacity`

Enables `BufReader::with_capacity`.

```rust
pub assume_specification<R: std::io::Read>[ BufReader::with_capacity ](cap: usize, inner: R) -> (ret: BufReader<R>)
    requires
        cap > 0,
    ensures
        ret.inv(),
        spec_slice_len(ret.buf()) == cap,
        ret.pos() == 0,
        ret.filled() == 0,
        *ret.inner() == inner,
        ;
```


### `BufReader::get_ref`

Enables `BufReader::get_ref`.

```rust
pub assume_specification<R: ?Sized>[ BufReader::get_ref ](r: &BufReader<R>) -> (ret: &R)
    requires
        r.inv(),
    ensures
        ret == r.inner(),
        ;
```


### `BufReader::buffer`

Enables `BufReader::buffer`.

```rust
pub assume_specification<R: ?Sized>[ BufReader::buffer ](r: &BufReader<R>) -> (ret: &[u8])
    requires
        r.inv(),
    ensures
        ret@ =~= r.valid_buf(),
        ;
```


### `BufReader::capacity`

Enables `BufReader::capacity`.

```rust
pub assume_specification<R: ?Sized>[ BufReader::capacity ](r: &BufReader<R>) -> (ret: usize)
    requires
        r.inv(),
    ensures
        ret == spec_slice_len(r.buf()),
        ;
```


### `BufWriter::new`

```rust
pub assume_specification<W: std::io::Write>[ BufWriter::new ](inner: W) -> (ret: BufWriter<W>)
    ensures
        ret.inv(),
        ret.pos() == 0,
        *ret.inner() == inner,
        ;
```


### `BufWriter::with_capacity`

```rust
pub assume_specification<W: std::io::Write>[ BufWriter::with_capacity ](cap: usize, inner: W) -> (ret: BufWriter<W>)
    requires
        cap > 0,
    ensures
        ret.inv(),
        spec_slice_len(ret.buf()) == cap,
        ret.pos() == 0,
        *ret.inner() == inner,
        ;
```


### `BufWriter::get_ref`

```rust
pub assume_specification<W: ?Sized + std::io::Write>[ BufWriter::get_ref ](w: &BufWriter<W>) -> (ret: &W)
    requires
        w.inv(),
    ensures
        ret == w.inner(),
        ;
```


### `BufWriter::buffer`

```rust
pub assume_specification<W: ?Sized + std::io::Write>[ BufWriter::buffer ](w: &BufWriter<W>) -> (ret: &[u8])
    requires
        w.inv(),
    ensures
        ret@ =~= w.valid_buf(),
        ;
```


### `BufWriter::capacity`

```rust
pub assume_specification<W: ?Sized + std::io::Write>[ BufWriter::capacity ](w: &BufWriter<W>) -> (ret: usize)
    requires
        w.inv(),
    ensures
        ret == spec_slice_len(w.buf()),
        ;
```


### `LineWriter::new`

```rust
pub assume_specification<W: std::io::Write>[ LineWriter::new ](inner: W) -> (ret: LineWriter<W>)
    ensures
        ret.inv(),
        ret.pos() == 0,
        *ret.inner() == inner,
        ;
```


### `LineWriter::with_capacity`

```rust
pub assume_specification<W: std::io::Write>[ LineWriter::with_capacity ](cap: usize, inner: W) -> (ret: LineWriter<W>)
    requires
        cap > 0,
    ensures
        ret.inv(),
        spec_slice_len(ret.buf()) == cap,
        ret.pos() == 0,
        *ret.inner() == inner,
        ;
```


### `LineWriter::get_ref`

```rust
pub assume_specification<W: ?Sized + std::io::Write>[ LineWriter::get_ref ](w: &LineWriter<W>) -> (ret: &W)
    requires
        w.inv(),
    ensures
        ret == w.inner(),
        ;
```


### `Cursor::new`

Enables `Cursor::<T>::new()`.

```rust
pub assume_specification<T>[ Cursor::new ](inner: T) -> (ret: Cursor<T>)
    ensures
        ret.inv(),
        ret.pos() == 0,
        *ret.inner() == inner,
    no_unwind
        ;
```


### `Cursor::into_inner`

Enables `Cursor::<T>::into_inner()`.

```rust
pub assume_specification<T>[ Cursor::into_inner ](this: Cursor<T>) -> (ret: T)
    requires
        this.inv(),
    ensures
        ret == *this.inner(),
    no_unwind
        ;
```


### `Cursor::get_ref`

Enables `Cursor::<T>::get_ref()`.

```rust
pub assume_specification<T>[ Cursor::get_ref ](this: &Cursor<T>) -> (ret: &T)
    requires
        this.inv(),
    ensures
        *ret == *this.inner(),
    no_unwind
        ;
```


### `Cursor::position`

Enables `Cursor::<T>::position()`.

```rust
pub assume_specification<T>[ Cursor::position ](this: &Cursor<T>) -> (ret: u64)
    requires
        this.inv(),
    ensures
        ret == this.pos(),
    no_unwind
        ;
```


### `Cursor::set_position`

Enables `Cursor::<T>::set_position()`.

```rust
pub assume_specification<T>[ Cursor::set_position ](this: &mut Cursor<T>, pos: u64)
    requires
        old(this).inv(),
        pos <= usize::MAX,
    ensures
        this.inv(),
        this.pos() == pos,
        *this.inner() == *old(this).inner(),
    no_unwind
        ;
```


### `<ErrorKind as Clone>::clone`

```rust
pub assume_specification[ <ErrorKind as Clone>::clone ](this: &ErrorKind) -> (ret: ErrorKind)
    ensures
        ret == *this,
        ;
```


### `<Empty as Clone>::clone`

```rust
pub assume_specification[ <Empty as Clone>::clone ](this: &Empty) -> (ret: Empty)
    ensures
        ret == *this,
        ;
```


### `<Cursor<T> as Clone>::clone`

```rust
pub assume_specification<T: Clone>[ <Cursor<T> as Clone>::clone ](this: &Cursor<T>) -> (ret: Cursor<T>)
    ensures
        ret == *this,
        ;
```


## Type Aliases


### `Result`

```rust
pub type Result<T> = std::result::Result<T, Error>;
```
