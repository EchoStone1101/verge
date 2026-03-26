//! Specifications and lemmas for `std`-based I/O functionality.
//!
//! The `verge::io` module lays down the general abstraction for inputting 
//! and outputting data from various sources. The overall API design mimicks 
//! `std::io` (https://doc.rust-lang.org/std/io/index.html), but the interface 
//! is kept deliberately minimal.
//! 
//! The core of this module includes the `ReadSpec` and `WriteSpec` traits, as well as 
//! the access to `stdin`, `stdout`, and `stderr`.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::slice::{slice_subrange, spec_slice_len};
use vstd::std_specs::result::spec_unwrap;
use crate::str::{StrView, BytesView};
use crate::error::ErrorSpec;

use core::ops::Range;
use std::collections::VecDeque;
pub use std::io::{
    Error, ErrorKind, Empty, Repeat,
    BufReader, BufWriter, LineWriter, Cursor, IntoInnerError,
    empty, repeat,
};

/// The `ReadBuf` trait defines types that can be used as the destination buffer for `Read::read`.
/// 
/// It is essentially `AsMut<[u8]>` with a `View` bound. This has to be external due to Verus's
/// limited support of `&mut`. See comments on `Read` for more information.
#[verifier::external]
pub trait ReadBuf: View<V = Seq<u8>> {
    fn as_mut(&mut self, range: Option<Range<usize>>) -> &mut [u8];
}

#[verifier::external]
impl ReadBuf for [u8] {
    fn as_mut(&mut self, range: Option<Range<usize>>) -> &mut [u8] {
        match range {
            Some(range) => &mut <Self as AsMut<[u8]>>::as_mut(self)[range],
            None => <Self as AsMut<[u8]>>::as_mut(self),
        }
    }
}

#[verifier::external]
impl<const N: usize> ReadBuf for [u8; N] {
    fn as_mut(&mut self, range: Option<Range<usize>>) -> &mut [u8] {
        match range {
            Some(range) => &mut self.as_mut_slice()[range],
            None => self.as_mut_slice(),
        }
    }
}

#[verifier::external]
impl ReadBuf for Vec<u8> {
    fn as_mut(&mut self, range: Option<Range<usize>>) -> &mut [u8] {
        match range {
            Some(range) => &mut <Self as AsMut<[u8]>>::as_mut(self)[range],
            None => <Self as AsMut<[u8]>>::as_mut(self),
        }
    }
}

verus! {

pub mod stdio;
pub mod impls;

pub use stdio::*;
pub use impls::*;

#[verifier::external_trait_specification]
pub trait ExReadBuf: View<V = Seq<u8>> {
    type ExternalTraitSpecificationFor: ReadBuf;
}

#[verifier::external_trait_specification]
pub trait ExRead {
    type ExternalTraitSpecificationFor: std::io::Read;
}

#[verifier::external_trait_specification]
pub trait ExBufRead: std::io::Read {
    type ExternalTraitSpecificationFor: std::io::BufRead;
}

#[verifier::external_trait_specification]
pub trait ExWrite {
    type ExternalTraitSpecificationFor: std::io::Write;
}

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExError(Error);

impl ErrorSpec for Error {}

#[verifier::external_type_specification]
pub struct ExErrorKind(ErrorKind);

pub uninterp spec fn spec_error_kind(e: &Error) -> ErrorKind;
#[verifier::when_used_as_spec(spec_error_kind)]
pub assume_specification[Error::kind](e: &Error) -> (kind: ErrorKind)
    ensures
        spec_error_kind(e) == kind,
;

#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(W)]
pub struct ExIntoInnerError<W>(IntoInnerError<W>);

pub uninterp spec fn spec_err_into_error<W>(e: IntoInnerError<W>) -> Error;
#[verifier::when_used_as_spec(spec_err_into_error)]
pub assume_specification<W>[IntoInnerError::into_error](e: IntoInnerError<W>) -> (err: Error)
    ensures
        spec_err_into_error(e) == err,
;
pub assume_specification<W>[IntoInnerError::error](e: &IntoInnerError<W>) -> (err: &Error)
    ensures
        spec_err_into_error(*e) == *err,
;

pub uninterp spec fn spec_err_into_inner<W>(e: IntoInnerError<W>) -> W;
#[verifier::when_used_as_spec(spec_err_into_inner)]
pub assume_specification<W>[IntoInnerError::into_inner](e: IntoInnerError<W>) -> (ret: W)
    ensures
        spec_err_into_inner(e) == ret,
;

pub type Result<T> = std::result::Result<T, Error>;

/// The `Read` trait allows for reading bytes from a source.
///
/// ### Notes on the interface
/// `Read::read()`'s interface is different from `std::io::Read::read()`, in that the buffer is `&mut B where B: ReadBuf` 
/// instead of `&mut [u8]`, and it also accepts an extra argument `range: Option<Range>` for writing to a 
/// subrange of the read buffer. 
/// 
/// This is entirely a workaround for Verus's limited support of `&mut`. In native Rust, the caller 
/// can produce an `&mut` subrange from various actual buffers like `[u8; N]` or `Vec<u8>`. 
/// However, `&mut` at the return position is currently forbidden in Verus, making such an interface 
/// essentially unusable.
/// 
/// We solve this with the `ReadBuf` trait and the separate `range` argument. Implementors of `ReadBuf` 
/// bypass the `&mut` issue by using external operations.
pub trait Read: ReadSpec {

    // Required methods

    /// Pull some bytes from this source into the specified buffer, returning how many bytes were read.
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

    // Provided methods

    /// Reads all bytes until EOF in this source, appending them to `buf`.
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

    /// Reads all bytes until EOF in this source, appending them to `buf`.
    ///
    /// If the data in this stream is not valid UTF-8 then an error is returned and `buf` is unchanged.
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

    /// Reads the exact number of bytes required to fill `buf`.
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
}

/// The `ReadSpec` trait specifies `std::io::Read` by describing the behavior of
/// reading bytes from a source.
/// 
/// This trait should be implemented by types that also implement `std::io::Read`. 
/// Implementors should customize the following basic functions for instance-specific semantics:
/// 
/// * `bytes()`: the remaining bytes that can be read from this source;
/// 
/// * `read_inv()`: invariants of this instance; 
/// 
/// * `read_ok()`: extra *composable* post-conditions for a successful read; 
/// 
/// * `read_err()`: post-conditions for an erroneous read; can be `false` if `read()` cannot fail;
/// 
/// * `read_eof()`: post-conditions after an EOF read; 
/// 
/// ### Understanding EOF
/// `ReadSpec::read_eof()` is intended to *not* be a terminal state (i.e., `read_eof(*old(self))` does not 
/// necessarily imply `read_eof(old(self))`; although for specifc implemenators it does, for example 
/// when `read_eof() <==> self.bytes().len() == 0`). 
/// In fact, `ReadSpec::read_eof(*self)` doesn't even guarantee that the next `read()` will return 0 bytes; 
/// its whole purpose is to expose some extra post-conditions to the caller of `read()`.
pub trait ReadSpec {

    spec fn bytes(&self) -> Seq<u8>;
    open spec fn read_inv(&self) -> bool { true }
    spec fn read_ok(pre_self: &Self, post_self: &Self) -> bool;
    spec fn read_err(error: Error, pre_self: &Self, post_self: &Self) -> bool;
    spec fn read_eof(&self) -> bool;

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

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self)
        requires
            pre_self.read_inv() && mid_self.read_inv() && post_self.read_inv(),
            Self::read_ok(pre_self, mid_self),
            Self::read_ok(mid_self, post_self),
        ensures 
            Self::read_ok(pre_self, post_self),
    ;

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error)
        requires
            pre_self.read_inv() && mid_self.read_inv() && post_self.read_inv(),
            Self::read_ok(pre_self, mid_self),
            Self::read_err(error, mid_self, post_self),
        ensures
            Self::read_err(error, pre_self, post_self),
    ;

}

/// A `BufRead` is a type of reader which has an internal buffer, allowing it to perform extra ways of reading. 
pub trait BufRead: Read + BufReadSpec {

    // Required methods

    /// Returns the contents of the internal buffer, filling it with more data, 
    /// via `Read` methods, if empty.
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

    /// Marks the given amount of additional bytes from the internal buffer as having been read. 
    /// Subsequent calls to `read` only return bytes that have not been marked as read.
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

    // Provided methods

    /// Reads all bytes into `buf` until the delimiter `byte` or EOF is reached.
    ///
    /// This function will read bytes from the underlying stream until the delimiter or EOF is found. 
    /// Once found, all bytes up to, and including, the delimiter (if found) will be appended to `buf`.
    /// If successful, this function will return the total number of bytes read.
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

    /// Skips all bytes until the delimiter `byte` or EOF is reached.
    /// 
    /// This function will read (and discard) bytes from the underlying stream until the delimiter or EOF is found.
    /// If successful, this function will return the total number of bytes read, including the delimiter byte if found.
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

    /// Reads all bytes until a newline (the `0xA` byte) is reached, and append them to the provided `String` buffer.
    ///
    /// This function will read bytes from the underlying stream until the newline delimiter (the 0xA byte) or EOF is found. 
    /// Once found, all bytes up to, and including, the delimiter (if found) will be appended to buf.
    /// If successful, this function will return the total number of bytes read.
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
}

/// The `BufReadSpec` trait specifies `std::io::BufRead` by describing the behavior of 
/// buffered reading.
///
/// The specification is based on `Read` and `Read::bytes()`, with the addition of the
/// `buffer()` spec function to represent buffering semantics.
pub trait BufReadSpec: ReadSpec {

    spec fn buffer(&self) -> Seq<u8>;

    open spec fn consume_extra_ensures(
        pre_self: &Self, post_self: &Self, amt: usize
    ) -> bool { true }

    proof fn buffer_is_prefix_of_bytes(inst: &Self)
        requires    
            inst.read_inv(),
        ensures 
            inst.buffer().is_prefix_of(inst.bytes()),
    ;

}

/// The `Write` trait is for objects which are byte-oriented sinks.
pub trait Write: WriteSpec + Sized {

    // Required methods

    /// Writes a buffer into this writer, returning how many bytes were written.
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

    /// Flushes this output stream, ensuring that all intermediately buffered contents reach their destination.
    ///
    /// It is considered an error if not all bytes could be written due to I/O errors or EOF being reached.
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

    // Provided methods

    /// Attempts to write an entire buffer into this writer.
    ///
    /// If the buffer contains no data, this will never call write.
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

}

/// The `WriteSpec` trait specifies `std::io::Write` by describing the behavior of
/// writing bytes to a (potentially buffered) sink.
///
/// This trait should be implemented by types that also implement `std::io::Write`. 
/// Implementors should customize the following basic functions for instance-specific semantics:
/// 
/// * `bytes()`: the bytes currently in the sink.
///
/// * `buffer()`: the bytes in the buffer (also considered "in the sink").
/// 
/// * `write_inv()`: invariants of this instance; 
/// 
/// * `write_ok()`: extra *composable* post-conditions for a successful write;
/// 
/// * `write_err()`: post-conditions for an erroneous write; can be `false` if `write()` cannot fail;
///
/// * `write_eof()`: post-conditions after an EOF write; 
/// 
/// ### `flush()` and Buffering
/// `Write` is more like `BufRead` (compared to `Read`) in the sense that it assumes buffering 
/// capabilities of a sink. If a sink is buffered, then asserting that `Write::bytes()` contains 
/// some sequence of bytes (i.e., the sequence is "in the sink") does not prove that the sequence 
/// is truly "written" - you must also prove that the sequence is not in the buffer, which is 
/// only possible by calling the `flush()` method on buffered sinks. Meanwhile, unbuffered sinks 
/// should be specified in a way where `Write::buffer()` is always empty.
pub trait WriteSpec {
    
    spec fn bytes(&self) -> Seq<u8>;
    spec fn buffer(&self) -> Seq<u8>;
    open spec fn write_inv(&self) -> bool { true }
    spec fn write_ok(pre_self: &Self, post_self: &Self) -> bool;
    spec fn write_err(error: Error, pre_self: &Self, post_self: &Self) -> bool;
    spec fn write_eof(&self) -> bool;

    open spec fn write_ok_extra_ensures(pre_self: &Self, post_self: &Self, buf: Seq<u8>, res: Result<usize>) -> bool 
        { true }

    open spec fn flush_extra_ensures(pre_self: &Self, post_self: &Self, res: Result<()>) -> bool 
        { true }

    proof fn buffer_is_suffix_of_bytes(inst: &Self)
        requires
            inst.write_inv(),
        ensures
            inst.buffer().is_suffix_of(inst.bytes()),
    ;

    proof fn write_ok_is_reflexive(inst: &Self)
        requires
            inst.write_inv(),
        ensures
            Self::write_ok(inst, inst),
    ;

    proof fn write_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self)
        requires
            pre_self.write_inv() && mid_self.write_inv() && post_self.write_inv(),
            Self::write_ok(pre_self, mid_self),
            Self::write_ok(mid_self, post_self),
        ensures 
            Self::write_ok(pre_self, post_self),
    ;

    proof fn write_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error)
        requires
            pre_self.write_inv() && mid_self.write_inv() && post_self.write_inv(),
            Self::write_ok(pre_self, mid_self),
            Self::write_err(error, mid_self, post_self),
        ensures
            Self::write_err(error, pre_self, post_self),
    ;

}

/// Enables `std::io::Empty`.
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExEmpty(Empty);
pub assume_specification[ std::io::empty ]() -> Empty
    no_unwind
;

/// Enables `std::io::Repeat`.
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExRepeat(Repeat);
pub trait RepeatSpec {
    spec fn byte(&self) -> u8;
}
impl RepeatSpec for Repeat {
    uninterp spec fn byte(&self) -> u8;
}
pub assume_specification[ std::io::repeat ](b: u8) -> (ret: Repeat)
    ensures ret.byte() == b,
    no_unwind
;

/// Enables `std::io::BufReader`.
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(R)]
pub struct ExBufReader<R: ?Sized>(BufReader<R>);
pub trait BufReaderSpec<R: ?Sized> {
    /// Invariant of `BufReader`.
    open spec fn inv(&self) -> bool {
        &&& 0 <= self.pos() <= self.filled() <= spec_slice_len(self.buf())
        &&& spec_slice_len(self.buf()) > 0
    }

    /// In-use region of the internal buffer.
    #[verifier::inline]
    open spec fn valid_buf(&self) -> Seq<u8> {
        self.buf()@.subrange(self.pos(), self.filled())
    }

    /// The full internal buffer.
    spec fn buf(&self) -> &[u8];

    /// Start offset of the in-use buffer range.
    spec fn pos(&self) -> int;

    /// End offset of the in-use buffer range.
    spec fn filled(&self) -> int;

    /// Underlying reader instance.
    spec fn inner(&self) -> &R;
}
impl<R: ?Sized> BufReaderSpec<R> for BufReader<R> {
    uninterp spec fn buf(&self) -> &[u8];
    uninterp spec fn pos(&self) -> int;
    uninterp spec fn filled(&self) -> int;
    uninterp spec fn inner(&self) -> &R;
}
pub assume_specification<R: std::io::Read>[ BufReader::new ](inner: R) -> (ret: BufReader<R>)
    ensures
        ret.inv(),
        ret.pos() == 0,
        ret.filled() == 0,
        *ret.inner() == inner,
;
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
pub assume_specification<R: ?Sized>[ BufReader::get_ref ](r: &BufReader<R>) -> (ret: &R)
    requires
        r.inv(),
    ensures
        ret == r.inner(),
;
pub assume_specification<R: ?Sized>[ BufReader::buffer ](r: &BufReader<R>) -> (ret: &[u8])
    requires
        r.inv(),
    ensures
        ret@ =~= r.valid_buf(),
;
pub assume_specification<R: ?Sized>[ BufReader::capacity ](r: &BufReader<R>) -> (ret: usize)
    requires
        r.inv(),
    ensures
        ret == spec_slice_len(r.buf()),
;
/// XXX: this is a workaround for an issue of `assume_specification` when the trait bound is `Sized + ?Sized`.
pub trait BufReaderIntoInnerFns<R: Read + Sized> {
    fn into_inner(self) -> R;
}
impl<R: Read + Sized> BufReaderIntoInnerFns<R> for BufReader<R> {
    #[verifier::external_body]
    fn into_inner(self) -> (ret: R)
        ensures
            self.inv() ==> ret == *self.inner(),
    {
        self.into_inner()
    }
}

/// Enables `std::io::BufWriter`.
///
/// ### `Drop` and Flushing
/// In native Rust, the buffer of a `BufWriter` is flushed whenever the writer itself goes out of scope, 
/// using a custom `Drop::drop` implementation, which Verus does not yet support.
/// While this does potentially creates a discrepancy between specification and actual program states, 
/// it will only matter when those inner sink states are part of some `spec`. And when they are, `Write`'s
/// specification will in fact not derive anything specific about the inner sink (e.g., how much bytes are 
/// truly written) without inspecting or flushing the buffer in `exec` code; thus there is no real soundness issue here.
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(W)]
pub struct ExBufWriter<W: ?Sized + std::io::Write>(BufWriter<W>);
pub trait BufWriterSpec<W: ?Sized> {
    /// Invariant of `BufWriter`.
    open spec fn inv(&self) -> bool {
        &&& 0 <= self.pos() <= spec_slice_len(self.buf())
        &&& spec_slice_len(self.buf()) > 0
    }

    /// In-use region of the internal buffer.
    #[verifier::inline]
    open spec fn valid_buf(&self) -> Seq<u8> {
        self.buf()@.take(self.pos())
    }

    /// The full internal buffer.
    spec fn buf(&self) -> &[u8];

    /// End offset of the in-use buffer range.
    spec fn pos(&self) -> int;

    /// Underlying writer instance.
    spec fn inner(&self) -> &W;
}
impl<W: ?Sized + std::io::Write> BufWriterSpec<W> for BufWriter<W> {
    uninterp spec fn buf(&self) -> &[u8];
    uninterp spec fn pos(&self) -> int;
    uninterp spec fn inner(&self) -> &W;
}
pub assume_specification<W: std::io::Write>[ BufWriter::new ](inner: W) -> (ret: BufWriter<W>)
    ensures
        ret.inv(),
        ret.pos() == 0,
        *ret.inner() == inner,
;
pub assume_specification<W: std::io::Write>[ BufWriter::with_capacity ](cap: usize, inner: W) -> (ret: BufWriter<W>)
    requires
        cap > 0,
    ensures
        ret.inv(),
        spec_slice_len(ret.buf()) == cap,
        ret.pos() == 0,
        *ret.inner() == inner,
;
pub assume_specification<W: ?Sized + std::io::Write>[ BufWriter::get_ref ](w: &BufWriter<W>) -> (ret: &W)
    requires
        w.inv(),
    ensures
        ret == w.inner(),
;
pub assume_specification<W: ?Sized + std::io::Write>[ BufWriter::buffer ](w: &BufWriter<W>) -> (ret: &[u8])
    requires
        w.inv(),
    ensures
        ret@ =~= w.valid_buf(),
;
pub assume_specification<W: ?Sized + std::io::Write>[ BufWriter::capacity ](w: &BufWriter<W>) -> (ret: usize)
    requires
        w.inv(),
    ensures
        ret == spec_slice_len(w.buf()),
;
pub trait BufWriterIntoInnerFns<W: Write + std::io::Write> {
    fn into_inner(self) -> std::result::Result<W, IntoInnerError<BufWriter<W>>>;
}
impl<W: Write + std::io::Write> BufWriterIntoInnerFns<W> for BufWriter<W> {
    #[verifier::external_body]
    fn into_inner(self) -> (ret: std::result::Result<W, IntoInnerError<BufWriter<W>>>)
        ensures
            self.inv() ==> {
                match ret {
                    // `flush` on destruction
                    Ok(ret) => {
                        &&& ret.write_inv()
                        &&& ret.bytes() =~= self.bytes()
                        &&& W::write_ok(self.inner(), &ret)
                    },
                    Err(e) => {
                        &&& e.into_inner().write_inv()
                        &&& e.into_inner().bytes() =~= self.bytes()
                        &&& WriteSpec::buffer(&e.into_inner()).len() <= WriteSpec::buffer(&self).len()
                        &&& W::write_err(e.into_error(), self.inner(), e.into_inner().inner())
                        &&& e.into_error().kind() != ErrorKind::Interrupted
                        &&& e.into_error().kind() == ErrorKind::WriteZero
                            ==> e.into_inner().write_eof()
                    },
                }
            },
    {
        self.into_inner()
    }
}


/// Enables `std::io::LineWriter`.
///
/// ### `Drop` and Flushing
/// See the comments on `BufWriter` for the issue on `LineWriter`'s drop specification.
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(W)]
pub struct ExLineWriter<W: ?Sized + std::io::Write>(LineWriter<W>);
pub trait LineWriterSpec<W: ?Sized> {
    /// Invariant of `LineWriter`.
    open spec fn inv(&self) -> bool {
        &&& 0 <= self.pos() <= spec_slice_len(self.buf())
        &&& spec_slice_len(self.buf()) > 0
        &&& !self.valid_buf().contains(0xA)
    }

    /// In-use region of the internal buffer.
    #[verifier::inline]
    open spec fn valid_buf(&self) -> Seq<u8> {
        self.buf()@.take(self.pos())
    }

    /// The full internal buffer.
    spec fn buf(&self) -> &[u8];

    /// End offset of the in-use buffer range.
    spec fn pos(&self) -> int;

    /// Underlying writer instance.
    spec fn inner(&self) -> &W;
}
impl<W: ?Sized + std::io::Write> LineWriterSpec<W> for LineWriter<W> {
    uninterp spec fn buf(&self) -> &[u8];
    uninterp spec fn pos(&self) -> int;
    uninterp spec fn inner(&self) -> &W;
}
pub assume_specification<W: std::io::Write>[ LineWriter::new ](inner: W) -> (ret: LineWriter<W>)
    ensures
        ret.inv(),
        ret.pos() == 0,
        *ret.inner() == inner,
;
pub assume_specification<W: std::io::Write>[ LineWriter::with_capacity ](cap: usize, inner: W) -> (ret: LineWriter<W>)
    requires
        cap > 0,
    ensures
        ret.inv(),
        spec_slice_len(ret.buf()) == cap,
        ret.pos() == 0,
        *ret.inner() == inner,
;
pub assume_specification<W: ?Sized + std::io::Write>[ LineWriter::get_ref ](w: &LineWriter<W>) -> (ret: &W)
    requires
        w.inv(),
    ensures
        ret == w.inner(),
;
pub trait LineWriterIntoInnerFns<W: Write + std::io::Write> {
    fn into_inner(self) -> std::result::Result<W, IntoInnerError<LineWriter<W>>>;
}
impl<W: Write + std::io::Write> LineWriterIntoInnerFns<W> for LineWriter<W> {
    #[verifier::external_body]
    fn into_inner(self) -> (ret: std::result::Result<W, IntoInnerError<LineWriter<W>>>)
        ensures
            self.inv() ==> {
                match ret {
                    // `flush` on destruction
                    Ok(ret) => {
                        &&& ret.write_inv()
                        &&& ret.bytes() =~= self.bytes()
                        &&& W::write_ok(self.inner(), &ret)
                    },
                    Err(e) => {
                        &&& e.into_inner().write_inv()
                        &&& e.into_inner().bytes() =~= self.bytes()
                        &&& WriteSpec::buffer(&e.into_inner()).len() <= WriteSpec::buffer(&self).len()
                        &&& W::write_err(e.into_error(), self.inner(), e.into_inner().inner())
                        &&& e.into_error().kind() != ErrorKind::Interrupted
                        &&& e.into_error().kind() == ErrorKind::WriteZero
                            ==> e.into_inner().write_eof()
                    },
                }
            },
    {
        self.into_inner()
    }
}

/// Enables `std::io::Cursor`.
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(T)]
pub struct ExCursor<T>(Cursor<T>);
pub trait CursorSpec<T> {

    /// Invariant of `Cursor`.
    /// 
    /// NOTE: Verge restricts the cursor to always fit within `usize`, not `u64`.
    open spec fn inv(&self) -> bool {
        self.pos() <= usize::MAX
    }

    /// The current cursor position of the in-memory buffer.
    spec fn pos(&self) -> nat;

    /// Underlying buffer instance.
    spec fn inner(&self) -> &T;
}
impl<T> CursorSpec<T> for Cursor<T> {
    uninterp spec fn pos(&self) -> nat;
    uninterp spec fn inner(&self) -> &T;
}

/// Enables `Cursor::<T>::new()`.
pub assume_specification<T>[ Cursor::new ](inner: T) -> (ret: Cursor<T>)
    ensures
        ret.inv(),
        ret.pos() == 0,
        *ret.inner() == inner,
    no_unwind
;

/// Enables `Cursor::<T>::into_inner()`.
pub assume_specification<T>[ Cursor::into_inner ](this: Cursor<T>) -> (ret: T)
    requires
        this.inv(),
    ensures
        ret == *this.inner(),
    no_unwind
;

/// Enables `Cursor::<T>::get_ref()`.
pub assume_specification<T>[ Cursor::get_ref ](this: &Cursor<T>) -> (ret: &T)
    requires
        this.inv(),
    ensures
        *ret == *this.inner(),
    no_unwind
;

/// Enables `Cursor::<T>::position()`.
pub assume_specification<T>[ Cursor::position ](this: &Cursor<T>) -> (ret: u64)
    requires
        this.inv(),
    ensures
        ret == this.pos(),
    no_unwind
;

/// Enables `Cursor::<T>::set_position()`.
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

// `Clone` for I/O types

pub assume_specification[ <ErrorKind as Clone>::clone ](this: &ErrorKind) -> (ret: ErrorKind) 
    ensures
        ret == *this,
;

pub assume_specification[ <Empty as Clone>::clone ](this: &Empty) -> (ret: Empty) 
    ensures
        ret == *this,
;

pub assume_specification<T: Clone>[ <Cursor<T> as Clone>::clone ](this: &Cursor<T>) -> (ret: Cursor<T>) 
    ensures
        ret == *this,
;

mod tests {
    use super::*;
    // TODO(rilin): test more functions
}

} // verus!