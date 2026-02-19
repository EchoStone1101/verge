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

use core::ops::Range;
use std::collections::VecDeque;
pub use std::io::{
    Error, ErrorKind, Empty, Repeat, BufReader,
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

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExError(Error);

#[verifier::external_type_specification]
pub struct ExErrorKind(ErrorKind);

pub uninterp spec fn spec_error_kind(e: Error) -> ErrorKind;
pub assume_specification[Error::kind](e: &Error) -> (kind: ErrorKind)
    ensures
        spec_error_kind(*e) == kind,
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
                    Ok(nread) => ({
                        &&& nread <= old(self).bytes().len() && nread <= end - start
                        &&& buf@ =~= 
                            old(buf)@.take(start) 
                            + old(self).bytes().take(nread as int) 
                            + old(buf)@.skip(start + nread as int)
                        &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                        // ^ basic read semantics
                        &&& Self::read_ok(old(self), self)
                        &&& end - start > 0 && nread == 0 ==> self.read_eof() 
                    }),
                    Err(e) => ({
                        &&& self.bytes() =~= old(self).bytes() 
                        &&& buf@ =~= old(buf)@
                        &&& spec_error_kind(e) == ErrorKind::Interrupted ==> Self::read_ok(old(self), self)
                        &&& spec_error_kind(e) != ErrorKind::UnexpectedEof // not returned in base `read`
                        // ^ basic error semantics
                        &&& Self::read_err(e, old(self), self)
                    })
                }
            }),
    ;

    // Provided methods

    /// Reads all bytes until EOF in this source, appending them to `buf`.
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> (res: Result<usize>)
        requires 
            old(self).read_inv(),
            old(buf)@.len() + old(self).bytes().len() <= isize::MAX,
        ensures
            self.read_inv(),
            ({
                match res {
                    Ok(nread) => ({
                        &&& self.read_eof()
                        &&& nread <= old(self).bytes().len() && buf@.len() == old(buf)@.len() + nread 
                        &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread as int) 
                        &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                        &&& Self::read_ok(old(self), self)
                    }),
                    Err(e) => ({
                        let nread = old(self).bytes().len() - self.bytes().len();
                        &&& nread >= 0 
                        &&& self.bytes() =~= old(self).bytes().skip(nread)
                        &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread) 
                        //  ^ bytes already read are in `buf`
                        &&& spec_error_kind(e) != ErrorKind::Interrupted // interrupts are retried
                        &&& Self::read_err(e, old(self), self) 
                    }),
                }
            }),
    ;

    // fn read_to_string(&mut self, buf: &mut String) -> (res: Result<(usize)>);

    /// Reads the exact number of bytes required to fill `buf`.
    fn read_exact<B: ReadBuf>(&mut self, buf: &mut B) -> (res: Result<()>) 
        requires 
            old(self).read_inv(),
        ensures
            self.read_inv(),
            ({
                match res {
                    Ok(_) => ({
                        &&& old(buf)@.len() <= old(self).bytes().len() 
                        &&& buf@ =~= old(self).bytes().take(old(buf)@.len() as int) 
                        &&& self.bytes() =~= old(self).bytes().skip(old(buf)@.len() as int)
                        &&& Self::read_ok(old(self), self)
                    }),
                    Err(e) if spec_error_kind(e) == ErrorKind::UnexpectedEof => 
                        self.read_eof(),
                    Err(e) => ({
                        &&& spec_error_kind(e) != ErrorKind::Interrupted // interrupts are retried
                        &&& Self::read_err(e, old(self), self)
                    }),
                }
            }),
    ;
}

/// The `ReadSpec` trait specifies `std::io::Read` by describing the behavior of
/// reading bytes from a source.
/// 
/// This trait should be implemented by types that also implement `std::io::Read`. 
/// Implementors should customize the following functions for instance-specific semantics:
/// 
/// * `bytes()`: the remaining bytes that can be read from this source;
/// 
/// * `read_inv()`: invariants of this instance; 
/// 
/// * `read_ok()`: extra post-conditions for a successful read; 
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
        ensures
            Self::read_ok(inst, inst),
    ;

    proof fn read_ok_is_composable(pre_self: &Self, mid_self: &Self, post_self: &Self)
        requires
            Self::read_ok(pre_self, mid_self),
            Self::read_ok(mid_self, post_self),
        ensures 
            Self::read_ok(pre_self, post_self),
    ;

    proof fn read_ok_err_are_composable(pre_self: &Self, mid_self: &Self, post_self: &Self, error: Error)
        requires
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
                    &&& spec_error_kind(e) == ErrorKind::Interrupted ==> Self::read_ok(old(self), self)
                    &&& spec_error_kind(e) != ErrorKind::UnexpectedEof
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
            old(buf)@.len() + old(self).bytes().len() <= isize::MAX,
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
                        &&& spec_error_kind(e) != ErrorKind::Interrupted // interrupts are retried
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
                        &&& spec_error_kind(e) != ErrorKind::Interrupted // interrupts are retried
                        &&& Self::read_err(e, old(self), self) 
                    }),
                }
            }),
    ;

    // TODO: read_lines and others
        
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
}


// TODO: Seek & Cursor?
// TODO: StdinLock


// /// The `Write` trait allows for writing bytes to a sink.
// /// 
// /// The design of this trait is generally similar to `std::io::Write` (https://doc.rust-lang.org/std/io/trait.Write.html).
// /// In fact, `Write` is intended to be implementable for any type that implements `std::io::Write`.
// /// Its `ensure` clauses include the basic writing semantics in `spec` mode; implementors then customize 
// /// the following functions for instance-specific semantics:
// /// 
// /// * `bytes()`: the bytes currently in the sink.
// ///
// /// * `buffer()`: the bytes in the buffer (not yet in the sink).
// /// 
// /// * `write_inv()`: invariants of this instance; by default it is only upheld when `write()` returns `Ok`, 
// ///   in case that an erroneous write corrupts future writes;
// /// 
// /// * `write_ok()`: extra post-conditions for a successful write;
// /// 
// /// * `write_err()`: post-conditions for an erroneous write; can be `false` if `write()` cannot fail;
// pub trait Write {
//     // Required methods
//     spec fn bytes(&self) -> Seq<u8>;
//     // fn flush(&mut self) -> Result<()>;
//     fn write(&mut self, buf: &[u8]) -> (res: Result<usize>)
//         ensures
//             ({
//                 match res {
//                     Ok(nwritten) => 
//                         nwritten <= buf.len() 
//                         && Self::write_ok(nwritten, old(self), self, buf@.take(nwritten as int)),
//                     Err(error) => Self::write_err(error, old(self), self, buf@),
//                 }
//             }),
//     ;
//     spec fn write_ok(nwritten: usize, pre_self: &Self, post_self: &Self, buf: Seq<u8>) -> bool;
//     spec fn write_err(error: Error, pre_self: &Self, post_self: &Self, buf: Seq<u8>) -> bool;

//     // Provided methods
//     fn write_all(&mut self, buf: &[u8]) -> (res: Result<usize>)
//         ensures
//             ({
//                 match res {
//                     Ok(nwritten) => 
//                         nwritten == buf.len() 
//                         && Self::write_ok(nwritten, old(self), self, buf@),
//                     Err(error) => Self::write_err(error, old(self), self, buf@),
//                 }
//             }),
//     {
//         assume(false);
//         unreached()
//     }
//     // fn by_ref(&mut self) -> &mut Self
//     //    where Self: Sized { ... }
// }

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

} // verus!