//! Specifications and lemmas for `std`-based I/O functionality.
//!
//! The `verge::io` module lays down the general abstraction for inputting 
//! and outputting data from various sources. The overall API design mimicks 
//! `std::io` (https://doc.rust-lang.org/std/io/index.html), but the interface 
//! is kept deliberately minimal.
//! 
//! The core of this module includes the `Read` and `Write` traits, as well as 
//! the access to `stdin`, `stdout`, and `stderr`.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::slice::{slice_subrange, spec_slice_len};
use vstd::std_specs::result::{spec_unwrap, spec_unwrap_err};
use vstd::std_specs::vec::axiom_spec_len;
use vstd::math::min;

use core::ops::Range;
use std::collections::VecDeque;
use std::io::{Error, ErrorKind};
use std::mem::MaybeUninit;

verus! {

const PROBE_SIZE: usize = 32;
const DEFAULT_BUFSIZE: usize = 32768;

pub mod stdio;
pub mod impls;

pub use stdio::{init, Stdin, Stdout, Stderr};
pub use impls::*;

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

pub assume_specification [<Error as From<ErrorKind>>::from](kind: ErrorKind) -> (e: Error)
    ensures spec_error_kind(e) == kind,
;

pub type Result<T> = std::result::Result<T, Error>;

#[verifier::external_body]
fn vec_into_boxed_slice<T>(vec: Vec<T>) -> (ret: Box<[T]>) 
    ensures vec@ =~= ret@
{
    vec.into_boxed_slice()
}

#[verifier::external_body]
fn vec_grow(vec: &mut Vec<u8>, amt: usize)
    requires
        old(vec)@.len() + amt <= usize::MAX,
    ensures 
        vec@.len() == old(vec)@.len() + amt,
        vec@.take(old(vec)@.len() as int) =~= old(vec)@,
{
    if vec.capacity() < vec.len() + amt {
        vec.reserve(vec.len() + amt - vec.capacity());
    }
    unsafe { vec.set_len(vec.len() + amt); }
}

/// The `Read` trait allows for reading bytes from a source.
/// 
/// The design of this trait is generally similar to `std::io::Read` (https://doc.rust-lang.org/std/io/trait.Read.html).
/// In fact, `Read` is intended to be generally implementable for any type that implements `std::io::Read`.
/// Its `ensure` clauses include the basic reading semantics in `spec` mode; implementors then customize 
/// the following functions for instance-specific semantics:
/// 
/// * `bytes()`: the remaining bytes that can be read from this source;
/// 
/// * `read_inv()`: invariants of this instance; 
/// 
/// * `read_ok()`: extra post-conditions for a successful read; for example, `&[u8]` as a `Read` instance will
///   not return short reads.
/// 
/// * `read_err()`: post-conditions for an erroneous read; can be `false` if `read()` cannot fail;
/// 
/// * `read_eof()`: post-conditions after an EOF read; 
///
/// ### Notes on the interface
/// `Read::read()`'s interface is different from `std::io::Read::read()`, in that the buffer is `&mut impl ReadBuf` 
/// instead of `&mut [u8]`, and it also accepts an extra argument `range: Option<Range>` for writing to a 
/// subrange of the read buffer. 
/// 
/// This is entirely a workaround for Verus's limited support of `&mut`. In native Rust, the caller 
/// can produce an `&mut` subrange from various actual buffers like `[u8; N]` or `Vec<u8>`. 
/// However, `&mut` at the return position is currently forbidden in Verus, making such an interface 
/// essentially unusable.
/// 
/// We solve this with the `ReadBuf` trait and the separate `range` argument. Implementors of `ReadBuf` 
/// bypass the `&mut` issue by using external operations. The soundness impact is minimized to the 
/// implementations themselves.
/// 
/// ### Understanding EOF
/// `Read::read_eof()` is intended to *not* be a terminal state (i.e., `read_eof(*old(self))` does not 
/// necessarily imply `read_eof(old(self))`; although for specifc implemenators it does, for example 
/// when `read_eof() <==> self.bytes().len() == 0`). 
/// In fact, `Read::read_eof(*self)` doesn't even guarantee that the next `read()` will return 0 bytes; 
/// its whole purpose is to expose some extra post-conditions to the caller of `read()`.
pub trait Read: Sized {

    spec fn bytes(&self) -> Seq<u8>;

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
                        &&& Self::read_ok(*old(self), *self)
                        &&& end - start > 0 && nread == 0 ==> Self::read_eof(*self) 
                    }),
                    Err(e) => ({
                        &&& self.bytes() =~= old(self).bytes() 
                        &&& buf@ =~= old(buf)@
                        &&& spec_error_kind(e) == ErrorKind::Interrupted ==> Self::read_ok(*old(self), *self)
                        &&& spec_error_kind(e) != ErrorKind::UnexpectedEof // not returned in base `read`
                        // ^ basic error semantics
                        &&& Self::read_err(e, *old(self), *self)
                    })
                }
            }),
    ;
    open spec fn read_inv(&self) -> bool { true }
    spec fn read_ok(pre_self: Self, post_self: Self) -> bool;
    spec fn read_err(error: Error, pre_self: Self, post_self: Self) -> bool;
    spec fn read_eof(inst: Self) -> bool;

    proof fn read_ok_is_reflexive(inst: Self)
        ensures
            Self::read_ok(inst, inst),
    ;

    proof fn read_ok_is_composable(pre_self: Self, mid_self: Self, post_self: Self)
        requires
            Self::read_ok(pre_self, mid_self),
            Self::read_ok(mid_self, post_self),
        ensures 
            Self::read_ok(pre_self, post_self),
    ;

    proof fn read_ok_err_are_composable(pre_self: Self, mid_self: Self, post_self: Self, error: Error)
        requires
            Self::read_ok(pre_self, mid_self),
            Self::read_err(error, mid_self, post_self),
        ensures
            Self::read_err(error, pre_self, post_self),
    ;

}

/// The `ReadBuf` trait defines types that can be used as the destination buffer for `Read::read`.
/// 
/// This trait marked `unsafe` because implementing it necessarily involves external operations 
/// that Verus simply admits.
pub unsafe trait ReadBuf: View<V = Seq<u8>> {
    /// `ReadBuf::read_from` overwrites `self[range]`.
    fn read_from(&mut self, src: &[u8], range: Option<Range<usize>>) -> (nread: usize)
        requires
            match range {
                Some(range) => 0 <= range.start <= range.end <= old(self)@.len(),
                _ => true,
            },
        ensures
            ({
                let (start, end) = match range {
                    Some(range) => (range.start as int, range.end as int),
                    _ => (0int, self@.len() as int),
                }; 
                &&& start + src.len() <= end
                    ==> self@ =~= old(self)@.take(start) + src@ + old(self)@.skip(start + src@.len() as int)
                &&& start + src.len() > end
                    ==> self@ =~= old(self)@.take(start) + src@.take(end - start) + old(self)@.skip(end)
                &&& nread == min(src.len() as int, end - start)
            })
    ;

    fn fill(&mut self, byte: u8, range: Option<Range<usize>>) -> (nbytes: usize)
        requires
            match range {
                Some(range) => 0 <= range.start <= range.end <= old(self)@.len(),
                _ => true,
            },
        ensures
            ({
                let (start, end) = match range {
                    Some(range) => (range.start as int, range.end as int),
                    _ => (0int, self@.len() as int),
                }; 
                &&& self@ =~= old(self)@.take(start) + seq![byte; (end - start) as nat] + old(self)@.skip(end)
                &&& nbytes == end - start
            }),
    ;

    fn buf_len(&self) -> (ret: usize)
        ensures self@.len() == ret,
    ;

    unsafe fn as_mut_ptr(&mut self) -> *mut u8;

}

/// Defines additional ways to read based on `Read`.
pub trait ReadAdditionalFns: Read {

    /// NOTE: this function appends to `buf` rather than overwriting it as in `Read::read()`.
    #[verifier::exec_allows_no_decreases_clause]
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> (res: Result<usize>)
        requires 
            old(self).read_inv(),
            old(buf)@.len() + old(self).bytes().len() <= isize::MAX,
        ensures
            self.read_inv(),
            ({
                match res {
                    Ok(nread) => ({
                        &&& Self::read_eof(*self)
                        &&& nread <= old(self).bytes().len() && buf@.len() == old(buf)@.len() + nread 
                        &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread as int) 
                        &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                        &&& Self::read_ok(*old(self), *self)
                    }),
                    Err(e) => ({
                        let nread = old(self).bytes().len() - self.bytes().len();
                        &&& nread >= 0 
                        &&& self.bytes() =~= old(self).bytes().skip(nread)
                        &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread) 
                        //  ^ bytes already read are in `buf`
                        &&& spec_error_kind(e) != ErrorKind::Interrupted // interrupts are retried
                        &&& Self::read_err(e, *old(self), *self) 
                    }),
                }
            }),
    {
        // XXX(xyx): The `std::io` implementation (https://doc.rust-lang.org/src/std/io/mod.rs.html#409) 
        // is probably more efficient. However porting that version involves some more work and is 
        // not priority right now. 
        let ofs = buf.buf_len();
        let mut probe = [0u8; PROBE_SIZE];
        let mut res: Result<usize> = Ok(0); 
        // An initial loop to probe if already EOF, without touching `buf`
        proof { 
            axiom_spec_len(buf); 
            Self::read_ok_is_reflexive(*self);
        }
        loop 
            invariant_except_break  
                matches!(res, Ok(0usize)),
                self.read_inv(),
                self.bytes() =~= old(self).bytes(),
                Self::read_ok(*old(self), *self),
            ensures 
                self.read_inv(),
                ({
                    match res {
                        Err(e) => ({
                            &&& spec_error_kind(e) != ErrorKind::Interrupted // interrupts are retried
                            &&& self.bytes() =~= old(self).bytes()
                            &&& Self::read_err(e, *old(self), *self)
                        }),
                        Ok(0) => ({
                            &&& Self::read_eof(*self)
                            &&& self.bytes() =~= old(self).bytes()
                            &&& Self::read_ok(*old(self), *self)
                        }),
                        Ok(nread) => ({
                            &&& 0 < nread <= old(self).bytes().len() && nread <= PROBE_SIZE
                            &&& probe@.take(nread as int) =~= old(self).bytes().take(nread as int) 
                            &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                            &&& Self::read_ok(*old(self), *self)
                        }),
                    }
                }),
        {
            let ghost mid_self: Self = *self;
            match self.read(&mut probe, None) {
                Ok(nread) => {
                    proof { Self::read_ok_is_composable(*old(self), mid_self, *self) }
                    res = Ok(nread);
                    break;
                }
                Err(e) => {
                    if matches!(e.kind(), ErrorKind::Interrupted) {
                        proof { Self::read_ok_is_composable(*old(self), mid_self, *self) }
                        continue;
                    }
                    proof { Self::read_ok_err_are_composable(*old(self), mid_self, *self, e) }
                    res = Err(e);
                    break;
                }
            }
        }
        let nread = res?;
        if nread == 0 {
            // Already EOF
            return Ok(0);
        }

        buf.extend_from_slice(slice_subrange(probe.as_slice(), 0, nread));
        let mut res = Ok(nread);
        proof { axiom_spec_len(buf); }

        // Second loop for bulk in-place reads
        loop 
            invariant_except_break
                res.is_ok(),
                self.read_inv(),
                ({
                    match res {
                        Ok(nread) => ({
                            &&& old(buf)@.len() + old(self).bytes().len() <= isize::MAX
                            &&& 0 < nread <= old(self).bytes().len() && ofs == old(buf)@.len() && ofs + nread <= buf@.len() <= usize::MAX
                            &&& buf@.take(ofs + nread as int) =~= old(buf)@ + old(self).bytes().take(nread as int) 
                            &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                            &&& Self::read_ok(*old(self), *self)
                        }),
                        _ => false,
                    }
                }),
            ensures 
                self.read_inv(),
                ({
                    match res {
                        Ok(nread) => ({
                            &&& Self::read_eof(*self) 
                            &&& 0 < nread <= old(self).bytes().len() && buf@.len() >= old(buf)@.len() + nread 
                            &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread as int) 
                            &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                            &&& Self::read_ok(*old(self), *self)
                        }),
                        Err(e) => ({
                            let nread = old(self).bytes().len() - self.bytes().len();
                            &&& nread >= 0 
                            &&& self.bytes() =~= old(self).bytes().skip(nread)
                            &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread) 
                            &&& spec_error_kind(e) != ErrorKind::Interrupted 
                            &&& Self::read_err(e, *old(self), *self)
                        }),
                    }
                }),
        {
            let ghost mid_self: Self = *self;
            let nread = *res.as_ref().unwrap();
            let start = ofs + nread;
            
            if buf.buf_len() - start < DEFAULT_BUFSIZE {
                // Ensure that `buf` has at least `DEFAULT_BUFSIZE` free space
                vec_grow(buf, start + DEFAULT_BUFSIZE - buf.buf_len());
            }
            let end = start + DEFAULT_BUFSIZE;
            
            assert(buf@.take(ofs + nread as int) =~= old(buf)@ + old(self).bytes().take(nread as int));
            match self.read(buf, Some(start..end)) {
                Ok(more) => {
                    proof { Self::read_ok_is_composable(*old(self), mid_self, *self) }
                    if more == 0 {
                        buf.truncate(ofs + nread);
                        break;
                    }
                    res = Ok(nread + more);
                },
                Err(e) => {
                    if matches!(e.kind(), ErrorKind::Interrupted) {
                        proof { Self::read_ok_is_composable(*old(self), mid_self, *self) }
                        continue;
                    }
                    proof { Self::read_ok_err_are_composable(*old(self), mid_self, *self, e) }
                    buf.truncate(ofs + *res.as_ref().unwrap());
                    res = Err(e);
                    break;
                }
            }
        }
        res
    }

    /// NOTE: this function appends to `buf` rather than overwriting it as in `Read::read()`.
    // fn read_to_string(&mut self, buf: &mut String) -> (res: Result<(usize)>)
    // ; // XXX(xyx): implement once `string` is ready

    /// Reads the exact number of bytes required to fill `buf`.
    #[verifier::exec_allows_no_decreases_clause]
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
                        &&& Self::read_ok(*old(self), *self)
                    }),
                    Err(e) if spec_error_kind(e) == ErrorKind::UnexpectedEof => 
                        Self::read_eof(*self),
                    Err(e) => ({
                        &&& spec_error_kind(e) != ErrorKind::Interrupted // interrupts are retried
                        &&& Self::read_err(e, *old(self), *self)
                    }),
                }
            }),
    { 
        proof { Self::read_ok_is_reflexive(*self); }

        if buf.buf_len() == 0 {
            // No need to read anything
            return Ok(());
        }
        let mut res = Ok(0usize);
        loop 
            invariant_except_break
                res.is_ok(),
                self.read_inv(),
                ({
                    match res {
                        Ok(nread) => ({
                            &&& nread <= old(self).bytes().len() && nread < old(buf)@.len()
                            &&& buf@ =~= old(self).bytes().take(nread as int) + old(buf)@.skip(nread as int)
                            &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                            &&& Self::read_ok(*old(self), *self)
                        }),
                        _ => false,
                    }
                }),
            ensures 
                self.read_inv(),
                match res {
                    Ok(_) => ({
                        &&& old(buf)@.len() <= old(self).bytes().len() 
                        &&& buf@ =~= old(self).bytes().take(old(buf)@.len() as int) 
                        &&& self.bytes() =~= old(self).bytes().skip(old(buf)@.len() as int)
                        &&& Self::read_ok(*old(self), *self)
                    }),
                    Err(e) if spec_error_kind(e) == ErrorKind::UnexpectedEof => 
                        Self::read_eof(*self),
                    Err(e) => ({
                        &&& spec_error_kind(e) != ErrorKind::Interrupted // interrupts are retried
                        &&& Self::read_err(e, *old(self), *self)
                    }),
                }
        {
            let ghost mid_self: Self = *self;
            let start = *res.as_ref().unwrap();
            let end = buf.buf_len();
            match self.read(buf, Some(start..end)) {
                Ok(nread) => {
                    proof { Self::read_ok_is_composable(*old(self), mid_self, *self) }
                    if nread == 0 {
                        // No more bytes to read
                        res = Err(Error::from(ErrorKind::UnexpectedEof));
                        break;
                    }
                    if start + nread == end {
                        // Finished
                        break;
                    }
                    res = Ok(start + nread);
                },
                Err(e) => {
                    if matches!(e.kind(), ErrorKind::Interrupted) {
                        proof { Self::read_ok_is_composable(*old(self), mid_self, *self) }
                        continue;
                    }
                    proof { Self::read_ok_err_are_composable(*old(self), mid_self, *self, e) }
                    res = Err(e);
                    break;
                }
            }
        }
        res?;
        Ok(())
    }
}

/// A `BufRead` is a type of reader which has an internal buffer, allowing it to perform extra ways of reading. 
/// 
/// `BufRead`'s specification is based on `Read` and `Read::bytes()`, while adding the `BufRead::buffer() to 
/// represent buffering semantics.
pub trait BufRead: Read {

    spec fn buffer(&self) -> Seq<u8>;

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
                    &&& Self::read_ok(*old(self), *self)
                    &&& buflen == 0 ==> Self::read_eof(*self)
                }),
                Err(e) => ({
                    // effectively one failed `read`
                    &&& old(self).buffer().len() == 0 && self.buffer().len() == 0
                    &&& self.buffer() =~= old(self).buffer()
                    &&& spec_error_kind(e) == ErrorKind::Interrupted ==> Self::read_ok(*old(self), *self)
                    &&& spec_error_kind(e) != ErrorKind::UnexpectedEof
                    &&& Self::read_err(e, *old(self), *self)
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
            Self::read_ok(*old(self), *self),
            Self::read_eof(*old(self)) ==> Self::read_eof(*self),
    ;
        
}

/// Defines additional ways to read based on `BufRead`.
pub trait BufReadAdditionalFns: BufRead {

    /// Reads all bytes into `buf` until the delimiter `byte` or EOF is reached.
    ///
    /// This function will read bytes from the underlying stream until the delimiter or EOF is found. 
    /// Once found, all bytes up to, and including, the delimiter (if found) will be appended to `buf`.
    /// If successful, this function will return the total number of bytes read.
    #[verifier::exec_allows_no_decreases_clause]
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
                        &&& (nread == 0 || buf@.last() != byte) ==> Self::read_eof(*self)
                        &&& Self::read_ok(*old(self), *self)
                    }),
                    Err(e) => ({
                        let nread = old(self).bytes().len() - self.bytes().len();
                        &&& nread >= 0 
                        &&& self.bytes() =~= old(self).bytes().skip(nread)
                        &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread) 
                        &&& forall|i: int| #![auto] old(buf)@.len() <= i < buf@.len() ==> buf[i] != byte 
                        //  ^ bytes already read are in `buf`
                        &&& spec_error_kind(e) != ErrorKind::Interrupted // interrupts are retried
                        &&& Self::read_err(e, *old(self), *self) 
                    }),
                }
            }),
    {
        let mut res: Result<usize> = Ok(0);
        proof { Self::read_ok_is_reflexive(*self); }
        loop 
            invariant_except_break
                self.read_inv(),
                res.is_ok(),
                old(buf)@.len() + old(self).bytes().len() <= isize::MAX,
                ({
                    match res {
                        Ok(nread) => ({
                            &&& nread + self.bytes().len() == old(self).bytes().len() 
                            &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread as int) 
                            &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                            &&& forall|i: int| #![auto] old(buf)@.len() <= i < buf@.len() ==> buf[i] != byte 
                            &&& Self::read_ok(*old(self), *self)
                        }),
                        _ => false,
                    }
                }),
            ensures
                self.read_inv(),
                ({
                    match res {
                        Ok(nread) => ({
                            &&& nread <= old(self).bytes().len()
                            &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread as int) 
                            &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                            &&& forall|i: int| #![auto] old(buf)@.len() <= i < buf@.len() - 1 ==> buf[i] != byte 
                            &&& (nread == 0 || buf@.last() != byte) ==> Self::read_eof(*self)
                            &&& Self::read_ok(*old(self), *self)
                        }),
                        Err(e) => ({
                            let nread = old(self).bytes().len() - self.bytes().len();
                            &&& nread >= 0 
                            &&& self.bytes() =~= old(self).bytes().skip(nread)
                            &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread) 
                            &&& forall|i: int| #![auto] old(buf)@.len() <= i < buf@.len() ==> buf[i] != byte 
                            &&& spec_error_kind(e) != ErrorKind::Interrupted 
                            &&& Self::read_err(e, *old(self), *self) 
                        }),
                    }
                }),
        {
            let ghost mid_self: Self = *self;
            let nread = *res.as_ref().unwrap();
            let (done, used) = {
                let available = match self.fill_buf() {
                    Ok(n) => n,
                    Err(e) => {
                        if matches!(e.kind(), ErrorKind::Interrupted) {
                            proof { Self::read_ok_is_composable(*old(self), mid_self, *self) }
                            continue;
                        }
                        proof { Self::read_ok_err_are_composable(*old(self), mid_self, *self, e) }
                        res = Err(e);
                        return res;
                    },
                };
                proof { 
                    Self::read_ok_is_reflexive(mid_self);
                    Self::read_ok_is_composable(*old(self), mid_self, *self);
                }
                match memchr::memchr(byte, available) {
                    Some(i) => {
                        buf.extend_from_slice(slice_subrange(available, 0, i + 1));
                        (true, i + 1)
                    }
                    None => {
                        buf.extend_from_slice(available);
                        (false, available.len())
                    }
                }
            };
            let ghost mid_self: Self = *self;
            self.consume(used);
            proof { Self::read_ok_is_composable(*old(self), mid_self, *self) }
            res = Ok(nread + used);
            if done || used == 0 {
                return res;
            }
        }
    }

    /// Skips all bytes until the delimiter `byte` or EOF is reached.
    /// 
    /// This function will read (and discard) bytes from the underlying stream until the delimiter or EOF is found.
    /// If successful, this function will return the total number of bytes read, including the delimiter byte if found.
    #[verifier::exec_allows_no_decreases_clause]
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
                        &&& (nread == 0 || old(self).bytes()[nread as int - 1] != byte) ==> Self::read_eof(*self)
                        &&& Self::read_ok(*old(self), *self)
                    }),
                    Err(e) => ({
                        let nread = old(self).bytes().len() - self.bytes().len();
                        &&& nread >= 0 
                        &&& self.bytes() =~= old(self).bytes().skip(nread)
                        &&& forall|i: int| #![auto] 0 <= i < nread ==> old(self).bytes()[i] != byte 
                        &&& spec_error_kind(e) != ErrorKind::Interrupted // interrupts are retried
                        &&& Self::read_err(e, *old(self), *self) 
                    }),
                }
            }),
    {
        let mut res: Result<usize> = Ok(0);
        proof { Self::read_ok_is_reflexive(*self); }
        loop 
            invariant_except_break
                self.read_inv(),
                res.is_ok(),
                old(self).bytes().len() <= isize::MAX,
                ({
                    match res {
                        Ok(nread) => ({
                            &&& nread + self.bytes().len() == old(self).bytes().len() 
                            &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                            &&& forall|i: int| #![auto] 0 <= i < nread ==> old(self).bytes()[i] != byte 
                            &&& Self::read_ok(*old(self), *self)
                        }),
                        _ => false,
                    }
                }),
            ensures
                self.read_inv(),
                ({
                    match res {
                        Ok(nread) => ({
                            &&& nread <= old(self).bytes().len()
                            &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                            &&& forall|i: int| #![auto] 0 <= i < nread as int - 1 ==> old(self).bytes()[i] != byte 
                            &&& (nread == 0 || old(self).bytes()[nread as int - 1] != byte) ==> Self::read_eof(*self)
                            &&& Self::read_ok(*old(self), *self)
                        }),
                        Err(e) => ({
                            let nread = old(self).bytes().len() - self.bytes().len();
                            &&& nread >= 0 
                            &&& self.bytes() =~= old(self).bytes().skip(nread)
                            &&& forall|i: int| #![auto] 0 <= i < nread ==> old(self).bytes()[i] != byte 
                            &&& spec_error_kind(e) != ErrorKind::Interrupted // interrupts are retried
                            &&& Self::read_err(e, *old(self), *self) 
                        }),
                    }
                }),
        {
            let ghost mid_self: Self = *self;
            let nread = *res.as_ref().unwrap();
            let (done, used, available) = {
                let available = match self.fill_buf() {
                    Ok(n) => n,
                    Err(e) => {
                        if matches!(e.kind(), ErrorKind::Interrupted) {
                            proof { Self::read_ok_is_composable(*old(self), mid_self, *self) }
                            continue;
                        }
                        proof { Self::read_ok_err_are_composable(*old(self), mid_self, *self, e) }
                        res = Err(e);
                        return res;
                    },
                };
                proof { 
                    Self::read_ok_is_reflexive(mid_self);
                    Self::read_ok_is_composable(*old(self), mid_self, *self);
                }
                match memchr::memchr(byte, available) {
                    Some(i) => (true, i + 1, available),
                    None => {
                        assert(available@ =~= old(self).bytes().subrange(nread as int, nread + available@.len() as int));
                        (false, available.len(), available)
                    },
                }
            };
            let ghost mid_self: Self = *self;
            self.consume(used);
            proof { Self::read_ok_is_composable(*old(self), mid_self, *self) }
            res = Ok(nread + used);
            assert(forall|i: int| #![auto] nread <= i < nread + used ==> old(self).bytes()[i] == available[(i - nread) as int]);
            if done || used == 0 {
                return res;
            }
        }
    }

    // /// Reads all bytes until a newline (the 0xA byte) is reached, and append them to the provided `String` buffer.
    // ///
    // /// This function will read bytes from the underlying stream until the newline delimiter (the 0xA byte) or EOF is found. 
    // /// Once found, all bytes up to, and including, the delimiter (if found) will be appended to `buf`.
    // /// If successful, this function will return the total number of bytes read.
    // fn read_line(&mut self, buf: &mut String) -> (res: Result<usize>)
    // ;
}

// TODO: Seek & Cursor?
// TODO: StdinLock


/// The `Write` trait allows for writing bytes to a sink.
/// 
/// The design of this trait is generally similar to `std::io::Write` (https://doc.rust-lang.org/std/io/trait.Write.html).
/// In fact, `Write` is intended to be implementable for any type that implements `std::io::Write`.
/// Its `ensure` clauses include the basic writing semantics in `spec` mode; implementors then customize 
/// the following functions for instance-specific semantics:
/// 
/// * `bytes()`: the bytes currently in the sink.
///
/// * `buffer()`: the bytes in the buffer (not yet in the sink).
/// 
/// * `write_inv()`: invariants of this instance; by default it is only upheld when `write()` returns `Ok`, 
///   in case that an erroneous write corrupts future writes;
/// 
/// * `write_ok()`: extra post-conditions for a successful write;
/// 
/// * `write_err()`: post-conditions for an erroneous write; can be `false` if `write()` cannot fail;
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


/// `Empty` ignores any data written via `Write`, and will always be empty (returning zero bytes) 
/// when read via `Read`.
/// This struct is generally created by calling `empty()`.
pub struct Empty;

pub const fn empty() -> Empty {
    Empty
}

/// A reader which yields one byte over and over and over and over and over and...
/// 
/// This struct is generally created by calling `repeat()`. 
pub struct Repeat(u8);

pub const fn repeat(byte: u8) -> (ret: Repeat) 
    ensures ret.byte() == byte,
{
    Repeat(byte)
}

impl Repeat {

    pub closed spec fn byte(&self) -> u8 {
        self.0
    }
}

/// The `BufReader<R>` struct adds buffering to any reader.
pub struct BufReader<R> {
    buf: Box<[u8]>, 
    pos: usize,
    filled: usize,
    inner: R,
}

impl<R> BufReader<R> {

    pub open spec fn inv(&self) -> bool {
        &&& 0 <= self.pos() <= self.filled() <= spec_slice_len(self.buf())
        &&& spec_slice_len(self.buf()) > 0
    }

    pub closed spec fn buf(&self) -> &[u8] {
        &*self.buf
    }

    #[verifier::inline]
    pub open spec fn valid_buf(&self) -> Seq<u8> {
        self.buf()@.subrange(self.pos(), self.filled())
    }

    pub closed spec fn pos(&self) -> int {
        self.pos as int
    }

    pub closed spec fn filled(&self) -> int {
        self.filled as int
    }
}

impl<R: Read> BufReader<R> {

    pub closed spec fn inner(&self) -> R {
        self.inner
    }

    pub fn new(inner: R) -> (ret: BufReader<R>)
        ensures
            ret.inv(),
            ret.inner() == inner,
            ret.pos() == 0,
            ret.filled() == 0,
    {
        BufReader {
            buf: vec_into_boxed_slice(vec![0u8; DEFAULT_BUFSIZE]),
            pos: 0,
            filled: 0,
            inner,
        }
    }

    pub fn with_capacity(capacity: usize, inner: R) -> (ret: BufReader<R>)
        requires
            capacity > 0,
        ensures
            ret.inv(),
            spec_slice_len(ret.buf()) == capacity,
            ret.inner() == inner,
            ret.pos() == 0,
            ret.filled() == 0,
    {
        BufReader {
            buf: vec_into_boxed_slice(vec![0u8; capacity]),
            pos: 0,
            filled: 0,
            inner,
        }
    }

    pub fn get_ref(&self) -> (ret: &R) 
        ensures
            *ret == self.inner(),
    {
        &self.inner
    }

    pub fn buffer(&self) -> (ret: &[u8]) 
        requires
            self.inv(),
        ensures
            ret@ =~= self.valid_buf(),
    {
        slice_subrange(&*self.buf, self.pos, self.filled)
    }

    pub fn capacity(&self) -> (ret: usize)
        ensures
            ret == spec_slice_len(self.buf()),
    {
        self.buf.len()
    }

    /// NOTE: this will discard any bytes not consumed in the internal buffer, 
    /// potentially causing data loss.
    pub fn into_inner(self) -> (ret: R) 
        ensures
            ret == self.inner(),
    {
        self.inner
    }

}

} // verus!