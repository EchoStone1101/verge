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
use vstd::slice::slice_subrange;
use vstd::std_specs::result::{spec_unwrap, spec_unwrap_err};
use vstd::std_specs::vec::axiom_spec_len;
use vstd::math::min;

use core::ops::Range;
use std::collections::VecDeque;
use std::io::{Error, ErrorKind};
use std::mem::MaybeUninit;

verus! {

const PROBE_SIZE: usize = 32;
const DEFAULT_READ_BUFSIZE: usize = 32768;

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

    // Required methods
    spec fn bytes(&self) -> Seq<u8>;
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
                        &&& Self::read_ok(nread as nat, *old(self), *self)
                        &&& end - start > 0 && nread == 0 ==> Self::read_eof(*self) 
                    }),
                    Err(e) => ({
                        &&& self.bytes() =~= old(self).bytes() 
                        &&& buf@ =~= old(buf)@
                        &&& spec_error_kind(e) == ErrorKind::Interrupted ==> Self::read_ok(0, *old(self), *self)
                        &&& spec_error_kind(e) != ErrorKind::UnexpectedEof // not returned in base `read`
                        // ^ basic error semantics
                        &&& Self::read_err(e, *old(self), *self)
                    })
                }
            }),
    ;
    open spec fn read_inv(&self) -> bool { true }
    spec fn read_ok(nread: nat, pre_self: Self, post_self: Self) -> bool;
    spec fn read_err(error: Error, pre_self: Self, post_self: Self) -> bool;
    spec fn read_eof(inst: Self) -> bool;

    proof fn read_ok_is_reflexive(inst: Self)
        ensures 
            Self::read_ok(0, inst, inst),
    ;

    proof fn read_ok_is_composable(
        pre_self: Self, nread1: nat, 
        mid_self: Self, nread2: nat, 
        post_self: Self,
    )
        requires
            Self::read_ok(nread1, pre_self, mid_self),
            Self::read_ok(nread2, mid_self, post_self),
        ensures 
            Self::read_ok(nread1 + nread2, pre_self, post_self),
    ;

    proof fn read_ok_err_are_composable(
        pre_self: Self, nread: nat, 
        mid_self: Self, error: Error,
        post_self: Self,
    )
        requires
            Self::read_ok(nread, pre_self, mid_self),
            Self::read_err(error, mid_self, post_self),
        ensures
            Self::read_err(error, pre_self, post_self),
    ;

}

/// Defines additional ways based on `Read::read()`.
pub trait ReadAdditionalSpecs: Read {

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
                        &&& nread <= old(self).bytes().len() && buf@.len() >= old(buf)@.len() + nread 
                        &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread as int) 
                        &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                        &&& Self::read_ok(nread as nat, *old(self), *self)
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
                Self::read_ok(0, *old(self), *self),
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
                            &&& Self::read_ok(0, *old(self), *self)
                        }),
                        Ok(nread) => ({
                            &&& 0 < nread <= old(self).bytes().len() && nread <= PROBE_SIZE
                            &&& probe@.take(nread as int) =~= old(self).bytes().take(nread as int) 
                            &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                            &&& Self::read_ok(nread as nat, *old(self), *self)
                        }),
                    }
                }),
        {
            let ghost mid_self: Self = *self;
            match self.read(&mut probe, None) {
                Ok(nread) => {
                    proof {
                        Self::read_ok_is_composable(
                            *old(self), 0, mid_self, nread as nat, *self,
                        )
                    }
                    res = Ok(nread);
                    break;
                }
                Err(e) => {
                    if matches!(e.kind(), ErrorKind::Interrupted) {
                        proof {
                            Self::read_ok_is_composable(
                                *old(self), 0, mid_self, 0, *self,
                            )
                        }
                        continue;
                    }
                    proof {
                        Self::read_ok_err_are_composable(
                            *old(self), 0, mid_self, e, *self,
                        )
                    }
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
                            &&& Self::read_ok(nread as nat, *old(self), *self)
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
                            &&& Self::read_ok(nread as nat, *old(self), *self)
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
            
            if buf.buf_len() - start < DEFAULT_READ_BUFSIZE {
                // Ensure that `buf` has at least `DEFAULT_READ_BUFSIZE` free space
                vec_grow(buf, start + DEFAULT_READ_BUFSIZE - buf.buf_len());
            }
            let end = start + DEFAULT_READ_BUFSIZE;
            
            assert(buf@.take(ofs + nread as int) =~= old(buf)@ + old(self).bytes().take(nread as int));
            match self.read(buf, Some(start..end)) {
                Ok(more) => {
                    proof {
                        Self::read_ok_is_composable(
                            *old(self), spec_unwrap(res) as nat,
                            mid_self, more as nat,
                            *self,
                        )
                    }
                    if more == 0 {
                        buf.truncate(ofs + nread);
                        break;
                    }
                    res = Ok(nread + more);
                },
                Err(e) => {
                    if matches!(e.kind(), ErrorKind::Interrupted) {
                        proof {
                            Self::read_ok_is_composable(
                                *old(self), spec_unwrap(res) as nat,
                                mid_self, 0,
                                *self,
                            )
                        }
                        continue;
                    }
                    proof {
                        Self::read_ok_err_are_composable(
                            *old(self), spec_unwrap(res) as nat,
                            mid_self, e,
                            *self,
                        )
                    }
                    buf.truncate(ofs + *res.as_ref().unwrap());
                    res = Err(e);
                    break;
                }
            }
        }
        res
    }

    /// NOTE: this function appends to `buf` rather than overwriting it as in `Read::read()`.
    fn read_to_string(&mut self, buf: &mut String) -> (res: Result<(usize)>) 
    {
        // XXX(xyx): implement once `string` is ready
        assume(false);
        unreached()
    }

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
                        &&& Self::read_ok(old(buf)@.len(), *old(self), *self)
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
                            &&& Self::read_ok(nread as nat, *old(self), *self)
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
                        &&& Self::read_ok(old(buf)@.len(), *old(self), *self)
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
                    proof {
                        Self::read_ok_is_composable(
                            *old(self), start as nat,
                            mid_self, nread as nat,
                            *self,
                        )
                    }
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
                        proof {
                            Self::read_ok_is_composable(
                                *old(self), start as nat,
                                mid_self, 0,
                                *self,
                            )
                        }
                        continue;
                    }
                    proof {
                        Self::read_ok_err_are_composable(
                            *old(self), start as nat,
                            mid_self, e,
                            *self,
                        )
                    }
                    res = Err(e);
                    break;
                }
            }
        }
        res?;
        Ok(())
    }
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



} // verus!