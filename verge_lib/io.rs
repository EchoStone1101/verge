//! Specifications and lemmas for `std`-based I/O functionality.
//!
//! The `verge::io` module lays down the general abstraction for inputting 
//! and outputting data from various sources. The overall API design mimicks 
//! `std::io` (https://doc.rust-lang.org/std/io/index.html), but the interface 
//! is kept deliberately minimal.
//! 
//! The core of this module includes the `ExRead` and `ExWrite` traits, as well as 
//! the access to `stdin`, `stdout`, and `stderr`.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::std_specs::result::spec_unwrap;
use vstd::slice::slice_subrange;
use vstd::math::min;

use std::collections::VecDeque;
use std::io::Error;

verus! {

const DEFAULT_READ_BUFSIZE: usize = 32768;

pub mod stdio;
pub mod impls;

pub use impls::*;

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExError(Error);

pub type Result<T> = std::result::Result<T, Error>;

/// The `Read` trait allows for reading bytes from a source.
/// 
/// The design of this trait is generally similar to `std::io::Read` (https://doc.rust-lang.org/std/io/trait.Read.html).
/// In fact, `Read` is intended to be generally implementable for any type that implements `std::io::Read`.
/// `read_ok_basic()` specifies the basic reading semantics in `spec` mode; implementors then customize 
/// the following functions for instance-specific semantics:
/// 
/// * `bytes()`: the remaining bytes that can be read from this source;
/// 
/// * `read_inv()`: invariants of this instance; by default it is only upheld when `read()` returns `Ok`, 
///   in case that an erroneous read corrupts future reads;
/// 
/// * `read_ok()`: extra post-conditions for a successful read; for example, `&[u8]` as a `Read` instance will
///   not return short reads.
/// 
/// * `read_err()`: post-conditions for an erroneous read; can be `false` if `read()` cannot fail;
/// 
/// * `read_eof()`: post-conditions after an EOF read; to avoid non-termination, `read_eof()` MUST NOT be 
///   always `false`; note that this means `Read` cannot be implemented for true endless sources like `std::io::Repeat`.
pub trait Read: Sized {

    // Required methods
    spec fn bytes(&self) -> Seq<u8>;
    fn read<B: ReadBuf>(&mut self, buf: &mut B) -> (res: Result<usize>)
        requires 
            old(self).read_inv(),
        ensures
            ({
                match res {
                    Ok(nread) => ({
                        &&& read_ok_basic(nread as nat, old(self).bytes(), old(buf)@, self.bytes(), buf@)
                        &&& self.read_inv()
                        &&& Self::read_ok(nread as nat, *old(self), *self)
                        &&& buf@.len() > 0 ==> ({
                            &&& nread == 0 ==> Self::read_eof(*old(self))
                            &&& Self::read_eof(*old(self)) ==> Self::read_eof(*self) 
                        })
                    }),
                    Err(error) => Self::read_err(error, *old(self), *self),
                }
            }),
    ;
    open spec fn read_inv(&self) -> bool { true }
    spec fn read_ok(nread: nat, pre_self: Self, post_self: Self) -> bool;
    spec fn read_err(error: Error, pre_self: Self, post_self: Self) -> bool;
    spec fn read_eof(inst: Self) -> bool;

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

    fn read_eof_is_possible()
        ensures 
            exists|inst: Self| Self::read_eof(inst),
    ;

    // Provided methods

    // fn read_to_string(&mut self, buf: &mut String) -> Result<usize> { ... }

    // fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> { ... }


}

pub open spec fn read_ok_basic(
    nread: nat, pre_bytes: Seq<u8>, pre_buf: Seq<u8>, post_bytes: Seq<u8>, post_buf: Seq<u8>, 
) -> bool {
    &&& pre_bytes.len() <= usize::MAX // prevents overflow
    &&& nread <= pre_bytes.len() && nread <= pre_buf.len()
    &&& post_buf =~= pre_bytes.take(nread as int) + pre_buf.skip(nread as int)
    &&& post_bytes =~= pre_bytes.skip(nread as int)
}

/// Defines additional ways based on `Read::read()`.
pub trait ReadAdditionalSpecs: Read {

    /// NOTE: this function appends to `buf` rather than overwriting it as in `Read::read()`.
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> (res: Result<usize>)
        requires 
            old(self).read_inv(),
        ensures
            ({
                match res {
                    Ok(nread) => ({
                        &&& self.read_inv()
                        &&& Self::read_eof(*self)
                        &&& nread <= old(self).bytes().len() 
                        &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread as int) 
                        &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                        &&& Self::read_ok(nread as nat, *old(self), *self)
                    }),
                    Err(error) => Self::read_err(error, *old(self), *self),
                }
            }),
    {
        // TODO(xyx): the current implementation allocates on stack, and involves twice as much copying.
        // The `std::io` implementation (https://doc.rust-lang.org/src/std/io/mod.rs.html#409).
        // However porting that version involves some more work and is not priority right now. 
        let mut tmp = [0u8; DEFAULT_READ_BUFSIZE];
        let nread = self.read(&mut tmp)?;
        if nread == 0 {
            // Already EOF
            return Ok(0);
        }
        buf.extend_from_slice(slice_subrange(tmp.as_slice(), 0, nread));

        let mut res: Result<usize> = Ok(nread);
        loop 
            invariant_except_break
                res.is_ok(),
                ({
                    match res {
                        Ok(nread) => ({
                            &&& self.read_inv() 
                            &&& old(self).bytes().len() <= usize::MAX
                            &&& nread <= old(self).bytes().len() 
                            &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread as int) 
                            &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                            &&& Self::read_ok(nread as nat, *old(self), *self)
                        }),
                        _ => false,
                    }
                }),
            ensures 
                ({
                    match res {
                        Ok(nread) => ({
                            &&& self.read_inv()
                            &&& Self::read_eof(*self)
                            &&& nread <= old(self).bytes().len() 
                            &&& buf@ =~= old(buf)@ + old(self).bytes().take(nread as int) 
                            &&& self.bytes() =~= old(self).bytes().skip(nread as int)
                            &&& Self::read_ok(nread as nat, *old(self), *self)
                        }),
                        Err(error) => Self::read_err(error, *old(self), *self),
                    }
                }),
            decreases self.bytes().len(),
        {
            let ghost mid_self: Self = *self;
            match self.read(&mut tmp) {
                Ok(nread) => {
                    proof {
                        Self::read_ok_is_composable(
                            *old(self), spec_unwrap(res) as nat,
                            mid_self, nread as nat,
                            *self,
                        )
                    }
                    if nread == 0 {
                        break;
                    }
                    res = Ok(res.unwrap() + nread);
                    buf.extend_from_slice(slice_subrange(tmp.as_slice(), 0, nread));
                },
                Err(e) => {
                    proof {
                        Self::read_ok_err_are_composable(
                            *old(self), spec_unwrap(res) as nat,
                            mid_self, e,
                            *self,
                        )
                    }
                    res = Err(e);
                    break;
                }
            }
        }
        res
    }
}

/// The `ReadBuf` trait defines types that can be used as the destination buffer for `Read::read`.
/// 
/// This trait exists mainly as a workaround for Verus's limited support of `&mut`. In native Rust
/// `Read::read` just takes `&mut [u8]`, which the caller can produce from various actual buffers 
/// like `[u8; N]` or `Vec<u8>`. However, `&mut` at the return position is currently forbidden in 
/// Verus, making such an interface essentially unusable.
/// 
/// Implementors of `ReadBuf` bypass this issue by using external operations. The soundness impact 
/// is minimized to the implementations themselves.
pub trait ReadBuf: View<V = Seq<u8>> {
    /// `ReadBuf::read_from` always overwrites `self`.
    fn read_from(&mut self, src: &[u8]) -> (nread: usize)
        ensures
            src.len() <= old(self)@.len() ==> self@ =~= src@ + old(self)@.skip(src@.len() as int),
            src.len() > old(self)@.len() ==> self@ =~= src@.take(old(self)@.len() as int),
            nread == min(src.len() as int, self@.len() as int),
    ;

    fn fill(&mut self, byte: u8) -> (nfilled: usize)
        ensures
            self@ == seq![byte; old(self)@.len()],
            nfilled == old(self)@.len(),
    ;
}


/// The `Write` trait allows for writing bytes to a sink.
/// 
/// The design of this trait is generally similar to `std::io::Write` (https://doc.rust-lang.org/std/io/trait.Write.html).
/// In fact, `Write` is intended to be implementable for any type that implements `std::io::Write`.
/// This is done by adding the `spec` functions `bytes()`, `write_ok()`, and `write_err()` for specifying the 
/// writing semantics in `spec` mode, 
/// Implementors are free to customize these `spec` functions for proper semantics.
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


} // verus!