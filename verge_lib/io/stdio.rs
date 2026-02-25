//! Specifications and lemmas for standard I/O.
//!
//! Example usage:
//! ```rust
//! let (stdin, stdout, stderr) = verge::io::stdio::init();
//! let mut buf = vec![0u8; 32];
//! stdin.read(&mut buf);
//! stdout.write(&buf);
//! stderr.write("no error\n");
//! ```

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::view::View;
use vstd::std_specs::result::spec_unwrap;
use crate::io::{ReadBuf, Result, ErrorKind, spec_error_kind};

use std::sync::Once;
use core::ops::Range;

verus! {

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExStdin(std::io::Stdin);

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExStdinLock<'a>(std::io::StdinLock<'a>);

pub use std::io::StdinLock as Stdin;

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExStdout(std::io::Stdout);

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExStdoutLock<'a>(std::io::StdoutLock<'a>);

pub use std::io::StdoutLock as Stdout;

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExStderr(std::io::Stderr);

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExStderrLock<'a>(std::io::StderrLock<'a>);

pub use std::io::StderrLock as Stderr;

/// Specification for `std::io::Stdin` (disguised `StdinLock`).
pub trait StdinSpec {
    spec fn inv(&self) -> bool; 
    spec fn stream() -> Seq<u8>;
    spec fn nbyte(&self) -> nat;
    spec fn buf(&self) -> Seq<u8>;
}
impl StdinSpec for Stdin<'static> {

    /// Invariant of `Stdin`.
    open spec fn inv(&self) -> bool {
        &&& self.nbyte() <= Stdin::stream().len()
        &&& self.buf().is_prefix_of(Stdin::stream().skip(self.nbyte() as int))
    }

    /// All input bytes in the input stream, ever.
    uninterp spec fn stream() -> Seq<u8>;

    /// Number of bytes already revealed in the input stream.
    uninterp spec fn nbyte(&self) -> nat;

    /// Bytes in the internal buffer. 
    /// 
    /// NOTE: The actual implementation of `Stdin` is in fact a `BufReader` of `StdinRaw`, 
    /// meaning that there is an internal buffer. Concretely, this has an impact on how many
    /// bytes each `Stdin::read` can pull in one go.  
    /// However, because that buffer is unspecified, there isn't much to leverage in proofs. 
    /// As such, Verge chooses to be completely oblivious of that detail and leave the buffer 
    /// uninterpreted.
    uninterp spec fn buf(&self) -> Seq<u8>;

}

/// Specification for `std::io::Stdout` (disguised `StdoutLock`).
pub trait StdoutSpec {
    spec fn inv(&self) -> bool; 
    spec fn stream() -> Seq<u8>;
    spec fn nbyte(&self) -> nat;
    spec fn buf(&self) -> Seq<u8>;
}
impl StdoutSpec for Stdout<'static> {

    /// Invariant of `Stdout`.
    open spec fn inv(&self) -> bool {
        &&& self.nbyte() <= Stdout::stream().len()
        &&& self.buf().is_suffix_of(Stdout::stream().take(self.nbyte() as int))
        &&& !self.buf().contains(0xA) // `Stdout` flushes on newlines
    }

    /// All output bytes in the output stream, ever.
    uninterp spec fn stream() -> Seq<u8>;

    /// Number of bytes already revealed in the output stream.
    uninterp spec fn nbyte(&self) -> nat;

    /// Bytes in the internal buffer. 
    /// 
    /// NOTE: The actual implementation of `Stdin` is in fact a `LineWriter` of `StdoutRaw`.
    /// See `StdinSpec` for comments on why the buffer is specified this way.
    uninterp spec fn buf(&self) -> Seq<u8>;
}

/// Specification for `std::io::Stderr` (disguised `StderrLock`).
/// 
/// Note that `Stderr` is unbuffered.
pub trait StderrSpec {
    spec fn inv(&self) -> bool; 
    spec fn stream() -> Seq<u8>;
    spec fn nbyte(&self) -> nat;
}
impl StderrSpec for Stderr<'static> {

    /// Invariant of `Stderr`.
    open spec fn inv(&self) -> bool {
        &&& self.nbyte() <= Stderr::stream().len()
    }

    /// All input bytes in the error stream, ever.
    uninterp spec fn stream() -> Seq<u8>;

    /// Number of bytes already revealed in the error stream.
    uninterp spec fn nbyte(&self) -> nat;

}

/// Initialize unique handles for accessing `Stdin`, `Stdout`, and `Stderr`.
///
/// NOTE: this function should not be called multiple times. Any subsequent invocation
/// will result in a panic.
#[verifier::external_body]
pub fn init() -> (ret: (Stdin<'static>, Stdout<'static>, Stderr<'static>))
    ensures
        ret.0.nbyte() == 0,
        ret.0.buf().len() == 0,
        ret.0.inv(),
{
    static STDIO_INIT: Once = Once::new();
    assert!(!STDIO_INIT.is_completed(), "stdio::init() can only be called once");
    STDIO_INIT.call_once(|| {});

    // Locked once, then passed around
    (
        std::io::stdin().lock(),
        std::io::stdout().lock(),
        std::io::stderr().lock(),
    )
}

} // verus!