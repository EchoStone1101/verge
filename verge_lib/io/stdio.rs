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
pub use std::io::{Stdin, Stdout, Stderr};

verus! {

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExStdin(Stdin);

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExStdout(Stdout);

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExStderr(Stderr);

#[verifier::external_body]
fn stdin() -> Stdin {
    std::io::stdin()
}

#[verifier::external_body]
fn stdout() -> Stdout {
    std::io::stdout()
}

#[verifier::external_body]
fn stderr() -> Stderr {
    std::io::stderr()
}

/// Enables `std::io::Stdin`.
pub trait StdinSpec {
    spec fn inv(&self) -> bool; 
    spec fn stream() -> Seq<u8>;
    spec fn nbyte(&self) -> nat;
}
impl StdinSpec for Stdin {

    /// Invariant of `Stdin`.
    open spec fn inv(&self) -> bool {
        self.nbyte() <= Stdin::stream().len()
    }

    /// All input bytes in the input stream, ever.
    uninterp spec fn stream() -> Seq<u8>;

    /// Number of bytes already revealed in the input stream.
    uninterp spec fn nbyte(&self) -> nat;

}

/// Initialize unique handles for accessing `Stdin`, `Stdout`, and `Stderr`.
///
/// NOTE: this function should not be called multiple times. Any subsequent invocation
/// will result in a panic.
#[verifier::external_body]
pub fn init() -> (ret: (Stdin, Stdout, Stderr))
    ensures
        ret.0.nbyte() == 0,
        ret.0.inv(),
{
    static STDIO_INIT: Once = Once::new();
    assert!(!STDIO_INIT.is_completed(), "stdio::init() can only be called once");
    STDIO_INIT.call_once(|| {});

    (stdin(), stdout(), stderr())
}

} // verus!