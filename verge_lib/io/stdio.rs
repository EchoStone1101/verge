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
pub struct ExStdout(std::io::Stdout);

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExStderr(std::io::Stderr);

#[verifier::external_body]
fn stdin_raw() -> std::io::Stdin {
    std::io::stdin()
}

#[verifier::external_body]
fn stdout_raw() -> std::io::Stdout {
    std::io::stdout()
}

#[verifier::external_body]
fn stderr_raw() -> std::io::Stderr {
    std::io::stderr()
}

/// Initialize unique handles for accessing `stdin`, `stdout`, and `stderr`.
///
/// NOTE: this function should not be called multiple times. Any subsequent invocation
/// will result in a panic.
/// XXX: to enforce this, maybe make this external, and make it a common header?
#[verifier::external_body]
pub fn init() -> (ret: (Stdin, Stdout, Stderr))
    ensures
        ret.0.nbyte() == 0,
{
    static STDIO_INIT: Once = Once::new();
    assert!(!STDIO_INIT.is_completed(), "stdio::init() can only be called once");
    STDIO_INIT.call_once(|| {});

    (
        Stdin { inner: stdin_raw(), nbyte: Ghost(0) },
        Stdout { inner: stdout_raw(), nbyte: Ghost(0) },
        Stderr { inner: stderr_raw(), nbyte: Ghost(0) },
    )
}

/// Singleton state for the standard input of the current process.
pub struct Stdin {
    inner: std::io::Stdin,
    nbyte: Ghost<nat>,
}

/// Singleton state for the standard output of the current process.
pub struct Stdout {
    inner: std::io::Stdout,
    nbyte: Ghost<nat>,
}

/// Singleton state for the standard error of the current process.
pub struct Stderr {
    inner: std::io::Stderr,
    nbyte: Ghost<nat>,
}

impl Stdin {

    #[verifier::type_invariant]
    pub open spec fn inv(&self) -> bool {
        self.nbyte() <= Stdin::stream().len()
    }

    /// All input bytes in the input stream, ever.
    pub uninterp spec fn stream() -> Seq<u8>;

    /// Number of bytes already revealed in the input stream.
    pub closed spec fn nbyte(&self) -> nat {
        self.nbyte@
    }

    #[verifier::external_body]
    pub(crate) fn read_raw<B: ReadBuf + ?Sized>(&mut self, buf: &mut B, range: Option<Range<usize>>) -> (res: Result<usize>) 
        ensures
            ({
                let (start, end) = match range {
                    Some(range) => (range.start as int, range.end as int),
                    _ => (0int, buf@.len() as int),
                };
                match res {
                    Ok(nread) => ({
                        &&& old(self).nbyte() + nread <= Stdin::stream().len() && nread <= end - start
                        &&& buf@ =~= 
                            old(buf)@.take(start) 
                            + Stdin::stream().skip(old(self).nbyte() as int).take(nread as int) 
                            + old(buf)@.skip(start + nread as int)
                        &&& self.nbyte() == old(self).nbyte() + spec_unwrap(res)
                        &&& end - start > 0 && nread == 0 ==> self.nbyte() == Stdin::stream().len()
                    }),
                    Err(e) => ({
                        &&& buf@ =~= old(buf)@
                        &&& self.nbyte() == old(self).nbyte()
                        &&& spec_error_kind(e) != ErrorKind::UnexpectedEof
                    }),
                }
            })
    {
        use std::io::Read;

        let mut buf = unsafe { std::slice::from_raw_parts_mut(buf.as_mut_ptr(), buf.buf_len()) };
        if let Some(range) = range {
            buf = &mut buf[range];
        }
        let nread = self.inner.read(buf)?;
        self.nbyte = Ghost((self.nbyte@ + nread) as nat);
        Ok(nread)
    }

}

} // verus!