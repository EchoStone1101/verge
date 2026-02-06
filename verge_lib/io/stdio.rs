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

use std::sync::Once;

verus! {

/// Initialize unique handles for accessing `stdin`, `stdout`, and `stderr`.
///
/// NOTE: this function should not be called multiple times. Any subsequent invocation
/// will result in a panic.
#[verifier::external_body]
pub fn init() -> (Stdin, Stdout, Stderr)
{
    static STDIO_INIT: Once = Once::new();
    assert!(!STDIO_INIT.is_completed(), "stdio::init() can only be called once");
    STDIO_INIT.call_once(|| {});

    (Stdin(Tracked(0)), Stdout(Tracked(0)), Stderr(Tracked(0)))
}

/// Singleton state for the standard input of the current process.
pub struct Stdin(Tracked<int>);

/// Singleton state for the standard output of the current process.
pub struct Stdout(Tracked<int>);

/// Singleton state for the standard error of the current process.
pub struct Stderr(Tracked<int>);



// #[verifier::external_body]
// pub fn stdin() -> Stdin {
//     &*STDIN
// }

//     /// Initialize the standard I/O states, returning a unique handle.
//     /// 
//     /// NOTE: `Stdio::init()` can be called at most once. Subsequent invocations 
//     /// will result in a panic. 
//     #[verifier::external_body]
//     fn init() -> (stdio: Stdio) 
//         ensures 
//             stdio.ninput@ == 0 && stdio.noutout@ == 0 && stdio.nerror@ == 0,
//     {
//         static STDIO_INIT: Once = Once::new();
//         assert!(!STDIO_INIT.is_completed(), "Stdio::init() has already been called");
//         STDIO_INIT.call_once(|| {});

//         Stdio { ninput: Tracked(0), noutput: Tracked(0), nerror: Tracked(0) }
//     }

//     /// Abstraction of the entire input as a byte sequence. 
//     /// 
//     /// This is used to uniquely specify the effect of reading from `stdin`. 
//     /// In fact, Std
//     uninterp spec fn input() -> Seq<u8>;
// }

} // verus!