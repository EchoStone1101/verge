//! Specifications and lemmas for the file system.
//!
//! ### Specification of File I/O, not File Systems
//! Currently, Verge exposes a minimal yet generally complete subset of Rust's
//! file system APIs, so that file I/O can be specified in `spec`.
//! Note that this is different from fully specifying the underlying file system (FS), 
//! which would require much more consideration and might even demand a custom 
//! Verus-friendly FS implementation in the future.
//!
//! Here is an example to demonstrate the gap: file I/O specification only works 
//! with abstract file objects, while FS specification needs to go deep 
//! into the stack (e.g., inodes in POSIX) and reason about what really happens 
//! with I/O and other FS operations (which, arguably, should be a separate 
//! undertaking for FS developers).
//!
//! The downside, however, is that specifications in this module generally 
//! only appears as post-conditions for describing behaviors, but never as pre-conditions
//! for predicting the results of FS APIs. For example, knowing `<File as Write>::bytes(f)` 
//! does not give any information to the results of a subsequent `f.read()`.

use vstd::prelude::*;

pub use std::fs::{
    File
};

verus! {

/// A singleton handle representing the state of the entire file system.
/// 
/// `Fs` is represented as a combination of the entire file system state (check comments 
/// for `File` for details) and a ghost `ops` sequence that tracks mutation operations 
/// through  
pub struct Fs;

#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExFile(File);

/// An object providing access to an open file on the file system.
/// 
/// ### `spec` Abstraction of `File`s
/// Verge models the file system simply as a `Map` from paths (strings with constraints) 
/// to files, where each file is essentially a collection of epoch-controlled byte sequences:
/// ```
/// fs::file("foo.txt")
///     0   1   2   3   4   5   6   7   8
///   +-----------------------------------> offset
/// 0 |[x] [x] [x] [x] [x] [x] [x] [x] [x]
/// 1 |[ ] [ ] [ ] [x] [x] [x] [x] [x] [x]
/// 2 |[ ] [x] [x] [x] [x] [x] [x] [x] [x]
/// 3 |[ ] [ ] [ ] [ ] [ ] [ ] [ ] [ ] [ ]
///   v
/// epoch 
/// ```
/// Epoch is required to account for the external changes made to the file system
/// (i.e., a file is never owned by a `File` in the sense of Rust ownership; its content 
/// can be changed by other programs at any time). It is only ever incremented by
/// Verge's FS APIs, which means "the FS might have changed" since the last epoch.
/// This representation then unifies both non-existent files and non-existent ranges in a file:
/// - "foo.txt" does not exist yet at epoch 0; the entry for this path still exists in `Fs`, 
/// but the value is just all non-existent bytes
/// - "foo.txt" gets truncated at epoch 2; its byte at offset 1 goes from existent to non-existent.
/// 
/// Theoretically, we could use this directly as an accurate specifiction of `File`. 
/// However, it would be quite an inconvenient one. For example, sequentially reading a file 
/// could yield either:
/// ```
///   +-----------------------------------> 
/// 1 |[ ] [ ]
///   |        [ ] 
///   |            [ ] [ ] [ ] [ ] [ ] [ ]
///   v
/// ```
/// or: 
/// ```
///   +-----------------------------------> 
/// 1 |[ ] [ ] [ ] [ ] [ ] [ ] [ ] [ ]
///   |                           
///   |                                [ ]
///   v
/// ```
/// depending on how `File::read()` goes. But more often than not we do not care about 
/// this level of details, and just want to express "all the bytes in a file" in specifications.
///
/// Hence, by default, Verge treats `File` as *one* epoch-controlled `Seq<u8>`, where `f.bytes()` can 
/// represent either of the above as long as `f.epoch() == 1`. Special care is taken to ensure 
/// Verus's spec equality does not introduce unsound condtions - any attempts to rewind the byte stream 
/// (e.g., seeking back via `Seek`) will increment the `File`'s epoch, ensuring that reading 
/// the same range of bytes twice does *not* yield the same result in `spec` (which is unsound, 
/// as the file content could have changed in between).  
/// To make the accurate specifiction still accessible, Verge also allows an alternative specifiction 
/// for `File` where the epoch of its bytes can be explicitly specified (see the `spec` functions below).
pub struct File(std::fs::File);



} // verus!