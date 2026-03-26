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
//! does not give any information to the result of a subsequent `f.read()`.
//! 
//! ### Non-UTF-8 File Paths
//! In native Rust, `Path`s is represented by `OsStr` which might not be UTF-8 strings
//! (indeed, Unix systems would accept any byte sequences that do not contain the NUL byte
//! as file paths). For the sake of simplicity, however, Verge currently supports only 
//! UTF-8 paths, essentially treating them as strings.
//!
//! ### Excluding Externals
//! By default, the epoch-based FS specification in Verge assumes *arbitrary external interference*;
//! namely, the entire file system and the content of any file may completely change between 
//! multiple FS APIs. A common type of error - TOCTOU (time-of-check to time-of use) - occurs
//! because of incorrectly neglecting external interference.
//!
//! Of course, this is an over-estimation in many cases, and it disallows some common use cases of the 
//! file system (e.g., caching some intermediate results).
//! Hence, Verge also provides an opt-in assumption, `Fs::no_ext()`, that neglects *any external interference*.
//! This assumption, if assumed as a pre-condition, will unlock a series of further conditions that assert 
//! association between file system states across epochs.
//! TODO: this is currently not yet implemented and needs more consideration to do right.

use vstd::prelude::*;
use vstd::view::View;
use vstd::std_specs::result::{spec_unwrap, spec_unwrap_err};
use crate::{dummy, dummy2};
use crate::io::{Error, ErrorKind, Result};
use crate::str::*;
use crate::iter::IteratorView;
use crate::error::ErrorSpec;

pub use std::fs::{
    File, ReadDir, DirEntry,
};
use std::sync::Once;

mod path;
mod metadata;

pub use path::*;
pub use metadata::*;

verus! {

/// A singleton handle representing the state of the entire file system.
/// 
/// `Fs` is represented mainly as a combination of the entire file system state (check comments 
/// in the `impl` block for details) and a ghost `ops` sequence that tracks mutation operations to
/// the file system (i.e., creating/removing files, or opening files with the write permission).
/// The latter allows for specifying the program's local effect on the file system - 
/// for example, if `fs.ops` is empty, then the program does not *accidentally* clear `/root`.
pub struct Fs {
    epoch: Ghost<int>,
    ops: Ghost<Seq<FsMutOp>>,
    read_dir_count: Ghost<int>, // see the comments for `Fs::read_dir()`
}

/// File system mutation operations.
pub enum FsMutOp {
    /// Mutation (opening with write permissions) of a file with the given path;
    /// this includes file creation.
    Mutate(PathView),
    /// Deletion of a file with the given path.
    Delete(PathView),
}

impl Fs {
    /// ### `spec` Abstraction of `Fs` and `File`s
    /// Verge models the file system simply as a `Map` from paths (`PathView`) to files, where each file 
    /// is essentially a collection of epoch-controlled byte sequences:
    /// ```
    /// Fs::file(0, "foo")
    ///     0   1   2   3   4   5   6   7   8
    ///   +-----------------------------------> offset
    /// 0 |[x] [x] [x] [x] [x] [x] [x] [x] [x]
    /// 1 |[ ] [ ] [ ] [x] [x] [x] [x] [x] [x]
    /// 2 |[ ] [x] [x] [x] [x] [x] [x] [x] [x]
    /// 3 |[ ] [ ] [ ] [ ] [ ] [ ] [ ] [ ] [ ]
    ///   v
    /// epoch 
    /// ```
    /// Epoch is required to account for external changes made to the file system
    /// (i.e., a file is never owned by a `File` in the sense of Rust ownership; its content 
    /// can be changed by other programs at any time). It is only ever incremented by
    /// Verge's FS APIs, which means "the FS might have changed" since the last epoch.
    /// This representation also unifies both non-existent files and non-existent ranges in a file:
    /// - "foo.txt" does not exist yet at epoch 0; the entry for this path still exists in `Fs`, 
    /// but the value is just all non-existent bytes;
    /// - "foo.txt" gets truncated at epoch 2; its byte at offset 1 goes from existent to non-existent;
    /// 
    /// Theoretically, this representation, a.k.a. `Fs::file_when()`, is already an accurate specifiction 
    /// of `File`s for Verge's FS APIs. However, using it as-is would be quite inconvenient. 
    /// For example, sequentially reading "foo" could yield either:
    /// ```
    ///   +-----------------------------------> 
    /// 1 |[ ] [ ]                              file_when(1, "foo").subrange(0, 2)
    /// 2 |        [ ]                          file_when(2, "foo").subrange(2, 3)
    /// 3 |            [ ] [ ] [ ] [ ] [ ] [ ]  file_when(3, "foo").subrange(3, 9)
    ///   v
    /// ```
    /// or: 
    /// ```
    ///   +-----------------------------------> 
    /// 1 |[ ] [ ] [ ] [ ] [ ] [ ] [ ] [ ]      file_when(1, "foo").subrange(0, 8)               
    /// 2 |                                [ ]  file_when(2, "foo").subrange(8, 9)
    ///   v
    /// ```
    /// depending on how `File::read()` goes. Yet more often than not we do not care about 
    /// this level of details, and just want to express "all the bytes in a file" in specifications.
    ///
    /// Hence, Verge also provides an alternative view for each `File` as *one* epoch-controlled `Seq<u8>`, 
    /// a.k.a. `Fs::file`, as the default representation.
    /// The precise definition of `Fs::file(epoch, path)` is: for the file determined by `epoch` and `path`
    /// in the file system, all the bytes that could be accessed *since* `epoch`.
    /// Essentially, `Fs::file` abstracts over `File::file_when` by late-binding and hiding the actual
    /// epoch of access for the bytes. For instance, `Fs::file(1, "foo")` can be either cases
    /// in the above.
    /// 
    /// Of course, special care is taken to ensure Verus's spec equality does not introduce unsound conditions.
    /// In general, `file(e1, ...)` soundly abstracts any single `file_when(e2, ...)` (`e2 >= e1`), 
    /// but not for multiple epochs (otherwise, we allow `file_when(e2, ...)` == ``file_when(e3, ...)`).
    /// To enforce this, any attempts to rewind the byte stream (e.g., seeking back via `Seek`) will increment 
    /// the `File`'s epoch, and later access of the `File` yields `Fs::file()` using the new epoch.
    ///
    /// ### Path Resolution
    /// Currently, Verge's FS specification does not model any kind of links (hard or symbolic). 
    /// All FS properties are defined *as if all links are followed*. For example, if `path` is a link
    /// to `actual`, then `Fs::file(_, path)` refers to the content of `actual`, not the link entity itself.
    ///
    /// ### Known Limitations 
    /// This specification currently does not support:
    /// - Read-write mode `File`s. Technically the specification can be written, but it would not be
    /// able to distinguish in `spec` whether any byte in `Fs::file` is read from the file or written by the program, 
    /// and hence basically useless.
    /// - Append-mode `File`s. The semantics of append-mode involves "seeking" (to the current EOF), which
    /// necessarily bumps the file epoch, making the specification, again, basically useless. 
    /// In other words, ironically, appending to a file may not yield consequtive bytes (`Fs::file`) because 
    /// later appends can overwrite previous ones.
    /// - Links (hard or symbolic). All specifications and their underlying system calls follow links, 
    /// so there is no way to specify or even identify links.
    /// - Metadata permissions are not modeled.

    /// The "no external" assumption. See the top-level comments of this module for details.
    pub uninterp spec fn noext() -> bool;

    #[verifier::type_invariant]
    pub open spec fn inv(&self) -> bool {
        forall|i: int| #![trigger self.ops()[i]] 0 <= i < self.ops().len() ==> 
            ({
                match self.ops()[i] {
                    FsMutOp::Mutate(path) => path.is_normalized(),
                    FsMutOp::Delete(path) => path.is_normalized(),
                }
            })
    }

    pub closed spec fn epoch(&self) -> int 
        { self.epoch@ }
    
    pub closed spec fn ops(&self) -> Seq<FsMutOp> 
        { self.ops@ }

    pub closed spec fn read_dir_count(&self) -> int 
        { self.read_dir_count@ }

    /// Enables the use of `<=` on `Fs`.
    pub open spec fn spec_le(&self, other: &Fs) -> bool { 
        &&& self.epoch() <= other.epoch() 
        &&& self.ops().is_prefix_of(other.ops())
    }

    /// This function encodes some time `t` between two file system states `pre` and `post`.
    ///
    /// Used by Verge FS APIs to specify the epoch of results.
    pub open spec fn between(pre: &Self, post: &Self) -> int 
        recommends
            pre <= post,
    {
        choose|t: int| #![trigger dummy(t)] pre.epoch() <= t <= post.epoch()
    }

    // FS properties

    /// This function encodes whether the file at `path` exists in the file system,
    /// exactly at the time specified by `epoch`.
    /// 
    /// The semantics of this function is identical to the `fs::exists()` API. 
    /// Notably, in some FS it is possible to unlink an open file, so that the file "does not exist"
    /// but remains accessible (and hence `Fs::file` is meaningful) until closed.
    pub uninterp spec fn file_exists(epoch: int, path: PathView) -> bool
        recommends
            path.is_valid(),
    ;

    /// This function encodes the file at `path` as a sequence of bytes, accessible since `epoch`.
    ///
    /// This encoding hides the actual epoch of access for bytes, and is suitable when the result of 
    /// individual I/O operations are irrelevant.
    pub uninterp spec fn file(epoch: int, path: PathView) -> Seq<u8>
        recommends
            path.is_valid(),
    ;

    /// This function encodes the file at `path` as a sequence of bytes, exactly at the time specified by `epoch`.
    /// 
    /// This encoding is the most accurate one, and it allows for specifying individual I/O operations.
    pub uninterp spec fn file_when(epoch: int, path: PathView) -> Seq<u8>
        recommends
            path.is_valid(),
    ;

    /// This function encodes whether the file at `path` is a directory, exactly at the 
    /// time specified by `epoch`.
    ///
    /// This is only meaningful when the entity specified by `epoch` and `path` exists.
    pub uninterp spec fn file_is_dir(epoch: int, path: PathView) -> bool
        recommends
            Fs::file_exists(epoch, path),
    ;

    /// This function encodes all files (non-recursive) under the directory at `path`, exactly at the 
    /// time specified by `epoch`.
    ///
    /// This is only meaningful when the entity specified by `epoch` and `path` exists and is 
    /// a directory to begin with.
    pub open spec fn files_in_dir(epoch: int, path: PathView) -> Set<PathView>
        recommends
            Fs::file_exists(epoch, path),
            Fs::file_is_dir(epoch, path),
    {
        Set::<PathView>::new(
            |subpath: PathView| {
                &&& subpath.is_normalized() // `*/.` not considered
                &&& subpath.path.len() > 0 && subpath.path.last() != seq!['.', '.', MAIN_SEPARATOR] // `*/..` not considered
                &&& subpath.parent() == path.normalize()
                &&& Fs::file_exists(epoch, subpath) 
            }
        )
    }

    // Lemmas for the file system states

    /// This axiom reduces properties on a non-normalized path to its normalized form. 
    #[verifier::external_body]
    pub axiom fn lemma_fs_path_normalized(epoch: int, path: PathView)
        requires 
            path.is_valid(),
        ensures
            Fs::file_exists(epoch, path) == Fs::file_exists(epoch, path.normalize()),
            Fs::file(epoch, path) == Fs::file(epoch, path.normalize()),
            Fs::file_when(epoch, path) == Fs::file_when(epoch, path.normalize()),
            Fs::file_is_dir(epoch, path) == Fs::file_is_dir(epoch, path.normalize()),
            Fs::files_in_dir(epoch, path) == Fs::files_in_dir(epoch, path.normalize()),
    ;

    /// This axiom asserts that a relative path "**" is equivalent to "./**".
    /// 
    /// XXX: by the normalization standard, "**" and "./**" should really be the same;
    /// however the Rust standard library treats them differently, so our specification 
    /// also does. This axiom exists to bridge the gap.
    #[verifier::external_body]
    pub axiom fn lemma_fs_cur_dir_normalized(epoch: int, path: PathView)
        requires 
            path.is_normalized(),
            !path.abs && path.len() > 0,
        ensures
            ({
                let cur_path = PathView { abs: false, path: seq![seq!['.', MAIN_SEPARATOR]] + path.path };
                &&& Fs::file_exists(epoch, path) == Fs::file_exists(epoch, cur_path)
                &&& Fs::file(epoch, path) == Fs::file(epoch, cur_path)
                &&& Fs::file_when(epoch, path) == Fs::file_when(epoch, cur_path)
                &&& Fs::file_is_dir(epoch, path) == Fs::file_is_dir(epoch, cur_path)
                &&& Fs::files_in_dir(epoch, path) == Fs::files_in_dir(epoch, cur_path)
            }),
    ;

    /// This axiom asserts that the root directory always exists.
    #[verifier::external_body]
    pub axiom fn lemma_fs_root_dir(epoch: int)
        ensures
            Fs::file_exists(epoch, path_view![/]),
            Fs::file_is_dir(epoch, path_view![/]),
    ;

    /// This axiom asserts that the "**/.." file exists for any directory "**".
    #[verifier::external_body]
    pub axiom fn lemma_fs_parent_dir(epoch: int, path: PathView)
        requires
            path.is_normalized(),
            Fs::file_exists(epoch, path),
            Fs::file_is_dir(epoch, path),
        ensures
            Fs::file_exists(epoch, path.join(seq!['.', '.', MAIN_SEPARATOR])),
            Fs::file_is_dir(epoch, path.join(seq!['.', '.', MAIN_SEPARATOR])),
    ;

    /// This axiom asserts that the parent of an existent file also exists, and is a directory.
    /// 
    /// NOTE: "**/*/.." is not necessarily equivalent to "**" because of potential links.
    #[verifier::external_body]
    pub axiom fn lemma_fs_parent(epoch: int, path: PathView)
        requires 
            path.is_normalized(),
            path.len() > 0,
            Fs::file_exists(epoch, path),
        ensures
            Fs::file_exists(epoch, path.parent()),
            Fs::file_is_dir(epoch, path.parent()),
    ;

    /// This axiom asserts that if a path does not exist, or if it exists but is not a directory,
    /// then all subpaths cannot exist.
    pub axiom fn lemma_fs_not_exists(epoch: int, path: PathView)
        requires 
            path.is_normalized(),
            !Fs::file_exists(epoch, path) || (Fs::file_exists(epoch, path) && !Fs::file_is_dir(epoch, path)),
        ensures
            forall|subpath: PathView| #[trigger] subpath.parent() == path 
                ==> !Fs::file_exists(epoch, subpath),
    ;

    /// This axiom asserts that the set `files_in_dir` is finite.
    #[verifier::external_body]
    pub axiom fn lemma_fs_files_in_dir_finite(epoch: int, path: PathView)
        requires
            path.is_normalized(),
            Fs::file_exists(epoch, path),
            Fs::file_is_dir(epoch, path),
        ensures 
            Fs::files_in_dir(epoch, path).finite(),
    ;

}

/// Initialize the file system state.
///
/// NOTE: this function should not be called multiple times. Any subsequent invocation
/// will result in a panic.
#[verifier::external_body]
pub fn init() -> (ret: Fs)
    ensures
        ret.ops().len() == 0,
        ret.read_dir_count() == 0,
{
    static FS_INIT: Once = Once::new();
    assert!(!FS_INIT.is_completed(), "fs::init() can only be called once");
    FS_INIT.call_once(|| {});

    Fs {
        epoch: Ghost(0int),
        ops: Ghost(seq![]),
        read_dir_count: Ghost(0int),
    }
}

/// An object providing access to an open file on the file system.
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExFile(File);

/// Iterator over the entries in a directory.
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExReadDir(ReadDir);

/// Entries returned by the `ReadDir` iterator.
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExDirEntry(DirEntry);

/// The `FileSpec` trait specifies `File`s.
pub trait FileSpec {
    /// Epoch of the file when it is opened or last rewound (`seek` in reverse).
    spec fn otime(&self) -> int;
    /// Epoch of the file when it is last accessed.
    spec fn atime(&self) -> int;
    /// Path of the file as it is opened.
    spec fn path(&self) -> PathView;

    /// Invariant of the file.
    spec fn inv(&self) -> bool;
    /// Offset of the open file.
    spec fn offset(&self) -> int;
    /// Maximum offset that has been reached into the file.
    spec fn maxofs(&self) -> int;

    /// An axiom that asserts that at any time, the epoch of the file system must be more recent 
    /// than the last access time of a `File`.
    ///
    /// This axiom is needed to bridge between the epochs tracked over `Fs` and `File`s.
    /// For example:
    /// ```rust
    /// let mut f1 = fs.open("foo");
    /// let res1 = f1.read(...)?;
    /// proof { f1.sync(fs); }
    /// let mut f2 = fs.open("foo");
    /// let res2 = f2.read(...)?;
    /// assert(exists |t1: int, t2: int| {
    ///     &&& t1 <= t2 
    ///     &&& res1 == Fs::file_when(t1, "foo"@).subrange(...)
    ///     &&& res2 == Fs::file_when(t2, "foo"@).subrange(...)
    /// });
    /// ```
    /// Without `sync`, it would not be possible to deduce `t1 <= t2` because `f1.atime()` and 
    /// `f2.atime()` are not associated with `fs.epoch()` (`read()` does *not* take `fs` as an 
    /// argument), and thus are not ordered.
    proof fn sync(&self, fs: &mut Fs)
        requires
            self.inv(),
        ensures 
            self.atime() <= fs.epoch(),
            old(fs).epoch() <= fs.epoch(),
    ;

    /// Drops the file and asserts that it is accessed up to its max offset.
    /// 
    /// This is essentially explicitly calling `drop`, but with `spec` to mark the range 
    /// of mutation for file; otherwise there is no way to specify that bytes beyond the 
    /// max offset is not modified.
    /// Note also that this works on only one instance (`File`) of a file. If a file is 
    /// opened multiple times, `fs.ops` will contain multiple entries, all of which need 
    /// to be sealed separately.
    fn seal(self)
        requires
            self.inv(),
        ensures
            Fs::file(self.otime(), self.path()).len() == self.maxofs(),
    ;

}

impl FileSpec for File {
    uninterp spec fn otime(&self) -> int;
    uninterp spec fn atime(&self) -> int;
    uninterp spec fn path(&self) -> PathView;
    uninterp spec fn offset(&self) -> int;
    uninterp spec fn maxofs(&self) -> int;

    open spec fn inv(&self) -> bool {
        &&& self.path().is_valid()
        &&& self.otime() <= self.atime()
        &&& self.offset() <= self.maxofs()
        // The `isize::MAX` bound allows for calling methods like `Read::read_to_end()`;
        &&& 0 <= self.offset() <= Fs::file(self.otime(), self.path()).len() <= isize::MAX
        &&& self.offset() <= Fs::file_when(self.atime(), self.path()).len()
    }

    #[verifier::external_body]
    axiom fn sync(&self, fs: &mut Fs);

    #[verifier::external_body]
    fn seal(self) {}

}

impl Fs {

    /// The error condition for `ErrorKind::NotADirectory` when treating `path` as a file.
    pub open spec fn file_not_a_directory(epoch: int, path: PathView) -> bool {
        // part of the path is not a directory
        &&& path.len() > 1
        &&& exists|i: int| #![trigger path.ancestor(i)]
            1 <= i < path.len() 
            && Fs::file_exists(epoch, path.ancestor(i))
            && !Fs::file_is_dir(epoch, path.ancestor(i))
    }

    /// Enables `fs::exists` (check if the path points at an existing entity).
    #[verifier::external_body]
    pub fn exists(&mut self, path: &str) -> (ret: Result<bool>)
        ensures
            old(self) <= self,
            old(self).ops() == self.ops(),
            ({
                let path = path@.as_path().normalize();
                match ret {
                    Ok(true) => Fs::file_exists(old(self).epoch(), path),
                    Ok(false) => !Fs::file_exists(old(self).epoch(), path),
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::InvalidFilename | 
                            ErrorKind::OutOfMemory | ErrorKind::NotADirectory | 
                            ErrorKind::Other)
                        &&& e.kind() == ErrorKind::NotADirectory
                            ==> Fs::file_not_a_directory(old(self).epoch(), path)
                    },
                }
            }),
    {
        std::fs::exists(path)
    }

    /// Enables `File::open` (open a file in read-only mode).
    #[verifier::external_body]
    pub fn open(&mut self, path: &str) -> (ret: Result<File>)
        ensures
            old(self) <= self,
            old(self).ops() == self.ops(),
            ({
                let path = path@.as_path().normalize();
                match ret {
                    Ok(file) => {
                        &&& Fs::file_exists(old(self).epoch(), path)
                        &&& file.inv()
                        &&& file.otime() == old(self).epoch()
                        &&& file.path() == path
                        &&& file.offset() == 0
                        &&& file.maxofs() == 0
                    },
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::FileTooLarge | 
                            ErrorKind::Interrupted | ErrorKind::InvalidInput | 
                            ErrorKind::IsADirectory | ErrorKind::InvalidFilename | 
                            ErrorKind::NotFound | ErrorKind::OutOfMemory | 
                            ErrorKind::NotADirectory | ErrorKind::Other)
                        &&& e.kind() == ErrorKind::NotFound ==> !Fs::file_exists(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::NotADirectory 
                            ==> Fs::file_not_a_directory(old(self).epoch(), path)
                        // `open` cannot access directories
                        &&& e.kind() == ErrorKind::IsADirectory ==> 
                            Fs::file_exists(old(self).epoch(), path) && Fs::file_is_dir(old(self).epoch(), path)
                    },
                }
            }),
    {
        use std::io::Read;
        let mut f = File::open(path)?;
        f.read(&mut [0u8; 0])?; // an empty read to check that the file is not a directory
        Ok(f)
    }

    /// Enables `File::create` (open a file in write-only mode; truncate if existent).
    #[verifier::external_body]
    pub fn create(&mut self, path: &str) -> (ret: Result<File>)
        requires
            old(self).read_dir_count() == 0,
        ensures
            old(self) <= self,
            ({
                let path = path@.as_path().normalize();
                match ret {
                    Ok(file) => {
                        &&& self.ops() == old(self).ops().push(FsMutOp::Mutate(path))
                        &&& Fs::file_exists(old(self).epoch(), path)
                        &&& !Fs::file_is_dir(old(self).epoch(), path) // `create` does not create directories
                        &&& file.inv()
                        &&& file.otime() == old(self).epoch()
                        &&& file.path() == path
                        &&& file.offset() == 0
                        &&& file.maxofs() == 0
                        // file is truncated
                        &&& Fs::file_when(old(self).epoch(), path).len() == 0
                    },
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& self.ops() == old(self).ops()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::QuotaExceeded | 
                            ErrorKind::FileTooLarge | ErrorKind::Interrupted | 
                            ErrorKind::InvalidInput | ErrorKind::IsADirectory | 
                            ErrorKind::InvalidFilename | ErrorKind::NotFound | 
                            ErrorKind::OutOfMemory | ErrorKind::StorageFull | 
                            ErrorKind::NotADirectory | ErrorKind::ReadOnlyFilesystem |
                            ErrorKind::ExecutableFileBusy | ErrorKind::Other)
                        // if the parent existed, the error would not be `NotFound`
                        &&& e.kind() == ErrorKind::NotFound ==> 
                            !Fs::file_exists(old(self).epoch(), path.parent())
                        &&& e.kind() == ErrorKind::NotADirectory 
                            ==> Fs::file_not_a_directory(old(self).epoch(), path)
                        // `create` cannot truncate directories
                        &&& e.kind() == ErrorKind::IsADirectory ==> 
                            Fs::file_exists(old(self).epoch(), path) && Fs::file_is_dir(old(self).epoch(), path)
                    },
                }
            }),
    {
        File::create(path)
    }

    /// Enable `File::create_new` (creates a new file in *write* mode; error if the file exists).
    #[verifier::external_body]
    pub fn create_new(&mut self, path: &str) -> (ret: Result<File>)
        requires
            old(self).read_dir_count() == 0,
        ensures
            old(self) <= self,
            ({
                let path = path@.as_path().normalize();
                let t = Fs::between(old(self), self);
                match ret {
                    Ok(file) => {
                        &&& self.ops() == old(self).ops().push(FsMutOp::Mutate(path))
                        &&& !Fs::file_exists(old(self).epoch(), path) && Fs::file_exists(t, path)
                        &&& !Fs::file_is_dir(t, path) // `create_new` does not create directories
                        &&& file.inv()
                        &&& file.otime() == t
                        &&& file.path() == path
                        &&& file.offset() == 0
                        &&& file.maxofs() == 0
                        // file is empty
                        &&& Fs::file_when(t, path).len() == 0
                    },
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& self.ops() == old(self).ops()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::ResourceBusy | 
                            ErrorKind::QuotaExceeded | ErrorKind::FileTooLarge | 
                            ErrorKind::Interrupted | ErrorKind::InvalidInput | 
                            ErrorKind::AlreadyExists | ErrorKind::InvalidFilename | 
                            ErrorKind::NotFound | ErrorKind::OutOfMemory | 
                            ErrorKind::StorageFull | ErrorKind::NotADirectory | 
                            ErrorKind::ReadOnlyFilesystem | ErrorKind::Other)
                        &&& e.kind() == ErrorKind::AlreadyExists ==> Fs::file_exists(old(self).epoch(), path) 
                        // if the parent existed, the error would not be `NotFound`
                        &&& e.kind() == ErrorKind::NotFound ==> 
                            !Fs::file_exists(old(self).epoch(), path.parent())
                        &&& e.kind() == ErrorKind::NotADirectory 
                            ==> Fs::file_not_a_directory(old(self).epoch(), path)
                    },
                }
            }),
    {
        File::options().read(false).write(true).create_new(true).open(path)
    }

    /// Enable `fs::read` (reads the entire contents of a file into a bytes vector).
    #[verifier::external_body]
    pub fn read(&mut self, path: &str) -> (ret: Result<Vec<u8>>)
        ensures
            old(self) <= self,
            self.ops() == old(self).ops(),
            ({
                let path = path@.as_path().normalize();
                match ret {
                    Ok(bytes) => {
                        &&& Fs::file_exists(old(self).epoch(), path)
                        &&& !Fs::file_is_dir(old(self).epoch(), path) // `read` does not work on directories
                        &&& Fs::file(old(self).epoch(), path) =~= bytes@
                    },
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::FileTooLarge | 
                            ErrorKind::Interrupted | ErrorKind::InvalidInput | 
                            ErrorKind::IsADirectory | ErrorKind::InvalidFilename | 
                            ErrorKind::NotFound | ErrorKind::OutOfMemory | 
                            ErrorKind::NotADirectory | ErrorKind::Other)
                        &&& e.kind() == ErrorKind::NotFound ==> !Fs::file_exists(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::NotADirectory 
                            ==> Fs::file_not_a_directory(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::IsADirectory ==> 
                            Fs::file_exists(old(self).epoch(), path) && Fs::file_is_dir(old(self).epoch(), path)
                        
                    },
                }
            }),
    {
        std::fs::read(path)
    }

    /// Enable `fs::read_to_string` (reads the entire contents of a file into a string).
    #[verifier::external_body]
    pub fn read_to_string(&mut self, path: &str) -> (ret: Result<String>)
        ensures
            old(self) <= self,
            self.ops() == old(self).ops(),
            ({
                let path = path@.as_path().normalize();
                match ret {
                    Ok(string) => {
                        &&& Fs::file_exists(old(self).epoch(), path)
                        &&& !Fs::file_is_dir(old(self).epoch(), path) // `read` does not work on directories
                        &&& Fs::file(old(self).epoch(), path) =~= string@.as_bytes()
                    },
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::FileTooLarge | 
                            ErrorKind::Interrupted | ErrorKind::InvalidInput | 
                            ErrorKind::IsADirectory | ErrorKind::InvalidFilename | 
                            ErrorKind::NotFound | ErrorKind::OutOfMemory | 
                            ErrorKind::NotADirectory | ErrorKind::InvalidData | ErrorKind::Other)
                        &&& e.kind() == ErrorKind::NotFound ==> !Fs::file_exists(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::NotADirectory 
                            ==> Fs::file_not_a_directory(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::IsADirectory ==> 
                            Fs::file_exists(old(self).epoch(), path) && Fs::file_is_dir(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::InvalidData ==> 
                            Fs::file_exists(old(self).epoch(), path) && !Fs::file(old(self).epoch(), path).is_utf8()
                    },
                }
            }),
    {
        std::fs::read_to_string(path)
    }

    /// Enable `fs::write` (writes a slice as the entire contents of a file.
    /// This function will create a file if it does not exist, and will entirely replace its contents if it does).
    #[verifier::external_body]
    pub fn write(&mut self, path: &str, contents: &[u8]) -> (ret: Result<()>)
        ensures
            old(self) <= self,
            ({
                let path = path@.as_path().normalize();
                match ret {
                    Ok(_) => {
                        &&& self.ops() == old(self).ops().push(FsMutOp::Mutate(path))
                        &&& Fs::file_exists(old(self).epoch(), path)
                        &&& !Fs::file_is_dir(old(self).epoch(), path) // `write` does not work on directories
                        &&& Fs::file(old(self).epoch(), path) =~= contents@
                    },
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& self.ops() == old(self).ops()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::QuotaExceeded | 
                            ErrorKind::FileTooLarge | ErrorKind::Interrupted | 
                            ErrorKind::InvalidInput | ErrorKind::IsADirectory | 
                            ErrorKind::InvalidFilename | ErrorKind::NotFound | 
                            ErrorKind::OutOfMemory | ErrorKind::StorageFull | 
                            ErrorKind::NotADirectory | ErrorKind::ReadOnlyFilesystem |
                            ErrorKind::ExecutableFileBusy | ErrorKind::Other)
                        // if the parent existed, the error would not be `NotFound`
                        &&& e.kind() == ErrorKind::NotFound ==> !Fs::file_exists(old(self).epoch(), path.parent())
                        &&& e.kind() == ErrorKind::NotADirectory 
                            ==> Fs::file_not_a_directory(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::IsADirectory ==> 
                            Fs::file_exists(old(self).epoch(), path) && Fs::file_is_dir(old(self).epoch(), path)
                    },
                }
            }),
    {
        std::fs::write(path, contents)
    }

    /// Enable `fs::remove_file` (removes a file from the filesystem).
    #[verifier::external_body]
    pub fn remove(&mut self, path: &str) -> (ret: Result<()>)
        requires
            old(self).read_dir_count() == 0,
        ensures
            old(self) <= self,
            ({
                let path = path@.as_path().normalize();
                let t = Fs::between(old(self), self);
                match ret {
                    Ok(_) => {
                        &&& self.ops() == old(self).ops().push(FsMutOp::Delete(path))
                        &&& Fs::file_exists(old(self).epoch(), path) && !Fs::file_exists(t, path)
                        &&& !Fs::file_is_dir(old(self).epoch(), path) // `remove` does not remove directories
                    },
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& self.ops() == old(self).ops()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::ResourceBusy | 
                            ErrorKind::IsADirectory | ErrorKind::InvalidFilename | 
                            ErrorKind::NotFound | ErrorKind::OutOfMemory | 
                            ErrorKind::NotADirectory | ErrorKind::ReadOnlyFilesystem | ErrorKind::Other)
                        &&& e.kind() == ErrorKind::NotFound ==> !Fs::file_exists(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::NotADirectory 
                            ==> Fs::file_not_a_directory(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::IsADirectory ==> 
                            Fs::file_exists(old(self).epoch(), path) && Fs::file_is_dir(old(self).epoch(), path)
                    },
                }
            }),
    {
        std::fs::remove_file(path)
    }

    /// Enables `fs::create_dir` (creates a new, empty directory at the provided path).
    #[verifier::external_body]
    pub fn create_dir(&mut self, path: &str) -> (ret: Result<()>)
        requires
            old(self).read_dir_count() == 0,
        ensures
            old(self) <= self,
            ({
                let path = path@.as_path().normalize();
                let t = Fs::between(old(self), self);
                match ret {
                    Ok(_) => {
                        &&& self.ops() == old(self).ops().push(FsMutOp::Mutate(path))
                        &&& !Fs::file_exists(old(self).epoch(), path) && Fs::file_exists(t, path)
                        &&& Fs::file_is_dir(t, path) 
                        // directory is empty
                        &&& Fs::files_in_dir(t, path).is_empty()
                    },
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& self.ops() == old(self).ops()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::QuotaExceeded | 
                            ErrorKind::AlreadyExists | ErrorKind::InvalidInput | 
                            ErrorKind::InvalidFilename | ErrorKind::NotFound | 
                            ErrorKind::OutOfMemory | ErrorKind::StorageFull | 
                            ErrorKind::NotADirectory | ErrorKind::ReadOnlyFilesystem | ErrorKind::Other)
                        &&& e.kind() == ErrorKind::AlreadyExists ==> Fs::file_exists(old(self).epoch(), path)
                        // if the parent existed, the error would not be `NotFound`
                        &&& e.kind() == ErrorKind::NotFound ==> !Fs::file_exists(old(self).epoch(), path.parent())
                        &&& e.kind() == ErrorKind::NotADirectory 
                            ==> Fs::file_not_a_directory(old(self).epoch(), path)
                    },
                }
            }),
    {
        std::fs::create_dir(path)
    }

    /// Enables `fs::remove_dir` (removes an empty directory).
    #[verifier::external_body]
    pub fn remove_dir(&mut self, path: &str) -> (ret: Result<()>)
        requires
            old(self).read_dir_count() == 0,
        ensures
            old(self) <= self,
            ({
                let path = path@.as_path().normalize();
                let t = Fs::between(old(self), self);
                match ret {
                    Ok(_) => {
                        &&& self.ops() == old(self).ops().push(FsMutOp::Delete(path))
                        &&& Fs::file_exists(old(self).epoch(), path) && !Fs::file_exists(t, path)
                        &&& Fs::file_is_dir(old(self).epoch(), path) 
                        // directory was empty
                        &&& Fs::files_in_dir(old(self).epoch(), path).is_empty()
                    },
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& self.ops() == old(self).ops()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::ResourceBusy | 
                            ErrorKind::InvalidInput | ErrorKind::InvalidFilename | 
                            ErrorKind::NotFound | ErrorKind::OutOfMemory | 
                            ErrorKind::NotADirectory | ErrorKind::DirectoryNotEmpty | 
                            ErrorKind::ReadOnlyFilesystem | ErrorKind::Other)
                        &&& e.kind() == ErrorKind::NotFound ==> !Fs::file_exists(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::NotADirectory ==> {
                            // `path` itself is not a directory
                            ||| Fs::file_exists(old(self).epoch(), path) && !Fs::file_is_dir(old(self).epoch(), path)
                            // part of `path` is not a directory
                            ||| Fs::file_not_a_directory(old(self).epoch(), path)
                        }
                        &&& e.kind() != ErrorKind::IsADirectory
                        // XXX: is this sound according to https://man7.org/linux/man-pages/man2/rmdir.2.html?
                        &&& e.kind() == ErrorKind::DirectoryNotEmpty ==>
                            !Fs::files_in_dir(old(self).epoch(), path).is_empty()
                    },
                }
            }),
    {
        std::fs::remove_dir(path)
    }

    /// Enables `fs::read_dir` (returns an iterator over the entries within a directory).
    /// 
    /// NOTE: the result of `read_dir` is unspecified if files are added to / removed from the directory 
    /// in between calls (https://pubs.opengroup.org/onlinepubs/007904875/functions/readdir_r.html), 
    /// in which case specification becomes impossible.
    /// As such, Verge tracks the number of outstanding `ReadDir`s with `read_dir_count`, and 
    /// further requires the count to be 0 before performing any operation that would alter 
    /// directories (e.g., creating a file). Note that banning access of the entire file system 
    /// is necessary because of potential links - `Fs::create` may create a file under 
    /// a `ReadDir`-referenced directory, even if the path appears lexically different. 
    #[verifier::external_body]
    pub fn read_dir(&mut self, path: &str) -> (ret: Result<ReadDir>)
        ensures
            old(self) <= self,
            self.ops() == old(self).ops(),
            ({
                let path = path@.as_path();
                match ret {
                    Ok(dirs) => {
                        &&& self.read_dir_count() == old(self).read_dir_count() + 1
                        &&& Fs::file_exists(old(self).epoch(), path)
                        &&& Fs::file_is_dir(old(self).epoch(), path) 
                        &&& dirs.inv()
                        // the order of entries is unspecified
                        &&& {
                            let (index, seq) = dirs@;
                            &&& index == 0
                            &&& seq.len() <= Fs::files_in_dir(old(self).epoch(), path).len()
                            // only the last item could be an error
                            &&& forall|i: int| 0 <= i < seq.len() - 1 ==> #[trigger] seq[i].is_ok()
                            // error semantics
                            &&& seq.last().is_err() ==> spec_unwrap_err(seq.last()).is_fs_error()
                            // non-error item is an entry
                            &&& forall|i: int| 0 <= i < seq.len() && #[trigger] seq[i].is_ok() 
                                ==> Fs::files_in_dir(old(self).epoch(), path)
                                        .contains(spec_unwrap(seq[i])@.normalize())
                            // if no error, then all entries have been visited
                            &&& (forall|i: int| 0 <= i < seq.len() ==> #[trigger] seq[i].is_ok()) 
                                ==> seq.len() == Fs::files_in_dir(old(self).epoch(), path).len()
                        }
                    },
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& self.read_dir_count() == old(self).read_dir_count()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::FileTooLarge | 
                            ErrorKind::Interrupted | ErrorKind::InvalidInput | 
                            ErrorKind::InvalidFilename | ErrorKind::NotFound | 
                            ErrorKind::OutOfMemory | ErrorKind::NotADirectory | 
                            ErrorKind::Other)
                        &&& e.kind() == ErrorKind::NotFound ==> !Fs::file_exists(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::NotADirectory ==> {
                            // `path` itself is not a directory
                            ||| Fs::file_exists(old(self).epoch(), path) && !Fs::file_is_dir(old(self).epoch(), path)
                            // part of `path` is not a directory
                            ||| Fs::file_not_a_directory(old(self).epoch(), path)
                        }
                    },
                }
            })
    {
        std::fs::read_dir(path)
    }

    /// Enables `fs::metadata` (queries the file system to get information about a file).
    #[verifier::external_body]
    pub fn metadata(&mut self, path: &str) -> (ret: Result<Metadata>)
        ensures
            old(self) <= self,
            self.ops() == old(self).ops(),
            ({
                let path = path@.as_path().normalize();
                match ret {
                    Ok(m) => {
                        &&& m.inv()
                        &&& m.epoch() == old(self).epoch()
                        &&& m.path() == path
                    },
                    Err(e) => {
                        &&& e.is_fs_error()
                        &&& matches!(e.kind(), 
                            ErrorKind::PermissionDenied | ErrorKind::InvalidFilename | 
                            ErrorKind::NotFound | ErrorKind::OutOfMemory | 
                            ErrorKind::NotADirectory | ErrorKind::Other)
                        &&& e.kind() == ErrorKind::NotFound ==> !Fs::file_exists(old(self).epoch(), path)
                        &&& e.kind() == ErrorKind::NotADirectory ==> Fs::file_not_a_directory(old(self).epoch(), path)
                    },
                }
            }),
    {
        std::fs::metadata(path)
    }

}

impl IteratorView for ReadDir {
    type Item = Result<DirEntry>;

    uninterp spec fn view(&self) -> (int, Seq<Self::Item>);
}

pub assume_specification [ ReadDir::next ] (this: &mut ReadDir) -> (r: Option<Result<DirEntry>>)
    ensures
        old(this).inv() ==> {
            let (old_index, old_seq) = old(this)@;
            match r {
                None => {
                    &&& this.inv()
                    &&& this@ == old(this)@
                    &&& old_index >= old_seq.len()
                },
                Some(k) => {
                    let (new_index, new_seq) = this@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& k == old_seq[old_index]
                    &&& k.is_ok() ==> this.inv()
                },
            }
        },
;

/// This trait specifies `ReadDir`.
pub trait ReadDirSpec {

    /// Invariant of the iterator (broke at the first error).
    spec fn inv(&self) -> bool;
    
    /// Drops the iterator and decreases `read_dir_count`.
    /// 
    /// This is essentially explicitly calling `drop`, but with `spec` to 
    /// update the file system states.
    fn seal(self, fs: &mut Fs)
        requires 
            self.inv(),
            old(fs).read_dir_count() > 0,
        ensures 
            old(fs) <= fs,
            old(fs).ops() == fs.ops(),
            old(fs).read_dir_count() - 1 == fs.read_dir_count(),
    ;

}

impl ReadDirSpec for ReadDir {
    uninterp spec fn inv(&self) -> bool;

    #[verifier::external_body]
    fn seal(self, fs: &mut Fs) {}
}

/// This trait specifies `DirEntry`.
pub trait DirEntrySpec {
    spec fn view(&self) -> PathView;
}

impl DirEntrySpec for DirEntry {
    uninterp spec fn view(&self) -> PathView;
}

/// Enable `DirEntry::path`.
pub assume_specification [ DirEntry::path ] (dir: &DirEntry) -> (ret: PathBuf)
    ensures
        ret@ == dir@,
;

// TODO(rilin): tests

} // verus!