# `verge::fs`

Specifications and lemmas for the file system.

### Specification of File I/O, not File Systems
Currently, Verge exposes a minimal yet functionally complete subset of Rust's
file system APIs, so that file I/O can be specified in specs.
Note that this is different from fully specifying the underlying file system (FS),
which would require much more consideration and might even demand a custom
Verus-friendly FS implementation in the future.

To demonstrate the gap: file I/O specification only works with abstract file objects,
while FS specification needs to go deep into the stack (e.g., inodes in POSIX) and
reason about what really happens with I/O and other FS operations (which, arguably,
should be a separate undertaking for FS developers).

The downside, however, is that specifications in this module generally
only appears as post-conditions for describing behaviors, but never as pre-conditions
for predicting the results of FS APIs. For example, knowing `<File as Write>::bytes(f)`
does not give any information about the result of a subsequent `f.read()`.

### Non-UTF-8 File Paths
In native Rust, `Path`s is represented by `OsStr` which might not be UTF-8 strings.
For the sake of simplicity, however, Verge currently supports only
UTF-8 paths, essentially treating them as strings.

### Excluding Externals (WIP)
By default, the epoch-based FS specification (see `impl Fs`) in Verge assumes *arbitrary external interference*;
namely, the entire file system and the content of any file may completely change between
FS interactions. A common type of error - TOCTOU (time-of-check to time-of use) - occurs
because of incorrectly neglecting external interference.

Of course, this is an over-estimation in many cases, and it disallows some common use cases of the
file system (e.g., caching some intermediate results).
Hence, in the future, Verge plans to provide an opt-in assumption, `Fs::no_ext()`, that neglects
*any external interference*.
This assumption, if assumed as a pre-condition, will unlock a series of further conditions that assert
association between file system states across epochs.


## Structs


### `Fs`

A singleton handle representing the state of the entire file system.

`Fs` is characterized mainly as a combination of the entire file system state (check comments
in the `impl` block for details) and a ghost `ops` sequence that tracks mutation operations to
the file system (i.e., creating/removing files, or opening files with the write permission).
The latter allows for specifying the program's local effect on the file system -
for example, if `fs.ops` is empty, then the program does not *accidentally* clear `/root`.

```rust
pub struct Fs
```


### `ExFile`

An object providing access to an open file on the file system.

```rust
pub struct ExFile(File);
```


### `ExReadDir`

Iterator over the entries in a directory.

```rust
pub struct ExReadDir(ReadDir);
```


### `ExDirEntry`

Entries returned by the `ReadDir` iterator.

```rust
pub struct ExDirEntry(DirEntry);
```


## Enums


### `FsMutOp`

File system mutation operations.

```rust
pub enum FsMutOp
```


## Traits


### `FileSpec`

The `FileSpec` trait specifies `File`s.

```rust
pub trait FileSpec
```


#### `otime`

Epoch of the file when it is opened or last rewound (`seek` in reverse).

```rust
spec fn otime(&self) -> int;
```


#### `atime`

Epoch of the file when it is last accessed.

```rust
spec fn atime(&self) -> int;
```


#### `path`

Path of the file as it is opened.

```rust
spec fn path(&self) -> PathView;
```


#### `inv`

Invariant of the file.

```rust
spec fn inv(&self) -> bool;
```


#### `offset`

Offset of the open file.

```rust
spec fn offset(&self) -> int;
```


#### `maxofs`

Maximum offset that has been reached into the file.

```rust
spec fn maxofs(&self) -> int;
```


#### `sync`

An axiom that asserts that at any time, the epoch of the file system must be more recent
than the last access time of a `File`.

This axiom is needed to bridge between the epochs tracked over `Fs` and `File`s.
For example:
```rust
let mut f1 = fs.open("foo");
let res1 = f1.read(...)?;
proof { f1.sync(fs); }
let mut f2 = fs.open("foo");
let res2 = f2.read(...)?;
assert(exists |t1: int, t2: int| {
    &&& t1 <= t2
    &&& res1 == Fs::file_when(t1, "foo"@).subrange(...)
    &&& res2 == Fs::file_when(t2, "foo"@).subrange(...)
});
```
Without `sync`, it would not be possible to deduce `t1 <= t2` because `f1.atime()` and
`f2.atime()` are not associated with `fs.epoch()` (`read()` does *not* take `fs` as an
argument), and thus are not ordered.

```rust
proof fn sync(&self, fs: &mut Fs)
    requires
        self.inv(),
    ensures
        self.atime() <= fs.epoch(),
        old(fs).epoch() <= fs.epoch(),
        ;
```


#### `seal`

Drops the file and asserts that it is accessed up to its max offset.

This is essentially explicitly calling `drop`, but with specs to mark the range
of mutation for file; otherwise there is no way to specify that bytes beyond the
max offset is not modified.
Note also that this works on only one instance (`File`) of a file. If a file is
opened multiple times, `fs.ops` will contain multiple entries, all of which need
to be sealed separately.

```rust
fn seal(self)
    requires
        self.inv(),
    ensures
        Fs::file(self.otime(), self.path()).len() == self.maxofs(),
        ;
```


### `ReadDirSpec`

This trait specifies `ReadDir`.

```rust
pub trait ReadDirSpec
```


#### `inv`

Invariant of the iterator (broke at the first error).

```rust
spec fn inv(&self) -> bool;
```


#### `seal`

Drops the iterator and decreases `read_dir_count`.

This is essentially explicitly calling `drop`, but with `spec` to
update the file system states.

```rust
fn seal(self, fs: &mut Fs)
    requires
        self.inv(),
        old(fs).read_dir_count() > 0,
    ensures
        old(fs) <= fs,
        old(fs).ops() == fs.ops(),
        old(fs).read_dir_count() - 1 == fs.read_dir_count(),
        ;
```


### `DirEntrySpec`

This trait specifies `DirEntry`.

```rust
pub trait DirEntrySpec
```


#### `view`

```rust
spec fn view(&self) -> PathView;
```


## Functions


### `init`

Initialize the file system state.

NOTE: this function should not be called multiple times. Any subsequent invocation
will result in a panic.

```rust
pub fn init() -> (ret: Fs)
    ensures
        ret.ops().len() == 0,
        ret.read_dir_count() == 0,
```


### `ReadDir::next`

Enables `ReadDir` as an iterator.

```rust
pub assume_specification [ ReadDir::next ] (this: &mut ReadDir) -> (r: Option<Result<DirEntry>>)
    ensures
        old(this).inv() ==> {
            let (old_index, old_seq) = old(this)@;
```


### `DirEntry::path`

Enables `DirEntry::path`.

```rust
pub assume_specification [ DirEntry::path ] (dir: &DirEntry) -> (ret: PathBuf)
    ensures
        ret@ == dir@,
        ;
```


## Implementations


### `impl Fs`

```rust
impl Fs
```


#### `noext`

WIP: The "no external" assumption. See the top-level comments of this module for details.

```rust
pub uninterp spec fn noext() -> bool;
```


#### `inv`

Invariant of the file system.

```rust
pub open spec fn inv(&self) -> bool {
    forall|i: int| #![trigger self.ops()[i]] 0 <= i < self.ops().len() ==>
    ({
    match self.ops()[i] {
    FsMutOp::Mutate(path) => path.is_normalized(),
    FsMutOp::Delete(path) => path.is_normalized(),
    }
    })
    }
```


#### `epoch`

Epoch of the file system.

```rust
pub closed spec fn epoch(&self) -> int
    { self.epoch@ }
```


#### `ops`

Mutation operations made to the file system.

```rust
pub closed spec fn ops(&self) -> Seq<FsMutOp>
    { self.ops@ }
```


#### `read_dir_count`

Number of outstanding `ReadDir` iterators.

See the comments for `Fs::read_dir()`

```rust
pub closed spec fn read_dir_count(&self) -> int
    { self.read_dir_count@ }
```


#### `spec_le`

Enables the use of `<=` on `Fs`.

```rust
pub open spec fn spec_le(&self, other: &Fs) -> bool {
    &&& self.epoch() <= other.epoch()
    &&& self.ops().is_prefix_of(other.ops())
    }
```


#### `between`

This function encodes some time `t` between two file system states `pre` and `post`.

Used by Verge FS APIs to specify the epoch of results.

```rust
pub open spec fn between(pre: &Self, post: &Self) -> int
    recommends
        pre <= post,
        {
        choose|t: int| #![trigger dummy(t)] pre.epoch() <= t <= post.epoch()
        }
```


#### `file_exists`

This function encodes whether the file at `path` exists in the file system,
exactly at the time specified by `epoch`.

The semantics of this function is identical to the `fs::exists()` API.
Notably, in some FS it is possible to unlink an open file, so that the file "does not exist"
but remains accessible (and hence `Fs::file` is meaningful) until closed.

```rust
pub uninterp spec fn file_exists(epoch: int, path: PathView) -> bool
    recommends
        path.is_valid(),
        ;
```


#### `file`

This function encodes the file at `path` as a sequence of bytes, accessible since `epoch`.

This encoding hides the actual epoch of access for bytes, and is suitable when the result of
individual I/O operations are irrelevant.

```rust
pub uninterp spec fn file(epoch: int, path: PathView) -> Seq<u8>
    recommends
        path.is_valid(),
        ;
```


#### `file_when`

This function encodes the file at `path` as a sequence of bytes, exactly at the time specified by `epoch`.

This encoding is the most accurate one, and it allows for specifying individual I/O operations.

```rust
pub uninterp spec fn file_when(epoch: int, path: PathView) -> Seq<u8>
    recommends
        path.is_valid(),
        ;
```


#### `file_is_dir`

This function encodes whether the file at `path` is a directory, exactly at the
time specified by `epoch`.

This is only meaningful when the entity specified by `epoch` and `path` exists.

```rust
pub uninterp spec fn file_is_dir(epoch: int, path: PathView) -> bool
    recommends
        Fs::file_exists(epoch, path),
        ;
```


#### `files_in_dir`

This function encodes all files (non-recursive) under the directory at `path`, exactly at the
time specified by `epoch`.

This is only meaningful when the entity specified by `epoch` and `path` exists and is
a directory to begin with.

```rust
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
```


#### `lemma_fs_path_normalized`

This axiom reduces properties on a non-normalized path to its normalized form.

```rust
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
```


#### `lemma_fs_cur_dir_normalized`

This axiom asserts that a relative path "**" is equivalent to "./**".

XXX: by the normalization standard, "**" and "./**" should really be the same;
however the Rust standard library treats them differently, so our specification
also does. This axiom exists to bridge the gap.

```rust
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
```


#### `lemma_fs_root_dir`

This axiom asserts that the root directory always exists.

```rust
pub axiom fn lemma_fs_root_dir(epoch: int)
    ensures
        Fs::file_exists(epoch, path_view![/]),
        Fs::file_is_dir(epoch, path_view![/]),
        ;
```


#### `lemma_fs_parent_dir`

This axiom asserts that the "**/.." file exists for any directory "**".

```rust
pub axiom fn lemma_fs_parent_dir(epoch: int, path: PathView)
    requires
        path.is_normalized(),
        Fs::file_exists(epoch, path),
        Fs::file_is_dir(epoch, path),
    ensures
        Fs::file_exists(epoch, path.join(seq!['.', '.', MAIN_SEPARATOR])),
        Fs::file_is_dir(epoch, path.join(seq!['.', '.', MAIN_SEPARATOR])),
        ;
```


#### `lemma_fs_parent`

This axiom asserts that the parent of an existent file also exists, and is a directory.

NOTE: "**/*/.." is not necessarily equivalent to "**" because of potential links.

```rust
pub axiom fn lemma_fs_parent(epoch: int, path: PathView)
    requires
        path.is_normalized(),
        path.len() > 0,
        Fs::file_exists(epoch, path),
    ensures
        Fs::file_exists(epoch, path.parent()),
        Fs::file_is_dir(epoch, path.parent()),
        ;
```


#### `lemma_fs_not_exists`

This axiom asserts that if a path does not exist, or if it exists but is not a directory,
then all subpaths cannot exist.

```rust
pub axiom fn lemma_fs_not_exists(epoch: int, path: PathView)
    requires
        path.is_normalized(),
        !Fs::file_exists(epoch, path) || (Fs::file_exists(epoch, path) && !Fs::file_is_dir(epoch, path)),
    ensures
        forall|subpath: PathView| #[trigger] subpath.parent() == path
            ==> !Fs::file_exists(epoch, subpath),
        ;
```


#### `lemma_fs_files_in_dir_finite`

This axiom asserts that the set `files_in_dir` is finite.

```rust
pub axiom fn lemma_fs_files_in_dir_finite(epoch: int, path: PathView)
    requires
        path.is_normalized(),
        Fs::file_exists(epoch, path),
        Fs::file_is_dir(epoch, path),
    ensures
        Fs::files_in_dir(epoch, path).finite(),
        ;
```


### `impl Fs`

```rust
impl Fs
```


#### `file_not_a_directory`

The error condition for `ErrorKind::NotADirectory` when treating `path` as a file.

```rust
pub open spec fn file_not_a_directory(epoch: int, path: PathView) -> bool {
    // part of the path is not a directory
    &&& path.len() > 1
    &&& exists|i: int| #![trigger path.ancestor(i)]
    1 <= i < path.len()
    && Fs::file_exists(epoch, path.ancestor(i))
    && !Fs::file_is_dir(epoch, path.ancestor(i))
    }
```


#### `exists`

Enables `fs::exists` (check if the path points at an existing entity).

```rust
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
```


#### `open`

Enables `File::open` (open a file in read-only mode).

```rust
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
```


#### `create`

Enables `File::create` (open a file in write-only mode; truncate if existent).

```rust
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
```


#### `create_new`

Enable `File::create_new` (creates a new file in *write* mode; error if the file exists).

```rust
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
```


#### `read`

Enable `fs::read` (reads the entire contents of a file into a bytes vector).

```rust
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
```


#### `read_to_string`

Enable `fs::read_to_string` (reads the entire contents of a file into a string).

```rust
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
```


#### `write`

Enable `fs::write` (writes a slice as the entire contents of a file.
This function will create a file if it does not exist, and will entirely replace its contents if it does).

```rust
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
```


#### `remove`

Enable `fs::remove_file` (removes a file from the filesystem).

```rust
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
```


#### `create_dir`

Enables `fs::create_dir` (creates a new, empty directory at the provided path).

```rust
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
```


#### `remove_dir`

Enables `fs::remove_dir` (removes an empty directory).

```rust
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
```


#### `read_dir`

Enables `fs::read_dir` (returns an iterator over the entries within a directory).

NOTE: the result of `read_dir` is unspecified if files are added to / removed from the directory
in between calls (https://pubs.opengroup.org/onlinepubs/007904875/functions/readdir_r.html),
in which case specification becomes impossible.
As such, Verge tracks the number of outstanding `ReadDir`s with `read_dir_count`, and
further requires the count to be 0 before performing any operation that would alter
directories (e.g., creating a file). Note that banning access of the entire file system
is necessary because of potential links - `Fs::create` may create a file under
a `ReadDir`-referenced directory, even if the path appears lexically different.

```rust
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
```


#### `metadata`

Enables `fs::metadata` (queries the file system to get information about a file).

```rust
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
```
