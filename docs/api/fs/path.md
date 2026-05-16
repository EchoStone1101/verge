# `verge::fs::path`

Specifications and lemmas for file system paths.

Verge models paths lexically with `PathView`; see the documentation of `PathView`
for details.


## Structs


### `ExPath`

A slice of a path (akin to `str`).
Paths are separated by `/` (`path::MAIN_SEPARATOR`).

```rust
pub struct ExPath(Path);
```


### `ExPathBuf`

An owned, mutable path (akin to `String`).

```rust
pub struct ExPathBuf(PathBuf);
```


### `PathView`

The `PathView` type represents a path in `spec`. For example, `path_view![/ "verge/", "lib/"]`.
It also enables *lexical* reasoning about path relations.

Note that lexically valid paths can still be invalid for the actual file system; e.g., a `Path` on Unix systems
can contain `\0`, but that path is invalid for the FS.

```rust
pub struct PathView
```


### `Ancestors`

```rust
pub struct Ancestors<'a>(std::path::Ancestors<'a>);
```


### `ExAncestors`

Enable `std::path::Ancestors` as an iterator.

```rust
pub struct ExAncestors<'a>(Ancestors<'a>);
```


### `Iter`

```rust
pub struct Iter<'a>(std::path::Iter<'a>);
```


### `ExIter`

Enable `std::path::Iter` as an iterator.

```rust
pub struct ExIter<'a>(Iter<'a>);
```


## Traits


### `AsPathView`

The `AsPathView` trait allows strings (`Seq<char>`) to be viewed as paths (`PathView`).

The `lemma_str_as_path_*` axioms fully specify this conversion.

```rust
pub trait AsPathView
```


#### `as_path`

```rust
spec fn as_path(self) -> PathView;
```


### `PathAdditionalFns`

This trait adds additional methods to the `Path` type.

```rust
pub trait PathAdditionalFns
```


#### `str_view`

```rust
spec fn str_view(&self) -> Seq<char>;
```


#### `view`

```rust
spec fn view(&self) -> PathView;
```


#### `new`

```rust
fn new(s: &str) -> &Path
    no_unwind;
```


#### `as_str`

```rust
fn as_str(&self) -> &str
    no_unwind;
```


#### `filename`

```rust
fn filename(&self) -> Option<&str>
    no_unwind;
```


#### `starts_with`

```rust
fn starts_with(&self, base: &Path) -> bool
    no_unwind;
```


#### `ends_with`

```rust
fn ends_with(&self, child: &Path) -> bool
    no_unwind;
```


### `PathBufAdditionalFns`

This trait adds additional methods to the `PathBuf` type.

```rust
pub trait PathBufAdditionalFns
```


#### `str_view`

```rust
spec fn str_view(&self) -> Seq<char>;
```


#### `view`

```rust
spec fn view(&self) -> PathView;
```


#### `as_str`

```rust
fn as_str(&self) -> &str
    no_unwind;
```


#### `into_string`

```rust
fn into_string(self) -> String
    no_unwind;
```


#### `push`

```rust
fn push(&mut self, path: &Path);
```


## Functions


### `axiom_main_separator_literal`

Proof that reveals the literal value of `MAIN_SEPARATOR`.

```rust
pub broadcast axiom fn axiom_main_separator_literal()
    ensures (#[trigger] MAIN_SEPARATOR) == '/'
        ;
```


### `lemma_str_as_path_empty`

`as_path` for empty strings produce an empty relative path.

```rust
pub axiom fn lemma_str_as_path_empty(s: Seq<char>)
    requires
        s.len() == 0,
    ensures
        s.as_path() == path_view![],
        ;
```


### `lemma_str_as_path_trailing_sep`

Adding a missing trailing separator for non empty strings does not change `as_path`.

```rust
pub axiom fn lemma_str_as_path_trailing_sep(s: Seq<char>)
    requires
        s.len() > 0 && s.last() != MAIN_SEPARATOR,
    ensures
        s.as_path() == s.push(MAIN_SEPARATOR).as_path(),
        ;
```


### `lemma_str_as_path_split`

`as_path` works by splitting at the separator for a separator-terminated string.

```rust
pub axiom fn lemma_str_as_path_split(s: Seq<char>, p: PathView)
    requires
        s.as_path() == p,
        s.last() == MAIN_SEPARATOR,
    ensures
        p.is_valid(),
        s.first() == MAIN_SEPARATOR <==> p.abs,
        p.abs ==> s == seq![MAIN_SEPARATOR] + p.path.flatten(),
        !p.abs ==> s == p.path.flatten(),
        ;
```


### `lemma_str_as_path_valid`

Proof that any `s.as_path()` is lexically valid for any string `s`.

```rust
pub broadcast proof fn lemma_str_as_path_valid(s: Seq<char>)
    ensures
        #[trigger] s.as_path().is_valid(),
```


### `Path::to_path_buf`

Enable `Path::to_path_buf`.

```rust
pub assume_specification [ Path::to_path_buf ] (p: &Path) -> (ret: PathBuf)
    ensures
        ret.str_view() == p.str_view(),
        ;
```


### `Path::is_absolute`

Enable `Path::is_absolute`.

```rust
pub assume_specification [ Path::is_absolute ] (p: &Path) -> (ret: bool)
    returns
        p@.abs,
    no_unwind
        ;
```


### `Path::is_relative`

Enable `Path::path_is_relative`.

```rust
pub assume_specification [ Path::is_relative ] (p: &Path) -> (ret: bool)
    returns
        !p@.abs,
    no_unwind
        ;
```


### `Path::parent`

Enable `Path::parent`.

```rust
pub assume_specification [ Path::parent ] (p: &Path) -> (ret: Option<&Path>)
    ensures
        ({
            match ret {
                Some(parent) => {
                    &&& parent@.is_normalized()
                    &&& parent@ == p@.normalize().parent()
                },
                None => p@.normalize().path.len() == 0,
            }
        })
    no_unwind
        ;
```


### `impl_iterator_verge!(path_ancestors)`

```rust
impl_iterator_verge!(
    Ancestors['a] where Item = &'a Path
    [ path_ancestors via Path::ancestors ] (p: &'a Path) -> |seq| {
    let norm = p@.normalize();
    &&& seq.len() == norm.path.len() + 1
    &&& forall|i: int| #![trigger seq[i]] 0 <= i < seq.len()
    ==> {
    &&& seq[i]@.is_normalized()
    &&& seq[i]@.abs == p@.abs
    &&& seq[i]@.path == norm.path.take(norm.path.len() - i)
    }
    }
    );
```


### `path_iter`

Enables `Path::iter()`.

```rust
pub fn path_iter<'a>(p: &'a Path) -> (ret: Iter<'a>)
    ensures
        ({
            let (index, seq) = ret@;
            let norm = p@.normalize();
            &&& index == 0
            &&& !norm.abs ==> {
                &&& seq.len() == norm.path.len()
                &&& forall|i: int| #![trigger seq[i]] 0 <= i < seq.len()
                    ==> seq[i]@ == norm.path[i].drop_last()
            }
            &&& norm.abs ==> {
                &&& seq.len() == norm.path.len() + 1
                &&& seq[0]@ == seq![MAIN_SEPARATOR]
                &&& forall|i: int| #![trigger seq[i]] 0 <= i < seq.len()
                    ==> seq[i+1]@ == norm.path[i].drop_last()
            }
        }),
    no_unwind
```


### `PathBuf::new`

Enable `PathBuf::new`.

```rust
pub assume_specification [ PathBuf::new ] () -> (ret: PathBuf)
    ensures
        ret.str_view() == Seq::<char>::empty(),
    no_unwind
        ;
```


### `PathBuf::with_capacity`

Enable `PathBuf::with_capacity`.

```rust
pub assume_specification [ PathBuf::with_capacity ] (cap: usize) -> (ret: PathBuf)
    ensures
        ret.str_view() == Seq::<char>::empty(),
        ;
```


### `PathBuf::as_path`

Enable `PathBuf::as_path`.

```rust
pub assume_specification [ PathBuf::as_path ] (buf: &PathBuf) -> (ret: &Path)
    ensures
        ret.str_view() == buf.str_view(),
    no_unwind
        ;
```


### `PathBuf::clear`

Enable `PathBuf::clear`.

```rust
pub assume_specification [ PathBuf::clear ] (buf: &mut PathBuf)
    ensures
        buf.str_view() == Seq::<char>::empty(),
    no_unwind
        ;
```


### `PathBuf::pop`

Enable `PathBuf::pop`.

```rust
pub assume_specification [ PathBuf::pop ] (buf: &mut PathBuf) -> (ret: bool)
    ensures
        ({
            let norm = old(buf)@.normalize();
            &&& ret == (norm.path.len() > 0)
            &&& ret ==> buf@.normalize() == norm.parent()
            &&& !ret ==> *buf == *old(buf)
        }),
    no_unwind
        ;
```


### `<PathBuf as Clone>::clone`

Enable `<PathBuf as Clone>::clone`.

```rust
pub assume_specification [ <PathBuf as Clone>::clone ] (this: &PathBuf) -> (ret: PathBuf)
    ensures
        ret == *this,
        ;
```


### `<Path as PartialEq>::eq`

Enable `<Path as PartialEq>::eq`.

```rust
pub assume_specification<'a, 'b> [ <Path as PartialEq>::eq ] (this: &'a Path, other: &'b Path) -> (ret: bool)
    returns
        this@.normalize() == other@.normalize(),
    no_unwind
        ;
```


### `<PathBuf as PartialEq>::eq`

Enable `<PathBuf as PartialEq>::eq`.

```rust
pub assume_specification<'a, 'b> [ <PathBuf as PartialEq>::eq ] (this: &'a PathBuf, other: &'b PathBuf) -> (ret: bool)
    returns
        this@.normalize() == other@.normalize(),
    no_unwind
        ;
```


### `<Path as PartialEq<PathBuf>>::eq`

Enable `<Path as PartialEq<PathBuf>>::eq`.

```rust
pub assume_specification<'a, 'b> [ <Path as PartialEq<PathBuf>>::eq ] (this: &'a Path, other: &'b PathBuf) -> (ret: bool)
    returns
        this@.normalize() == other@.normalize(),
    no_unwind
        ;
```


### `<PathBuf as PartialEq<Path>>::eq`

Enable `<PathBuf as PartialEq<Path>>::eq`.

```rust
pub assume_specification<'a, 'b> [ <PathBuf as PartialEq<Path>>::eq ] (this: &'a PathBuf, other: &'b Path) -> (ret: bool)
    returns
        this@.normalize() == other@.normalize(),
    no_unwind
        ;
```


### `<Path as PartialEq<str>>::eq`

Enable `<Path as PartialEq<str>>::eq`.

```rust
pub assume_specification<'a, 'b> [ <Path as PartialEq<str>>::eq ] (this: &'a Path, other: &'b str) -> (ret: bool)
    returns
        this@.normalize() == other@.as_path().normalize(),
    no_unwind
        ;
```


### `<Path as PartialEq<String>>::eq`

Enable `<Path as PartialEq<String>>::eq`.

```rust
pub assume_specification<'a, 'b> [ <Path as PartialEq<String>>::eq ] (this: &'a Path, other: &'b String) -> (ret: bool)
    returns
        this@.normalize() == other@.as_path().normalize(),
    no_unwind
        ;
```


### `<PathBuf as PartialEq<str>>::eq`

Enable `<PathBuf as PartialEq<str>>::eq`.

```rust
pub assume_specification<'a, 'b> [ <PathBuf as PartialEq<str>>::eq ] (this: &'a PathBuf, other: &'b str) -> (ret: bool)
    returns
        this@.normalize() == other@.as_path().normalize(),
    no_unwind
        ;
```


### `<PathBuf as PartialEq<String>>::eq`

Enable `<PathBuf as PartialEq<String>>::eq`.

```rust
pub assume_specification<'a, 'b> [ <PathBuf as PartialEq<String>>::eq ] (this: &'a PathBuf, other: &'b String) -> (ret: bool)
    returns
        this@.normalize() == other@.as_path().normalize(),
    no_unwind
        ;
```


### `<str as PartialEq<Path>>::eq`

Enable `<str as PartialEq<Path>>::eq`.

```rust
pub assume_specification<'a, 'b> [ <str as PartialEq<Path>>::eq ] (this: &'a str, other: &'b Path) -> (ret: bool)
    returns
        this@.as_path().normalize() == other@.normalize(),
    no_unwind
        ;
```


### `<str as PartialEq<PathBuf>>::eq`

Enable `<str as PartialEq<PathBuf>>::eq`.

```rust
pub assume_specification<'a, 'b> [ <str as PartialEq<PathBuf>>::eq ] (this: &'a str, other: &'b PathBuf) -> (ret: bool)
    returns
        this@.as_path().normalize() == other@.normalize(),
    no_unwind
        ;
```


### `<String as PartialEq<Path>>::eq`

Enable `<String as PartialEq<Path>>::eq`.

```rust
pub assume_specification<'a, 'b> [ <String as PartialEq<Path>>::eq ] (this: &'a String, other: &'b Path) -> (ret: bool)
    returns
        this@.as_path().normalize() == other@.normalize(),
    no_unwind
        ;
```


### `<String as PartialEq<PathBuf>>::eq`

Enable `<String as PartialEq<PathBuf>>::eq`.

```rust
pub assume_specification<'a, 'b> [ <String as PartialEq<PathBuf>>::eq ] (this: &'a String, other: &'b PathBuf) -> (ret: bool)
    returns
        this@.as_path().normalize() == other@.normalize(),
    no_unwind
        ;
```


## Implementations


### `impl PathView`

```rust
impl PathView
```


#### `len`

This function encodes the length (number of segments) of a `PathView`.

```rust
pub open spec fn len(self) -> nat
    { self.path.len() }
```


#### `is_valid`

Whether the path is lexically valid:
- segments in a path view must end with separators;
- segments cannot contain separators in any other position;
- for a relative path, segments cannot be `/` at the front (in which case the path should be absolute);
For example, `path_view!["a"@, "b/"@, "c/"@]`, `path_view!["a/"@, "b/c/"@]`, and
`path_view!["/"@, "a/"@, "b/"@, "c/"@]` are all invalid.

```rust
pub open spec fn is_valid(self) -> bool {
    forall|i: int| #![trigger self.path[i]] 0 <= i < self.path.len()
    ==> {
    &&& self.path[i].len() > 0
    &&& self.path[i].last() == MAIN_SEPARATOR
    &&& !self.path[i].drop_last().contains(MAIN_SEPARATOR)
    &&& (self.path[i] == seq![MAIN_SEPARATOR] && !self.abs) ==> i > 0
    }
    }
```


#### `is_normalized`

Whether the path is normalized.

Normalization is defined as in `Path::components()`; in short:
- no `/` segments (i.e., consecutive separators);
- no `./` segements except when at the front and the path is relative;

```rust
pub open spec fn is_normalized(self) -> bool {
    &&& self.is_valid()
    &&& forall|i: int| 0 <= i < self.path.len() ==> #[trigger] self.path[i] != seq![MAIN_SEPARATOR]
    &&& forall|i: int| 0 <= i < self.path.len()
    ==> (#[trigger] self.path[i]) != seq!['.', MAIN_SEPARATOR] || (i == 0 && !self.abs)
    }
```


#### `normalize`

Converts a valid path into its normalized form.

```rust
pub open spec fn normalize(self) -> PathView
    recommends self.is_valid(),
        {
        if !self.abs && self.path.first() == seq!['.', MAIN_SEPARATOR] {
        PathView {
            abs: false,
            path: seq![seq!['.', MAIN_SEPARATOR]] + self.path.drop_first()
                .filter(|s: Seq<char>| s != seq![MAIN_SEPARATOR] && s != seq!['.', MAIN_SEPARATOR])
        }
        } else {
        PathView {
            abs: self.abs,
            path: self.path.filter(|s: Seq<char>| s != seq![MAIN_SEPARATOR] && s != seq!['.', MAIN_SEPARATOR])
        }
        }
        }
```


#### `parent`

This function encodes the parent of a path, if there is one.

Notably, the parent of the root directory (`/`) does *not* exist - not to be confused
with `/../`, which is lexically a different path.

```rust
pub open spec fn parent(self) -> PathView
    recommends
        self.is_normalized(),
        self.path.len() > 0,
        {
        PathView {
        abs: self.abs,
        path: self.path.drop_last(),
        }
        }
```


#### `filename`

This function encodes the file name part (i.e., final segment) of a path, if there is one.

Notably, a path that terminates in `..` does not have a file name.

```rust
pub open spec fn filename(self) -> Seq<char>
    recommends
        self.is_normalized(),
        self.path.len() > 0,
        self.path.last() != seq!['.', '.', MAIN_SEPARATOR],
        {
        self.path.last().drop_last()
        }
```


#### `join`

This function encodes the path obtained by joining a path by a name.

```rust
pub open spec fn join(self, name: Seq<char>) -> PathView {
    PathView {
    abs: self.abs,
    path: self.path.push(name),
    }
    }
```


#### `ancestor`

This function encodes the `i`-th ancestor of a path, numbered from the root.

```rust
pub open spec fn ancestor(self, i: int) -> PathView
    recommends
        0 <= i <= self.len(),
        {
        PathView {
        abs: self.abs,
        path: self.path.take(i),
        }
        }
```
