//! Specifications and lemmas for file system paths.

use super::*;
use crate::iter::{IteratorView, impl_iterator_verge};

pub use std::path::{
    Path, PathBuf,
};

verus! {

/// A slice of a path (akin to `str`).
/// Paths are separated by `/` (`path::MAIN_SEPARATOR`).
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExPath(Path);

/// An owned, mutable path (akin to `String`).
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExPathBuf(PathBuf);

/// Enable `path::MAIN_SEPARATOR`.
#[verifier::external_body]
pub const MAIN_SEPARATOR: char = std::path::MAIN_SEPARATOR;

#[verifier::external_body]
pub broadcast axiom fn axiom_main_separator_literal()
    ensures (#[trigger] MAIN_SEPARATOR) == '/'
;

/// The `PathView` type represents a path in `spec`. For example, `path_view!["/", "verge/", "lib/"]`.
/// It also enables *lexical* reasoning about path relations.
/// 
/// Note that lexically valid paths can still be invalid for the actual file system; e.g., a `Path` on Unix systems 
/// can contain `\0`, but that path is invalid for the FS.
pub struct PathView {
    /// Whether the path is absolute (starts with the separator).
    pub abs: bool,
    /// Path, segmented by the separator.
    pub path: Seq<Seq<char>>,
}

impl PathView {

    pub open spec fn len(self) -> nat 
        { self.path.len() }

    /// Whether the path is lexically valid.
    /// 
    /// Segments in a path view must end with separators. Further, segments cannot contain separators 
    /// in any other position, as it maps into an impossible file system entity. 
    /// For example, `path_view!["a/"@, "b/c/"@]` can never exist as a file.
    pub open spec fn is_valid(self) -> bool {
        forall|i: int| #![trigger self.path[i]] 0 <= i < self.path.len()
            ==> {
                &&& self.path[i].len() > 0 
                &&& self.path[i].last() == MAIN_SEPARATOR
                &&& !self.path[i].drop_last().contains(MAIN_SEPARATOR)
            }
    }

    /// Whether the path is normalized.
    /// 
    /// Normalization is defined as in `Path::components()`; in short:
    /// - no `/` segments (i.e., consecutive separators);
    /// - no `./` segements except when at the front and the path is relative;
    pub open spec fn is_normalized(self) -> bool {
        &&& self.is_valid()
        &&& forall|i: int| 0 <= i < self.path.len() ==> #[trigger] self.path[i] != seq![MAIN_SEPARATOR]
        &&& forall|i: int| 0 <= i < self.path.len() 
            ==> (#[trigger] self.path[i]) != seq!['.', MAIN_SEPARATOR] || (i == 0 && !self.abs)
    }

    /// Converts a valid path into its normalized form.
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

    /// This function encodes the parent of a path, if there is one.
    /// 
    /// Notably, the parent of the root directory (`/`) does *not* exist; not to be confused 
    /// with `/..` which is lexically a different path.
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

    /// This function encodes the file name part (i.e., final segment) of a path, if there is one.
    ///
    /// Notably, a path that terminates in `..` does not have a file name.
    pub open spec fn filename(self) -> Seq<char>
        recommends
            self.is_normalized(),
            self.path.len() > 0,
            self.path.last() != seq!['.', '.', MAIN_SEPARATOR],
    {
        self.path.last().drop_last()
    }

    /// This function encodes the path obtained by joining a path by a name.
    pub open spec fn join(self, name: Seq<char>) -> PathView {
        PathView {
            abs: self.abs,
            path: self.path.push(name),
        }
    }

    /// This function encodes the `i`-th ancestor of a path, numbered from the left.
    pub open spec fn ancestor(self, i: int) -> PathView 
        recommends
            0 <= i <= self.len(),
    {
        PathView {
            abs: self.abs,
            path: self.path.take(i),
        }
    }

}

#[doc(hidden)]
#[macro_export]
macro_rules! path_internal {
    [$abs:expr $(,)?] => {
        $crate::verge::fs::path::PathView {
            abs: $abs,
            path: vstd::seq::Seq::<Seq<char>>::empty(),
        }
    };
    [$abs:expr, $elem:expr $(,)?] => {
        $crate::verge::fs::path::PathView {
            abs: $abs,
            path: vstd::seq::Seq::empty().push($elem),
        }
    };
    [$abs:expr, $($elem:expr),+ $(,)?] => {
        $crate::verge::fs::path::PathView {
            abs: $abs,
            path: <_ as vstd::view::View>::view(&[$($elem),+]),
        }
    };
}

/// Creates a `PathView` containing the given segments.
/// 
/// Examples:
/// ```rust
/// path_view!["tmp/"@, "playground/"@]             // `tmp/playground`
/// path_view![/ "this/"@, "is/"@, "absolute/"@]    // `/this/is/absolute`
/// path_view!["an"@, "invalid/path/"@]             
/// path_view!["valid/"@, "/"@, "but/"@, "not/"@, "./"@, "normalized/"@] // `valid//but/not/./normalized`
/// ```
#[macro_export]
macro_rules! path_view {
    [/ $($tail:tt)*] => {
        vstd::prelude::verus_proof_macro_exprs!(
            $crate::verge::fs::path::path_internal!(true, $($tail)*)
        )
    };
    [$($tail:tt)*] => {
        vstd::prelude::verus_proof_macro_exprs!(
            $crate::verge::fs::path::path_internal!(false, $($tail)*)
        )
    };
}

#[doc(hidden)]
pub use path_internal;
pub use path_view;

/// The `AsPathView` trait allows strings (`Seq<char>`) to be viewed as paths (`PathView`).
/// 
/// The `lemma_str_as_path_*` axioms fully specify this conversion.
pub trait AsPathView {
    spec fn as_path(self) -> PathView;
}

impl AsPathView for Seq<char> {

    /// View a string as a path. 
    uninterp spec fn as_path(self) -> PathView; 
}

/// `as_path` for empty strings produce an empty relative path.
#[verifier::external_body]
pub axiom fn lemma_str_as_path_empty(s: Seq<char>)
    requires 
        s.len() == 0,
    ensures
        s.as_path() == path_view![],
;

/// Adding a missing trailing separator for non empty strings does not change `as_path`. 
#[verifier::external_body]
pub axiom fn lemma_str_as_path_trailing_sep(s: Seq<char>)
    requires 
        s.len() > 0 && s.last() != MAIN_SEPARATOR,
    ensures
        s.as_path() == s.push(MAIN_SEPARATOR).as_path(),
;

/// `as_path` works by splitting at the separator for separator-terminated strings.
#[verifier::external_body]
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

/// Proof that any `s.as_path()` is lexically valid for any `s`.
pub broadcast proof fn lemma_str_as_path_valid(s: Seq<char>)
    ensures
        #[trigger] s.as_path().is_valid(),
{
    if s.len() == 0 {
        lemma_str_as_path_empty(s);
    } else if s.last() != MAIN_SEPARATOR {
        lemma_str_as_path_trailing_sep(s);
        let p = s.push(MAIN_SEPARATOR).as_path();
        lemma_str_as_path_split(s.push(MAIN_SEPARATOR), p);
    } else {
        let p = s.as_path();
        lemma_str_as_path_split(s, p);
    }
}

/// This trait adds additional methods to the `Path` type.
pub trait PathAdditionalFns {
    spec fn str_view(&self) -> Seq<char>;
    spec fn view(&self) -> PathView;

    fn new(s: &str) -> &Path
        no_unwind;
    fn as_str(&self) -> &str
        no_unwind;
    fn filename(&self) -> Option<&str>
        no_unwind;
    fn starts_with(&self, base: &Path) -> bool
        no_unwind;
    fn ends_with(&self, child: &Path) -> bool
        no_unwind;
}

impl PathAdditionalFns for Path {

    /// Verge currently models paths as UTF-8 strings instead of the more accurate `OsString`s. 
    /// See the top-level comment of `fs` for more details.
    uninterp spec fn str_view(&self) -> Seq<char>;

    open spec fn view(&self) -> PathView 
        { self.str_view().as_path() }

    /// Directly wraps a string slice as a `Path` slice.
    #[verifier::external_body]
    fn new(s: &str) -> (ret: &Path)
        ensures
            ret.str_view() == s@,
    {
        Path::new(s)
    }

    /// Yields the underlying string slice.
    /// 
    /// Note that this no longer requires checking because paths are UTF-8 in Verge.
    #[verifier::external_body]
    fn as_str(&self) -> (ret: &str)
        ensures
            ret@ == self.str_view(),
    {
        unsafe { str::from_utf8_unchecked(self.as_os_str().as_encoded_bytes()) }
    }

    /// Returns the final component of the `Path`, if there is one.
    /// 
    /// Returns `None` if the path terminates in `..`.
    #[verifier::external_body]
    fn filename(&self) -> (ret: Option<&str>)
        ensures
            ({
                let norm = self@.normalize();
                match ret {
                    Some(name) => {
                        &&& name@ == norm.filename()
                        &&& name@ != seq!['.', '.']
                    },
                    None => norm.path.len() == 0 || norm.path.last() == seq!['.', '.', MAIN_SEPARATOR],
                }
            })
    {
        match self.file_name() {
            Some(s) => unsafe { Some(str::from_utf8_unchecked(s.as_encoded_bytes())) },
            None => None,
        }
    }

    /// Determines whether `base` is a prefix of `self`.
    #[verifier::external_body]
    fn starts_with(&self, base: &Path) -> (ret: bool)
        returns
            self@.abs == base@.abs && base@.normalize().path.is_prefix_of(self@.normalize().path),
    {
        self.starts_with(base)
    }

    /// Determines whether `child` is a suffix of `self`.
    #[verifier::external_body]
    fn ends_with(&self, child: &Path) -> (ret: bool)
        returns
            // `child` can be absolute only when it is exactly `self`
            (child@.abs == (self@.abs && child@.normalize().path == self@.normalize().path))
            && child@.normalize().path.is_suffix_of(self@.normalize().path),
    {
        self.ends_with(child)
    }

}

/// Enable `Path::to_path_buf`.
pub assume_specification [ Path::to_path_buf ] (p: &Path) -> (ret: PathBuf)
    ensures
        ret.str_view() == p.str_view(),
;

/// Enable `Path::is_absolute`.
pub assume_specification [ Path::is_absolute ] (p: &Path) -> (ret: bool)
    returns
        p@.abs,
    no_unwind
;

/// Enable `Path::path_is_relative`.
pub assume_specification [ Path::is_relative ] (p: &Path) -> (ret: bool)
    returns
        !p@.abs,
    no_unwind
;

/// Enable `Path::parent`.
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

/// Enable `std::path::Ancestors` as an iterator.
#[verifier::external]
pub struct Ancestors<'a>(std::path::Ancestors<'a>);
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExAncestors<'a>(Ancestors<'a>);

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

/// Enable `std::path::Iter` as an iterator.
#[verifier::external]
pub struct Iter<'a>(std::path::Iter<'a>);
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExIter<'a>(Iter<'a>);

impl<'a> IteratorView for Iter<'a> {
    type Item = &'a str;

    uninterp spec fn view(&self) -> (int, Seq<Self::Item>);
}

#[verifier::external_body]
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
{
    Iter(p.iter())
}

impl<'a> core::iter::Iterator for Iter<'a> {
    type Item = &'a str;

    #[verifier::external_body]
    fn next(&mut self) -> (r: Option<Self::Item>)
        ensures
            ({
                let (old_index, old_seq) = old(self)@;
                match r {
                    None => {
                        &&& self@ == old(self)@
                        &&& old_index >= old_seq.len()
                    },
                    Some(k) => {
                        let (new_index, new_seq) = self@;
                        &&& 0 <= old_index < old_seq.len()
                        &&& new_seq == old_seq
                        &&& new_index == old_index + 1
                        &&& k == old_seq[old_index]
                    },
                }
            }),
    {
        match self.0.next() {
            Some(s) => unsafe { Some(str::from_utf8_unchecked(s.as_encoded_bytes())) },
            None => None,
        }
    }
}

/// This trait adds additional methods to the `PathBuf` type.
pub trait PathBufAdditionalFns {
    spec fn str_view(&self) -> Seq<char>;
    spec fn view(&self) -> PathView;

    fn as_str(&self) -> &str
        no_unwind;
    fn into_string(self) -> String 
        no_unwind;
    fn push(&mut self, path: &Path);
}

impl PathBufAdditionalFns for PathBuf {

    uninterp spec fn str_view(&self) -> Seq<char>;

    open spec fn view(&self) -> PathView 
        { self.str_view().as_path() }

    /// Yields the underlying string slice.
    /// 
    /// Note that this no longer requires checking because paths are UTF-8 in Verge.
    #[verifier::external_body]
    fn as_str(&self) -> (ret: &str)
        ensures
            ret@ == self.str_view(),
    {
        unsafe { str::from_utf8_unchecked(self.as_os_str().as_encoded_bytes()) }
    }

    /// Consumes the `PathBuf`, yielding its internal `String` storage.
    #[verifier::external_body]
    fn into_string(self) -> (ret: String)
        ensures
            ret@ == self.str_view(),
    {
        unsafe { String::from_utf8_unchecked(self.into_os_string().into_encoded_bytes()) }
    }

    /// Extends `self` with `path`.
    /// 
    /// If `path` is absolute, it replaces the current path.
    #[verifier::external_body]
    fn push(&mut self, path: &Path)
        ensures
            path@.abs ==> self.str_view() == path.str_view(),
            !path@.abs ==> {
                &&& self@.abs == old(self)@.abs
                &&& self@.path == old(self)@.path + path@.path
            },
    {
        self.push(path)
    }
}

/// Enable `PathBuf::new`.
pub assume_specification [ PathBuf::new ] () -> (ret: PathBuf)
    ensures
        ret.str_view() == Seq::<char>::empty(),
    no_unwind
;

/// Enable `PathBuf::with_capacity`.
pub assume_specification [ PathBuf::with_capacity ] (cap: usize) -> (ret: PathBuf)
    ensures
        ret.str_view() == Seq::<char>::empty(),
;

/// Enable `PathBuf::as_path`.
pub assume_specification [ PathBuf::as_path ] (buf: &PathBuf) -> (ret: &Path)
    ensures
        ret.str_view() == buf.str_view(),
    no_unwind
;

/// Enable `PathBuf::clear`.
pub assume_specification [ PathBuf::clear ] (buf: &mut PathBuf)
    ensures
        buf.str_view() == Seq::<char>::empty(),
    no_unwind
;

/// Enable `PathBuf::pop`.
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


// Trait specifications

/// Enable `<PathBuf as Clone>::clone`.
pub assume_specification [ <PathBuf as Clone>::clone ] (this: &PathBuf) -> (ret: PathBuf)
    ensures
        ret == *this,
;

/// Enable `<Path as PartialEq>::eq`.
pub assume_specification<'a, 'b> [ <Path as PartialEq>::eq ] (this: &'a Path, other: &'b Path) -> (ret: bool)
    returns
        this@.normalize() == other@.normalize(),
    no_unwind
;

/// Enable `<PathBuf as PartialEq>::eq`.
pub assume_specification<'a, 'b> [ <PathBuf as PartialEq>::eq ] (this: &'a PathBuf, other: &'b PathBuf) -> (ret: bool)
    returns
        this@.normalize() == other@.normalize(),
    no_unwind
;

/// Enable `<Path as PartialEq<PathBuf>>::eq`.
pub assume_specification<'a, 'b> [ <Path as PartialEq<PathBuf>>::eq ] (this: &'a Path, other: &'b PathBuf) -> (ret: bool)
    returns
        this@.normalize() == other@.normalize(),
    no_unwind
;

/// Enable `<PathBuf as PartialEq<Path>>::eq`.
pub assume_specification<'a, 'b> [ <PathBuf as PartialEq<Path>>::eq ] (this: &'a PathBuf, other: &'b Path) -> (ret: bool)
    returns
        this@.normalize() == other@.normalize(),
    no_unwind
;

/// Enable `<Path as PartialEq<str>>::eq`.
pub assume_specification<'a, 'b> [ <Path as PartialEq<str>>::eq ] (this: &'a Path, other: &'b str) -> (ret: bool)
    returns
        this@.normalize() == other@.as_path().normalize(),
    no_unwind
;

/// Enable `<Path as PartialEq<String>>::eq`.
pub assume_specification<'a, 'b> [ <Path as PartialEq<String>>::eq ] (this: &'a Path, other: &'b String) -> (ret: bool)
    returns
        this@.normalize() == other@.as_path().normalize(),
    no_unwind
;

/// Enable `<PathBuf as PartialEq<str>>::eq`.
pub assume_specification<'a, 'b> [ <PathBuf as PartialEq<str>>::eq ] (this: &'a PathBuf, other: &'b str) -> (ret: bool)
    returns
        this@.normalize() == other@.as_path().normalize(),
    no_unwind
;

/// Enable `<PathBuf as PartialEq<String>>::eq`.
pub assume_specification<'a, 'b> [ <PathBuf as PartialEq<String>>::eq ] (this: &'a PathBuf, other: &'b String) -> (ret: bool)
    returns
        this@.normalize() == other@.as_path().normalize(),
    no_unwind
;

/// Enable `<str as PartialEq<Path>>::eq`.
pub assume_specification<'a, 'b> [ <str as PartialEq<Path>>::eq ] (this: &'a str, other: &'b Path) -> (ret: bool)
    returns
        this@.as_path().normalize() == other@.normalize(),
    no_unwind
;

/// Enable `<str as PartialEq<PathBuf>>::eq`.
pub assume_specification<'a, 'b> [ <str as PartialEq<PathBuf>>::eq ] (this: &'a str, other: &'b PathBuf) -> (ret: bool)
    returns
        this@.as_path().normalize() == other@.normalize(),
    no_unwind
;

/// Enable `<String as PartialEq<Path>>::eq`.
pub assume_specification<'a, 'b> [ <String as PartialEq<Path>>::eq ] (this: &'a String, other: &'b Path) -> (ret: bool)
    returns
        this@.as_path().normalize() == other@.normalize(),
    no_unwind
;

/// Enable `<String as PartialEq<PathBuf>>::eq`.
pub assume_specification<'a, 'b> [ <String as PartialEq<PathBuf>>::eq ] (this: &'a String, other: &'b PathBuf) -> (ret: bool)
    returns
        this@.as_path().normalize() == other@.normalize(),
    no_unwind
;

// TODO(rilin): tests

} // verus!