//! Specifications for errors and error semantics in Verus.
//!
//! By the nature of errors, error semantics (a.k.a., the precise pre- and post-conditions of errors)
//! is often incomplete. At some point the specification must call it a day and accept under-specified
//! errors. 
//! In this case, Verge uses the `is_*_error()` spec functions on the `ErrorSpec` trait to convery a little 
//! more information and help specify program behavior. Ideally, Verge allows a Verus program's spec to
//! be complete up to Verge's API boundary (in many cases, also the `std` and OS boundary); any error 
//! beyond is at least tagged by the `is_*_error()` predicates. For example, for a program that does file I/O, 
//! Verge allows its spec to be "either returns `Ok` (success semantics), or returns `Err` and the error 
//! is a file system error (incomplete error semantics)".

use vstd::prelude::*;
pub use std::error::Error;
use std::fmt::{Display, Debug};

verus! {

// XXX: `std::error::Error` cannot be introduced due to a Verus bug

/// Extends types with error semantics.
/// 
/// The tagging methods are neither exhaustive nor orthogonal. Verge will 
/// likely add more of these as it expands to more domains.
pub trait ErrorSpec: Sized {

    /// Tags this error as a file system error.
    closed spec fn is_fs_error(self) -> bool 
        { is_fs_error(self) }

    /// Tags this error as a standard I/O error.
    closed spec fn is_stdio_error(self) -> bool
        { is_stdio_error(self) }

    /// Tags this error as a string UTF-8 conversion error.
    closed spec fn is_str_utf8_error(self) -> bool
        { is_str_utf8_error(self) }

    /// Tags this error as a string parsing error.
    closed spec fn is_str_parse_error(self) -> bool
        { is_str_parse_error(self) }
}

uninterp spec fn is_fs_error<T>(t: T) -> bool;
uninterp spec fn is_stdio_error<T>(t: T) -> bool;
uninterp spec fn is_str_utf8_error<T>(t: T) -> bool;
uninterp spec fn is_str_parse_error<T>(t: T) -> bool;

} // verus!