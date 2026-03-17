//! Specifications and lemmas for file system metadata.

use super::*;

pub use std::fs::Metadata;

verus! {

/// Metadata information about a file.
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExMetadata(Metadata);

/// The `MetadataSpec` trait specifies `Metadata`s.
pub trait MetadataSpec {
    /// Epoch of the file metadata when it is queried.
    spec fn epoch(&self) -> int;
    /// Path of the file metadata as it is queried.
    spec fn path(&self) -> PathView;

    /// Invariant of the metadata.
    spec fn inv(&self) -> bool;
}

impl MetadataSpec for Metadata {
    uninterp spec fn epoch(&self) -> int;
    uninterp spec fn path(&self) -> PathView;

    open spec fn inv(&self) -> bool {
        self.path().is_valid()
    }
}

/// Enable `Metadata::is_dir`.
pub assume_specification [ Metadata::is_dir ] (m: &Metadata) -> (ret: bool)
    returns
        Fs::file_is_dir(m.epoch(), m.path()),
    no_unwind
;

/// Enable `Metadata::len`.
pub assume_specification [ Metadata::len ] (m: &Metadata) -> (ret: u64)
    ensures
        ret as nat == Fs::file_when(m.epoch(), m.path()).len(),
    no_unwind
;

/// Enable `<Metadata as Clone>::clone`.
pub assume_specification [ <Metadata as Clone>::clone ] (this: &Metadata) -> (ret: Metadata)
    ensures
        ret == *this,
;

} // verus!