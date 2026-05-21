//! Specifications and lemmas for string pattern related operations.
//!
//! ## Methodology
//! To specify `str::split`, `str::matches`, and other methods that make use of 
//! the `std::str::Pattern` trait, Verge models the `Pattern` trait by directly 
//! adding the method specs to relevant types.

use super::*;
use core::str::pattern::Pattern;

verus! {

#[verifier::external_trait_specification]
pub trait ExPattern: Sized {
    type ExternalTraitSpecificationFor: Pattern;
}

}