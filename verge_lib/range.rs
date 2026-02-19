//! Specifications and lemmas for ranges.

use vstd::prelude::*;
use vstd::view::View;

use core::ops::{
    Bound, RangeBounds,
    Range, RangeInclusive,
    RangeTo, RangeFrom, RangeFull, RangeToInclusive,
};

verus! {

// TODO: RangeBounds, RangeBoundsSpec, Bound
// then the actual Range types 

// #[verifier::external_type_specification]
// pub struct ExBound<T>(Bound<T>);

// #[verifier::external_type_specification]
// pub struct ExRangeTo<T>(RangeTo<T>);

// #[verifier::external_type_specification]
// pub struct ExRangeFrom<T>(RangeFrom<T>);

// #[verifier::external_type_specification]
// pub struct ExRangeFull(RangeFull);

// #[verifier::external_type_specification]
// pub struct ExRangeToInclusive<T>(RangeToInclusive<T>);

// impl View for Range<T> {
//     type V = (Bound<T>, Bound<T>);

//     open spec fn view(&self) -> Self::V {
//         (Bound::Included(self.start), Bound::Excluded(self.end))
//     }
// }

// impl View for RangeInclusive<T> {
//     type V = (Bound<T>, Bound<T>);

//     open spec fn view(&self) -> Self::V {
//         (Bound::Included(self.start), Bound::Included(self.end))
//     }
// }

// impl View for RangeTo<T> {
//     type V = (Bound<T>, Bound<T>);

//     open spec fn view(&self) -> Self::V {
//         (Bound::Unbounded, Bound::Excluded(self.end))
//     }
// }

// impl View for RangeToInclusive<T> {
//     type V = (Bound<T>, Bound<T>);

//     open spec fn view(&self) -> Self::V {
//         (Bound::Unbounded, Bound::Included(self.end))
//     }
// }

// impl View for RangeFrom<T> {
//     type V = (Bound<T>, Bound<T>);

//     open spec fn view(&self) -> Self::V {
//         (Bound::Included(self.start), Bound::Unbounded)
//     }
// }

// impl View for RangeFull {
//     type V = (Bound<T>, Bound<T>);

//     open spec fn view(&self) -> Self::V {
//         (Bound::Included(self.start), Bound::Unbounded)
//     }
// }

} // verus!


