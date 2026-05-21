//! Specifications and lemmas for the `Iterator` trait.
//!
//! This module includes a template specification for various implementations 
//! of the `core::iter::Iterator` trait and its `next` method.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::std_specs::iter::*;

verus! {

/// This trait is used for specifying `(DoubleEnded)Iterator` types by adding the index and 
/// the full sequence as `spec` functions.
pub trait VergeIteratorView {
    type Item;

    spec fn seq(&self) -> Seq<Self::Item>;
    spec fn idx(&self) -> int;
    spec fn ridx(&self) -> int;
}

/// Adapter trait that bridges Verge's `VergeIteratorView`-based encoding 
/// into vstd's `IteratorSpec`-based encoding, due to the orphan rule banning Verge 
/// from implementing `IteratorSpec` for `std` iterator types.
pub trait VergeIterator: VergeIteratorView + Sized {
    type Target: Iterator<Item = <Self as VergeIteratorView>::Item>;

    /// Maps an `std` iterator type (view-based encoding) into a Verge iterator type 
    /// (`IteratorSpec`-based encoding).
    fn verge_iter(self) -> (ret: Self::Target)
        ensures 
            // only meant to be used for proper iterators
            Self::Target::obeys_prophetic_iter_laws(&ret),
            Self::Target::will_return_none(&ret),
            Self::Target::decrease(&ret) is Some,
            // briding sematics
            Self::Target::remaining(&ret) == self.seq().subrange(self.idx(), self.ridx()),
    ;
}

/// Use for `#[external_type_specification]` types.
//~doc-macro
macro_rules! impl_iterator_default {
    // no requires clause
    (
        $type:path as $vtype:path [$($gen:tt)*] where Item = $ity:ty
        [ $method:path ] ($($params:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator_default!(
            @impl $type as $vtype [$($gen)*] where Item = $ity
            [ $method ] ($($params)*) () -> |$seq| $($exp)+
        );
    };

    // with requires clause
    (
        $type:path as $vtype:path [$($gen:tt)*] where Item = $ity:ty
        [ $method:path ] ($($params:tt)*) requires($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator_default!(
            @impl $type as $vtype [$($gen)*] where Item = $ity
            [ $method ] ($($params)*) (requires $($requires)*) -> |$seq| $($exp)+
        );
    };

    // internal implementation
    (
        @impl $type:path as $vtype:path [$($gen:tt)*] where Item = $ity:ty
        [ $method:path ] ($($params:tt)*) ($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        verus! {
        // View-based encoding
        impl<$($gen)*> VergeIteratorView for $type<$($gen)*> {
            type Item = $ity;

            uninterp spec fn seq(&self) -> Seq<Self::Item>;
            uninterp spec fn idx(&self) -> int;
            uninterp spec fn ridx(&self) -> int;
        }
        pub assume_specification<$($gen)*> [ $method ] ($($params)*) -> (ret: $type<$($gen)*>)
            $($requires)*
            ensures
                ({
                    let $seq = ret.seq();
                    &&& ret.idx() == 0
                    &&& ret.ridx() == $seq.len()
                    &&& $($exp)+
                }),
            no_unwind
        ;
        pub assume_specification<$($gen)*> [ $type::<$($gen)*>::next ] 
            (this: &mut $type<$($gen)*>) -> (r: Option<$ity>)
            ensures
                final(this).seq() == old(this).seq(),
                final(this).ridx() == old(this).ridx(),
                ({
                    let old_idx = old(this).idx();
                    let old_seq = old(this).seq();
                    match r {
                        None => {
                            &&& final(this).idx() == old(this).idx()
                            &&& old_idx == old(this).ridx()
                            &&& 0 <= old_idx <= old_seq.len()
                        },
                        Some(k) => {
                            let new_idx = final(this).idx();
                            let new_seq = final(this).seq();
                            &&& 0 <= old_idx < old(this).ridx() <= old_seq.len()
                            &&& new_idx == old_idx + 1
                            &&& k == old_seq[old_idx]
                        },
                    }
                }),
        ;
        // IteratorSpec-based encoding
        pub struct $vtype<$($gen)*>($type<$($gen)*>);
        impl<$($gen)*> VergeIterator for $type<$($gen)*> {
            type Target = $vtype<$($gen)*>;

            fn verge_iter(self) -> (ret: Self::Target) {
                $vtype(self)
            }
        }
        impl<$($gen)*> $vtype<$($gen)*> {
            pub closed spec fn idx(self) -> int 
                { self.0.idx() }
            
            pub closed spec fn ridx(self) -> int 
                { self.0.ridx() }

            pub closed spec fn seq(self) -> Seq<<Self as core::iter::Iterator>::Item> 
                { self.0.seq() }
        }
        impl<$($gen)*> core::iter::Iterator for $vtype<$($gen)*> {
            type Item = $ity;

            fn next(&mut self) -> (ret: Option<$ity>) {
                self.0.next()
            }
        }
        impl<$($gen)*> IteratorSpecImpl for $vtype<$($gen)*> {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool 
                { true }
            open spec fn will_return_none(&self) -> bool 
                { true }
            open spec fn remaining(&self) -> Seq<<Self as core::iter::Iterator>::Item> 
                { self.seq().subrange(self.idx(), self.ridx()) }
            open spec fn decrease(&self) -> Option<nat> 
                { Some((self.ridx() - self.idx()) as nat) }
            open spec fn initial_value_relation(&self, init: &Self) -> bool {
                &&& init.seq() == self.seq()
                &&& init.idx() == self.idx()
                &&& init.ridx() == self.ridx()
            }
            open spec fn peek(&self, i: int) -> Option<<Self as core::iter::Iterator>::Item> {
                if 0 <= self.idx() + i < self.ridx() {
                    Some(self.seq()[self.idx() + i])
                } else {
                    None
                }
            }
        }
        }
    };
}

/// Use for `#[external_type_specification]` types.
//~doc-macro
macro_rules! impl_double_ended_iterator_default {
    (
        $type:path as $vtype:path [$($gen:tt)*] where Item = $ity:ty
    ) => {
        verus!{
        // View-based encoding
        pub assume_specification<$($gen)*> [ $type::<$($gen)*>::next_back ] 
            (this: &mut $type<$($gen)*>) -> (r: Option<$ity>)
            ensures
                final(this).seq() == old(this).seq(),
                final(this).idx() == old(this).idx(),
                ({
                    let old_ridx = old(this).ridx();
                    let old_seq = old(this).seq();
                    match r {
                        None => {
                            &&& final(this).ridx() == old(this).ridx()
                            &&& old_ridx == old(this).idx()
                            &&& 0 <= old_ridx <= old_seq.len()
                        },
                        Some(k) => {
                            let new_ridx = final(this).ridx();
                            let new_seq = final(this).seq();
                            &&& 0 <= old(this).idx() < old_ridx <= old_seq.len()
                            &&& new_ridx == old_ridx - 1
                            &&& k == old_seq[new_ridx]
                        },
                    }
                }),
        ;
        // IteratorSpec-based encoding
        impl<$($gen)*> core::iter::DoubleEndedIterator for $vtype<$($gen)*> {
            fn next_back(&mut self) -> (ret: Option<$ity>) {
                self.0.next_back()
            }
        }
        impl<$($gen)*> DoubleEndedIteratorSpecImpl for $vtype<$($gen)*> {
            open spec fn peek_back(&self, index: int) -> Option<<Self as core::iter::Iterator>::Item> {
                if self.idx() <= self.ridx() - index - 1 < self.seq().len() {
                    Some(self.seq()[self.ridx() - index - 1])
                } else {
                    None
                }
            }
        }
        }
    };
}

/// Use for Verge-defined wrapped types.
//~doc-macro
macro_rules! impl_iterator_verge {
    // no requires clause
    (
        $type:path [$($gen:tt)*] where Item = $ity:ty
        [ $method:ident via $implfn:path ] ($($arg:ident : $aty:ty),+) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator_verge!(
            @impl $type [$($gen)*] where Item = $ity
            [ $method via $implfn ] ($($arg : $aty),+) () -> |$seq| $($exp)+
        );
    };

    // with requires clause
    (
        $type:path [$($gen:tt)*] where Item = $ity:ty
        [ $method:ident via $implfn:path ] ($($arg:ident : $aty:ty),+) requires($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator_verge!(
            @impl $type [$($gen)*] where Item = $ity
            [ $method via $implfn ] ($($arg : $aty),+) (requires $($requires)*) -> |$seq| $($exp)+
        );
    };

    // internal implementation
    (
        @impl $type:path [$($gen:tt)*] where Item = $ity:ty
        [ $method:ident via $implfn:path ] ($($arg:ident : $aty:ty),+) ($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        verus! {
        // View-based encoding
        impl<$($gen)*> VergeIteratorView for $type<$($gen)*> {
            type Item = $ity;

            uninterp spec fn seq(&self) -> Seq<Self::Item>;
            uninterp spec fn idx(&self) -> int;
            uninterp spec fn ridx(&self) -> int;
        }
        #[verifier::external_body]
        pub fn $method<$($gen)*>($($arg: $aty),+) -> (ret: $type<$($gen)*>) 
            $($requires)*
            ensures
                ({
                    let $seq = ret.seq();
                    &&& ret.idx() == 0
                    &&& ret.ridx() == $seq.len()
                    &&& $($exp)+
                }),
            no_unwind
        {
            $type($implfn($($arg),+))
        } 
        impl<$($gen)*> core::iter::Iterator for $type<$($gen)*> {
            type Item = $ity;
            #[verifier::external_body]
            fn next(&mut self) -> (r: Option<Self::Item>)
                ensures
                    final(self).seq() == old(self).seq(),
                    final(self).ridx() == old(self).ridx(),
                    ({
                        let old_idx = old(self).idx();
                        let old_seq = old(self).seq();
                        match r {
                            None => {
                                &&& final(self).idx() == old(self).idx()
                                &&& old_idx == old(self).ridx()
                                &&& 0 <= old_idx <= old_seq.len()
                            },
                            Some(k) => {
                                let new_idx = final(self).idx();
                                let new_seq = final(self).seq();
                                &&& 0 <= old_idx < old(self).ridx() <= old_seq.len()
                                &&& new_idx == old_idx + 1
                                &&& k == old_seq[old_idx]
                            },
                        }
                    }),
            {
                self.0.next()
            }
        }
        }
    };
}

/// Use for Verge-defined wrapped types.
//~doc-macro
#[allow(unused_macros)]
macro_rules! impl_double_ended_iterator_verge {
    (
        $type:path [$($gen:tt)*] where Item = $ity:ty
    ) => {
        verus! {
        impl<$($gen)*> core::iter::DoubleEndedIterator for $type<$($gen)*> {
            #[verifier::external_body]
            fn next_back(&mut self) -> (r: Option<Self::Item>)
                ensures
                    final(self).seq() == old(self).seq(),
                    final(self).idx() == old(self).idx(),
                    ({
                        let old_ridx = old(self).ridx();
                        let old_seq = old(self).seq();
                        match r {
                            None => {
                                &&& final(self).ridx() == old(self).ridx()
                                &&& old_ridx == old(self).idx()
                                &&& 0 <= old_ridx <= old_seq.len()
                            },
                            Some(k) => {
                                let new_ridx = final(self).ridx();
                                let new_seq = final(self).seq();
                                &&& 0 <= old(self).idx() < old_ridx <= old_seq.len()
                                &&& new_ridx == old_ridx - 1
                                &&& k == old_seq[new_ridx]
                            },
                        }
                    }),
            {
                self.0.next_back()
            }
        }
        }
    };
}

pub(crate) use impl_iterator_default;
pub(crate) use impl_double_ended_iterator_default;
pub(crate) use impl_iterator_verge;
pub(crate) use impl_double_ended_iterator_verge;

} // verus!