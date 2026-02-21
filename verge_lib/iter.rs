//! Specifications and lemmas for the `Iterator` trait.
//!
//! This module includes a template specification for various implementations 
//! of the `core::iter::Iterator` trait and its `next` method.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// This trait adds the `view()` method for any iterator.
pub trait IteratorView {
    type Item;

    spec fn view(&self) -> (int, Seq<Self::Item>);
}

// TODO: enumerate and Enumerate

/// Use for `#[external_type_specification]` types.
macro_rules! impl_iterator_default {
    // no requires clause
    (
        $type:path [$($gen:tt)+] where Item = $ity:ty
        [ $method:path ] ($($params:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator_default!(
            @impl $type [$($gen)+] where Item = $ity
            [ $method ] ($($params)*) () -> |$seq| $($exp)+
        );
    };

    // with requires clause
    (
        $type:path [$($gen:tt)+] where Item = $ity:ty
        [ $method:path ] ($($params:tt)*) requires($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator_default!(
            @impl $type [$($gen)+] where Item = $ity
            [ $method ] ($($params)*) (requires $($requires)*) -> |$seq| $($exp)+
        );
    };

    // internal implementation
    (
        @impl $type:path [$($gen:tt)+] where Item = $ity:ty
        [ $method:path ] ($($params:tt)*) ($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        verus! {
        impl<$($gen)+> IteratorView for $type<$($gen)+> {
            type Item = $ity;

            uninterp spec fn view(&self) -> (int, Seq<Self::Item>);
        }
        pub assume_specification<$($gen)+> [ $method ] ($($params)*) -> (ret: $type<$($gen)+>)
            $($requires)*
            ensures
                ({
                    let (index, $seq) = ret@;
                    &&& index == 0
                    &&& $($exp)+
                }),
            no_unwind
        ;
        pub assume_specification<$($gen)+> [ $type::<$($gen)+>::next ] 
            (this: &mut $type<$($gen)+>) -> (r: Option<$ity>)
            ensures
                ({
                    let (old_index, old_seq) = old(this)@;
                    match r {
                        None => {
                            &&& this@ == old(this)@
                            &&& old_index >= old_seq.len()
                        },
                        Some(k) => {
                            let (new_index, new_seq) = this@;
                            &&& 0 <= old_index < old_seq.len()
                            &&& new_seq == old_seq
                            &&& new_index == old_index + 1
                            &&& k == old_seq[old_index]
                        },
                    }
                }),
        ;
        }
    };
}

/// Use for Verge-defined wrapped types.
macro_rules! impl_iterator_verge {
    // no requires clause
    (
        $type:path [$($gen:tt)+] where Item = $ity:ty
        [ $method:ident via $implfn:path ] ($($arg:ident : $aty:ty),+) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator_verge!(
            @impl $type [$($gen)+] where Item = $ity
            [ $method via $implfn ] ($($arg : $aty),+) () -> |$seq| $($exp)+
        );
    };

    // with requires clause
    (
        $type:path [$($gen:tt)+] where Item = $ity:ty
        [ $method:ident via $implfn:path ] ($($arg:ident : $aty:ty),+) requires($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator_verge!(
            @impl $type [$($gen)+] where Item = $ity
            [ $method via $implfn ] ($($arg : $aty),+) (requires $($requires)*) -> |$seq| $($exp)+
        );
    };

    // internal implementation
    (
        @impl $type:path [$($gen:tt)+] where Item = $ity:ty
        [ $method:ident via $implfn:path ] ($($arg:ident : $aty:ty),+) ($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        verus! {
        impl<$($gen)+> IteratorView for $type<$($gen)+> {
            type Item = $ity;

            uninterp spec fn view(&self) -> (int, Seq<Self::Item>);
        }
        #[verifier::external_body]
        pub fn $method<$($gen)+>($($arg: $aty),+) -> (ret: $type<$($gen)+>) 
            $($requires)*
            ensures
                ({
                    let (index, $seq) = ret@;
                    &&& index == 0
                    &&& $($exp)+
                }),
            no_unwind
        {
            $type($implfn($($arg),+))
        } 
        impl<$($gen)+> core::iter::Iterator for $type<$($gen)+> {
            type Item = $ity;
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
                self.0.next()
            }
        }
            
        }
    };
}

pub(crate) use impl_iterator_default;
pub(crate) use impl_iterator_verge;

} // verus!