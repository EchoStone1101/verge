//! Specifications and lemmas for `Iterator` types.
//!
//! ## Specification Methodology
//! This module includes a template specification for various implementations 
//! of the `Iterator` trait, built upon `vstd`'s `IteratorSpec` encoding. 
//! In time, these specifications should be upstreamed by `vstd` itself.
//! However, as it is, Rust's orphan rules forbid implementing `IteratorSpec` 
//! on the actual types. Thus, wrapper types are introduced, and the 
//! constructor methods for the iterators are added by extension traits 
//! with a uniform naming convention:
//! - `str::char_indices() -> CharIndices` into `str::char_indices_iter() -> VergeCharIndices`;
//! - `path::iter() -> path::Iter` into `path::iterate() -> path::VergeIter`;
//! This workaround does not affect downstream crates. Users of Verge should
//! simply make use of the `IteratorSpec` trait.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::std_specs::iter::*;
pub use paste::paste;

verus! {

/// This trait is used for specifying `(DoubleEnded)Iterator` types by adding the index and 
/// the full sequence as `spec` functions.
/// It is only meant to be for Verge's internal use on the wrapper types.
pub trait VergeIteratorSpec {
    type Item;

    spec fn seq(&self) -> Seq<Self::Item>;
    spec fn idx(&self) -> int;
    spec fn ridx(&self) -> int;
}

//~doc-macro
macro_rules! impl_iterator {
    // Step 1 - optional requires clause
    (
        $(#[$attr:meta])*
        $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty
        [ $($constructor:tt)+ ] ($($params:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator!(
            @step1 $(#[$attr])* $type [$($gen)*] as $vtype [$($retgen)*] :: Item = $ity
            [ $($constructor)+ ] ($($params)*) () -> |$seq| $($exp)+
        );
    };
    (
        $(#[$attr:meta])*
        $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty
        [ $($constructor:tt)+ ] ($($params:tt)*) requires($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator!(
            @step1 $(#[$attr])* $type [$($gen)*] as $vtype [$($retgen)*] :: Item = $ity
            [ $($constructor)+ ] ($($params)*) (requires $($requires)*) -> |$seq| $($exp)+
        );
    };

    // Step 2 - function or trait method for constructor
    (
        @step1 $(#[$attr:meta])* $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty
        [ $method:ident via $implfn:ident $($where:tt)* ] ($($arg:ident: $aty:ty),*) ($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator!(
            @step2 $(#[$attr])* $type as $vtype [$($gen)*] :: Item = $ity
            [ verus!{ 
            #[verifier::external_body]
            pub fn $method<$($gen)*>($($arg: $aty),*) -> (iter: $vtype<$($retgen)*>) 
                $($where)*
                $($requires)*
                ensures
                    ({
                        let $seq = iter.seq();
                        &&& iter.idx() == 0
                        &&& iter.ridx() == $seq.len()
                        &&& $($exp)+
                    }),
                no_unwind
            { $vtype($implfn($($arg),*)) }
            } ] $($where)*
        );
    };
    (
        @step1 $(#[$attr:meta])* $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty
        [ [$hty:path as $($hbound:tt)+] :: $method:ident via $implfn:ident $($where:tt)* ] 
        (&$self:ident, $($arg:ident: $aty:ty),*) ($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator!(
            @step2 $(#[$attr])* $type as $vtype [$($gen)*] :: Item = $ity
            [ paste!{verus!{
            pub trait [<$vtype Fn>]: $($hbound)+ {
                fn $method<$($gen)*>(&$self, $($arg: $aty),*) -> (iter: $vtype<$($retgen)*>)
                    $($where)*
                    $($requires)*
                    ensures
                        ({
                            let $seq = iter.seq();
                            &&& iter.idx() == 0
                            &&& iter.ridx() == $seq.len()
                            &&& $($exp)+
                        }),
                    no_unwind;
            }
            impl [<$vtype Fn>] for $hty {
                #[verifier::external_body]
                fn $method<$($gen)*>(&$self, $($arg: $aty),*) -> (iter: $vtype<$($retgen)*>) 
                    $($where)*
                { $vtype($hty::$implfn(&$self, $($arg),*)) }
            }
            }} ] $($where)*
        );
    };

    // internal implementation
    (
        @step2 $(#[$attr:meta])* $type:path as $vtype:path [$($gen:tt)*] :: Item = $ity:ty 
        [ $($constructor:tt)+ ] $($where:tt)*
    ) => {
        paste!{ verus!{ 
        // Define the wrapper type
        #[verifier::external]
        pub struct $vtype<$($gen)*>($type<$($gen)*>) 
            $($where)*;
        #[verifier::external_body]
        #[verifier::external_type_specification]
        $(#[$attr])*
        pub struct [<Ex $vtype>]<$($gen)*>($vtype<$($gen)*>)
            $($where)*; 
        // Specify the wrapper type 
        impl<$($gen)*> VergeIteratorSpec for $vtype<$($gen)*> 
            $($where)*
        {
            type Item = $ity;
            uninterp spec fn seq(&self) -> Seq<Self::Item>;
            uninterp spec fn idx(&self) -> int;
            uninterp spec fn ridx(&self) -> int;
        }
        // Prepare the wrapper type as an `Iterator`
        impl<$($gen)*> IteratorSpecImpl for $vtype<$($gen)*> 
            $($where)*
        {
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
                if 0 <= self.idx() + i < self.ridx() { Some(self.seq()[self.idx() + i]) } else { None }
            }
        }
        }}
        // Define the constructor method 
        $($constructor)+
    };
}

//~doc-macro
macro_rules! impl_double_ended_iterator {
    (
        $type:path as $vtype:path [$($gen:tt)*] :: Item = $ity:ty
    ) => {
        verus! {
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

pub(crate) use impl_iterator;
pub(crate) use impl_double_ended_iterator;

} // verus!