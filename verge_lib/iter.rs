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

#[verifier::external]
pub(crate) trait IteratorImpl: Iterator {
    fn next_impl(&mut self) -> Option<<Self as Iterator>::Item>;
}

#[verifier::external]
pub(crate) trait DoubleEndedIteratorImpl: DoubleEndedIterator {
    fn next_back_impl(&mut self) -> Option<<Self as Iterator>::Item>;
}

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
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        [ $($constructor:tt)+ ] $(#[$custom:meta])? ($($params:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator!(
            @step1 $(#[$attr])* 
            [ $type [$($gen)*] as $vtype [$($retgen)*] :: Item = $ity $(where $($where)*)? ]
            [ $($constructor)+ ] $(#[$custom])? ($($params)*) () -> |$seq| $($exp)+
        );
    };
    (
        $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        [ $($constructor:tt)+ ] $(#[$custom:meta])? ($($params:tt)*) requires($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator!(
            @step1 $(#[$attr])* 
            [ $type [$($gen)*] as $vtype [$($retgen)*] :: Item = $ity $(where $($where)*)? ]
            [ $($constructor)+ ] $(#[$custom])? ($($params)*) (requires $($requires)*) -> |$seq| $($exp)+
        );
    };

    // Step 2 - function or trait method for constructor
    (
        @step1 $(#[$attr:meta])* 
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        [ $method:ident via $implfn:ident $(where $($wherecon:tt)*)? ] $(#[$custom:meta])?
        ($($arg:ident: $aty:ty),*) ($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator!(
            $(#[$custom])? @step2 $(#[$attr])* 
            [ $type as $vtype [$($gen)*] :: Item = $ity $(where $($where)*)? ]
            [ verus!{ 
            #[verifier::external_body]
            pub fn $method<$($gen)*>($($arg: $aty),*) -> (iter: $vtype<$($retgen)*>) 
            where
                $($($where)*)?
                $($($wherecon)*)?
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
            } ] 
        );
    };
    (
        @step1 $(#[$attr:meta])* 
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        [ [$hty:path as $($hbound:tt)+] :: $method:ident via $implfn:ident $(where $($wherecon:tt)*)? ] $(#[$custom:meta])?
        (&$self:ident, $($arg:ident: $aty:ty),*) ($($requires:tt)*) -> |$seq:ident| $($exp:tt)+
    ) => {
        impl_iterator!(
            $(#[$custom])? @step2 $(#[$attr])* 
            [ $type as $vtype [$($gen)*] :: Item = $ity $(where $($where)*)? ]
            [ paste!{verus!{
            pub trait [<$vtype Fn>]: $($hbound)+ {
                fn $method<$($gen)*>(&$self, $($arg: $aty),*) -> (iter: $vtype<$($retgen)*>)
                where
                    $($($where)*)?
                    $($($wherecon)*)?
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
                where
                    $($($where)*)?
                    $($($wherecon)*)?
                { $vtype($hty::$implfn(&$self, $($arg),*)) }
            }
            }} ]
        );
    };

    // internal implementation
    (
        $(#[$custom:meta])? @step2 $(#[$attr:meta])* 
        [ $type:path as $vtype:path [$($gen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        [ $($constructor:tt)+ ] 
    ) => {
        paste!{ verus!{ 
        // Define the wrapper type
        #[verifier::external]
        pub struct $vtype<$($gen)*>($type<$($gen)*>) 
            $(where $($where)*)?;
        #[verifier::external_body]
        #[verifier::external_type_specification]
        $(#[$attr])*
        pub struct [<Ex $vtype>]<$($gen)*>($vtype<$($gen)*>)
            $(where $($where)*)?;
        // Specify the wrapper type 
        impl<$($gen)*> VergeIteratorSpec for $vtype<$($gen)*> 
        where
            $($($where)*)?
        {
            type Item = $ity;
            uninterp spec fn seq(&self) -> Seq<Self::Item>;
            uninterp spec fn idx(&self) -> int;
            uninterp spec fn ridx(&self) -> int;
        }
        // Implement the wrapper type as an `Iterator`
        impl<$($gen)*> IteratorSpecImpl for $vtype<$($gen)*> 
        where
            $($($where)*)?
        {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool 
                { true }
            open spec fn will_return_none(&self) -> bool 
                { true }
            open spec fn remaining(&self) -> Seq<$ity> 
                { self.seq().subrange(self.idx(), self.ridx()) }
            open spec fn decrease(&self) -> Option<nat> 
                { Some((self.ridx() - self.idx()) as nat) }
            open spec fn initial_value_relation(&self, init: &Self) -> bool {
                &&& init.seq() == self.seq()
                &&& init.idx() == self.idx()
                &&& init.ridx() == self.ridx()
            }
            open spec fn peek(&self, i: int) -> Option<$ity> {
                if 0 <= self.idx() + i < self.ridx() { Some(self.seq()[self.idx() + i]) } else { None }
            }
        }
        _impl_iterator_next!($(#[$custom])? $vtype [$($gen)*] $($($where)*)?); 
        }}
        // Define the constructor method 
        $($constructor)+
    };
}

macro_rules! _impl_iterator_next {
    // custom impl
    (#[custom_next] $($rest:tt)*) => {};
    // specialized impl
    // XXX: the whole point of this case is a workaround of Verus's Trait Conflict Checker, 
    // which doesn't handle certain trait bounds.
    (#[specialized_next($($wherenext:tt)*)] $vtype:path [$($gen:tt)*] $($where:tt)*) => {
        verus! {
            #[verifier::external]
            impl<$($gen)*> IteratorImpl for $vtype<$($gen)*> 
            where $($where)*
            {
                default fn next_impl(&mut self) -> Option<<Self as Iterator>::Item> 
                    { unimplemented!()  }
            }
            #[verifier::external]
            impl<$($gen)*> IteratorImpl for $vtype<$($gen)*> 
            where 
                $($where)*
                $($wherenext)*
            {
                fn next_impl(&mut self) -> Option<<Self as Iterator>::Item> 
                    { self.0.next() }
            }
            impl<$($gen)*> core::iter::Iterator for $vtype<$($gen)*> 
            where $($where)*
            {
                type Item = <Self as VergeIteratorSpec>::Item;
                #[verifier::external_body]
                fn next(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
                    { IteratorImpl::next_impl(self) }
            }
        }
    };
    // default impl
    ($vtype:path [$($gen:tt)*] $($where:tt)*) => {
        verus! {
            impl<$($gen)*> core::iter::Iterator for $vtype<$($gen)*> 
            where $($where)*
            {
                type Item = <Self as VergeIteratorSpec>::Item;
                #[verifier::external_body]
                fn next(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
                    { self.0.next() }
            }
        }
    };
}

//~doc-macro
macro_rules! impl_double_ended_iterator {
    (
        $(#[$custom:meta])?
        $type:path as $vtype:path [$($gen:tt)*] :: Item = $ity:ty
        $(where $($where:tt)+)? 
    ) => {
        verus! {
        impl<$($gen)*> DoubleEndedIteratorSpecImpl for $vtype<$($gen)*> 
            $(where $($where)+)? 
        {
            open spec fn peek_back(&self, index: int) -> Option<$ity> {
                if self.idx() <= self.ridx() - index - 1 < self.seq().len() {
                    Some(self.seq()[self.ridx() - index - 1])
                } else {
                    None
                }
            }
        }
        _impl_double_ended_iterator_next_back!(
            $(#[$custom])? $vtype [$($gen)*] $(where $($where)+)?
        );
        }
    };
}

macro_rules! _impl_double_ended_iterator_next_back {
    // custom impl
    (#[custom_next] $($rest:tt)*) => {};
    // specialized impl
    (#[specialized_next($($wherenext:tt)*)] $vtype:path [$($gen:tt)*] $(where $($where:tt)+)?) => {
        verus! {
            #[verifier::external]
            impl<$($gen)*> DoubleEndedIteratorImpl for $vtype<$($gen)*> 
            where $($($where)+)? 
            {
                default fn next_back_impl(&mut self) -> Option<<Self as Iterator>::Item> 
                    { unimplemented!()  }
            }
            #[verifier::external]
            impl<$($gen)*> DoubleEndedIteratorImpl for $vtype<$($gen)*> 
            where 
                $($($where)+)? 
                $($wherenext)*
            {
                fn next_back_impl(&mut self) -> Option<<Self as Iterator>::Item> 
                    { self.0.next_back() }
            }
            impl<$($gen)*> core::iter::DoubleEndedIterator for $vtype<$($gen)*> 
            where $($($where)+)? 
            {
                #[verifier::external_body]
                fn next_back(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
                    { DoubleEndedIteratorImpl::next_back_impl(self) }
            }
        }
    };
    // default impl
    ($vtype:path [$($gen:tt)*] $(where $($where:tt)+)?) => {
        verus! {
            impl<$($gen)*> core::iter::DoubleEndedIterator for $vtype<$($gen)*> 
                $(where $($where)+)? 
            {
                #[verifier::external_body]
                fn next_back(&mut self) -> (ret: Option<<Self as VergeIteratorSpec>::Item>) 
                    { self.0.next_back() }
            }
        }
    };
}

pub(crate) use impl_iterator;
pub(crate) use impl_double_ended_iterator;
pub(crate) use _impl_iterator_next;
pub(crate) use _impl_double_ended_iterator_next_back;

} // verus!