//! Specifications and lemmas for `Iterator` types.
//!
//! ## Specification Methodology
//! This module includes a template specification for implementations of the
//! `Iterator` trait that are not yet covered by `vstd`'s `IteratorSpec`
//! encoding. Rust's orphan rules forbid implementing `IteratorSpec` on the
//! actual types, so wrapper types are introduced and constructor methods are
//! added by extension traits with a uniform naming convention:
//! - `str::char_indices() -> CharIndices` into `str::char_indices_iter() -> VergeCharIndices`;
//! - `path::iter() -> path::Iter` into `path::iterate() -> path::VergeIter`;
//! This workaround does not affect downstream crates. Users of Verge should
//! simply make use of the `IteratorSpec` trait.

#[allow(unused_imports)]
use crate::cmp::*;
use crate::clone::*;
use crate::seq::*;
use crate::{is_deterministic, is_total};
use vstd::prelude::*;
use vstd::pervasive::cloned;
use vstd::std_specs::iter::*;
use vstd::relations::sorted_by;
pub use paste::paste;

use std::cmp::Ordering;

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
pub trait VergeIteratorSpec: Sized + crate::Sealed {
    type Item;

    spec fn seq(&self) -> Seq<Self::Item>;
    spec fn idx(&self) -> int;
    spec fn ridx(&self) -> int;

    /// Creates a fresh iterator-typed value with the given `seq` view.
    ///
    /// This function enables the creation of iterators (which are typically meant for `exec`-mode usage)
    /// in `proof`-mode. It is sound because `VergeIteratorSpec` is a sealed trait and is
    /// only implemented on iterator types with no inherent type invariants, nor additional proof properties.
    /// The sole point of this function is to allow for reasoning about Verge iterators in proofs.
    proof fn new_dummy(seq: Seq<Self::Item>) -> (ret: Self)
        ensures
            ret.idx() == 0,
            ret.ridx() == seq.len(),
            ret.seq() == seq,
    {
        let dummy_iter = choose |dummy_iter: Self| #[trigger] dummy_iter.seq() == seq;
        admit();
        dummy_iter
    }
}

// TODO: does the `by_ref` pattern work?

/// Enables `Iterator::count`, which consumes the iterator.
#[verifier::external_body]
pub fn iter_count<I: Iterator>(iter: I) -> (ret: usize)
    requires
        iter.obeys_prophetic_iter_laws() && iter.will_return_none(),
    ensures
        ret == iter.remaining().len(),
    { iter.count() }

/// Enables `Iterator::last`, which consumes the iterator.
#[verifier::external_body]
pub fn iter_last<I: Iterator>(iter: I) -> (ret: Option<I::Item>)
    requires
        iter.obeys_prophetic_iter_laws() && iter.will_return_none(),
    ensures
        ret is Some ==> (iter.remaining().len() > 0 && ret->0 == iter.remaining().last()),
        ret is None ==> iter.remaining().len() == 0,
    { iter.last() }

/// Enables `Iterator::max`, which consumes the iterator.
#[verifier::external_body]
pub fn iter_max<I: Iterator>(iter: I) -> (ret: Option<I::Item>)
    where
        I::Item: OrdVerified,
    requires
        iter.obeys_prophetic_iter_laws() && iter.will_return_none(),
    ensures
        ret is None ==> iter.remaining().len() == 0,
        ret is Some ==> {
            &&& iter.remaining().len() > 0
            &&& ret->0 == iter.remaining()
                .max_via(|x: I::Item, y: I::Item| call_ensures(I::Item::le, (&x, &y), true))
        }
    { iter.max() }

/// Enables `Iterator::min`, which consumes the iterator.
#[verifier::external_body]
pub fn iter_min<I: Iterator>(iter: I) -> (ret: Option<I::Item>)
    where
        I::Item: OrdVerified,
    requires
        iter.obeys_prophetic_iter_laws() && iter.will_return_none(),
    ensures
        ret is None ==> iter.remaining().len() == 0,
        ret is Some ==> {
            &&& iter.remaining().len() > 0
            &&& ret->0 == iter.remaining()
                .min_via(|x: I::Item, y: I::Item| call_ensures(I::Item::le, (&x, &y), true))
        }
    { iter.min() }

/// Enables `Iterator::max_by`, which consumes the iterator.
#[verifier::external_body]
pub fn iter_max_by<I: Iterator, F>(iter: I, compare: F) -> (ret: Option<I::Item>)
    where
        F: FnMut(&I::Item, &I::Item) -> Ordering,
    requires
        iter.obeys_prophetic_iter_laws() && iter.will_return_none(),
        is_deterministic(compare) && is_total(compare),
    ensures
        ret is None ==> iter.remaining().len() == 0,
        ret is Some ==> {
            &&& iter.remaining().len() > 0
            &&& ret->0 == iter.remaining()
                .max_via(|x: I::Item, y: I::Item|
                    call_ensures(compare, (&x, &y), Ordering::Less)
                    || call_ensures(compare, (&x, &y), Ordering::Equal)
                )
        }
    { iter.max_by(compare) }

/// Enables `Iterator::min_by`, which consumes the iterator.
#[verifier::external_body]
pub fn iter_min_by<I: Iterator, F>(iter: I, compare: F) -> (ret: Option<I::Item>)
    where
        F: FnMut(&I::Item, &I::Item) -> Ordering,
    requires
        iter.obeys_prophetic_iter_laws() && iter.will_return_none(),
        is_deterministic(compare) && is_total(compare),
    ensures
        ret is None ==> iter.remaining().len() == 0,
        ret is Some ==> {
            &&& iter.remaining().len() > 0
            &&& ret->0 == iter.remaining()
                .min_via(|x: I::Item, y: I::Item|
                    call_ensures(compare, (&x, &y), Ordering::Less)
                    || call_ensures(compare, (&x, &y), Ordering::Equal)
                )
        }
    { iter.min_by(compare) }

/// Enables `Iterator::cmp`.
#[verifier::external_body]
pub fn iter_cmp<I: Iterator>(this: I, other: I) -> (ret: Ordering)
    where
        I::Item: OrdVerified,
    requires
        this.obeys_prophetic_iter_laws() && this.will_return_none(),
        other.obeys_prophetic_iter_laws() && other.will_return_none(),
    ensures
        Some(ret) == lexico_cmp(this.remaining(), other.remaining()),
    { this.cmp(other) }

/// Enables `Iterator::partial_cmp`.
#[verifier::external_body]
pub fn iter_partial_cmp<I: Iterator>(this: I, other: I) -> (ret: Option<Ordering>)
    where
        I::Item: PartialOrdVerified,
    requires
        this.obeys_prophetic_iter_laws() && this.will_return_none(),
        other.obeys_prophetic_iter_laws() && other.will_return_none(),
    ensures
        ret == lexico_cmp(this.remaining(), other.remaining()),
    { this.partial_cmp(other) }

/// Enables `Iterator::eq`.
#[verifier::external_body]
pub fn iter_eq<I: Iterator>(this: I, other: I) -> (ret: bool)
    where
        I::Item: PartialEqVerified,
    requires
        this.obeys_prophetic_iter_laws() && this.will_return_none(),
        other.obeys_prophetic_iter_laws() && other.will_return_none(),
    ensures
        ret == lexico_eq(this.remaining(), other.remaining()),
    { this.eq(other) }

/// Enables `Iterator::ne`.
#[verifier::external_body]
pub fn iter_ne<I: Iterator>(this: I, other: I) -> (ret: bool)
    where
        I::Item: PartialEqVerified,
    requires
        this.obeys_prophetic_iter_laws() && this.will_return_none(),
        other.obeys_prophetic_iter_laws() && other.will_return_none(),
    ensures
        ret == !lexico_eq(this.remaining(), other.remaining()),
    { this.ne(other) }

/// Enables `Iterator::lt`.
#[verifier::external_body]
pub fn iter_lt<I: Iterator>(this: I, other: I) -> (ret: bool)
    where
        I::Item: PartialOrdVerified,
    requires
        this.obeys_prophetic_iter_laws() && this.will_return_none(),
        other.obeys_prophetic_iter_laws() && other.will_return_none(),
    ensures
        ret <==> (lexico_cmp(this.remaining(), other.remaining()) == Some(Ordering::Less)),
    { this.lt(other) }

/// Enables `Iterator::gt`.
#[verifier::external_body]
pub fn iter_gt<I: Iterator>(this: I, other: I) -> (ret: bool)
    where
        I::Item: PartialOrdVerified,
    requires
        this.obeys_prophetic_iter_laws() && this.will_return_none(),
        other.obeys_prophetic_iter_laws() && other.will_return_none(),
    ensures
        ret <==> (lexico_cmp(this.remaining(), other.remaining()) == Some(Ordering::Greater)),
    { this.gt(other) }

/// Enables `Iterator::le`.
#[verifier::external_body]
pub fn iter_le<I: Iterator>(this: I, other: I) -> (ret: bool)
    where
        I::Item: PartialOrdVerified,
    requires
        this.obeys_prophetic_iter_laws() && this.will_return_none(),
        other.obeys_prophetic_iter_laws() && other.will_return_none(),
    ensures
        ret <==> (
            lexico_cmp(this.remaining(), other.remaining()) == Some(Ordering::Less)
            || lexico_cmp(this.remaining(), other.remaining()) == Some(Ordering::Equal)
        ),
    { this.le(other) }

/// Enables `Iterator::ge`.
#[verifier::external_body]
pub fn iter_ge<I: Iterator>(this: I, other: I) -> (ret: bool)
    where
        I::Item: PartialOrdVerified,
    requires
        this.obeys_prophetic_iter_laws() && this.will_return_none(),
        other.obeys_prophetic_iter_laws() && other.will_return_none(),
    ensures
        ret <==> (
            lexico_cmp(this.remaining(), other.remaining()) == Some(Ordering::Greater)
            || lexico_cmp(this.remaining(), other.remaining()) == Some(Ordering::Equal)
        ),
    { this.ge(other) }

/// Enables `Iterator::is_sorted`, which consumes the iterator.
#[verifier::external_body]
pub fn iter_is_sorted<I: Iterator>(iter: I) -> (ret: bool)
    where
        I::Item: PartialOrdVerified,
    requires
        iter.obeys_prophetic_iter_laws() && iter.will_return_none(),
    ensures
        ret == sorted_by(iter.remaining(), |x: I::Item, y: I::Item| call_ensures(I::Item::le, (&x, &y), true)),
    { iter.is_sorted() }

/// Enables `Iterator::is_sorted_by`, which consumes the iterator.
#[verifier::external_body]
pub fn iter_is_sorted_by<I: Iterator, F>(iter: I, compare: F) -> (ret: bool)
    where
        F: FnMut(&I::Item, &I::Item) -> bool,
    requires
        iter.obeys_prophetic_iter_laws() && iter.will_return_none(),
        is_deterministic(compare) && is_total(compare),
    ensures
        ret == sorted_by(iter.remaining(), |x: I::Item, y: I::Item| call_ensures(compare, (&x, &y), true)),
    { iter.is_sorted_by(compare) }

/// Enables `Iterator::fold`, which consumes the iterator.
///
/// This function requires an explicit `f_spec` argument that specifies
/// the `spec`-mode equivalent of `f`, for the sake of more straightforward specs.
#[verifier::external_body]
pub fn iter_fold<I: Iterator, B, F>(
    iter: I,
    init: B,
    f: F,
    f_spec: Ghost<spec_fn(B, I::Item) -> B>,
) -> (ret: B)
    where
        F: FnMut(B, I::Item) -> B,
    requires
        iter.obeys_prophetic_iter_laws() && iter.will_return_none(),
        is_total(f),
        forall |acc: B, x: I::Item| #[trigger] call_ensures(f, (acc, x), f_spec(acc, x)),
    ensures
        ret == iter.remaining().fold_left(init, f_spec@),
    { iter.fold(init, f) }

/// Enables `Iterator::reduce`, which consumes the iterator.
///
/// This function requires an explicit `f_spec` argument that specifies
/// the `spec`-mode equivalent of `f`, for the sake of more straightforward specs.
#[verifier::external_body]
pub fn iter_reduce<I: Iterator, F>(
    iter: I,
    f: F,
    f_spec: Ghost<spec_fn(I::Item, I::Item) -> I::Item>,
) -> (ret: Option<I::Item>)
    where
        F: FnMut(I::Item, I::Item) -> I::Item,
    requires
        iter.obeys_prophetic_iter_laws() && iter.will_return_none(),
        is_total(f),
        forall |acc: I::Item, x: I::Item| #[trigger] call_ensures(f, (acc, x), f_spec(acc, x)),
    ensures
        ret is None ==> iter.remaining().len() == 0,
        ret is Some ==> {
            &&& iter.remaining().len() > 0
            &&& ret->0 == iter.remaining().drop_first()
                .fold_left(iter.remaining().first(), f_spec@)
        }
    { iter.reduce(f) }

/// Enables `Iterator::nth`.
#[verifier::external_body]
pub fn iter_nth<I: Iterator>(iter: &mut I, n: usize) -> (ret: Option<I::Item>)
    requires
        <I as IteratorSpec>::obeys_prophetic_iter_laws(iter),
    ensures
        // The iterator consistently obeys, completes, and decreases throughout its lifetime
        (*final(iter)).obeys_prophetic_iter_laws(),
        (*final(iter)).will_return_none() == (*old(iter)).will_return_none(),
        ((*old(iter)).decrease() is Some <==> (*final(iter)).decrease() is Some),
        // `nth` pops the head section of the prophesized remaining(), or returns None
        ({
            if (*old(iter)).remaining().len() > n {
                &&& (*final(iter)).remaining() == (*old(iter)).remaining().skip(n + 1)
                &&& ret == Some((*old(iter)).remaining()[n as int])
            } else {
                &&& (*final(iter)).remaining().len() == 0
                && ret == None && (*final(iter)).will_return_none()
            }
        }),
        // If the iterator isn't done yet, then it successfully decreases its metric (if any)
        (*old(iter)).remaining().len() > 0 && (*final(iter)).decrease() is Some ==>
            decreases_to!((*old(iter)).decrease()->0 => (*final(iter)).decrease()->0),
    { iter.nth(n) }

/// Specifies the iterator `VergeStepBy` which wraps `StepBy`,
/// contructed via `Iterator::step_by()`.
impl_iterator_method!(
    #[verifier::accept_recursive_types(I)]
    [ std::iter::StepBy[I] as VergeStepBy[Self] where I: Iterator + Sized ]
    [ step_by_iter via step_by ]
    (self, step: usize) requires(step > 0,) -> |iter| {
        iter.seq() == Seq::<Self::Item>::new(
            ((self.remaining().len() + step - 1) as int / (step as int)) as nat,
            |i: int| self.remaining()[i * step]
        )
    }
);

/// Specifies the iterator `VergeChain` which wraps `Chain`,
/// contructed via `Iterator::chain_iter()`.
impl_iterator_method!(
    #[verifier::accept_recursive_types(I)]
    #[verifier::accept_recursive_types(U)]
    [ std::iter::Chain[I, U] as VergeChain[Self, U]
        where
            I: Iterator + Sized,
            U: Iterator<Item = I::Item> + Sized,
    ] [ chain_iter[U] via chain
        where
            U: Iterator<Item = Self::Item> + Sized,
    ] (self, other: U) requires(
        other.obeys_prophetic_iter_laws(),
        other.will_return_none(),
    ) -> |iter| {
        iter.seq() == self.remaining() + other.remaining()
    }
);

/// Specifies the iterator `VergeEnumerate` which wraps `Enumerate`,
/// constructed via `Iterator::enumerate_iter()`.
impl_iterator_method!(
    #[verifier::accept_recursive_types(I)]
    [ std::iter::Enumerate[I] as VergeEnumerate[Self] where I: Iterator + Sized ]
    [ enumerate_iter via enumerate ]
    (self) -> |iter| {
        iter.seq() == self.remaining().map(|i: int, item: Self::Item| (i as usize, item))
    }
);

/// Specifies the iterator `VergeSkipWhile` which wraps `SkipWhile`,
/// constructed via `Iterator::skip_while_iter()`.
impl_iterator_method!(
    #[verifier::accept_recursive_types(I)]
    #[verifier::accept_recursive_types(P)]
    [ std::iter::SkipWhile[I, P] as VergeSkipWhile[Self, P]
        where
            I: Iterator + Sized,
            P: FnMut(&I::Item) -> bool,
    ] [ skip_while_iter[P] via skip_while
        where
            P: FnMut(&Self::Item) -> bool,
    ] (self, predicate: P) requires(
        is_deterministic(predicate),
        is_total(predicate),
    ) -> |iter| {
        iter.seq() == self.remaining()
            .skip_while(|item: Self::Item| call_ensures(predicate, (&item,), true))
    }
);

/// Specifies the iterator `VergeTakeWhile` which wraps `TakeWhile`,
/// constructed via `Iterator::take_while_iter()`.
impl_iterator_method!(
    #[verifier::accept_recursive_types(I)]
    #[verifier::accept_recursive_types(P)]
    [ std::iter::TakeWhile[I, P] as VergeTakeWhile[Self, P]
        where
            I: Iterator + Sized,
            P: FnMut(&I::Item) -> bool,
    ] [ take_while_iter[P] via take_while
        where
            P: FnMut(&Self::Item) -> bool,
    ] (self, predicate: P) requires(
        is_deterministic(predicate),
        is_total(predicate),
    ) -> |iter| {
        iter.seq() == self.remaining()
            .take_while(|item: Self::Item| call_ensures(predicate, (&item,), true))
    }
);

/// Specifies the iterator `VergeCopied` which wraps `Copied`,
/// constructed via `Iterator::copied_iter()`.
impl_iterator_method!(
    #[verifier::accept_recursive_types(I)]
    #[verifier::accept_recursive_types(T)]
    [ std::iter::Copied[I] as VergeCopied[Self, T] :: Item ['a; T] = T
        where
            I: Iterator<Item = &'a T> + Sized,
            T: CopyVerified + 'a,
    ] [ copied_iter['a, T] via copied
        where
            Self: Iterator<Item = &'a T>,
            T: CopyVerified + 'a,
    ] (self) -> |iter| {
        iter.seq() == self.remaining().map(|i: int, item: &'a T| *item)
    }
);

/// Specifies the iterator `VergeCloned` which wraps `Cloned`,
/// constructed via `Iterator::cloned_iter()`.
impl_iterator_method!(
    #[verifier::accept_recursive_types(I)]
    #[verifier::accept_recursive_types(T)]
    [ std::iter::Cloned[I] as VergeCloned[Self, T] :: Item ['a; T] = T
        where
            I: Iterator<Item = &'a T> + Sized,
            T: Clone + 'a,
    ] [ cloned_iter['a, T] via cloned
        where
            Self: Iterator<Item = &'a T>,
            T: Clone + 'a,
    ] (self) -> |iter| {
        &&& iter.seq().len() == self.remaining().len()
        &&& forall|i: int| #![trigger iter.seq()[i]]
            0 <= i < iter.seq().len() ==> cloned::<T>(*self.remaining()[i], iter.seq()[i])
    }
);

//~doc-macro
macro_rules! impl_iterator_method {
    // Explicit item type with extra impl-only lifetimes and generics for the wrapper impls.
    (
        $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item [$($ilt:lifetime),*; $($igen:tt)*] = $ity:ty $(where $($where:tt)*)? ]
        [ $method:ident [$($mgen:tt)*] via $std_method:ident $(where $($wherecon:tt)*)? ]
        ($self_:ident $(, $arg:ident: $aty:ty)*) $(requires($($requires:tt)*))? -> |$ret:ident| $($ensures:tt)+
    ) => {
        paste!{ verus!{
        #[verifier::external]
        pub struct $vtype<$($gen)*, $($igen)*>($type<$($gen)*>, core::marker::PhantomData<($($igen,)*)>)
            ;

        #[verifier::external_body]
        #[verifier::external_type_specification]
        $(#[$attr])*
        pub struct [<Ex $vtype>]<$($gen)*, $($igen)*>($vtype<$($gen)*, $($igen)*>)
            ;

        impl<$($ilt,)* $($gen)*, $($igen)*> core::iter::Iterator for $vtype<$($gen)*, $($igen)*>
        where
            $($($where)*)?
        {
            type Item = $ity;

            #[verifier::external_body]
            fn next(&mut self) -> (ret: Option<$ity>)
                { self.0.next() }
        }

        impl<$($ilt,)* $($gen)*, $($igen)*> VergeIteratorSpec for $vtype<$($gen)*, $($igen)*>
        where
            $($($where)*)?
        {
            type Item = $ity;

            uninterp spec fn seq(&self) -> Seq<Self::Item>;
            uninterp spec fn idx(&self) -> int;
            uninterp spec fn ridx(&self) -> int;

            proof fn new_dummy(seq: Seq<Self::Item>) -> (ret: Self)
                ensures
                    ret.idx() == 0,
                    ret.ridx() == seq.len(),
                    ret.seq() == seq,
            {
                let dummy_iter = choose |dummy_iter: Self| #[trigger] dummy_iter.seq() == seq;
                admit();
                dummy_iter
            }
        }

        impl<$($ilt,)* $($gen)*, $($igen)*> crate::Sealed for $vtype<$($gen)*, $($igen)*>
        where
            $($($where)*)?
        {}

        impl<$($ilt,)* $($gen)*, $($igen)*> IteratorSpecImpl for $vtype<$($gen)*, $($igen)*>
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
            open spec fn peek(&self, i: int) -> Option<$ity> {
                if 0 <= self.idx() + i < self.ridx() { Some(self.seq()[self.idx() + i]) } else { None }
            }
        }

        pub trait [<Iterator $vtype Fn>]: Iterator + IteratorSpec + Sized {
            fn $method<$($mgen)*>($self_, $($arg: $aty),*) -> ($ret: $vtype<$($retgen)*>)
                $(where $($wherecon)*)?
                requires
                    $self_.obeys_prophetic_iter_laws() && $self_.will_return_none(),
                    $($($requires)*)?
                ensures
                    $ret.idx() == 0,
                    $ret.ridx() == $ret.seq().len(),
                    ($($ensures)+),
            ;
        }

        impl<I: Iterator + IteratorSpec + Sized> [<Iterator $vtype Fn>] for I {
            #[verifier::external_body]
            fn $method<$($mgen)*>($self_, $($arg: $aty),*) -> ($ret: $vtype<$($retgen)*>)
                $(where $($wherecon)*)?
                { $vtype($self_.$std_method($($arg),*), core::marker::PhantomData::<($($igen,)*)>) }
        }
        }}
    };

    // Explicit item type with extra impl-only generics for the wrapper impls.
    (
        $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item [$($igen:tt)*] = $ity:ty $(where $($where:tt)*)? ]
        [ $method:ident [$($mgen:tt)*] via $std_method:ident $(where $($wherecon:tt)*)? ]
        ($self_:ident $(, $arg:ident: $aty:ty)*) $(requires($($requires:tt)*))? -> |$ret:ident| $($ensures:tt)+
    ) => {
        paste!{ verus!{
        #[verifier::external]
        pub struct $vtype<$($gen)*, $($igen)*>($type<$($gen)*>, core::marker::PhantomData<($($igen,)*)>)
            ;

        #[verifier::external_body]
        #[verifier::external_type_specification]
        $(#[$attr])*
        pub struct [<Ex $vtype>]<$($gen)*, $($igen)*>($vtype<$($gen)*, $($igen)*>)
            ;

        impl<$($gen)*, $($igen)*> core::iter::Iterator for $vtype<$($gen)*, $($igen)*>
        where
            $($($where)*)?
        {
            type Item = $ity;

            #[verifier::external_body]
            fn next(&mut self) -> (ret: Option<$ity>)
                { self.0.next() }
        }

        impl<$($gen)*, $($igen)*> VergeIteratorSpec for $vtype<$($gen)*, $($igen)*>
        where
            $($($where)*)?
        {
            type Item = $ity;

            uninterp spec fn seq(&self) -> Seq<Self::Item>;
            uninterp spec fn idx(&self) -> int;
            uninterp spec fn ridx(&self) -> int;

            proof fn new_dummy(seq: Seq<Self::Item>) -> (ret: Self)
                ensures
                    ret.idx() == 0,
                    ret.ridx() == seq.len(),
                    ret.seq() == seq,
            {
                let dummy_iter = choose |dummy_iter: Self| #[trigger] dummy_iter.seq() == seq;
                admit();
                dummy_iter
            }
        }

        impl<$($gen)*, $($igen)*> crate::Sealed for $vtype<$($gen)*, $($igen)*>
        where
            $($($where)*)?
        {}

        impl<$($gen)*, $($igen)*> IteratorSpecImpl for $vtype<$($gen)*, $($igen)*>
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
            open spec fn peek(&self, i: int) -> Option<$ity> {
                if 0 <= self.idx() + i < self.ridx() { Some(self.seq()[self.idx() + i]) } else { None }
            }
        }

        pub trait [<Iterator $vtype Fn>]: Iterator + IteratorSpec + Sized {
            fn $method<$($mgen)*>($self_, $($arg: $aty),*) -> ($ret: $vtype<$($retgen)*>)
                $(where $($wherecon)*)?
                requires
                    $self_.obeys_prophetic_iter_laws() && $self_.will_return_none(),
                    $($($requires)*)?
                ensures
                    $ret.idx() == 0,
                    $ret.ridx() == $ret.seq().len(),
                    ($($ensures)+),
            ;
        }

        impl<I: Iterator + IteratorSpec + Sized> [<Iterator $vtype Fn>] for I {
            #[verifier::external_body]
            fn $method<$($mgen)*>($self_, $($arg: $aty),*) -> ($ret: $vtype<$($retgen)*>)
                $(where $($wherecon)*)?
                { $vtype($self_.$std_method($($arg),*), core::marker::PhantomData::<($($igen,)*)>) }
        }
        }}
    };

    // Explicit item type without impl-only generics.
    (
        $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        [ $method:ident [$($mgen:tt)*] via $std_method:ident $(where $($wherecon:tt)*)? ]
        ($self_:ident $(, $arg:ident: $aty:ty)*) $(requires($($requires:tt)*))? -> |$ret:ident| $($ensures:tt)+
    ) => {
        impl_iterator_method!(
            $(#[$attr])*
            [ $type [$($gen)*] as $vtype [$($retgen)*] :: Item [] = $ity $(where $($where)*)? ]
            [ $method [$($mgen)*] via $std_method $(where $($wherecon)*)? ]
            ($self_ $(, $arg: $aty)*) $(requires($($requires)*))? -> |$ret| $($ensures)+
        );
    };
    (
        $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        [ $method:ident via $std_method:ident $(where $($wherecon:tt)*)? ]
        ($self_:ident $(, $arg:ident: $aty:ty)*) $(requires($($requires:tt)*))? -> |$ret:ident| $($ensures:tt)+
    ) => {
        impl_iterator_method!(
            $(#[$attr])*
            [ $type [$($gen)*] as $vtype [$($retgen)*] :: Item [] = $ity $(where $($where)*)? ]
            [ $method [] via $std_method $(where $($wherecon)*)? ]
            ($self_ $(, $arg: $aty)*) $(requires($($requires)*))? -> |$ret| $($ensures)+
        );
    };

    // Default item type from the wrapped std iterator.
    (
        $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] $(where $($where:tt)*)? ]
        [ $method:ident [$($mgen:tt)*] via $std_method:ident $(where $($wherecon:tt)*)? ]
        ($self_:ident $(, $arg:ident: $aty:ty)*) $(requires($($requires:tt)*))? -> |$ret:ident| $($ensures:tt)+
    ) => {
        paste!{ verus!{
        #[verifier::external]
        pub struct $vtype<$($gen)*>($type<$($gen)*>)
            $(where $($where)*)?;

        #[verifier::external_body]
        #[verifier::external_type_specification]
        $(#[$attr])*
        pub struct [<Ex $vtype>]<$($gen)*>($vtype<$($gen)*>)
            $(where $($where)*)?;

        impl<$($gen)*> core::iter::Iterator for $vtype<$($gen)*>
        where
            $($($where)*)?
        {
            type Item = <$type<$($gen)*> as Iterator>::Item;

            #[verifier::external_body]
            fn next(&mut self) -> (ret: Option<<$type<$($gen)*> as Iterator>::Item>)
                { self.0.next() }
        }

        impl<$($gen)*> VergeIteratorSpec for $vtype<$($gen)*>
        where
            $($($where)*)?
        {
            type Item = <$type<$($gen)*> as Iterator>::Item;

            uninterp spec fn seq(&self) -> Seq<Self::Item>;
            uninterp spec fn idx(&self) -> int;
            uninterp spec fn ridx(&self) -> int;

            proof fn new_dummy(seq: Seq<Self::Item>) -> (ret: Self)
                ensures
                    ret.idx() == 0,
                    ret.ridx() == seq.len(),
                    ret.seq() == seq,
            {
                let dummy_iter = choose |dummy_iter: Self| #[trigger] dummy_iter.seq() == seq;
                admit();
                dummy_iter
            }
        }

        impl<$($gen)*> crate::Sealed for $vtype<$($gen)*>
        where
            $($($where)*)?
        {}

        impl<$($gen)*> IteratorSpecImpl for $vtype<$($gen)*>
        where
            $($($where)*)?
        {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool
                { true }
            open spec fn will_return_none(&self) -> bool
                { true }
            open spec fn remaining(&self) -> Seq<<$type<$($gen)*> as Iterator>::Item>
                { self.seq().subrange(self.idx(), self.ridx()) }
            open spec fn decrease(&self) -> Option<nat>
                { Some((self.ridx() - self.idx()) as nat) }
            open spec fn peek(&self, i: int) -> Option<<$type<$($gen)*> as Iterator>::Item> {
                if 0 <= self.idx() + i < self.ridx() { Some(self.seq()[self.idx() + i]) } else { None }
            }
        }

        pub trait [<Iterator $vtype Fn>]: Iterator + IteratorSpec + Sized {
            fn $method<$($mgen)*>($self_, $($arg: $aty),*) -> ($ret: $vtype<$($retgen)*>)
                $(where $($wherecon)*)?
                requires
                    $self_.obeys_prophetic_iter_laws() && $self_.will_return_none(),
                    $($($requires)*)?
                ensures
                    $ret.idx() == 0,
                    $ret.ridx() == $ret.seq().len(),
                    ($($ensures)+),
            ;
        }

        impl<I: Iterator + IteratorSpec + Sized> [<Iterator $vtype Fn>] for I {
            #[verifier::external_body]
            fn $method<$($mgen)*>($self_, $($arg: $aty),*) -> ($ret: $vtype<$($retgen)*>)
                $(where $($wherecon)*)?
                { $vtype($self_.$std_method($($arg),*)) }
        }
        }}
    };

    (
        $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] $(where $($where:tt)*)? ]
        [ $method:ident via $std_method:ident $(where $($wherecon:tt)*)? ]
        ($self_:ident $(, $arg:ident: $aty:ty)*) $(requires($($requires:tt)*))? -> |$ret:ident| $($ensures:tt)+
    ) => {
        impl_iterator_method!(
            $(#[$attr])*
            [ $type [$($gen)*] as $vtype [$($retgen)*] $(where $($where)*)? ]
            [ $method [] via $std_method $(where $($wherecon)*)? ]
            ($self_ $(, $arg: $aty)*) $(requires($($requires)*))? -> |$ret| $($ensures)+
        );
    };
}

//~doc-macro
macro_rules! impl_iterator {
    // Header normalization for constructors whose iterator implementation
    // needs a specialized `ReverseSearcher` bound.
    (
        #[specialized_next_reverse_searcher]
        $(#[$attr:meta])*
        $type:ident <> as $vtype:ident <> :: Item = $ity:ty
        $(where { $($where:tt)* })?
        ; $($constructors:tt)*
    ) => {
        impl_iterator!(
            @new_specialized $(#[$attr])*
            [ $type [] as $vtype [] :: Item = $ity $(where $($where)*)? ]
            $($constructors)*
        );
    };
    (
        #[specialized_next_reverse_searcher]
        $(#[$attr:meta])*
        $type:ident <$gen:lifetime> as $vtype:ident <$retgen:lifetime> :: Item = $ity:ty
        $(where { $($where:tt)* })?
        ; $($constructors:tt)*
    ) => {
        impl_iterator!(
            @new_specialized $(#[$attr])*
            [ $type [$gen] as $vtype [$retgen] :: Item = $ity $(where $($where)*)? ]
            $($constructors)*
        );
    };
    (
        #[specialized_next_reverse_searcher]
        $(#[$attr:meta])*
        $type:ident <$gen:lifetime, $gen2:ident> as $vtype:ident <$retgen:lifetime, $retgen2:ident> :: Item = $ity:ty
        $(where { $($where:tt)* })?
        ; $($constructors:tt)*
    ) => {
        impl_iterator!(
            @new_specialized $(#[$attr])*
            [ $type [$gen, $gen2] as $vtype [$retgen, $retgen2] :: Item = $ity $(where $($where)*)? ]
            $($constructors)*
        );
    };

    (@new_specialized $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        $(#[$constructor_attr:meta])*
        [$hty:path as $($hbound:tt)+] :: $method:ident via $implfn:ident
        $(<$mgen:tt>)?
        (&$self:ident $(, $arg:ident: $aty:ty)* $(,)?)
        -> ($iter:ident : $($ret_ty:tt)+)
        $(where { $($wherecon:tt)* })?
        $(requires { $($requires:tt)* })?
        ensures { $($ensures:tt)* }
        $(;
            $(#[$constructor_attr2:meta])*
            [$hty2:path as $($hbound2:tt)+] :: $method2:ident via $implfn2:ident
            $(<$mgen2:tt>)?
            (&$self2:ident $(, $arg2:ident: $aty2:ty)* $(,)?)
            -> ($iter2:ident : $($ret_ty2:tt)+)
            $(where { $($wherecon2:tt)* })?
            $(requires { $($requires2:tt)* })?
            ensures { $($ensures2:tt)* }
        )*
        $(;)?) => {
        impl_iterator!(
            specialized_next_reverse_searcher @step2 $(#[$attr])*
            [ $type as $vtype [$($gen)*] :: Item = $ity $(where $($where)*)? ]
            [ paste!{verus!{
            pub trait [<$vtype Fn>]: $($hbound)+ {
                $(#[$constructor_attr])*
                fn $method $(<$mgen>)? (&$self $(, $arg: $aty)*) -> ($iter: $($ret_ty)+)
                where
                    $($($wherecon)*)?
                    $(requires $($requires)*)?
                    ensures
                        ({
                            &&& $iter.idx() == 0
                            &&& $iter.ridx() == $iter.seq().len()
                            &&& { $($ensures)* }
                        }),
                    no_unwind;
                $(
                    $(#[$constructor_attr2])*
                    fn $method2 $(<$mgen2>)? (&$self2 $(, $arg2: $aty2)*) -> ($iter2: $($ret_ty2)+)
                    where
                        $($($wherecon2)*)?
                        $(requires $($requires2)*)?
                        ensures
                            ({
                                &&& $iter2.idx() == 0
                                &&& $iter2.ridx() == $iter2.seq().len()
                                &&& { $($ensures2)* }
                            }),
                        no_unwind;
                )*
            }
            impl [<$vtype Fn>] for $hty {
                #[verifier::external_body]
                fn $method $(<$mgen>)? (&$self $(, $arg: $aty)*) -> ($iter: $($ret_ty)+)
                where
                    $($($wherecon)*)?
                { $vtype($hty::$implfn(&$self $(, $arg)*)) }
                $(
                    #[verifier::external_body]
                    fn $method2 $(<$mgen2>)? (&$self2 $(, $arg2: $aty2)*) -> ($iter2: $($ret_ty2)+)
                    where
                        $($($wherecon2)*)?
                    { $vtype($hty2::$implfn2(&$self2 $(, $arg2)*)) }
                )*
            }
            }} ]
        );
    };

    // New, denoised constructor syntax.
    (@new $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        #[custom_next]
        $($constructor:tt)*
    ) => {
        impl_iterator!(
            @new_custom_next $(#[$attr])*
            [ $type [$($gen)*] as $vtype [$($retgen)*] :: Item = $ity $(where $($where)*)? ]
            $($constructor)*
        );
    };

    (@new_custom_next $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        $(#[$constructor_attr:meta])*
        [$hty:path as $($hbound:tt)+] :: $method:ident via $implfn:ident
        $(<$mgen:tt>)?
        (&$self:ident $(, $arg:ident: $aty:ty)* $(,)?)
        -> ($iter:ident : $($ret_ty:tt)+)
        $(where { $($wherecon:tt)* })?
        $(requires { $($requires:tt)* })?
        ensures { $($ensures:tt)* }
        $(;)?) => {
        impl_iterator!(
            #[custom_next] @step2 $(#[$attr])*
            [ $type as $vtype [$($gen)*] :: Item = $ity $(where $($where)*)? ]
            [ paste!{verus!{
            pub trait [<$vtype Fn>]: $($hbound)+ {
                $(#[$constructor_attr])*
                fn $method $(<$mgen>)? (&$self $(, $arg: $aty)*) -> ($iter: $($ret_ty)+)
                where
                    $($($wherecon)*)?
                    $(requires $($requires)*)?
                    ensures
                        ({
                            &&& $iter.idx() == 0
                            &&& $iter.ridx() == $iter.seq().len()
                            &&& { $($ensures)* }
                        }),
                    no_unwind;
            }
            impl [<$vtype Fn>] for $hty {
                #[verifier::external_body]
                fn $method $(<$mgen>)? (&$self $(, $arg: $aty)*) -> ($iter: $($ret_ty)+)
                where
                    $($($wherecon)*)?
                { $vtype($hty::$implfn(&$self $(, $arg)*)) }
            }
            }} ]
        );
    };

    (@new $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        $(specialized_next($($wherenext:tt)*))?
        $(#[$constructor_attr:meta])*
        [$hty:path as $($hbound:tt)+] :: $method:ident via $implfn:ident
        $(<$mgen:tt>)?
        (&$self:ident $(, $arg:ident: $aty:ty)* $(,)?)
        -> ($iter:ident : $($ret_ty:tt)+)
        $(where { $($wherecon:tt)* })?
        $(requires { $($requires:tt)* })?
        ensures { $($ensures:tt)* }
        $(;
            $(#[$constructor_attr2:meta])*
            [$hty2:path as $($hbound2:tt)+] :: $method2:ident via $implfn2:ident
            $(<$mgen2:tt>)?
            (&$self2:ident $(, $arg2:ident: $aty2:ty)* $(,)?)
            -> ($iter2:ident : $($ret_ty2:tt)+)
            $(where { $($wherecon2:tt)* })?
            $(requires { $($requires2:tt)* })?
            ensures { $($ensures2:tt)* }
        )*
        $(;)?) => {
        impl_iterator!(
            $(#[specialized_next($($wherenext)*)])? @step2 $(#[$attr])*
            [ $type as $vtype [$($gen)*] :: Item = $ity $(where $($where)*)? ]
            [ paste!{verus!{
            pub trait [<$vtype Fn>]: $($hbound)+ {
                $(#[$constructor_attr])*
                fn $method $(<$mgen>)? (&$self $(, $arg: $aty)*) -> ($iter: $($ret_ty)+)
                where
                    $($($wherecon)*)?
                    $(requires $($requires)*)?
                    ensures
                        ({
                            &&& $iter.idx() == 0
                            &&& $iter.ridx() == $iter.seq().len()
                            &&& { $($ensures)* }
                        }),
                    no_unwind;
                $(
                    $(#[$constructor_attr2])*
                    fn $method2 $(<$mgen2>)? (&$self2 $(, $arg2: $aty2)*) -> ($iter2: $($ret_ty2)+)
                    where
                        $($($wherecon2)*)?
                        $(requires $($requires2)*)?
                        ensures
                            ({
                                &&& $iter2.idx() == 0
                                &&& $iter2.ridx() == $iter2.seq().len()
                                &&& { $($ensures2)* }
                            }),
                        no_unwind;
                )*
            }
            impl [<$vtype Fn>] for $hty {
                #[verifier::external_body]
                fn $method $(<$mgen>)? (&$self $(, $arg: $aty)*) -> ($iter: $($ret_ty)+)
                where
                    $($($wherecon)*)?
                { $vtype($hty::$implfn(&$self $(, $arg)*)) }
                $(
                    #[verifier::external_body]
                    fn $method2 $(<$mgen2>)? (&$self2 $(, $arg2: $aty2)*) -> ($iter2: $($ret_ty2)+)
                    where
                        $($($wherecon2)*)?
                    { $vtype($hty2::$implfn2(&$self2 $(, $arg2)*)) }
                )*
            }
            }} ]
        );
    };

    (@new $(#[$attr:meta])*
        [ $type:path [$($gen:tt)*] as $vtype:path [$($retgen:tt)*] :: Item = $ity:ty $(where $($where:tt)*)? ]
        $(#[$constructor_attr:meta])*
        $method:ident via $implfn:ident
        $(<$mgen:tt>)?
        ($($params:tt)*)
        -> ($iter:ident : $($ret_ty:tt)+)
        $(where { $($wherecon:tt)* })?
        $(requires { $($requires:tt)* })?
        ensures { $($ensures:tt)* }
        $(;)?) => {
        impl_iterator!(
            @step2 $(#[$attr])*
            [ $type as $vtype [$($gen)*] :: Item = $ity $(where $($where)*)? ]
            [ verus!{
            $(#[$constructor_attr])*
            #[verifier::external_body]
            pub fn $method<$($gen)*>($($params)*) -> ($iter: $($ret_ty)+)
            where
                $($($where)*)?
                $($($wherecon)*)?
                $(requires $($requires)*)?
                ensures
                    ({
                        &&& $iter.idx() == 0
                        &&& $iter.ridx() == $iter.seq().len()
                        &&& $($ensures)*
                    }),
                no_unwind
            { $vtype($implfn($($params)*)) }
            } ]
        );
    };

    // Public header normalization, without a generic metavariable ambiguity.
    (
        $(#[$attr:meta])* $type:ident <> as $vtype:ident <> :: Item = $ity:ty
        $(where { $($where:tt)* })? ; $($constructors:tt)*
    ) => { impl_iterator!(@new $(#[$attr])* [ $type [] as $vtype [] :: Item = $ity $(where $($where)*)? ] $($constructors)*); };
    (
        $(#[$attr:meta])* $type:ident <$gen:lifetime> as $vtype:ident <$retgen:lifetime> :: Item = $ity:ty
        $(where { $($where:tt)* })? ; $($constructors:tt)*
    ) => { impl_iterator!(@new $(#[$attr])* [ $type [$gen] as $vtype [$retgen] :: Item = $ity $(where $($where)*)? ] $($constructors)*); };
    (
        $(#[$attr:meta])* $type:ident <$gen:lifetime, $gen2:ident> as $vtype:ident <$retgen:lifetime, $retgen2:ident> :: Item = $ity:ty
        $(where { $($where:tt)* })? ; $($constructors:tt)*
    ) => { impl_iterator!(@new $(#[$attr])* [ $type [$gen, $gen2] as $vtype [$retgen, $retgen2] :: Item = $ity $(where $($where)*)? ] $($constructors)*); };

    // internal implementation
    (
        $($specialized_next_reverse_searcher:ident)? $(#[$custom:meta])? @step2 $(#[$attr:meta])*
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

            proof fn new_dummy(seq: Seq<Self::Item>) -> (ret: Self)
                ensures
                    ret.idx() == 0,
                    ret.ridx() == seq.len(),
                    ret.seq() == seq,
            {
                let dummy_iter = choose |dummy_iter: Self| #[trigger] dummy_iter.seq() == seq;
                admit();
                dummy_iter
            }
        }

        impl<$($gen)*> crate::Sealed for $vtype<$($gen)*>
        where
            $($($where)*)?
        {}
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
            open spec fn peek(&self, i: int) -> Option<$ity> {
                if 0 <= self.idx() + i < self.ridx() { Some(self.seq()[self.idx() + i]) } else { None }
            }
        }
        _impl_iterator_next!($($specialized_next_reverse_searcher)? $(#[$custom])? $vtype [$($gen)*] $($($where)*)?);
        }}
        // Define the constructor method
        $($constructor)+
    };
}

macro_rules! _impl_iterator_next {
    // custom impl
    (#[custom_next] $($rest:tt)*) => {};
    // specialized impl for str reverse-searcher pattern iterators.
    (specialized_next_reverse_searcher $vtype:path [$($gen:tt)*] $($where:tt)*) => {
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
                P::Searcher<'a>: ReverseSearcher<'a>
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
    // specialized impl
    // XXX(Verus): the whole point of this case is a workaround of Verus's Trait Conflict Checker,
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
use impl_iterator_method;

} // verus!
