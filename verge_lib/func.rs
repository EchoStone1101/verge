//! Specifications and lemmas for functions.

use vstd::prelude::*;

use std::marker::Tuple;

verus! {

/// This function encodes whether an `exec`-mode function `f` is deterministic.
pub open spec fn is_deterministic<F, Args: Tuple>(f: F) -> bool
where
    F: FnMut<Args>,
    Args: Tuple,
{
    forall |args: Args, o1: <F as FnOnce<Args>>::Output, o2: <F as FnOnce<Args>>::Output|
        #![trigger call_ensures(f, args, o1), call_ensures(f, args, o2)]
        call_requires(f, args) && call_ensures(f, args, o1) && call_ensures(f, args, o2) ==> o1 == o2
}

/// This function encodes whether an `exec`-mode function `f` is total.
pub open spec fn is_total<F, Args: Tuple>(f: F) -> bool
where
    F: FnMut<Args>,
    Args: Tuple,
{
    forall |args: Args| #[trigger] call_requires(f, args)
}

/// Used for a dummy one-term trigger.
pub uninterp spec fn dummy<A>(a: A) -> ();

/// Used for a dummy two-term trigger.
pub uninterp spec fn dummy2<A, B>(a: A, b: B) -> ();

} // verus!
