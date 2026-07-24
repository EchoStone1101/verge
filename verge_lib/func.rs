//! Specifications and lemmas for functions.
//!
//! ## Macros
//! The `assume_surjective` and `assume_injective_by` proc-macros derive admitted
//! proof lemmas from an existing `proof fn` or `exec fn` contract. They are gated
//! by the `func_assume_lemmas` feature because the generated lemmas are trusted.
//! The `assert_surjective` and `assert_injective_by` variants instead generate
//! private sanity-check lemmas that call a separately written proof function.
//! Dedicated submodules under `func` hold proof functions for other Verge modules'
//! function-contract sanity checks.

/// Generates an admitted proof lemma that assumes the function contract is surjective.
///
/// The generated lemma is named after the annotated function with `_surjective` appended.
/// It takes the original arguments plus any named return value, requires the original
/// postconditions, and ensures the original preconditions.
///
/// This macro only generates the lemma when the `func_assume_lemmas` feature is enabled.
pub use verge_macros::assume_surjective;

/// Generates an admitted proof lemma that assumes the function contract is injective.
///
/// The macro argument is split by a single `;`: expressions on the left are required
/// equal across two copies of the function arguments, while expressions on the right
/// are ensured equal. The generated lemma is named after the annotated function with
/// `_injective` appended.
///
/// This macro only generates the lemma when the `func_assume_lemmas` feature is enabled.
pub use verge_macros::assume_injective_by;

/// Generates a private proof lemma that checks the function contract is surjective.
///
/// The macro argument is the path to a proof function. The generated lemma is named
/// after the annotated function with `__` prepended and `_surjective` appended. Its
/// body forwards the original arguments plus any named return value to the proof.
pub use verge_macros::assert_surjective;

/// Generates a private proof lemma that checks the function contract is injective.
///
/// The macro argument is a proof function call split by a single `;`, such as
/// `path::to::proof(arg; ret)`. The expressions determine the injective equality
/// relation, and the generated lemma forwards its two argument copies to the proof.
pub use verge_macros::assert_injective_by;

use vstd::prelude::*;

use std::marker::Tuple;

verus! {

pub(crate) mod str;

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
