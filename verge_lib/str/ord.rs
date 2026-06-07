//! Specifications and lemmas for string ordering.
//!
//! ## Specification Methodology
//! `vstd` provides the `PartialOrdSpec` and `OrdSpec` traits as the standard 
//! way to build ordering specs. However, the orphan rule blocks Verge from 
//! implementing the traits directly on `&str` and `String` types. 
//! As a workaround, we introduce broadcast lemmas that link the `vstd` spec 
//! methods with actual spec clauses.

use super::*;
use vstd::calc;
use vstd::std_specs::cmp::*;

use core::cmp::{PartialOrd, Ord, Ordering};

verus! {

/// This function encodes lexicographical string ordering by byte values 
/// (which also happens to be the unicode code point ordering).
pub open spec fn lexicographical_ordering(a: Seq<u8>, b: Seq<u8>) -> Ordering 
    decreases a.len(),
{
    match (a.len() > 0, b.len() > 0) {
        (false, false) => Ordering::Equal, 
        (false, _) => Ordering::Less,
        (_, false) => Ordering::Greater,
        (_, _) => {
            if a.first() < b.first() {
                Ordering::Less
            } else if a.first() > b.first() {
                Ordering::Greater
            } else {
                lexicographical_ordering(a.drop_first(), b.drop_first())
            }
        },
    }
}

/// Proof that a common prefix does not affect the lexicographical ordering of `a` and `b`.
///
/// This can be used to easily prove `a.is_prefix_of(b) <==> lexicographical_ordering(a, b) is Less`, as 
/// it reduces the comparison to the base case.
pub proof fn lemma_lexicographical_ordering_prefix(a: Seq<u8>, b: Seq<u8>, prefix: Seq<u8>)
    requires
        prefix.is_prefix_of(a),
        prefix.is_prefix_of(b),
    ensures 
        lexicographical_ordering(a.skip(prefix.len() as int), b.skip(prefix.len() as int))
            == lexicographical_ordering(a, b),
    decreases
        prefix.len(),
{
    if prefix.len() == 0 {
        // base case
        assert(a == a.skip(0));
        assert(b == b.skip(0));
    } 
    else {
        assert(prefix.drop_first().is_prefix_of(a.drop_first()));
        assert(prefix.drop_first().is_prefix_of(b.drop_first()));
        calc! {
            (==)
            lexicographical_ordering(a, b); { 
                assert(a.first() == prefix.first());
                assert(b.first() == prefix.first());
            }
            lexicographical_ordering(a.drop_first(), b.drop_first()); {
                lemma_lexicographical_ordering_prefix(a.drop_first(), b.drop_first(), prefix.drop_first());
            } 
            lexicographical_ordering(a.drop_first().skip(prefix.len() - 1), b.drop_first().skip(prefix.len() - 1)); {
                assert(a.skip(prefix.len() as int) == a.drop_first().skip(prefix.len() - 1)); 
                assert(b.skip(prefix.len() as int) == b.drop_first().skip(prefix.len() - 1)); 
            }
            lexicographical_ordering(a.skip(prefix.len() as int), b.skip(prefix.len() as int));
        };
    }
}

/// Allows for `spec`-mode comparisions on strings.
pub trait StringSpecOrd {
    spec fn spec_lt(self, rhs: Self) -> bool;
    spec fn spec_le(self, rhs: Self) -> bool;
    spec fn spec_gt(self, rhs: Self) -> bool;
    spec fn spec_ge(self, rhs: Self) -> bool;
}

impl StringSpecOrd for Seq<char> {

    open spec fn spec_lt(self, rhs: Self) -> bool
        { lexicographical_ordering(self.as_bytes(), rhs.as_bytes()) == Ordering::Less }
    
    open spec fn spec_le(self, rhs: Self) -> bool
        { lexicographical_ordering(self.as_bytes(), rhs.as_bytes()) != Ordering::Greater }
    
    open spec fn spec_gt(self, rhs: Self) -> bool
        { lexicographical_ordering(self.as_bytes(), rhs.as_bytes()) == Ordering::Greater }
    
    open spec fn spec_ge(self, rhs: Self) -> bool
        { lexicographical_ordering(self.as_bytes(), rhs.as_bytes()) != Ordering::Less }
}

/// Linking lemmas for string ordering.
pub broadcast group group_str_ordering {
    lemma_str_obeys_partial_cmp_spec,
    lemma_string_obeys_partial_cmp_spec,
    lemma_str_lexico_partial_cmp_spec,
    lemma_string_lexico_partial_cmp_spec,
    lemma_str_obeys_cmp_spec,
    lemma_string_obeys_cmp_spec,
    lemma_str_lexico_cmp_spec,
    lemma_string_lexico_cmp_spec,
}

// `PartialOrd`

/// Proof that asserts `&str` obeys `PartialOrd`.
pub broadcast axiom fn lemma_str_obeys_partial_cmp_spec()
    ensures
        #[trigger] <str as PartialOrdSpec>::obeys_partial_cmp_spec(),
;

/// Proof that asserts `String` obeys `PartialOrd`.
pub broadcast axiom fn lemma_string_obeys_partial_cmp_spec()
    ensures
        #[trigger] <String as PartialOrdSpec>::obeys_partial_cmp_spec(),
;

/// Proof that links `PartialOrdSpec::partial_cmp_spec` for `&str` with actual specs.
pub broadcast axiom fn lemma_str_lexico_partial_cmp_spec(a: &str, b: &str)
    ensures
        #![trigger <str as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <str as PartialOrdSpec>::partial_cmp_spec(a, b) is Some,
        <str as PartialOrdSpec>::partial_cmp_spec(a, b)->0 == 
            lexicographical_ordering(a@.as_bytes(), b@.as_bytes()),
;

/// Proof that links `PartialOrdSpec::partial_cmp_spec` for `String` with actual specs.
pub broadcast axiom fn lemma_string_lexico_partial_cmp_spec(a: &String, b: &String)
    ensures
        #![trigger <String as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <String as PartialOrdSpec>::partial_cmp_spec(a, b) is Some,
        <String as PartialOrdSpec>::partial_cmp_spec(a, b)->0 == 
            lexicographical_ordering(a@.as_bytes(), b@.as_bytes()),
;

// `Ord`

/// Proof that asserts `&str` obeys `Ord`.
pub broadcast axiom fn lemma_str_obeys_cmp_spec()
    ensures
        #[trigger] <str as OrdSpec>::obeys_cmp_spec(),
;

/// Proof that asserts `String` obeys `Ord`.
pub broadcast axiom fn lemma_string_obeys_cmp_spec()
    ensures
        #[trigger] <String as OrdSpec>::obeys_cmp_spec(),
;

/// Proof that links `OrdSpec::cmp_spec` for `&str` with actual specs.
pub broadcast axiom fn lemma_str_lexico_cmp_spec(a: &str, b: &str)
    ensures
        #![trigger <str as OrdSpec>::cmp_spec(a, b)]
        <str as OrdSpec>::cmp_spec(a, b) == 
            lexicographical_ordering(a@.as_bytes(), b@.as_bytes()),
;

/// Proof that links `OrdSpec::cmp_spec` for `String` with actual specs.
pub broadcast axiom fn lemma_string_lexico_cmp_spec(a: &String, b: &String)
    ensures
        #![trigger <String as OrdSpec>::cmp_spec(a, b)]
        <String as OrdSpec>::cmp_spec(a, b) == 
            lexicographical_ordering(a@.as_bytes(), b@.as_bytes()),
;

fn test_partial_ord() {
    proof {
        broadcast use group_str_axioms;
        reveal_strlit("ab");
        reveal_strlit("ac");
        reveal_with_fuel(lexicographical_ordering, 3);
    }

    let a: &str = "ab";
    let b: &&str = &"ac"; // this works because `vstd` has spec on &A and &B ordering
    assert(a@ < b@);
    let r = (a < b);
    assert(r);
}

// `Ord`



} // verus!