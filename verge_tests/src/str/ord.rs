//! Tests for string ordering APIs.

use vstd::prelude::*;
use verge::prelude::*;
use verge::str::*;

verus! {

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

} // verus!
