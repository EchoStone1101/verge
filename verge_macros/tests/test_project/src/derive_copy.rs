//! Tests for #[verge_macros::derive_copy].

use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use vstd::pervasive::strictly_cloned;
use verge::cmp::PartialEqVerified;
use verge::clone::CopyVerified;

// derive_copy generates: struct + Copy + Clone (with spec) + CopyVerified
#[verge_macros::derive_copy(coord)]
pub struct Coord {
    pub x: u32,
    pub y: u32,
}

// PartialEq is needed separately (derive_copy doesn't generate it)
verus! {

impl PartialEq for Coord {
    fn eq(&self, other: &Self) -> (r: bool) {
        self.x == other.x && self.y == other.y
    }
}

impl PartialEqSpecImpl for Coord {
    open spec fn obeys_eq_spec() -> bool { true }
    open spec fn eq_spec(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl PartialEqVerified for Coord {
    proof fn lemma_eq_symmetric(a: &Self, b: &Self) {}
    proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {}
}

// --- Tests ---

fn test_coord_clone() {
    let a = Coord { x: 1, y: 2 };
    let b = a.clone();
    assert(coord_strictly_cloned(&a, &b));
    assert(b.x == a.x);
    assert(b.y == a.y);
}

fn test_coord_copy() {
    let a = Coord { x: 3, y: 4 };
    let b = a; // Copy
    let r = (a == b);
    assert(r);
}

proof fn test_strictly_cloned_spec_eq(a: Coord, b: Coord)
    requires strictly_cloned(a, b),
{
    assert(coord_strictly_cloned(&a, &b));
    assert(a == b);
}

}
