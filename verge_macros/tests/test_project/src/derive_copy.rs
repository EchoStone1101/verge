//! Tests for #[verge_macros::derive_copy].

use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use vstd::pervasive::strictly_cloned;
use verge::cmp::PartialEqVerified;
use verge::clone::CopyVerified;

// --- Named struct ---
#[verge_macros::derive_copy(coord)]
pub struct Coord {
    pub x: u32,
    pub y: u32,
}

// --- Tuple struct ---
#[verge_macros::derive_copy(pair)]
pub struct Pair(pub u32, pub bool);

// --- Unit struct ---
#[verge_macros::derive_copy(tag)]
pub struct Tag;

// --- Enum ---
#[verge_macros::derive_copy(dir)]
pub enum Dir {
    Up,
    Down,
    Custom(u8),
}

// PartialEq is needed separately for Coord (derive_copy doesn't generate it)
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

fn test_coord_clone() {
    let a = Coord { x: 1, y: 2 };
    let b = a.clone();
    assert(coord_strictly_cloned(&a, &b));
    assert(b.x == a.x);
}

fn test_coord_copy() {
    let a = Coord { x: 3, y: 4 };
    let b = a; // Copy
    let r = (a == b);
    assert(r);
}

fn test_pair_copy() {
    let a = Pair(5, true);
    let b = a;
    let c = a.clone();
    assert(pair_strictly_cloned(&a, &c));
}

fn test_tag_copy() {
    let a = Tag;
    let b = a;
    let c = a.clone();
    assert(tag_strictly_cloned(&a, &c));
}

fn test_dir_copy() {
    let a = Dir::Custom(42);
    let b = a;
    let c = a.clone();
    assert(dir_strictly_cloned(&a, &c));
}

proof fn test_copy_spec_eq(a: Coord, b: Coord)
    requires strictly_cloned(a, b),
{
    assert(coord_strictly_cloned(&a, &b));
    assert(a == b);
}

}
