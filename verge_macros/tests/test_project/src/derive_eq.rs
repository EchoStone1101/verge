//! Tests for #[verge_macros::derive_eq].

use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use verge::cmp::{PartialEqVerified, EqVerified};

// --- Named struct ---
#[verge_macros::derive_eq]
pub struct Coord {
    pub x: u32,
    pub y: u32,
}

// --- Tuple struct ---
#[verge_macros::derive_eq]
pub struct Pair(pub u32, pub u64);

// --- Unit struct ---
#[verge_macros::derive_eq]
pub struct Tag;

// --- Enum with mixed variants ---
#[verge_macros::derive_eq]
pub enum Direction {
    North,
    South,
    Bearing(u32),
    Named { degrees: u32, label: u8 },
}

verus! {

fn test_coord() {
    let a = Coord { x: 1, y: 2 };
    let b = Coord { x: 1, y: 2 };
    let r = (a == b);
    assert(r);
    let c = Coord { x: 1, y: 3 };
    let r2 = (a == c);
    assert(!r2);
}

fn test_pair() {
    let a = Pair(5, 100);
    let b = Pair(5, 100);
    let r = (a == b);
    assert(r);
}

fn test_tag() {
    let r = (Tag == Tag);
    assert(r);
}

fn test_direction() {
    let r1 = (Direction::North == Direction::North);
    assert(r1);
    let r2 = (Direction::North == Direction::South);
    assert(!r2);
    let r3 = (Direction::Bearing(90) == Direction::Bearing(90));
    assert(r3);
    let r4 = (Direction::Named { degrees: 45, label: 1 } == Direction::Named { degrees: 45, label: 1 });
    assert(r4);
    let r5 = (Direction::Named { degrees: 45, label: 1 } == Direction::Named { degrees: 45, label: 2 });
    assert(!r5);
}

proof fn test_reflexivity() {
    let a = Coord { x: 5, y: 10 };
    Coord::lemma_eq_reflexive(&a);
    assert(PartialEqSpec::eq_spec(&a, &a));
}

proof fn test_symmetry() {
    let a = Coord { x: 1, y: 2 };
    let b = Coord { x: 3, y: 4 };
    Coord::lemma_eq_symmetric(&a, &b);
    assert(PartialEqSpec::eq_spec(&a, &b) <==> PartialEqSpec::eq_spec(&b, &a));
}

}
