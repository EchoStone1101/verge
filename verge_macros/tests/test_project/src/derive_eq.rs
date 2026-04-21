//! Tests for #[verge_macros::derive_eq].

use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use verge::cmp::{PartialEqVerified, EqVerified};

#[verge_macros::derive_eq]
pub struct Coord {
    pub x: u32,
    pub y: u32,
}

#[verge_macros::derive_eq]
pub struct Segment {
    pub start: Coord,
    pub end: Coord,
}

#[verge_macros::derive_eq]
pub enum Direction {
    North,
    South,
    Bearing(u32),
}

#[verge_macros::derive_eq]
pub struct Marker;

verus! {

fn test_coord_eq() {
    let a = Coord { x: 1, y: 2 };
    let b = Coord { x: 1, y: 2 };
    let r = (a == b);
    assert(r);
    let c = Coord { x: 1, y: 3 };
    let r2 = (a == c);
    assert(!r2);
}

fn test_segment() {
    let a = Segment { start: Coord { x: 0, y: 0 }, end: Coord { x: 1, y: 1 } };
    let b = Segment { start: Coord { x: 0, y: 0 }, end: Coord { x: 1, y: 1 } };
    let r = (a == b);
    assert(r);
}

fn test_direction() {
    let r1 = (Direction::North == Direction::North);
    assert(r1);
    let r2 = (Direction::North == Direction::South);
    assert(!r2);
    let r3 = (Direction::Bearing(90) == Direction::Bearing(90));
    assert(r3);
}

fn test_marker() {
    let r = (Marker == Marker);
    assert(r);
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
