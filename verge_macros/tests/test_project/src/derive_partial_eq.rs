//! Tests for #[verge_macros::derive_partial_eq].

use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use verge::cmp::PartialEqVerified;

// --- Named struct (open eq_spec) ---
#[verge_macros::derive_partial_eq]
pub struct Point {
    pub x: u32,
    pub y: u32,
}

// --- Tuple struct ---
#[verge_macros::derive_partial_eq]
pub struct Pair(pub u32, pub bool);

// --- Unit struct ---
#[verge_macros::derive_partial_eq]
pub struct Marker;

// --- Struct with private field (closed eq_spec) ---
#[verge_macros::derive_partial_eq]
pub struct Token {
    secret: u64,
    pub label: u32,
}

// --- Nested composite ---
#[verge_macros::derive_partial_eq]
pub struct Line {
    pub start: Point,
    pub end: Point,
}

// --- Enum with mixed variants ---
#[verge_macros::derive_partial_eq]
pub enum Shape {
    Circle(u32),
    Rect { w: u32, h: u32 },
    Empty,
}

verus! {

fn test_point_eq() {
    let a = Point { x: 1, y: 2 };
    let b = Point { x: 1, y: 2 };
    let r = (a == b);
    assert(r);
}

fn test_point_ne() {
    let a = Point { x: 1, y: 2 };
    let b = Point { x: 1, y: 3 };
    let r = (a == b);
    assert(!r);
}

fn test_pair() {
    let a = Pair(5, true);
    let b = Pair(5, true);
    let r = (a == b);
    assert(r);
    let c = Pair(5, false);
    let r2 = (a == c);
    assert(!r2);
}

fn test_marker() {
    let r = (Marker == Marker);
    assert(r);
}

fn test_line() {
    let a = Line { start: Point { x: 0, y: 0 }, end: Point { x: 1, y: 1 } };
    let b = Line { start: Point { x: 0, y: 0 }, end: Point { x: 1, y: 1 } };
    let r = (a == b);
    assert(r);
}

fn test_shape() {
    let r1 = (Shape::Empty == Shape::Empty);
    assert(r1);
    let r2 = (Shape::Circle(5) == Shape::Circle(5));
    assert(r2);
    let r3 = (Shape::Circle(5) == Shape::Circle(6));
    assert(!r3);
    let r4 = (Shape::Rect { w: 3, h: 4 } == Shape::Rect { w: 3, h: 4 });
    assert(r4);
    let r5 = (Shape::Circle(5) == Shape::Empty);
    assert(!r5);
}

proof fn test_symmetry() {
    let a = Point { x: 1, y: 2 };
    let b = Point { x: 3, y: 4 };
    Point::lemma_eq_symmetric(&a, &b);
    assert(PartialEqSpec::eq_spec(&a, &b) <==> PartialEqSpec::eq_spec(&b, &a));
}

}
