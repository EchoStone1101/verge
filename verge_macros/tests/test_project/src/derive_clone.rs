//! Tests for #[verge_macros::derive_clone].

use vstd::prelude::*;
use vstd::pervasive::strictly_cloned;

// --- Struct ---

#[verge_macros::derive_clone(point)]
pub struct Point {
    pub x: u32,
    pub y: u32,
}

// --- Nested struct ---

#[verge_macros::derive_clone(segment)]
pub struct Segment {
    pub start: Point,
    pub end: Point,
}

// --- Enum ---

#[verge_macros::derive_clone(color)]
pub enum Color {
    Red,
    Green,
    Rgb(u8, u8, u8),
}

verus! {

// Test: clone produces field-level strictly_cloned
fn test_point_clone() {
    let a = Point { x: 1, y: 2 };
    let b = a.clone();
    // The assume_specification gives us point_strictly_cloned(&a, &b)
    assert(point_strictly_cloned(&a, &b));
    // Since u32::clone ensures ret == *self, strictly_cloned(u32) ==> equal
    assert(b.x == a.x);
    assert(b.y == a.y);
}

// Test: nested clone
fn test_segment_clone() {
    let a = Segment {
        start: Point { x: 0, y: 0 },
        end: Point { x: 1, y: 1 },
    };
    let b = a.clone();
    assert(segment_strictly_cloned(&a, &b));
}

// Test: enum clone
fn test_color_clone() {
    let a = Color::Rgb(10, 20, 30);
    let b = a.clone();
    assert(color_strictly_cloned(&a, &b));
}

// Test: strictly_cloned implies the field-level spec
proof fn test_strictly_cloned_implies_spec(a: Point, b: Point)
    requires strictly_cloned(a, b),
{
    // strictly_cloned(Point, Point) should imply point_strictly_cloned
    // because strictly_cloned encodes call_ensures(<Point as Clone>::clone, ...)
    // and the assume_specification gives point_strictly_cloned as postcondition
    assert(point_strictly_cloned(&a, &b));
}

}
