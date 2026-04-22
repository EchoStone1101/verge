//! Tests for #[verge_macros::derive_clone].

use vstd::prelude::*;
use vstd::pervasive::strictly_cloned;

// --- Named struct ---
#[verge_macros::derive_clone]
pub struct Point {
    pub x: u32,
    pub y: u32,
}

// --- Tuple struct ---
#[verge_macros::derive_clone]
pub struct Pair(pub u32, pub bool);

// --- Unit struct ---
#[verge_macros::derive_clone]
pub struct Tag;

// --- Nested struct ---
#[verge_macros::derive_clone]
pub struct Segment {
    pub start: Point,
    pub end: Point,
}

// --- Enum with all variant kinds ---
#[verge_macros::derive_clone]
pub enum Color {
    Red,
    Green,
    Rgb(u8, u8, u8),
    Named { r: u8, g: u8, b: u8 },
}

verus! {

fn test_point_clone() {
    let a = Point { x: 1, y: 2 };
    let b = a.clone();
    assert(Point::strictly_cloned(&a, &b));
    assert(b.x == a.x);
    assert(b.y == a.y);
}

fn test_pair_clone() {
    let a = Pair(42, true);
    let b = a.clone();
    assert(Pair::strictly_cloned(&a, &b));
}

fn test_tag_clone() {
    let a = Tag;
    let b = a.clone();
    assert(Tag::strictly_cloned(&a, &b));
}

fn test_segment_clone() {
    let a = Segment {
        start: Point { x: 0, y: 0 },
        end: Point { x: 1, y: 1 },
    };
    let b = a.clone();
    assert(Segment::strictly_cloned(&a, &b));
}

fn test_color_unit() {
    let a = Color::Red;
    let b = a.clone();
    assert(Color::strictly_cloned(&a, &b));
}

fn test_color_tuple() {
    let a = Color::Rgb(10, 20, 30);
    let b = a.clone();
    assert(Color::strictly_cloned(&a, &b));
}

fn test_color_named() {
    let a = Color::Named { r: 255, g: 0, b: 128 };
    let b = a.clone();
    assert(Color::strictly_cloned(&a, &b));
}

proof fn test_strictly_cloned_implies_spec(a: Point, b: Point)
    requires strictly_cloned(a, b),
{
    assert(Point::strictly_cloned(&a, &b));
}

}
