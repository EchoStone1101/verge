//! Tests for #[verge_macros::derive_default].

use vstd::prelude::*;

// --- Named struct ---
#[verge_macros::derive_default]
pub struct Point {
    pub x: u32,
    pub y: u32,
}

// --- Tuple struct ---
#[verge_macros::derive_default]
pub struct Pair(pub u32, pub bool);

// --- Unit struct ---
#[verge_macros::derive_default]
pub struct UnitStruct;

// --- Enum: #[default] on unit variant ---
#[verge_macros::derive_default]
pub enum Color {
    Red,
    #[default]
    Green,
    Blue,
}

// --- Enum: #[default] on variant with named fields ---
#[verge_macros::derive_default]
pub enum Holder {
    Empty,
    #[default]
    WithValue { val: u32 },
}

// --- Enum: #[default] on variant with unnamed fields ---
#[verge_macros::derive_default]
pub enum Wrapper {
    #[default]
    Single(u32),
    Double(u32, u32),
}

verus! {

fn test_point_default() {
    let p = Point::default();
    assert(Point::is_default(&p));
}

fn test_pair_default() {
    let p = Pair::default();
    assert(Pair::is_default(&p));
}

fn test_unit_default() {
    let u = UnitStruct::default();
    assert(UnitStruct::is_default(&u));
}

fn test_color_default() {
    let c = Color::default();
    assert(Color::is_default(&c));
}

fn test_color_non_default() {
    let c = Color::Red;
    assert(!Color::is_default(&c));
}

fn test_holder_default() {
    let h = Holder::default();
    assert(Holder::is_default(&h));
}

fn test_holder_non_default() {
    let h = Holder::Empty;
    assert(!Holder::is_default(&h));
}

fn test_wrapper_default() {
    let w = Wrapper::default();
    assert(Wrapper::is_default(&w));
}

}
