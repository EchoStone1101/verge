//! Tests for #[verge_macros::derive_default].

use vstd::prelude::*;

// --- Struct: named fields ---
#[verge_macros::derive_default(point)]
pub struct Point {
    pub x: u32,
    pub y: u32,
}

// --- Struct: unit ---
#[verge_macros::derive_default(unit)]
pub struct UnitStruct;

// --- Struct: unnamed fields ---
#[verge_macros::derive_default(pair)]
pub struct Pair(pub u32, pub bool);

// --- Enum with #[default] on unit variant ---
#[verge_macros::derive_default(color)]
pub enum Color {
    Red,
    #[default]
    Green,
    Blue,
}

// --- Enum with #[default] on variant with fields ---
#[verge_macros::derive_default(holder)]
pub enum Holder {
    Empty,
    #[default]
    WithValue { val: u32 },
}

verus! {

fn test_point_default() {
    let p = Point::default();
    assert(point_is_default(&p));
}

fn test_unit_default() {
    let u = UnitStruct::default();
    assert(unit_is_default(&u));
}

fn test_pair_default() {
    let p = Pair::default();
    assert(pair_is_default(&p));
}

fn test_color_default() {
    let c = Color::default();
    assert(color_is_default(&c));
}

fn test_holder_default() {
    let h = Holder::default();
    assert(holder_is_default(&h));
}

}
