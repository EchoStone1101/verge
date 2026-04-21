//! Tests for #[verge_macros::hash_key].

use vstd::prelude::*;
use vstd::std_specs::hash::obeys_key_model;
use std::hash::Hash;
use std::collections::HashMap;

// --- Basic struct ---

#[verge_macros::hash_key(point)]
pub struct Point {
    pub x: u32,
    pub y: u32,
}

// --- Duplicate field types ---

#[verge_macros::hash_key(triple)]
pub struct Triple {
    pub a: u64,
    pub b: u64,
    pub c: u64,
}

// --- Unit struct ---

#[verge_macros::hash_key(unit)]
pub struct Unit;

// --- Tuple struct ---

#[verge_macros::hash_key(pair)]
pub struct Pair(pub u32, pub u64);

// --- Enum ---

#[verge_macros::hash_key(color)]
pub enum Color {
    Red,
    Green,
    Blue,
    Custom(u8, u8, u8),
}

// --- Nested composite ---

#[verge_macros::hash_key(entry)]
pub struct Entry {
    pub key: Point,
    pub color: Color,
    pub priority: u32,
}

verus! {

fn test_point_hash_key() {
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use lemma_point_obeys_key_model;

    let mut map: HashMap<Point, bool> = HashMap::new();
    let key = Point { x: 1, y: 42 };
    map.insert(key, true);
    assert(map@.contains_key(Point { x: 1, y: 42 }));
}

fn test_nested_hash_key() {
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use lemma_point_obeys_key_model;
    broadcast use lemma_color_obeys_key_model;
    broadcast use lemma_entry_obeys_key_model;

    let mut map: HashMap<Entry, u32> = HashMap::new();
    let e = Entry { key: Point { x: 0, y: 0 }, color: Color::Red, priority: 1 };
    map.insert(e, 100);
}

}
