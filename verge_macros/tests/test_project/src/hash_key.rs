//! Tests for #[verge_macros::hash_key] and #[verge_macros::hash_key_with_clone].

use vstd::prelude::*;
use vstd::std_specs::hash::obeys_key_model;
use std::collections::HashMap;

// --- hash_key: struct (bans Clone) ---
#[verge_macros::hash_key]
pub struct Point {
    pub x: u32,
    pub y: u32,
}

// --- hash_key: unit struct ---
#[verge_macros::hash_key]
pub struct Unit;

// --- hash_key: tuple struct ---
#[verge_macros::hash_key]
pub struct Pair(pub u32, pub u64);

// --- hash_key: enum ---
#[verge_macros::hash_key]
pub enum Color {
    Red,
    Green,
    Blue,
    Custom(u8, u8, u8),
}

// --- hash_key_with_clone: struct ---
#[verge_macros::hash_key_with_clone]
pub struct Tag {
    pub id: u32,
    pub label: u64,
}

// --- hash_key_with_clone: enum ---
#[verge_macros::hash_key_with_clone]
pub enum Status {
    Active,
    Inactive,
    Code(u32),
}

// --- hash_key with #[ignored] ---
#[verge_macros::hash_key]
pub struct CachedKey {
    pub key: u32,
    #[ignored]
    pub cached: Option<u64>,
}

verus! {

fn test_point_hash_key() {
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use Point::lemma_obeys_key_model;

    let mut map: HashMap<Point, bool> = HashMap::new();
    let key = Point { x: 1, y: 42 };
    map.insert(key, true);
    assert(map@.contains_key(Point { x: 1, y: 42 }));
}

fn test_point_eq() {
    let a = Point { x: 1, y: 2 };
    let b = Point { x: 1, y: 2 };
    let r = (a == b);
    assert(r);
}

fn test_color_eq() {
    let r = (Color::Red == Color::Red);
    assert(r);
    let r2 = (Color::Red == Color::Green);
    assert(!r2);
}

fn test_tag_clone() {
    let a = Tag { id: 1, label: 42 };
    let b = a.clone();
    assert(Tag::strictly_cloned(&a, &b));
    assert(b.id == 1u32);
}

fn test_status_clone() {
    let a = Status::Code(42);
    let b = a.clone();
    assert(Status::strictly_cloned(&a, &b));
}

fn test_cached_key_eq() {
    let a = CachedKey { key: 42, cached: Some(100) };
    let b = CachedKey { key: 42, cached: None };
    let r = (a == b);
    assert(r);
}

}
