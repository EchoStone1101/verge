//! Test composability of derive macros and field attributes (#[ignored], #[ignored_with_default]).
//!
//! Tests: (derive_partial_ord | derive_ord) × (derive_clone | derive_copy),
//! and field-level #[ignored] / #[ignored_with_default] behavior.

use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use verge::cmp::*;
use verge::clone::*;
use core::cmp::Ordering;

verus! {

// === Composability: PartialOrd + Clone ===
#[verge_macros::derive_partial_ord]
#[verge_macros::derive_clone]
pub struct C1 { pub x: u32, pub y: u32 }

fn test_c1() {
    let a = C1 { x: 1, y: 2 };
    let b = C1 { x: 1, y: 2 };
    let r = (a == b);
    assert(r);
    let r2 = a.partial_cmp(&b);
    assert(r2 == Some(Ordering::Equal));
    let c = a.clone();
    assert(C1::strictly_cloned(&a, &c));
}

// === Composability: PartialOrd + Copy ===
#[verge_macros::derive_partial_ord]
#[verge_macros::derive_copy]
pub struct C2 { pub x: u32, pub y: u32 }

fn test_c2() {
    let a = C2 { x: 1, y: 2 };
    let b = C2 { x: 1, y: 3 };
    let r = (a == b);
    assert(!r);
    let r2 = a.partial_cmp(&b);
    assert(r2 == Some(Ordering::Less));
    let c = a.clone();
    assert(C2::strictly_cloned(&a, &c));
}

// === Composability: Ord + Clone ===
#[verge_macros::derive_ord]
#[verge_macros::derive_clone]
pub struct C3 { pub x: u32, pub y: u32 }

fn test_c3() {
    let a = C3 { x: 1, y: 2 };
    let b = C3 { x: 1, y: 2 };
    let r = (a == b);
    assert(r);
    let r2 = a.cmp(&b);
    assert(r2 == Ordering::Equal);
    let c = a.clone();
    assert(C3::strictly_cloned(&a, &c));
}

// === Composability: Ord + Copy ===
#[verge_macros::derive_ord]
#[verge_macros::derive_copy]
pub struct C4 { pub x: u32, pub y: u32 }

fn test_c4() {
    let a = C4 { x: 2, y: 0 };
    let b = C4 { x: 1, y: 9 };
    let r = (a == b);
    assert(!r);
    let r2 = a.cmp(&b);
    assert(r2 == Ordering::Greater);
    let c = a.clone();
    assert(C4::strictly_cloned(&a, &c));
}

}

// === #[ignored] with derive_partial_eq + derive_clone ===
#[verge_macros::derive_partial_eq]
#[verge_macros::derive_clone]
pub struct Cached {
    pub key: u32,
    #[ignored]
    pub cached_value: Option<u64>,
}

// === #[ignored] with derive_partial_ord ===
#[verge_macros::derive_partial_ord]
pub struct CachedOrd {
    pub key: u32,
    #[ignored]
    pub cached_value: Option<u64>,
}

// === #[ignored] with derive_ord ===
#[verge_macros::derive_ord]
pub struct CachedTotal {
    pub key: u32,
    #[ignored]
    pub cached_value: Option<u64>,
}

// === #[ignored_with_default] field with derive_clone (reset on clone) ===
#[verge_macros::derive_clone]
pub struct ResetCache {
    pub key: u32,
    #[ignored_with_default]
    pub cached_value: Option<u64>,
}

// === #[ignored_with_default] field with derive_clone on tuple struct ===
#[verge_macros::derive_clone]
pub struct ResetPair(pub u32, #[ignored_with_default] pub Option<u8>);

verus! {

fn test_ignored_eq() {
    let a = Cached { key: 42, cached_value: Some(100) };
    let b = Cached { key: 42, cached_value: None };
    let r = (a == b);
    assert(r);
}

fn test_ignored_ne() {
    let a = Cached { key: 1, cached_value: None };
    let b = Cached { key: 2, cached_value: None };
    let r = (a == b);
    assert(!r);
}

fn test_ignored_clone() {
    let a = Cached { key: 42, cached_value: Some(100) };
    let b = a.clone();
    assert(Cached::strictly_cloned(&a, &b));
}

fn test_ignored_partial_ord() {
    let a = CachedOrd { key: 1, cached_value: Some(999) };
    let b = CachedOrd { key: 2, cached_value: None };
    let r = a.partial_cmp(&b);
    assert(r == Some(Ordering::Less));
    // Same key, different cached_value: equal
    let c = CachedOrd { key: 5, cached_value: Some(1) };
    let d = CachedOrd { key: 5, cached_value: None };
    let r2 = (c == d);
    assert(r2);
}

fn test_ignored_ord() {
    let a = CachedTotal { key: 3, cached_value: None };
    let b = CachedTotal { key: 1, cached_value: Some(42) };
    let r = a.cmp(&b);
    assert(r == Ordering::Greater);
    let c = CachedTotal { key: 7, cached_value: Some(10) };
    let d = CachedTotal { key: 7, cached_value: None };
    let r2 = (c == d);
    assert(r2);
}

fn test_default_clone_resets() {
    let a = ResetCache { key: 42, cached_value: Some(100) };
    let b = a.clone();
    assert(ResetCache::strictly_cloned(&a, &b));
    assert(b.cached_value == Option::<u64>::None);
    assert(b.key == 42u32);
}

fn test_default_clone_tuple() {
    let a = ResetPair(99, Some(7));
    let b = a.clone();
    assert(ResetPair::strictly_cloned(&a, &b));
    assert(b.1 == Option::<u8>::None);
    assert(b.0 == 99u32);
}

}
