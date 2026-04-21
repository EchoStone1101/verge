//! Test composability of derive macros: (derive_partial_ord | derive_ord) × (derive_clone | derive_copy)
//!
//! Since PartialOrd/Ord already emit PartialEq, we don't stack eq macros separately.
//! All macros must be inside verus! { } for composability.

use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use verge::cmp::*;
use verge::clone::*;
use core::cmp::Ordering;

verus! {

// 1. PartialOrd + Clone
#[verge_macros::derive_partial_ord(c1)]
#[verge_macros::derive_clone(c1)]
pub struct C1 { pub x: u32, pub y: u32 }

// 2. PartialOrd + Copy
#[verge_macros::derive_partial_ord(c2)]
#[verge_macros::derive_copy(c2)]
pub struct C2 { pub x: u32, pub y: u32 }

// 3. Ord + Clone
#[verge_macros::derive_ord(c3)]
#[verge_macros::derive_clone(c3)]
pub struct C3 { pub x: u32, pub y: u32 }

// 4. Ord + Copy
#[verge_macros::derive_ord(c4)]
#[verge_macros::derive_copy(c4)]
pub struct C4 { pub x: u32, pub y: u32 }

// --- Tests ---

fn test_c1() {
    let a = C1 { x: 1, y: 2 };
    let b = C1 { x: 1, y: 2 };
    let r = (a == b);
    assert(r);
    let r2 = a.partial_cmp(&b);
    assert(r2 == Some(Ordering::Equal));
    let c = a.clone();
    assert(c1_strictly_cloned(&a, &c));
}

fn test_c2() {
    let a = C2 { x: 1, y: 2 };
    let b = C2 { x: 1, y: 3 };
    let r = (a == b);
    assert(!r);
    let r2 = a.partial_cmp(&b);
    assert(r2 == Some(Ordering::Less));
    let c = a.clone();
    assert(c2_strictly_cloned(&a, &c));
}

fn test_c3() {
    let a = C3 { x: 1, y: 2 };
    let b = C3 { x: 1, y: 2 };
    let r = (a == b);
    assert(r);
    let r2 = a.cmp(&b);
    assert(r2 == Ordering::Equal);
    let c = a.clone();
    assert(c3_strictly_cloned(&a, &c));
}

fn test_c4() {
    let a = C4 { x: 2, y: 0 };
    let b = C4 { x: 1, y: 9 };
    let r = (a == b);
    assert(!r);
    let r2 = a.cmp(&b);
    assert(r2 == Ordering::Greater);
    let c = a.clone();
    assert(c4_strictly_cloned(&a, &c));
}

// --- Test #[ignored] on fields ---

// derive_partial_eq + derive_clone: #[ignored] excludes cached_value from eq and clone spec
#[verge_macros::derive_partial_eq]
#[verge_macros::derive_clone(cached)]
pub struct Cached {
    pub key: u32,
    #[ignored]
    pub cached_value: Option<u64>,
}

// derive_partial_ord + #[ignored]: only key participates in ordering
#[verge_macros::derive_partial_ord(cached_ord)]
pub struct CachedOrd {
    pub key: u32,
    #[ignored]
    pub cached_value: Option<u64>,
}

// derive_ord + #[ignored]
#[verge_macros::derive_ord(cached_total)]
pub struct CachedTotal {
    pub key: u32,
    #[ignored]
    pub cached_value: Option<u64>,
}

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
    assert(cached_strictly_cloned(&a, &b));
}

fn test_ignored_partial_ord_lt() {
    let a = CachedOrd { key: 1, cached_value: Some(999) };
    let b = CachedOrd { key: 2, cached_value: None };
    let r = a.partial_cmp(&b);
    assert(r == Some(Ordering::Less));
}

fn test_ignored_partial_ord_eq() {
    let a = CachedOrd { key: 5, cached_value: Some(1) };
    let b = CachedOrd { key: 5, cached_value: None };
    let r = (a == b);
    assert(r);
}

fn test_ignored_ord_gt() {
    let a = CachedTotal { key: 3, cached_value: None };
    let b = CachedTotal { key: 1, cached_value: Some(42) };
    let r = a.cmp(&b);
    assert(r == Ordering::Greater);
}

fn test_ignored_ord_eq() {
    let a = CachedTotal { key: 7, cached_value: Some(10) };
    let b = CachedTotal { key: 7, cached_value: None };
    let r = (a == b);
    assert(r);
}

}

// --- Test #[default] on fields (derive_clone resets field to Default) ---

#[verge_macros::derive_clone(reset_cache)]
pub struct ResetCache {
    pub key: u32,
    #[default]
    pub cached_value: Option<u64>,
}

verus! {

fn test_default_clone_resets() {
    let a = ResetCache { key: 42, cached_value: Some(100) };
    let b = a.clone();
    // key is cloned normally, cached_value is reset to default (None)
    assert(reset_cache_strictly_cloned(&a, &b));
    // call_ensures for Option<u64>::default gives None
    assert(b.cached_value == Option::<u64>::None);
}

fn test_default_clone_key_preserved() {
    let a = ResetCache { key: 99, cached_value: Some(7) };
    let b = a.clone();
    assert(b.key == 99u32);
}

}
