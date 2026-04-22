//! Tests for #[verge_macros::derive_partial_ord].

use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use verge::cmp::{PartialEqVerified, PartialOrdVerified};
use core::cmp::Ordering;

// --- Named struct ---
#[verge_macros::derive_partial_ord(score)]
pub struct Score {
    pub primary: u32,
    pub secondary: u32,
}

// --- Tuple struct ---
#[verge_macros::derive_partial_ord(pair)]
pub struct Pair(pub u32, pub u8);

// --- Nested composite ---
#[verge_macros::derive_partial_ord(entry)]
pub struct Entry {
    pub priority: Score,
    pub category: u8,
    pub id: u64,
}

verus! {

fn test_score_eq() {
    let a = Score { primary: 1, secondary: 2 };
    let b = Score { primary: 1, secondary: 2 };
    let r = (a == b);
    assert(r);
}

fn test_score_lt() {
    let a = Score { primary: 1, secondary: 2 };
    let b = Score { primary: 2, secondary: 0 };
    let r = a.partial_cmp(&b);
    assert(r == Some(Ordering::Less));
}

fn test_score_secondary() {
    let a = Score { primary: 1, secondary: 2 };
    let b = Score { primary: 1, secondary: 3 };
    let r = a.partial_cmp(&b);
    assert(r == Some(Ordering::Less));
}

fn test_score_gt() {
    let a = Score { primary: 5, secondary: 0 };
    let b = Score { primary: 3, secondary: 9 };
    let r = a.partial_cmp(&b);
    assert(r == Some(Ordering::Greater));
}

fn test_pair() {
    let a = Pair(1, 5);
    let b = Pair(1, 10);
    let r = a.partial_cmp(&b);
    assert(r == Some(Ordering::Less));
    let r2 = (a == b);
    assert(!r2);
}

fn test_entry_lt() {
    let a = Entry {
        priority: Score { primary: 1, secondary: 0 },
        category: 5,
        id: 100,
    };
    let b = Entry {
        priority: Score { primary: 2, secondary: 0 },
        category: 3,
        id: 50,
    };
    let r = a.partial_cmp(&b);
    assert(r == Some(Ordering::Less));
}

fn test_entry_eq() {
    let a = Entry {
        priority: Score { primary: 1, secondary: 2 },
        category: 5,
        id: 100,
    };
    let b = Entry {
        priority: Score { primary: 1, secondary: 2 },
        category: 5,
        id: 100,
    };
    let r = (a == b);
    assert(r);
}

}
