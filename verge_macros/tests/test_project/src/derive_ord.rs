//! Tests for #[verge_macros::derive_ord].

use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use verge::cmp::{PartialEqVerified, EqVerified, PartialOrdVerified, OrdVerified};
use core::cmp::Ordering;

// --- Named struct ---
#[verge_macros::derive_ord]
pub struct Rank {
    pub tier: u32,
    pub points: u64,
}

// --- Tuple struct ---
#[verge_macros::derive_ord]
pub struct Pair(pub u32, pub u8);

// --- Nested composite ---
#[verge_macros::derive_ord]
pub struct Player {
    pub rank: Rank,
    pub name_hash: u32,
}

verus! {

fn test_rank_eq() {
    let a = Rank { tier: 1, points: 100 };
    let b = Rank { tier: 1, points: 100 };
    let r = (a == b);
    assert(r);
}

fn test_rank_ne() {
    let a = Rank { tier: 1, points: 100 };
    let b = Rank { tier: 1, points: 200 };
    let r = (a == b);
    assert(!r);
}

fn test_rank_cmp() {
    let a = Rank { tier: 1, points: 100 };
    let b = Rank { tier: 2, points: 50 };
    let r = a.cmp(&b);
    assert(r == Ordering::Less);
}

fn test_rank_cmp_secondary() {
    let a = Rank { tier: 1, points: 100 };
    let b = Rank { tier: 1, points: 200 };
    let r = a.cmp(&b);
    assert(r == Ordering::Less);
}

fn test_rank_gt() {
    let a = Rank { tier: 5, points: 0 };
    let b = Rank { tier: 3, points: 999 };
    let r = a.cmp(&b);
    assert(r == Ordering::Greater);
}

fn test_pair() {
    let a = Pair(1, 5);
    let b = Pair(1, 10);
    let r = a.cmp(&b);
    assert(r == Ordering::Less);
}

fn test_rank_partial_cmp() {
    let a = Rank { tier: 1, points: 100 };
    let b = Rank { tier: 2, points: 50 };
    let r = a.partial_cmp(&b);
    assert(r == Some(Ordering::Less));
}

fn test_player_cmp() {
    let a = Player {
        rank: Rank { tier: 1, points: 100 },
        name_hash: 42,
    };
    let b = Player {
        rank: Rank { tier: 2, points: 50 },
        name_hash: 10,
    };
    let r = a.cmp(&b);
    assert(r == Ordering::Less);
}

fn test_player_eq() {
    let a = Player {
        rank: Rank { tier: 1, points: 100 },
        name_hash: 42,
    };
    let b = Player {
        rank: Rank { tier: 1, points: 100 },
        name_hash: 42,
    };
    let r = (a == b);
    assert(r);
}

}
