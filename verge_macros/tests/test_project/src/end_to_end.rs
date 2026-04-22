//! End-to-end test: manual trait impls for a custom type with a "cached" field,
//! then derived impls for a nested type using that custom type as a field.
//!
//! CachedResult: key: u32 + cached: Option<u64> (ignored by all traits).
//! Entry: result: CachedResult + priority: u32 (derived Ord).

use vstd::prelude::*;
use vstd::std_specs::cmp::*;
use vstd::pervasive::strictly_cloned;
use verge::cmp::*;
use verge::clone::*;
use core::cmp::Ordering;

verus! {

// --- CachedResult: manual impls ---

pub struct CachedResult {
    pub key: u32,
    pub cached: Option<u64>,
}

impl PartialEq for CachedResult {
    fn eq(&self, other: &Self) -> (r: bool) {
        self.key == other.key
    }
}

impl Eq for CachedResult {}

impl PartialOrd for CachedResult {
    fn partial_cmp(&self, other: &Self) -> (r: Option<Ordering>) {
        self.key.partial_cmp(&other.key)
    }
}

impl Ord for CachedResult {
    fn cmp(&self, other: &Self) -> (r: Ordering) {
        self.key.cmp(&other.key)
    }
}

impl Clone for CachedResult {
    fn clone(&self) -> (ret: CachedResult)
        ensures
            ret.key == self.key,
            ret.cached.is_none(),
    {
        CachedResult { key: self.key, cached: None }
    }
}

// Spec impls

impl PartialEqSpecImpl for CachedResult {
    open spec fn obeys_eq_spec() -> bool { true }
    open spec fn eq_spec(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl PartialOrdSpecImpl for CachedResult {
    open spec fn obeys_partial_cmp_spec() -> bool { true }
    open spec fn partial_cmp_spec(&self, other: &Self) -> Option<Ordering> {
        <u32 as PartialOrdSpec>::partial_cmp_spec(&self.key, &other.key)
    }
}

impl OrdSpecImpl for CachedResult {
    open spec fn obeys_cmp_spec() -> bool { true }
    open spec fn cmp_spec(&self, other: &Self) -> Ordering {
        <u32 as OrdSpec>::cmp_spec(&self.key, &other.key)
    }
}

// Verified proofs

impl PartialEqVerified for CachedResult {
    proof fn lemma_eq_symmetric(a: &Self, b: &Self) {}
    proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {}
}

impl EqVerified for CachedResult {
    proof fn lemma_eq_reflexive(a: &Self) {}
}

impl PartialOrdVerified for CachedResult {
    proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self) {
        <u32 as PartialOrdVerified>::lemma_cmp_eq_consistent(&a.key, &b.key);
    }
    proof fn lemma_cmp_dual(a: &Self, b: &Self) {
        <u32 as PartialOrdVerified>::lemma_cmp_dual(&a.key, &b.key);
    }
    proof fn lemma_cmp_comparable(a: &Self, b: &Self, c: &Self) {
        <u32 as PartialOrdVerified>::lemma_cmp_comparable(&a.key, &b.key, &c.key);
    }
    proof fn lemma_cmp_less_transitive(a: &Self, b: &Self, c: &Self) {
        <u32 as PartialOrdVerified>::lemma_cmp_less_transitive(&a.key, &b.key, &c.key);
    }
    proof fn lemma_cmp_greater_transitive(a: &Self, b: &Self, c: &Self) {
        <u32 as PartialOrdVerified>::lemma_cmp_greater_transitive(&a.key, &b.key, &c.key);
    }
}

impl OrdVerified for CachedResult {
    proof fn lemma_cmp_consistent(a: &Self, b: &Self) {
        <u32 as OrdVerified>::lemma_cmp_consistent(&a.key, &b.key);
    }
}

impl ClonePartialEq for CachedResult {
    proof fn lemma_clone_preserves_eq(a: &CachedResult) {
        // clone preserves key, so eq_spec (which compares only key) holds
    }
}

// --- Entry: derived Ord + Clone (composable inside verus!) ---

#[verge_macros::derive_ord]
#[verge_macros::derive_clone]
pub struct Entry {
    pub result: CachedResult,
    pub priority: u32,
}

} // verus!

verus! {

// --- Tests ---

// CachedResult tests

fn test_cached_eq() {
    let a = CachedResult { key: 42, cached: Some(100) };
    let b = CachedResult { key: 42, cached: None };
    let r = (a == b); // same key, different cached — equal
    assert(r);
}

fn test_cached_ne() {
    let a = CachedResult { key: 1, cached: None };
    let b = CachedResult { key: 2, cached: None };
    let r = (a == b);
    assert(!r);
}

fn test_cached_ord() {
    let a = CachedResult { key: 1, cached: Some(999) };
    let b = CachedResult { key: 2, cached: None };
    let r = a.cmp(&b);
    assert(r == Ordering::Less);
}

fn test_cached_clone() {
    let a = CachedResult { key: 42, cached: Some(100) };
    let b = a.clone();
    assert(b.key == 42);
    assert(b.cached.is_none());
    let r = (a == b);
    assert(r);
}

// Entry tests (derived Ord)

fn test_entry_eq() {
    let a = Entry {
        result: CachedResult { key: 1, cached: Some(10) },
        priority: 5,
    };
    let b = Entry {
        result: CachedResult { key: 1, cached: None },
        priority: 5,
    };
    let r = (a == b);
    assert(r);
}

fn test_entry_ord() {
    let a = Entry {
        result: CachedResult { key: 1, cached: None },
        priority: 5,
    };
    let b = Entry {
        result: CachedResult { key: 2, cached: None },
        priority: 3,
    };
    let r = a.cmp(&b);
    assert(r == Ordering::Less);
}

fn test_entry_ord_secondary() {
    let a = Entry {
        result: CachedResult { key: 1, cached: None },
        priority: 3,
    };
    let b = Entry {
        result: CachedResult { key: 1, cached: Some(99) },
        priority: 5,
    };
    let r = a.cmp(&b);
    assert(r == Ordering::Less);
}

// Test: Entry clone (from derive_clone, composed with derive_ord)
fn test_entry_clone() {
    let a = Entry { result: CachedResult { key: 42, cached: Some(100) }, priority: 5 };
    let b = a.clone();
    assert(Entry::strictly_cloned(&a, &b));
}

// Proof test: symmetry holds for Entry via derived PartialEqVerified
proof fn test_entry_symmetry(a: &Entry, b: &Entry) {
    Entry::lemma_eq_symmetric(a, b);
}

}
