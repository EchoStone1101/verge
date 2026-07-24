//! Tests for function assumption proc-macros.

use verge::func::*;
use vstd::prelude::*;

verus! {

pub uninterp spec fn relation_post(x: int, y: int) -> bool;

pub open spec fn asserted_surjective_post(x: int, y: int) -> bool {
    x >= 0
}

pub open spec fn asserted_injective_post(x: int, y: int) -> bool {
    y == x + 1
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(x; y)]
pub proof fn lemma_relation(x: int, y: int)
    requires
        x >= 0,
    ensures
        #[trigger] relation_post(x, y),
{
    admit();
}

proof fn lemma_asserted_surjective_proof(x: int, y: int)
    requires
        asserted_surjective_post(x, y),
    ensures
        x >= 0,
{
}

#[verge::func::assert_surjective(crate::func::lemma_asserted_surjective_proof)]
pub proof fn lemma_asserted_surjective_relation(x: int, y: int)
    requires
        x >= 0,
    ensures
        #[trigger] asserted_surjective_post(x, y),
{
}

proof fn lemma_asserted_injective_proof(x1: int, y1: int, x2: int, y2: int)
    requires
        y1 == x1 + 1,
        asserted_injective_post(x1, y1),
        y2 == x2 + 1,
        asserted_injective_post(x2, y2),
        x1 == x2,
    ensures
        y1 == y2,
{
}

#[verge::func::assert_injective_by(crate::func::lemma_asserted_injective_proof(x; y))]
pub proof fn lemma_asserted_injective_relation(x: int, y: int)
    requires
        y == x + 1,
    ensures
        #[trigger] asserted_injective_post(x, y),
{
}

fn exec_increment(x: u64) -> (ret: u64)
    requires
        x < 10,
    ensures
        ret == x + 1,
{
    x + 1
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(x; ret)]
pub fn exec_increment_with_assumptions(x: u64) -> (ret: u64)
    requires
        x < 10,
    ensures
        ret == x + 1,
{
    x + 1
}

#[verge::func::assume_surjective]
#[verge::func::assume_injective_by(s@, offset; ret@)]
pub proof fn str_slice_relation_with_assumptions<'a>(s: &'a str, offset: int, ret: &'a str)
    requires
        0 <= offset <= s@.len(),
    ensures
        ret@ == s@.skip(offset),
{
    admit();
}

#[verge::func::assume_surjective]
pub fn exec_identity_returns_with_assumption(x: u64) -> (ret: u64)
    requires
        x < 10,
    returns
        x,
{
    x
}

pub struct MethodHost;

impl MethodHost {
    #[verge::func::assume_surjective]
    #[verge::func::assume_injective_by(self, x; ret)]
    pub fn method_with_assumptions(&self, x: u64) -> (ret: u64)
        ensures
            ret == x,
    {
        x
    }
}

pub trait MethodTrait {
    #[verge::func::assume_surjective]
    #[verge::func::assume_injective_by(self, x; ret)]
    fn trait_method_with_assumptions(&self, x: u64) -> (ret: u64)
        ensures
            ret == x;
}

proof fn test_relation_surjective(x: int, y: int)
    requires
        relation_post(x, y),
{
    lemma_relation_surjective(x, y);
    assert(x >= 0);
}

proof fn test_relation_injective(y1: int, y2: int)
    requires
        relation_post(5, y1),
        relation_post(5, y2),
{
    lemma_relation_injective(5, y1, 5, y2);
    assert(y1 == y2);
}

proof fn test_assert_surjective(x: int, y: int)
    requires
        asserted_surjective_post(x, y),
{
    __lemma_asserted_surjective_relation_surjective(x, y);
    assert(x >= 0);
}

proof fn test_assert_injective(x: int, y1: int, y2: int)
    requires
        y1 == x + 1,
        asserted_injective_post(x, y1),
        y2 == x + 1,
        asserted_injective_post(x, y2),
{
    __lemma_asserted_injective_relation_injective(x, y1, x, y2);
    assert(y1 == y2);
}

fn test_exec_surjective() {
    let ret = exec_increment(3);
    proof { exec_increment_with_assumptions_surjective(3, ret); }
    assert(3 < 10);
}

proof fn test_exec_injective() {
    exec_increment_with_assumptions_injective(4, 5, 4, 5);
    assert(5 == 5);
}

proof fn test_expression_injection<'a>(s1: &'a str, s2: &'a str, ret1: &'a str, ret2: &'a str)
    requires
        1 <= s1@.len(),
        1 <= s2@.len(),
        s1@ == s2@,
        ret1@ == s1@.skip(1),
        ret2@ == s2@.skip(1),
{
    str_slice_relation_with_assumptions_injective(s1, 1, ret1, s2, 1, ret2);
    assert(ret1@ == ret2@);
}

fn test_returns_surjective() {
    let ret = exec_identity_returns_with_assumption(2);
    proof { exec_identity_returns_with_assumption_surjective(2, ret); }
    assert(2 < 10);
}

} // verus!
