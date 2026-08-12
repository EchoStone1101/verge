//! Tests for function assumption proc-macros.

use verge::func::*;
use vstd::prelude::*;

verus! {

pub uninterp spec fn relation_pre(x: int, y: int) -> bool;
pub uninterp spec fn relation_post(x: int, y: int) -> bool;
pub uninterp spec fn relation_token(y: int) -> bool;

pub uninterp spec fn asserted_surjective_pre(x: int, y: int) -> bool;
pub uninterp spec fn asserted_surjective_post(x: int, y: int) -> bool;

pub uninterp spec fn asserted_injective_pre(x: int, y: int) -> bool;
pub uninterp spec fn asserted_injective_post(x: int, y: int) -> bool;
pub uninterp spec fn asserted_injective_token(y: int) -> bool;

pub uninterp spec fn exec_increment_pre(x: u64) -> bool;
pub uninterp spec fn exec_increment_post(x: u64, ret: u64) -> bool;
pub uninterp spec fn exec_increment_token(ret: u64) -> bool;

pub uninterp spec fn slice_pre(s: Seq<char>, offset: int) -> bool;
pub uninterp spec fn slice_post(s: Seq<char>, offset: int, ret: Seq<char>) -> bool;
pub uninterp spec fn slice_token(ret: Seq<char>) -> bool;

pub uninterp spec fn identity_pre(x: u64) -> bool;

pub proof fn lemma_relation_surjective(x: int, y: int)
    requires
        relation_post(x, y),
    ensures
        relation_pre(x, y),
{
    admit();
}

pub proof fn lemma_relation_injective(x1: int, y1: int, x2: int, y2: int)
    requires
        relation_pre(x1, y1),
        relation_post(x1, y1),
        relation_pre(x2, y2),
        relation_post(x2, y2),
        x1 == x2,
    ensures
        relation_token(y1) == relation_token(y2),
{
    admit();
}

#[verge::func::assume_surjective(crate::func::lemma_relation_surjective)]
#[verge::func::assume_injective_by(crate::func::lemma_relation_injective(x; relation_token(y)))]
pub proof fn lemma_relation(x: int, y: int)
    requires
        relation_pre(x, y),
    ensures
        #[trigger] relation_post(x, y),
{
    admit();
}

proof fn lemma_asserted_surjective_proof(x: int, y: int)
    requires
        asserted_surjective_post(x, y),
    ensures
        asserted_surjective_pre(x, y),
{
    admit();
}

#[verge::func::assert_surjective(crate::func::lemma_asserted_surjective_proof)]
pub proof fn lemma_asserted_surjective_relation(x: int, y: int)
    requires
        asserted_surjective_pre(x, y),
    ensures
        #[trigger] asserted_surjective_post(x, y),
{
    admit();
}

proof fn lemma_asserted_injective_proof(x1: int, y1: int, x2: int, y2: int)
    requires
        asserted_injective_pre(x1, y1),
        asserted_injective_post(x1, y1),
        asserted_injective_pre(x2, y2),
        asserted_injective_post(x2, y2),
        x1 == x2,
    ensures
        asserted_injective_token(y1) == asserted_injective_token(y2),
{
    admit();
}

#[verge::func::assert_injective_by(crate::func::lemma_asserted_injective_proof(x; asserted_injective_token(y)))]
pub proof fn lemma_asserted_injective_relation(x: int, y: int)
    requires
        asserted_injective_pre(x, y),
    ensures
        #[trigger] asserted_injective_post(x, y),
{
    admit();
}

fn exec_increment(x: u64) -> (ret: u64)
    requires
        x < 10,
    ensures
        ret == x + 1,
{
    x + 1
}

pub proof fn exec_increment_with_assumptions_surjective(x: u64, ret: u64)
    requires
        ret == x + 1,
        exec_increment_post(x, ret),
    ensures
        x < 10,
        exec_increment_pre(x),
{
    admit();
}

pub proof fn exec_increment_with_assumptions_injective(
    x1: u64,
    ret1: u64,
    x2: u64,
    ret2: u64,
)
    requires
        x1 < 10,
        exec_increment_pre(x1),
        ret1 == x1 + 1,
        exec_increment_post(x1, ret1),
        x2 < 10,
        exec_increment_pre(x2),
        ret2 == x2 + 1,
        exec_increment_post(x2, ret2),
        x1 == x2,
    ensures
        exec_increment_token(ret1) == exec_increment_token(ret2),
{
    admit();
}

#[verge::func::assume_surjective(crate::func::exec_increment_with_assumptions_surjective)]
#[verge::func::assume_injective_by(crate::func::exec_increment_with_assumptions_injective(x; exec_increment_token(ret)))]
pub fn exec_increment_with_assumptions(x: u64) -> (ret: u64)
    requires
        x < 10,
        exec_increment_pre(x),
    ensures
        ret == x + 1,
        exec_increment_post(x, ret),
{
    proof { admit(); }
    x + 1
}

pub proof fn str_slice_relation_with_assumptions_surjective<'a>(
    s: &'a str,
    offset: int,
    ret: &'a str,
)
    requires
        ret@ == s@.skip(offset),
        slice_post(s@, offset, ret@),
    ensures
        0 <= offset <= s@.len(),
        slice_pre(s@, offset),
{
    admit();
}

pub proof fn str_slice_relation_with_assumptions_injective<'a>(
    s1: &'a str,
    offset1: int,
    ret1: &'a str,
    s2: &'a str,
    offset2: int,
    ret2: &'a str,
)
    requires
        0 <= offset1 <= s1@.len(),
        slice_pre(s1@, offset1),
        ret1@ == s1@.skip(offset1),
        slice_post(s1@, offset1, ret1@),
        0 <= offset2 <= s2@.len(),
        slice_pre(s2@, offset2),
        ret2@ == s2@.skip(offset2),
        slice_post(s2@, offset2, ret2@),
        s1@ == s2@,
        offset1 == offset2,
    ensures
        slice_token(ret1@) == slice_token(ret2@),
{
    admit();
}

#[verge::func::assume_surjective(crate::func::str_slice_relation_with_assumptions_surjective)]
#[verge::func::assume_injective_by(crate::func::str_slice_relation_with_assumptions_injective(s@, offset; slice_token(ret@)))]
pub proof fn str_slice_relation_with_assumptions<'a>(s: &'a str, offset: int, ret: &'a str)
    requires
        0 <= offset <= s@.len(),
        slice_pre(s@, offset),
    ensures
        ret@ == s@.skip(offset),
        #[trigger] slice_post(s@, offset, ret@),
{
    admit();
}

pub proof fn exec_identity_returns_with_assumption_surjective(x: u64, ret: u64)
    requires
        spec_eq(ret, x),
    ensures
        identity_pre(x),
{
    admit();
}

#[verge::func::assume_surjective(crate::func::exec_identity_returns_with_assumption_surjective)]
pub fn exec_identity_returns_with_assumption(x: u64) -> (ret: u64)
    requires
        identity_pre(x),
    returns
        x,
{
    x
}

pub struct MethodHost;

pub uninterp spec fn method_pre(this: &MethodHost, x: u64) -> bool;
pub uninterp spec fn method_post(this: &MethodHost, x: u64, ret: u64) -> bool;
pub uninterp spec fn method_token(ret: u64) -> bool;

pub uninterp spec fn trait_method_pre<T>(this: &T, x: u64) -> bool;
pub uninterp spec fn trait_method_post<T>(this: &T, x: u64, ret: u64) -> bool;
pub uninterp spec fn trait_method_token(ret: u64) -> bool;

pub proof fn method_with_assumptions_surjective(this: &MethodHost, x: u64, ret: u64)
    requires
        ret == x,
        method_post(this, x, ret),
    ensures
        method_pre(this, x),
{
    admit();
}

pub proof fn method_with_assumptions_injective(
    this1: &MethodHost,
    x1: u64,
    ret1: u64,
    this2: &MethodHost,
    x2: u64,
    ret2: u64,
)
    requires
        method_pre(this1, x1),
        ret1 == x1,
        method_post(this1, x1, ret1),
        method_pre(this2, x2),
        ret2 == x2,
        method_post(this2, x2, ret2),
        this1 == this2,
        x1 == x2,
    ensures
        method_token(ret1) == method_token(ret2),
{
    admit();
}

pub proof fn trait_method_with_assumptions_surjective<T>(this: &T, x: u64, ret: u64)
    requires
        ret == x,
        trait_method_post(this, x, ret),
    ensures
        trait_method_pre(this, x),
{
    admit();
}

pub proof fn trait_method_with_assumptions_injective<T>(
    this1: &T,
    x1: u64,
    ret1: u64,
    this2: &T,
    x2: u64,
    ret2: u64,
)
    requires
        trait_method_pre(this1, x1),
        ret1 == x1,
        trait_method_post(this1, x1, ret1),
        trait_method_pre(this2, x2),
        ret2 == x2,
        trait_method_post(this2, x2, ret2),
        this1 == this2,
        x1 == x2,
    ensures
        trait_method_token(ret1) == trait_method_token(ret2),
{
    admit();
}

impl MethodHost {
    #[verge::func::assume_surjective(crate::func::method_with_assumptions_surjective)]
    #[verge::func::assume_injective_by(crate::func::method_with_assumptions_injective(self, x; method_token(ret)))]
    pub fn method_with_assumptions(&self, x: u64) -> (ret: u64)
        requires
            method_pre(self, x),
        ensures
            ret == x,
            method_post(self, x, ret),
    {
        proof { admit(); }
        x
    }
}

pub trait MethodTrait: Sized {
    #[verge::func::assume_surjective(crate::func::trait_method_with_assumptions_surjective)]
    #[verge::func::assume_injective_by(crate::func::trait_method_with_assumptions_injective(self, x; trait_method_token(ret)))]
    fn trait_method_with_assumptions(&self, x: u64) -> (ret: u64)
        requires
            trait_method_pre(self, x),
        ensures
            ret == x,
            trait_method_post(self, x, ret);
}

impl MethodTrait for MethodHost {
    fn trait_method_with_assumptions(&self, x: u64) -> (ret: u64)
        ensures
            ret == x,
            trait_method_post(self, x, ret),
    {
        proof { admit(); }
        x
    }
}

proof fn test_relation_surjective(x: int, y: int)
    requires
        relation_post(x, y),
{
    lemma_relation_surjective(x, y);
    assert(relation_pre(x, y));
}

proof fn test_relation_injective(y1: int, y2: int)
    requires
        relation_pre(5, y1),
        relation_post(5, y1),
        relation_pre(5, y2),
        relation_post(5, y2),
        relation_token(y1),
{
    lemma_relation_injective(5, y1, 5, y2);
    assert(relation_token(y2));
}

proof fn test_assert_surjective(x: int, y: int)
    requires
        asserted_surjective_post(x, y),
{
    lemma_asserted_surjective_proof(x, y);
    assert(asserted_surjective_pre(x, y));
}

proof fn test_assert_injective(x: int, y1: int, y2: int)
    requires
        asserted_injective_pre(x, y1),
        asserted_injective_post(x, y1),
        asserted_injective_pre(x, y2),
        asserted_injective_post(x, y2),
        asserted_injective_token(y1),
{
    lemma_asserted_injective_proof(x, y1, x, y2);
    assert(asserted_injective_token(y2));
}

proof fn test_exec_surjective(x: u64, ret: u64)
    requires
        ret == x + 1,
        exec_increment_post(x, ret),
{
    exec_increment_with_assumptions_surjective(x, ret);
    assert(exec_increment_pre(x));
}

proof fn test_exec_injective(x: u64, ret1: u64, ret2: u64)
    requires
        x < 10,
        exec_increment_pre(x),
        ret1 == x + 1,
        exec_increment_post(x, ret1),
        ret2 == x + 1,
        exec_increment_post(x, ret2),
        exec_increment_token(ret1),
{
    exec_increment_with_assumptions_injective(x, ret1, x, ret2);
    assert(exec_increment_token(ret2));
}

proof fn test_expression_injection<'a>(s1: &'a str, s2: &'a str, ret1: &'a str, ret2: &'a str)
    requires
        1 <= s1@.len(),
        1 <= s2@.len(),
        slice_pre(s1@, 1),
        slice_pre(s2@, 1),
        s1@ == s2@,
        ret1@ == s1@.skip(1),
        slice_post(s1@, 1, ret1@),
        ret2@ == s2@.skip(1),
        slice_post(s2@, 1, ret2@),
        slice_token(ret1@),
{
    str_slice_relation_with_assumptions_injective(s1, 1, ret1, s2, 1, ret2);
    assert(slice_token(ret2@));
}

proof fn test_expression_surjective<'a>(s: &'a str, ret: &'a str)
    requires
        ret@ == s@.skip(1),
        slice_post(s@, 1, ret@),
{
    str_slice_relation_with_assumptions_surjective(s, 1, ret);
    assert(slice_pre(s@, 1));
}

proof fn test_returns_surjective(x: u64, ret: u64)
    requires
        ret == x,
{
    exec_identity_returns_with_assumption_surjective(x, ret);
    assert(identity_pre(x));
}

proof fn test_method_assumption_surjective(host: &MethodHost)
    requires
        method_post(host, 3, 3),
{
    method_with_assumptions_surjective(host, 3, 3);
    assert(method_pre(host, 3));
}

proof fn test_method_assumption_injective(host: &MethodHost, ret1: u64, ret2: u64)
    requires
        method_pre(host, 3),
        ret1 == 3,
        method_post(host, 3, ret1),
        ret2 == 3,
        method_post(host, 3, ret2),
        method_token(ret1),
{
    method_with_assumptions_injective(host, 3, ret1, host, 3, ret2);
    assert(method_token(ret2));
}

proof fn test_trait_method_assumption_surjective(host: &MethodHost)
    requires
        trait_method_post(host, 4, 4),
{
    trait_method_with_assumptions_surjective(host, 4, 4);
    assert(trait_method_pre(host, 4));
}

proof fn test_trait_method_assumption_injective(host: &MethodHost, ret1: u64, ret2: u64)
    requires
        trait_method_pre(host, 4),
        ret1 == 4,
        trait_method_post(host, 4, ret1),
        ret2 == 4,
        trait_method_post(host, 4, ret2),
        trait_method_token(ret1),
{
    trait_method_with_assumptions_injective(host, 4, ret1, host, 4, ret2);
    assert(trait_method_token(ret2));
}

} // verus!
