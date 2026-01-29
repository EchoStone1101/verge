//! Open version for closed specifications in `vstd::seq`.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::relations::*;
use crate::open::set::{SetLiteral, set_literal};

// TODO: lemmas proving that the open versions are equivalent.

verus! {

pub open spec fn sort_by<A>(s: Seq<A>, leq: spec_fn(A, A) -> bool) -> Seq<A>
    recommends
        total_ordering(leq),
    decreases
        s.len(),
{
    if s.len() == 0 {
        s 
    } else {
        let head = s.first();
        let tail = sort_by(s.drop_first(), leq);
        sort_by_insert(tail, head, leq)
    }
}

pub open spec fn sort_by_insert<A>(s: Seq<A>, a: A, leq: spec_fn(A, A) -> bool) -> Seq<A>
    recommends
        total_ordering(leq),
    decreases
        s.len(),
{
    if s.len() == 0 {
        seq![a]
    } else if leq(a, s.first()) {
        seq![a] + s
    } else {
        s.subrange(0, 1) + sort_by_insert(s.drop_first(), a, leq)
    }
}

pub open spec fn sort(s: Seq<int>) -> Seq<int>
    decreases
        s.len(),
{
    sort_by(s, |a: int, b: int| a <= b)
}

pub open spec fn index_of_first<A>(s: Seq<A>, needle: A) -> Option<int>
    decreases
        s.len(),
{
    if s.len() == 0 {
        None
    } else if s.first() == needle {
        Some(0)
    } else {
        match index_of_first(s.drop_first(), needle) {
            Some(i) => Some(1 + i),
            None => None,
        }
    }
}

pub open spec fn index_of_last<A>(s: Seq<A>, needle: A) -> Option<int>
    decreases
        s.len(),
{
    if s.len() == 0 {
        None
    } else if s.last() == needle {
        Some(s.len() - 1)
    } else {
        index_of_last(s.drop_last(), needle)
    }
}

pub open spec fn unzip<A, B>(s: Seq<(A, B)>) -> (Seq<A>, Seq<B>)
    decreases s.len()
{
    if s.len() == 0 {
        (Seq::<A>::empty(), Seq::<B>::empty())
    } else {
        let (sa, sb) = unzip(s.drop_last());
        let (a, b) = s.last();
        (sa.push(a), sb.push(b))
    }
}

pub open spec fn to_set<A>(s: Seq<A>) -> SetLiteral<A> {
    SetLiteral { set: s.to_set(), seq: s }
}

mod tests {
    use super::*;
    use verus_builtin::assert_by_compute;

    uninterp spec fn dummy(i: int) -> bool;

    proof fn test_sort_by() {
        assert_by_compute(
            {
                let leq = |a: nat, b: nat| a <= b;
                let tmp0 = sort_by(seq![2nat, 1, 3], leq);
                forall|i, j| #![trigger dummy(i), dummy(j)] 0 <= i < j < tmp0.len()
                ==> leq(tmp0[i], tmp0[j])
            }
        );
    }

    proof fn test_sort() {
        assert_by_compute(
            {
                let tmp0 = sort(seq![2int, 1, 3]);
                forall|i, j| #![trigger dummy(i), dummy(j)] 0 <= i < j < tmp0.len()
                ==> tmp0[i] <= tmp0[j]
            }
        );
    }

    proof fn test_index_of_first() {
        assert_by_compute(
            index_of_first(seq![2int, 1, 3, 1], 1) == Some(1int)
        );

        assert_by_compute(
            index_of_first(seq![2int, 1, 3, 1], 4) == None::<int>
        );
    }

    proof fn test_index_of_last() {
        assert_by_compute(
            index_of_last(seq![2int, 1, 3, 1], 1) == Some(3int)
        );

        assert_by_compute(
            index_of_last(seq![2int, 1, 3, 1], 4) == None::<int>
        );
    }

    proof fn test_unzip() {
        assert_by_compute(
            unzip::<nat, int>(seq![(1nat, 2int), (3, 4), (5, 6)]) == (seq![1nat, 3, 5], seq![2int, 4, 6])
        );
    }

    proof fn test_to_set() {
        assert(
            SetLiteral::<_>::spec_eq(to_set(seq![1nat, 1, 2, 3]), set_literal!{1nat, 2, 3})
        ); 
    }
}

} // verus!

