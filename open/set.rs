//! Open version for closed specifications in `vstd::set`.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::calc;
use vstd::pervasive::arbitrary;
use vstd::set::fold::is_fun_commutative;
use vstd::relations::total_ordering;
pub use vstd::prelude::verus_proof_macro_exprs;

verus! {

#[doc(hidden)]
#[macro_export]
macro_rules! set_literal_internal {
    [$($elem:expr),* $(,)?] => {
        $crate::open::set::SetLiteral::empty()
            $(.insert($elem))*
    };
}

#[macro_export]
macro_rules! set_literal {
    [$($tail:tt)*] => {
        $crate::open::set::verus_proof_macro_exprs!($crate::open::set::set_literal_internal!($($tail)*))
    };
}

pub use set_literal_internal;
pub use set_literal;

#[verifier::ext_equal]
#[verifier::reject_recursive_types(A)]
pub struct SetLiteral<A> {
    pub set: Set<A>,
    pub seq: Seq<A>,
}

impl<A> SetLiteral<A> {

    // #[verifier::type_invariant]
    // pub closed spec fn inv(self) -> bool 
    //     { self.seq.to_set() =~= self.set && self.seq.len() == self.set.len() }

    pub open spec fn spec_eq(s1: SetLiteral<A>, s2: SetLiteral<A>) -> bool 
        { s1.set =~= s2.set }

    pub open spec fn empty() -> SetLiteral<A>
        { SetLiteral { set: Set::<A>::empty(), seq: []@ } }

    pub open spec fn choose(self) -> A 
        { self.seq.last() }

    pub open spec fn len(self) -> nat
        { self.seq.len() }
    
    pub open spec fn finite(self) -> bool
        { self.set.finite() }
    
    pub open spec fn is_empty(self) -> bool 
        { self.set.is_empty() }

    pub open spec fn contains(self, a: A) -> bool
        { self.set.contains(a) }

    pub open spec fn spec_has(self, a: A) -> bool
        { self.contains(a) }
    
    pub open spec fn subset_of(self, s2: SetLiteral<A>) -> bool
        { self.set.subset_of(s2.set) }
    
    pub open spec fn spec_le(self, s2: SetLiteral<A>) -> bool
        { self.subset_of(s2) }

    pub open spec fn disjoint(self, s2: SetLiteral<A>) -> bool
        { forall |a: A| self.contains(a) ==> !s2.contains(a) }
    
    pub open spec fn to_seq(self) -> Seq<A> {
        self.seq
    }
    
    pub open spec fn insert(self, a: A) -> SetLiteral<A> { 
        if self.set.contains(a) { 
            self 
        } else { 
            SetLiteral {
                set: self.set.insert(a),
                seq: self.seq.push(a),
            }
        }
    }

    pub open spec fn remove(self, a: A) -> SetLiteral<A> {
        if !self.set.contains(a) { 
            self 
        } else { 
            // proof { assume(seq.contains(a)); }
            SetLiteral {
                set: self.set.remove(a),
                seq: self.seq.remove(crate::open::seq::index_of_first(self.seq, a).unwrap()),
            }
        }
    }

    pub open spec fn fold<B>(self, z: B, f: spec_fn(B, A) -> B) -> B
        recommends is_fun_commutative(f),
    {
        self.seq.fold_left(z, f)
    }

    pub open spec fn union(self, s2: SetLiteral<A>) -> SetLiteral<A> 
        { s2.fold(self, |s: SetLiteral<A>, a: A| s.insert(a)) }

    pub open spec fn spec_add(self, s2: SetLiteral<A>) -> SetLiteral<A>
        { self.union(s2) }

    pub open spec fn difference(self, s2: SetLiteral<A>) -> SetLiteral<A> 
        { s2.fold(self, |s: SetLiteral<A>, a: A| s.remove(a)) }

    pub open spec fn spec_sub(self, s2: SetLiteral<A>) -> SetLiteral<A>
        { self.difference(s2) }

    pub open spec fn intersect(self, s2: SetLiteral<A>) -> SetLiteral<A> { 
        s2.fold(
            SetLiteral::<A>::empty(), 
            |s: SetLiteral<A>, a: A| if self.contains(a) { s.insert(a) } else { s }
        )
    }
    
    pub open spec fn spec_mul(self, s2: SetLiteral<A>) -> SetLiteral<A>
        { self.intersect(s2) }

    pub open spec fn all(self, pred: spec_fn(A,) -> bool) -> bool 
        { self.fold( true, |verdict: bool, a: A| verdict && pred(a)) }

    pub open spec fn any(self, pred: spec_fn(A,) -> bool) -> bool 
        { self.fold( false, |verdict: bool, a: A| verdict || pred(a)) }

    pub open spec fn filter(self, f: spec_fn(A,) -> bool) -> SetLiteral<A> {
        self.fold(
            SetLiteral::<A>::empty(), 
            |s: SetLiteral<A>, a: A| if f(a) { s.insert(a) } else { s }
        )
    }

    pub open spec fn map<B>(self, f: spec_fn(A,) -> B) -> SetLiteral<B> { 
        self.fold(
            SetLiteral::<B>::empty(), 
            |s: SetLiteral<B>, a: A| s.insert(f(a)),
        )
    }

    pub open spec fn filter_map<B>(self, f: spec_fn(A,) -> Option<B>) -> SetLiteral<B> {
        self.fold(
            SetLiteral::<B>::empty(), 
            |s: SetLiteral<B>, a: A| match f(a) {
                Option::Some(b) => s.insert(b),
                None => s,
            },
        )
    }

    pub open spec fn find_unique_maximal(self, leq: spec_fn(A, A) -> bool) -> A
        recommends 
            total_ordering(leq),
            !self.is_empty(),
    {
        let init = self.choose();
        SetLiteral { set: self.set.remove(init), seq: self.seq.drop_last() }
            .fold(self.choose(), |maximum: A, a: A| if leq(maximum, a) { a } else { maximum }) 
    }

    pub open spec fn find_unique_minimal(self, leq: spec_fn(A, A) -> bool) -> A
        recommends 
            total_ordering(leq),
            !self.is_empty(),
    {
        let init = self.choose();
        SetLiteral { set: self.set.remove(init), seq: self.seq.drop_last() }
            .fold(self.choose(), |minimum: A, a: A| if leq(a, minimum) { a } else { minimum }) 
    }
}

impl<A> SetLiteral<SetLiteral<A>> {

    pub open spec fn flatten(self) -> SetLiteral<A> {
        self.fold(
            SetLiteral::<A>::empty(),
            |s: SetLiteral<A>, a: SetLiteral<A>| s + a,
        )
    }

}

mod tests {
    use super::*;

    proof fn test_set_literal_basics() {
        assert(set_literal!{1int, 2}.contains(1));
        assert(set_literal!{1int, 2}.insert(3).choose() == 3);
        assert(SetLiteral::<_>::spec_eq(set_literal!{1int, 2}, set_literal!{2int, 1}));
        assert(SetLiteral::<_>::spec_eq(set_literal!{1int}.insert(2), set_literal!{1int, 2}));
        assert(
            SetLiteral::<_>::spec_eq(set_literal!{1int, 2}.remove(2), set_literal!{1int})
        ); 
    }

    proof fn test_set_literal_fold() {
        assert(
            set_literal!{2int, 3}.fold(1, (|sum: int, n: int| sum + n)) == 6
        ) by { reveal_with_fuel(Seq::<_>::fold_left, 5); } // by (compute); // hangs; why?

        assert(
            SetLiteral::<_>::spec_eq(set_literal!{1int, 2} + set_literal!{2int, 3}, set_literal!{1int, 2, 3})
        ) by { reveal_with_fuel(Seq::<_>::fold_left, 5); }

        assert(
            SetLiteral::<_>::spec_eq(set_literal!{1int, 2} - set_literal!{2int, 3}, set_literal!{1int})
        ) by { reveal_with_fuel(Seq::<_>::fold_left, 5); }

        assert(
            SetLiteral::<_>::spec_eq(set_literal!{1int, 2} * set_literal!{2int, 3}, set_literal!{2int})
        ) by { reveal_with_fuel(Seq::<_>::fold_left, 5); }

        assert(
            SetLiteral::<_>::spec_eq(
                set_literal!{1int} + set_literal!{2int} + set_literal!{3int} + set_literal!{4int},
                set_literal!{4int, 3, 2, 1}
            )
        ) by { reveal_with_fuel(Seq::<_>::fold_left, 5); }

        assert(
            set_literal!{1int, 2, 3}.all(|x: int| x > 0)
        ) by { reveal_with_fuel(Seq::<_>::fold_left, 5); }

        assert(
            !set_literal!{1int, 2, 3}.any(|x: int| x < 0)
        ) by { reveal_with_fuel(Seq::<_>::fold_left, 5); }

        assert(
            SetLiteral::<_>::spec_eq(
                set_literal!{1int, 2, 3}.filter(|x: int| x > 1),
                set_literal!{1int, 2}.map(|x: int| x + 1)
            )
        ) by { reveal_with_fuel(Seq::<_>::fold_left, 5); }

        assert(
            set_literal!{1int, 9, 2, 6, 0, 8, 1, 7}.find_unique_maximal(|a: int, b: int| a <= b) == 9
        ) by { reveal_with_fuel(Seq::<_>::fold_left, 10); }

        assert(
            set_literal!{1int, 9, 2, 6, 0, 8, 1, 7}.find_unique_minimal(|a: int, b: int| a <= b) == 0
        ) by { reveal_with_fuel(Seq::<_>::fold_left, 10); }

        assert(
            SetLiteral::<_>::spec_eq(
                set_literal!{set_literal!{1int, 2}, set_literal!{2int, 3}}.flatten(),
                set_literal!{1int, 2, 3},
            ) 
        ) by { reveal_with_fuel(Seq::<_>::fold_left, 10); }
    }
}

} // verus!