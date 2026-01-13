//! Definitions and lemmas for the Cartesian product of sets in Verus.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::arithmetic::mul::*;
use vstd::set::fold::*;
use vstd::set_lib::*;
use vstd::seq_lib::*;
use vstd::{assert_by_contradiction, calc};
use vstd::relations::injective_on;

verus! {

/// This function defines the Cartesian product of sets `a` and `b`.
pub open spec fn cart<A, B>(a: Set<A>, b: Set<B>) -> Set<(A, B)> {
    Set::<(A, B)>::new(|p: (A, B)| a.contains(p.0) && b.contains(p.1))
}

/// This function defines the left projection of a Cartesian product.
/// It is only meaningful when `s` is a Cartesian product.
closed spec fn proj_left<A, B>(s: Set<(A, B)>) -> Set<A> {
    s.map(|p: (A, B)| p.0)
}

/// This function defines the right projection of a Cartesian product.
/// It is only meaningful when `s` is a Cartesian product.
closed spec fn proj_right<A, B>(s: Set<(A, B)>) -> Set<B> {
    s.map(|p: (A, B)| p.1)
}

/// Proof that the left projection of `a x b` is `a` if `b` is not empty.
proof fn axiom_proj_left<A, B>(a: Set<A>, b: Set<B>)
    requires !b.is_empty(),
    ensures proj_left(cart(a, b)) == a,
{
    assert_sets_equal!(proj_left(cart(a, b)) == a, a0 => {
        if a.contains(a0) {
            let b0 = b.choose();
            assert(proj_left(cart(a, b)).contains(a0)) by {
                assert(cart(a, b).contains((a0, b0)));
            }
        }
        if proj_left(cart(a, b)).contains(a0) {
            let p = choose|p: (A, B)| #[trigger] cart(a, b).contains(p) && a0 == p.0;
            assert(a.contains(a0));
        }
    });
}

/// Proof that the right projection of `a x b` is `b` if `a` is not empty.
proof fn axiom_proj_right<A, B>(a: Set<A>, b: Set<B>)
    requires !a.is_empty(),
    ensures proj_right(cart(a, b)) == b,
{
    assert_sets_equal!(proj_right(cart(a, b)) == b, b0 => {
        if b.contains(b0) {
            let a0 = a.choose();
            assert(proj_right(cart(a, b)).contains(b0)) by {
                assert(cart(a, b).contains((a0, b0)));
            }
        }
        if proj_right(cart(a, b)).contains(b0) {
            let p = choose|p: (A, B)| #[trigger] cart(a, b).contains(p) && b0 == p.1;
            assert(b.contains(b0));
        }
    });
}

/// Proof that `a x b` is empty iff `a` is empty or `b` is empty.
pub proof fn lemma_cart_empty<A, B>(a: Set<A>, b: Set<B>) 
    ensures cart(a, b).is_empty() <==> a.is_empty() || b.is_empty()
{
    // ..the other way is trivial
    if cart(a, b).is_empty() {
        assert_by_contradiction!(a.is_empty() || b.is_empty(), {
            let a0 = a.choose();
            let b0 = b.choose();
            assert(cart(a, b).contains((a0, b0)));
        });
    }
}

/// Proof that (for non-empty sets) `a1 x b1 == a2 x b2` iff `a1 == a2` and `b1 == b2`.
pub proof fn lemma_cart_equality<A, B>(a1: Set<A>, b1: Set<B>, a2: Set<A>, b2: Set<B>)
    ensures 
        a1 == a2 && b1 == b2 ==> cart(a1, b1) == cart(a2, b2),
        !a1.is_empty() && !b1.is_empty() && !a2.is_empty() && !b2.is_empty()
            && cart(a1, b1) == cart(a2, b2) ==> a1 == a2 && b1 == b2,
{
    // ..the other way is trivial
    if !a1.is_empty() && !b1.is_empty() && !a2.is_empty() && !b2.is_empty() 
        && cart(a1, b1) == cart(a2, b2) 
    {
        assert(a1 == a2) by {
            axiom_proj_left(a1, b1);
            axiom_proj_left(a2, b2);
        }
        assert(b1 == b2) by {
            axiom_proj_right(a1, b1);
            axiom_proj_right(a2, b2);
        }
    }
}

/// Proof that (for non-empty sets) `a1 x b1 <= a2 x b2` iff `a1 <= a2` and `b1 <= b2`.
pub proof fn lemma_cart_subset<A, B>(a1: Set<A>, b1: Set<B>, a2: Set<A>, b2: Set<B>)
    ensures 
        a1.subset_of(a2) && b1.subset_of(b2) ==> cart(a1, b1).subset_of(cart(a2, b2)),
        !a1.is_empty() && !b1.is_empty() && !a2.is_empty() && !b2.is_empty() 
            && cart(a1, b1).subset_of(cart(a2, b2)) ==> a1.subset_of(a2) && b1.subset_of(b2),
{
    if a1.subset_of(a2) && b1.subset_of(b2) {
        assert forall|p: (A, B)| cart(a1, b1).contains(p)
        implies cart(a2, b2).contains(p) 
        by {
            assert(a2.contains(p.0) && b2.contains(p.1));
        }
    }
    if !a1.is_empty() && !b1.is_empty() && !a2.is_empty() && !b2.is_empty() 
        && cart(a1, b1).subset_of(cart(a2, b2))
    {
        assert(!cart(a1, b1).is_empty()) by { lemma_cart_empty(a1, b1); }
        assert forall|a0: A| a1.contains(a0) 
        implies a2.contains(a0)
        by {
            let p = cart(a1, b1).choose();
            let b0 = p.1;
            assert(b2.contains(b0)) by { assert(cart(a2, b2).contains(p)); }
            assert(a2.contains(a0)) by {
                assert(cart(a1, b1).contains((a0, b0)));
                assert(cart(a2, b2).contains((a0, b0)));
            }
        }
        assert forall|b0: B| b1.contains(b0) 
        implies b2.contains(b0)
        by {
            let p = cart(a1, b1).choose();
            let a0 = p.0;
            assert(a2.contains(a0)) by { assert(cart(a2, b2).contains(p)); }
            assert(b2.contains(b0)) by {
                assert(cart(a1, b1).contains((a0, b0)));
                assert(cart(a2, b2).contains((a0, b0)));
            }
        }
    }
}

/// Proof that `(a1 x b1) * (a2 x b2)` is equal to `(a1 * a2) x (b1 * b2)`.
pub proof fn lemma_cart_intersect<A, B>(a1: Set<A>, b1: Set<B>, a2: Set<A>, b2: Set<B>)
    ensures cart(a1, b1) * cart(a2, b2) == cart(a1 * a2, b1 * b2)
{
    assert_sets_equal!(cart(a1, b1) * cart(a2, b2) == cart(a1 * a2, b1 * b2), p => {
        if (cart(a1, b1) * cart(a2, b2)).contains(p) {
            assert((a1 * a2).contains(p.0));
            assert((b1 * b2).contains(p.1));
            assert(cart(a1 * a2, b1 * b2).contains(p));
        }
        if cart(a1 * a2, b1 * b2).contains(p) {
            assert(a1.contains(p.0) && b1.contains(p.1));
            assert(a2.contains(p.0) && b2.contains(p.1));
        }
    });
}

/// Proof that for sets `a1`, `a2`, and `b`, `a1 x b + a2 x b` is equal to
/// `(a1 + a2) x b`.
pub proof fn lemma_cart_union_left<A, B>(a1: Set<A>, a2: Set<A>, b: Set<B>)
    ensures cart(a1, b) + cart(a2, b) == cart(a1 + a2, b)
{
    assert_sets_equal!(cart(a1, b) + cart(a2, b) == cart(a1 + a2, b), p => {
        if (cart(a1, b) + cart(a2, b)).contains(p) {
            assert(b.contains(p.1));
            assert((a1 + a2).contains(p.0));
            assert(cart(a1 + a2, b).contains(p));
        }
        if cart(a1 + a2, b).contains(p) {
            assert(b.contains(p.1));
            assert(a1.contains(p.0) || a2.contains(p.0));
        }
    });
}

/// Proof that for sets `a`, `b1`, and `b2`, `a x b1 + a x b2` is equal to
/// `a x (b1 + b2)`.
pub proof fn lemma_cart_union_right<A, B>(a: Set<A>, b1: Set<B>, b2: Set<B>)
    ensures cart(a, b1) + cart(a, b2) == cart(a, b1 + b2)
{
    assert_sets_equal!(cart(a, b1) + cart(a, b2) == cart(a, b1 + b2), p => {
        if (cart(a, b1) + cart(a, b2)).contains(p) {
            assert(a.contains(p.0));
            assert((b1 + b2).contains(p.1));
            assert(cart(a, b1 + b2).contains(p));
        }
        if cart(a, b1 + b2).contains(p) {
            assert(a.contains(p.0));
            assert(b1.contains(p.1) || b2.contains(p.1));
        }
    });
}

/// Proof that for sets `a1`, `a2`, and `b`, `a1 x b - a2 x b` is equal to
/// `(a1 - a2) x b`.
pub proof fn lemma_cart_difference_left<A, B>(a1: Set<A>, a2: Set<A>, b: Set<B>)
    ensures cart(a1, b) - cart(a2, b) == cart(a1 - a2, b)
{
    assert_sets_equal!(cart(a1, b) - cart(a2, b) == cart(a1 - a2, b), p => {
        if (cart(a1, b) - cart(a2, b)).contains(p) {
            assert(b.contains(p.1));
            assert((a1 - a2).contains(p.0));
            assert(cart(a1 - a2, b).contains(p));
        }
        if cart(a1 - a2, b).contains(p) {
            assert(b.contains(p.1));
            assert(a1.contains(p.0) && !a2.contains(p.0));
        }
    });
}

/// Proof that for sets `a`, `b1`, and `b2`, `a x b1 - a x b2` is equal to
/// `a x (b1 - b2)`.
pub proof fn lemma_cart_difference_right<A, B>(a: Set<A>, b1: Set<B>, b2: Set<B>)
    ensures cart(a, b1) - cart(a, b2) == cart(a, b1 - b2)
{
    assert_sets_equal!(cart(a, b1) - cart(a, b2) == cart(a, b1 - b2), p => {
        if (cart(a, b1) - cart(a, b2)).contains(p) {
            assert(a.contains(p.0));
            assert((b1 - b2).contains(p.1));
            assert(cart(a, b1 - b2).contains(p));
        }
        if cart(a, b1 - b2).contains(p) {
            assert(a.contains(p.0));
            assert(b1.contains(p.1) && !b2.contains(p.1));
        }
    });
}

/// Proof that the Cartesian product of sets `a` and `b` is finite if 
/// `a` and `b` are both finite, and that its size is `a.len() * b.len()`. 
pub broadcast proof fn lemma_cart_len<A, B>(a: Set<A>, b: Set<B>)
    requires
        a.finite() && b.finite(),
    ensures
        #[trigger] cart(a, b).finite(),
        #[trigger] cart(a, b).len() == a.len() * b.len(),
    decreases a.len(),
{
    let ab = cart(a, b);
    if a.is_empty() {
        assert(forall|p: (A, B)| !ab.contains(p));
        assert(ab.is_empty());
        assert(ab.len() == 0);
        assert(a.len() * b.len() == 0) by { broadcast use group_mul_basics; }
    } else {
        let ha = a.choose();
        let ta = a.remove(ha);
        assert(ab == cart(ta, b) + cart(set!{ha}, b)) by {
            lemma_cart_union_left(ta, set!{ha}, b);
        }
        calc!{
            (==)
            cart(ta, b) * cart(set!{ha}, b); { lemma_cart_intersect(ta, b, set!{ha}, b); }
            cart(ta * set!{ha}, b * b); {}
            cart(Set::<A>::empty(), b); { lemma_cart_empty(Set::<A>::empty(), b); }
            Set::<(A, B)>::empty();
        }

        // ..new
        assert(cart(set!{ha}, b).finite() && cart(set!{ha}, b).len() == b.len()) by {
            let dom = b;
            let img = cart(set!{ha}, b);
            let f = |b0: B| (ha, b0);
            assert(injective_on(f, dom));
            assert_sets_equal!(dom.map(f) == img, p => {
                if dom.map(f).contains(p) {
                    assert(p.0 == ha);
                    let b0 = choose|b0: B| dom.contains(b0) && p == f(b0);
                    assert(p.1 == b0);
                    assert(img.contains(p));
                }
                if img.contains(p) {
                    assert(p.0 == ha);
                    assert(dom.contains(p.1));
                    assert(p == f(p.1));
                    assert(dom.map(f).contains(p));
                }
            });
            lemma_map_size(dom, img, f);
        }; 

        // ..induct
        lemma_cart_len(ta, b);
        assert(ab.finite());
        calc!{
            (==)
            ab.len(); { lemma_set_intersect_union_lens(cart(ta, b), cart(set!{ha}, b)); }
            (cart(ta, b).len() + cart(set!{ha}, b).len() - (cart(ta, b) * cart(set!{ha}, b)).len()) as nat; {}
            cart(ta, b).len() + b.len(); {}
            (a.len() - 1) as nat * b.len() + b.len(); { broadcast use group_mul_basics; }
            (a.len() - 1) as nat * b.len() + 1 * b.len(); { 
                lemma_mul_is_distributive_add_other_way(b.len() as int, (a.len() - 1) as int, 1);
            }
            a.len() * b.len();
        }
    }
}

} // verus!