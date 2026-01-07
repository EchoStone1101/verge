//! Utility proofs and specifications for number theory.

use super::*;
use vstd::prelude::*;

verus! {

/// Proof that `b^n > n` for `b > 1`.
pub(crate) proof fn lemma_pow_n_gt_n(b: nat, n: nat)
    requires b > 1,
    ensures pow(b as int, n) > n,
    decreases n,
{
    if n == 0 {
        lemma_pow0(b as int);
    } else {
        lemma_pow_strictly_increases(b, (n - 1) as nat, n);
        lemma_pow_n_gt_n(b, (n - 1) as nat);
    }
}

pub(crate) proof fn lemma_bezout_identity_epilogue1(a1: int, b1: int, d: int) 
    requires
        a1 > 0 && b1 > 0 && d > 0,
        set_nat_range(0, b1 as nat).map(|k: nat| ((k * a1) % b1) as nat) == set_nat_range(0, b1 as nat),
    ensures
        exists|x: int, y: int| 0 <= x < b1 && #[trigger] (a1 * d * x - b1 * d * y) == d,
{
    if b1 == 1 {
        // ..trivial
        assert(a1 * d * 0 == 0);
        assert(-(b1 * d * (-1)) == d) by (compute);
        assert(a1 * d * 0 - b1 * d * (-1) == d) by (compute);
    } else {
        let f = |k: nat| (((k * a1) % b1) as nat);
        let dom = set_nat_range(0, b1 as nat);
        let img = dom.map(f);
        assert(dom == img);
        lemma_nat_range(0, b1 as nat);
        assert(img.contains(1));

        let x: int = (choose|x: nat| dom.contains(x) && 1 == f(x)) as int;
        assert(0 <= x < b1);
        assert((x * a1) % b1 == 1);
        let y: int = (x * a1) / b1;
        assert(x * a1 == b1 * y + 1) by { broadcast use lemma_fundamental_div_mod; }
        assert(a1 * x - b1 * y == 1);
        calc!{
            (==)
            a1 * x * d - b1 * y * d; { broadcast use lemma_mul_is_distributive_sub_other_way; }
            (a1 * x - b1 * y) * d; {}
            1 * d; { broadcast use group_mul_basics; }
            d;
        }
        calc!{
            (==)
            a1 * x * d; { broadcast use lemma_mul_is_associative; }
            a1 * (x * d); { broadcast use lemma_mul_is_commutative; } 
            a1 * (d * x); { broadcast use lemma_mul_is_associative; }
            a1 * d * x; 
        }
        calc!{
            (==)
            b1 * y * d; { broadcast use lemma_mul_is_associative; }
            b1 * (y * d); { broadcast use lemma_mul_is_commutative; } 
            b1 * (d * y); { broadcast use lemma_mul_is_associative; }
            b1 * d * y; 
        }
        assert(0 <= x < b1 && (a1 * d * x - b1 * d * y) == d);
    }
}

pub(crate) proof fn lemma_bezout_identity_epilogue2(a1: int, b1: int, d: int)
    requires
        exists|x: int, y: int| 0 <= x < b1 && #[trigger] (a1 * d * x - b1 * d * y) == d,
    ensures
        exists|x: int, y: int| 0 <= x < b1 && #[trigger] (a1 * d * x + b1 * d * y) == d,
{
    // XXX: somehow lemma_mul_unary_negation blows up verification in `nt`...
    let (x, y) = choose|x: int, y: int| 0 <= x < b1 && #[trigger] (a1 * d * x - b1 * d * y) == d;
    assert(-(b1 * d * y) == b1 * d * (-y)) by { broadcast use lemma_mul_unary_negation; }
    assert(a1 * d * x + b1 * d * (-y) == d);
}

} // verus!