//! Utility proofs and specifications for number theory.

use super::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::relations::total_ordering;

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
        assert(x * a1 == b1 * y + 1) by { lemma_fundamental_div_mod(x * a1, b1); }
        assert(a1 * x - b1 * y == 1);
        calc!{
            (==)
            a1 * x * d - b1 * y * d; { lemma_mul_is_distributive_sub_other_way(d, a1 * x, b1 * y); }
            (a1 * x - b1 * y) * d; {}
            1 * d; { broadcast use group_mul_basics; }
            d;
        }
        calc!{
            (==)
            a1 * x * d; { lemma_mul_is_associative(a1, x, d); }
            a1 * (x * d); { lemma_mul_is_commutative(x, d); } 
            a1 * (d * x); { lemma_mul_is_associative(a1, d, x); }
            a1 * d * x; 
        }
        calc!{
            (==)
            b1 * y * d; { lemma_mul_is_associative(b1, y, d); }
            b1 * (y * d); { lemma_mul_is_commutative(y, d); } 
            b1 * (d * y); { lemma_mul_is_associative(b1, d, y); }
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

pub proof fn lemma_bezout_identity_ext1(a: nat, b: nat, m: int)
    requires
        a > 0 && b > 0,
        m % (gcd(a, b) as int) == 0,
    ensures 
        exists|x: int, y: int| 0 <= x < b / gcd(a, b) && #[trigger] (a * x + b * y) == m,
{
    let d = gcd(a, b);
    axiom_gcd_properties(a, b);
    let a1 = (a / d) as int;
    let b1 = (b / d) as int;
    let m1 = m / (d as int);
    assert(a == d * a1 + 0) by { lemma_fundamental_div_mod(a as int, d as int); }
    assert(b == d * b1 + 0) by { lemma_fundamental_div_mod(b as int, d as int); }
    assert(m == d * m1 + 0) by { lemma_fundamental_div_mod(m as int, d as int); }

    lemma_bezout_identity(a, b, d);
    let (x0, y0) = choose|x: int, y: int| 0 <= x < b / d && #[trigger] (a * x + b * y) == d;

    let q = (x0 * m1) / b1;
    let r = (x0 * m1) % b1;
    assert(x0 * m1 == b1 * q + r) by { lemma_fundamental_div_mod(x0 * m1, b1); }

    calc!{
        (==)
        m; {}
        d * m1; {}
        (a * x0 + b * y0) * m1; { lemma_mul_is_distributive_add_other_way(m1, a * x0, b * y0); }
        a * x0 * m1 + b * y0 * m1; { lemma_mul_is_associative(a as int, x0, m1); }
        a * (x0 * m1) + b * y0 * m1; {}
        a * (b1 * q + r) + b * y0 * m1; { lemma_mul_is_distributive_add(a as int, b1 * q, r); }
        a * (b1 * q) + a * r + b * y0 * m1; {}
        a * r + a * (b1 * q) + b * y0 * m1; {}
        a * r + d * a1 * (b1 * q) + b * y0 * m1; {
            calc!{
                (==)
                d * a1 * (b1 * q); { lemma_mul_is_commutative(d as int, a1); }
                a1 * d * (b1 * q); { lemma_mul_is_associative(a1, d as int, b1 * q); }
                a1 * (d * (b1 * q)); { lemma_mul_is_associative(d as int, b1, q); }
                a1 * (d * b1 * q); { assert(b == d * b1); }
                a1 * (b * q); { lemma_mul_is_commutative(a1, b as int); }
                b * q * a1; { lemma_mul_is_associative(b as int, q, a1); }
                b * (q * a1); { lemma_mul_is_commutative(q, a1); }
                b * (a1 * q);
            }
            assert(b * y0 * m1 == b * (y0 * m1)) by { lemma_mul_is_associative(b as int, y0, m1); }
        }
        a * r + b * (a1 * q) + b * (y0 * m1); { lemma_mul_is_distributive_add(b as int, a1 * q, y0 * m1); }
        a * r + b * (a1 * q + y0 * m1);
    }
    assert(0 <= r < b / gcd(a, b)) by { lemma_mod_bound(x0 * m1, b1); }
}

pub proof fn lemma_bezout_identity_ext2(a: nat, b: nat, m: int)
    requires
        a > 0 && b > 0,
        m % (gcd(a, b) as int) == 0,
    ensures 
        !exists|x1: int, y1: int, x2: int, y2: int| 
            0 <= x1 < x2 < b / gcd(a, b)
            && #[trigger] (a * x1 + b * y1) == m
            && #[trigger] (a * x2 + b * y2) == m,
{
    let d = gcd(a, b);
    axiom_gcd_properties(a, b);
    let a1 = (a / d) as int;
    let b1 = (b / d) as int;
    let m1 = m / (d as int);
    assert(a == d * a1 + 0) by { broadcast use lemma_fundamental_div_mod; }
    assert(b == d * b1 + 0) by { broadcast use lemma_fundamental_div_mod; }
    assert(m == d * m1 + 0) by { broadcast use lemma_fundamental_div_mod; }
    assert(is_coprime(b1 as nat, a1 as nat)) by {
        lemma_gcd_div(a, b, d);
        assert(gcd(a1 as nat, b1 as nat) == 1);
        axiom_coprime_gcd(a1 as nat, b1 as nat);
        axiom_is_coprime(a1 as nat, b1 as nat);
    }

    assert_by_contradiction!(!exists|x1: int, y1: int, x2: int, y2: int| 
        0 <= x1 < x2 < b / d
        && #[trigger] (a * x1 + b * y1) == m
        && #[trigger] (a * x2 + b * y2) == m,
    {
        let (x1, y1, x2, y2) = choose|x1: int, y1: int, x2: int, y2: int| 
            0 <= x1 < x2 < b / d
            && #[trigger] (a * x1 + b * y1) == m
            && #[trigger] (a * x2 + b * y2) == m;
        assert(1 <= x2 - x1 < b1);

        let d = d as int;
        calc!{
            (==)
            m1; {}
            m / d; {}
            (a * x1 + b * y1) / d; {}
            (d * a1 * x1 + d * b1 * y1) / d; {
                lemma_mul_is_associative(d, a1, x1);
                lemma_mul_is_associative(d, b1, y1);
            }
            (d * (a1 * x1) + d * (b1 * y1)) / d; {
                lemma_mul_is_distributive_add(d, a1 * x1, b1 * y1);
            }
            d * (a1 * x1 + b1 * y1) / d; {
                lemma_div_multiples_vanish(a1 * x1 + b1 * y1, d);
            }
            a1 * x1 + b1 * y1;
        }
        calc!{
            (==)
            m1; {}
            m / d; {}
            (a * x2 + b * y2) / d; {}
            (d * a1 * x2 + d * b1 * y2) / d; {
                lemma_mul_is_associative(d, a1, x2);
                lemma_mul_is_associative(d, b1, y2);
            }
            (d * (a1 * x2) + d * (b1 * y2)) / d; {
                lemma_mul_is_distributive_add(d, a1 * x2, b1 * y2);
            }
            d * (a1 * x2 + b1 * y2) / d; {
                lemma_div_multiples_vanish(a1 * x2 + b1 * y2, d);
            }
            a1 * x2 + b1 * y2;
        }
        calc!{
            (==)
            a1 * (x2 - x1); { lemma_mul_is_distributive_sub(a1, x2, x1); }
            a1 * x2 - a1 * x1; {}
            (m1 - b1 * y2) - (m1 - b1 * y1); {}
            b1 * y1 - b1 * y2; { lemma_mul_is_distributive_sub(b1, y1, y2); }
            b1 * (y1 - y2); { broadcast use lemma_mul_is_commutative; }
            (y1 - y2) * b1;
        }
 
        assert(is_factor_of((a1 * (x2 - x1)) as nat, b1 as nat)) by {
            lemma_mod_multiples_basic(y1 - y2, b1);
        }
        assert(is_factor_of((x2 - x1) as nat, b1 as nat)) by {
            lemma_coprime_factor(b1 as nat, a1 as nat, (x2 - x1) as nat);
        }
        lemma_is_factor_bound((x2 - x1) as nat, b1 as nat);
    });
}

} // verus!