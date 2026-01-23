//! Proofs and specifications for `gcd`-related properties.
//! Also contains lemmas about the [Euclidean method](https://en.wikipedia.org/wiki/Euclidean_algorithm).

use super::{
    set_nat_range, is_factor_of, is_common_factor, is_coprime,
    lemma_is_factor_bound, lemma_is_factor_transitive, 
    lemma_nat_range, lemma_is_factor_lincomb, lemma_is_factor_lincomb2, 
    lemma_is_factor_multiples, lemma_coprime_factor,
};
use vstd::prelude::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::div_mod::*;
use vstd::set_lib::*;
use vstd::math::{min, max};
use vstd::{assert_by_contradiction, calc};

verus! {

/// This function computes the greatest common divisor of `a` and `b` 
/// (denoted as `(a, b)`).
pub closed spec fn gcd(a: nat, b: nat) -> nat 
    recommends a > 0 && b > 0,
{
    let s = Set::<nat>::new(|d: nat| is_common_factor(a, b, d));
    let r = |x: nat, y: nat| x <= y;
    s.find_unique_maximal(r)
}

/// Proof of `(a, b)`'s properties.
pub proof fn axiom_gcd_properties(a: nat, b: nat)
    requires 
        a > 0 && b > 0,
    ensures 
        is_common_factor(a, b, gcd(a, b)),
        forall|d: nat| is_common_factor(a, b, d) ==> d <= #[trigger] gcd(a, b),
        gcd(a, b) == gcd(b, a),
{
    let d = gcd(a, b);
    let s = Set::<nat>::new(|d: nat| is_common_factor(a, b, d));
    let r = |x: nat, y: nat| x <= y;
    assert(s.finite()) by {
        assert forall|m: nat| s.contains(m) 
        implies set_nat_range(0, a + b).contains(m) 
        by { 
            lemma_is_factor_bound(a, m); 
            lemma_is_factor_bound(b, m); 
        };
        assert(s.subset_of(set_nat_range(0, a + b)));
        lemma_nat_range(0, a + b);
        lemma_len_subset(s, set_nat_range(0, a + b));
    };
    assert(s.len() > 0) by {
        assert(s.contains(1));
    };
    s.find_unique_maximal_ensures(r);

    // Goal 1
    assert(is_common_factor(a, b, d)) by {
        s.contains(d);
    }
    // Goal 2
    assert forall|d0: nat| is_common_factor(a, b, d0) 
    implies d0 <= d
    by { 
        assert_by_contradiction!(r(d0, d), { assert(r(d, d0)); }); 
    };
    // Goal 3
    assert (d == gcd(b, a)) by {
        let d2 = gcd(b, a);
        let s2 = Set::<nat>::new(|d: nat| is_common_factor(b, a, d));
        assert(s == s2);
        assert(d == d2);
    };
}

/// Proof that `(a, b) == 1` is equivalent to coprimeness.
pub proof fn axiom_coprime_gcd(a: nat, b: nat)
    ensures a > 0 && b > 0 && gcd(a, b) == 1 <==> is_coprime(a, b),
{
    if a > 0 && b > 0 && gcd(a, b) == 1 {
        axiom_gcd_properties(a, b);
    }
    if is_coprime(a, b) {
        let d = gcd(a, b);
        assert(d == 1) by {
            axiom_gcd_properties(a, b);
            assert(is_common_factor(a, b, d));
            assert(is_common_factor(a, b, 1));
        }
    }
}

/// Alternative, recursive specification for `gcd`. This form is useful for induction 
/// over the Euclidean method.
closed spec fn gcd_rec(a: nat, b: nat) -> nat
    recommends a > 0 && b > 0,
    decreases a, b
    when a > 0 && b > 0
    via gcd_rec_decreases_proof
{
    if a > b {
        gcd_rec(b, a)
    } else if b % a == 0 {
        a
    } else {
        gcd_rec(b % a, a)
    }
}

#[via_fn]
proof fn gcd_rec_decreases_proof(a: nat, b: nat) {
    if a <= b {
        assert(decreases_to!(a, b => b % a, a)) by {
            lemma_mod_bound(b as int, a as int);
        }
    }
}

/// Proof of `gcd_rec`'s basic properties.
proof fn lemma_gcd_rec(a: nat, b: nat) 
    requires
        a > 0 && b > 0,
    ensures
        is_factor_of(a, gcd_rec(a, b)),
        is_factor_of(b, gcd_rec(a, b)),
    decreases 
        a, b,
{
    let d = gcd_rec(a, b);
    if a <= b && b % a == 0 {
        assert(d == a);
        assert(is_factor_of(a, d));
        assert(is_factor_of(b, d));
    } else if a > b {
        assert(d == gcd_rec(b, a));
        lemma_gcd_rec(b, a);
    } else {
        assert(d == gcd_rec(b % a, a));
        lemma_gcd_rec(b % a, a);
        assert(is_factor_of(b, d)) by {
            assert(b == a * (b / a) + b % a) by { broadcast use lemma_fundamental_div_mod; }
            lemma_is_factor_lincomb(a, (b / a) as int, b % a, 1, d);
        }
    }
}

/// Proof that if the predicate `pred` is preserved by linear combination, 
/// then `pred(a) && pred(b)` implies `pred(gcd_rec(a, b))`.
proof fn lemma_euclidean_induct_rec(a: nat, b: nat, pred: spec_fn(nat) -> bool)
    requires
        a > 0 && b > 0,
        pred(a) && pred(b),
        forall|a0: nat, b0: nat, x: int, y: int| 
            pred(a0) && pred(b0) && a0 * x + b0 * y >= 0 
                ==> #[trigger] pred((a0 * x + b0 * y) as nat),
    ensures 
        pred(gcd_rec(a, b)),
    decreases 
        a, b,
{
    if a <= b && b % a == 0 {
        assert(gcd_rec(a, b) == a);
        let a = a as int;
        let b = b as int;
        assert(a == a * (1 - (b / a)) + b * 1) by {
            assert(b == a * (b / a) + 0) by { broadcast use lemma_fundamental_div_mod; }
            assert(a * (1 - (b / a)) == a * 1 - a * (b / a)) by { broadcast use lemma_mul_is_distributive_sub; }
            assert(a * 1 == a && b * 1 == b) by { broadcast use group_mul_properties; }
        }
        assert(pred(gcd_rec(a as nat, b as nat)));
    } else if a > b {
        lemma_euclidean_induct_rec(b, a, pred);
    } else {
        let a = a as int;
        let b = b as int;
        assert(b % a == b * 1 + a * (-(b / a))) by {
            assert(b == a * (b / a) + b % a) by { broadcast use lemma_fundamental_div_mod; }
            assert(b == b * 1) by (nonlinear_arith);
            assert(-(a * (b / a)) == a * (-(b / a))) by (nonlinear_arith);
        }
        lemma_euclidean_induct_rec((b % a) as nat, a as nat, pred);
    }
}

/// Proof that the two ways of defining `gcd` are equivalent.
proof fn lemma_gcd_is_gcd_rec(a: nat, b: nat) 
    requires a > 0 && b > 0,
    ensures gcd(a, b) == gcd_rec(a, b),
{
    // Idea: gcd_rec(a, b) <= gcd(a, b), and gcd(a, b) | gcd_rec(a, b)
    axiom_gcd_properties(a, b);
    lemma_gcd_rec(a, b);
    assert(gcd_rec(a, b) <= gcd(a, b)) by {
        assert(is_common_factor(a, b, gcd_rec(a, b)));
    }
    assert(is_factor_of(gcd_rec(a, b), gcd(a, b))) by {
        let pred = |n: nat| is_factor_of(n, gcd(a, b));
        assert forall|a0: nat, b0: nat, x: int, y: int| pred(a0) && pred(b0) && a0 * x + b0 * y >= 0 
        implies #[trigger] pred((a0 * x + b0 * y) as nat)
        by { lemma_is_factor_lincomb(a0, x, b0, y, gcd(a, b)); }
        lemma_euclidean_induct_rec(a, b, pred);
    }
    lemma_is_factor_bound(gcd_rec(a, b), gcd(a, b));
}

/// Proof that if the predicate `pred` is preserved by linear combination, 
/// then `pred(a) && pred(b)` implies `pred(gcd(a, b))`.
pub proof fn lemma_euclidean_induct(a: nat, b: nat, pred: spec_fn(nat) -> bool)
    requires
        a > 0 && b > 0,
        pred(a) && pred(b),
        forall|a0: nat, b0: nat, x: int, y: int| 
            pred(a0) && pred(b0) && a0 * x + b0 * y >= 0 
                ==> #[trigger] pred((a0 * x + b0 * y) as nat),
    ensures 
        pred(gcd(a, b)),
{
    lemma_euclidean_induct_rec(a, b, pred);
    lemma_gcd_is_gcd_rec(a, b);
}

/// Proof that any common factor `d` of `a` and `b` is also a factor of `(a, b)`.
pub proof fn lemma_gcd_common_factor(a: nat, b: nat, d: nat) 
    requires
        a > 0 && b > 0,
        is_common_factor(a, b, d),
    ensures
        is_factor_of(gcd(a, b), d),
{
    axiom_gcd_properties(a, b);
    let pred = |n: nat| is_factor_of(n, d);

    assert(pred(a) && pred(b));
    assert forall|a0: nat, b0: nat, x: int, y: int| pred(a0) && pred(b0) && a0 * x + b0 * y >= 0 
    implies #[trigger] pred((a0 * x + b0 * y) as nat)
    by { lemma_is_factor_lincomb(a0, x, b0, y, d); }

    lemma_euclidean_induct(a, b, pred);
}

/// Proof that `(a * c, b * c) == (a, b) * c`.
pub proof fn lemma_gcd_mul(a: nat, b: nat, c: nat)
    requires a > 0 && b > 0 && c > 0,
    ensures gcd(a * c, b * c) == gcd(a, b) * c,
{
    assert(a * c > 0 && b * c > 0) by { broadcast use group_mul_properties; }
    axiom_gcd_properties(a * c, b * c);
    axiom_gcd_properties(a, b);

    assert(is_factor_of(gcd(a * c, b * c), c)) by {
        let pred = |n: nat| is_factor_of(n, c);
        broadcast use { lemma_mod_multiples_basic, group_mul_properties };
        assert(pred(a * c));
        assert(pred(b * c));
        assert forall|a0: nat, b0: nat, x: int, y: int| pred(a0) && pred(b0) && a0 * x + b0 * y >= 0 
        implies #[trigger] pred((a0 * x + b0 * y) as nat)
        by { lemma_is_factor_lincomb(a0, x, b0, y, c); }
        lemma_euclidean_induct(a * c, b * c, pred);
    };
    let k = gcd(a * c, b * c) / c;
    assert(gcd(a * c, b * c) == k * c) by { 
        assert(gcd(a * c, b * c) == c * k + 0) by { broadcast use lemma_fundamental_div_mod; }
        assert(c * k == k * c) by (nonlinear_arith);
    }

    lemma_gcd_mul_mid1(a, b, c, k);
    lemma_gcd_mul_mid2(a, b, c, k);

    assert(k == gcd(a, b)) by { 
        assert(k * c == gcd(a, b) * c);
        broadcast use group_mul_properties;
    }
}

proof fn lemma_gcd_mul_mid1(a: nat, b: nat, c: nat, k: nat)
    requires 
        a > 0 && b > 0 && c > 0 && a * c > 0 && b * c > 0,
        is_factor_of(gcd(a * c, b * c), c),
        gcd(a * c, b * c) == k * c,
    ensures
        k * c <= gcd(a, b) * c,
{
    axiom_gcd_properties(a * c, b * c);
    axiom_gcd_properties(a, b);
    assert(is_common_factor(a, b, k)) by {
        assert(k > 0) by {
            broadcast use { lemma_mod_multiples_basic, group_mul_properties };
            assert(is_common_factor(a * c, b * c, c));
            assert(gcd(a * c, b * c) >= c);
            lemma_div_is_ordered(c as int, gcd(a * c, b * c) as int, c as int);
        }
        lemma_is_factor_multiples(a, k, c);
        lemma_is_factor_multiples(b, k, c);
    }
    lemma_mul_inequality(k as int, gcd(a, b) as int, c as int);
}

proof fn lemma_gcd_mul_mid2(a: nat, b: nat, c: nat, k: nat)
    requires 
        a > 0 && b > 0 && c > 0 && a * c > 0 && b * c > 0,
        is_factor_of(gcd(a * c, b * c), c),
        gcd(a * c, b * c) == k * c,
    ensures
        gcd(a, b) * c <= k * c,
{
    axiom_gcd_properties(a * c, b * c);
    axiom_gcd_properties(a, b);
    let d = gcd(a, b);
    assert(is_factor_of(a * c, d * c)) by {
        assert(a == d * (a / d) + 0) by { broadcast use lemma_fundamental_div_mod; }
        calc!{
            (==)
            a * c; {}
            d * (a / d) * c; { broadcast use lemma_mul_is_commutative; } 
            (a / d) * d * c; { broadcast use lemma_mul_is_associative; }
            (a / d) * (d * c);
        }
        lemma_mod_multiples_basic((a / d) as int, (d * c) as int);
    }
    assert(is_factor_of(b * c, d * c)) by {
        assert(b == d * (b / d) + 0) by { broadcast use lemma_fundamental_div_mod; }
        calc!{
            (==)
            b * c; {}
            d * (b / d) * c; { broadcast use lemma_mul_is_commutative; } 
            (b / d) * d * c; { broadcast use lemma_mul_is_associative; }
            (b / d) * (d * c);
        }
        lemma_mod_multiples_basic((b / d) as int, (d * c) as int);
    }
    assert(is_common_factor(a * c, b * c, d * c));
}

/// Proof that `(a / d, b / d) = (a, b) / d` for any common factor `d` of `a` and `b`.
pub proof fn lemma_gcd_div(a: nat, b: nat, d: nat) 
    requires 
        a > 0 && b > 0 && d > 0,
        is_common_factor(a, b, d),
    ensures 
        gcd(a / d, b / d) == gcd(a, b) / d,
{
    let a1 = a / d;
    let b1 = b / d;
    calc!{
        (==)
        a; { broadcast use lemma_fundamental_div_mod; }
        d * a1 + 0; {}
        a1 * d;
    }
    calc!{
        (==)
        b; { broadcast use lemma_fundamental_div_mod; }
        d * b1 + 0; {}
        b1 * d;
    } 
    assert(a1 > 0) by {
        lemma_is_factor_bound(a, d);
        lemma_div_non_zero(a as int, d as int);
    }
    assert(b1 > 0) by {
        lemma_is_factor_bound(b, d);
        lemma_div_non_zero(b as int, d as int);
    }

    calc!{
        (==)
        gcd(a, b) / d; { lemma_gcd_mul(a1, b1, d); }
        (gcd(a1, b1) * d) / d; { broadcast use lemma_mul_is_commutative; }
        (d * gcd(a1, b1)) / d; { broadcast use lemma_div_multiples_vanish; }
        gcd(a1, b1); 
    }
}

/// This function computes the least common multiple of `a` and `b` 
/// (denoted as `[a, b]`).
pub open spec fn lcm(a: nat, b: nat) -> nat
    recommends a > 0 && b > 0,
{
    a * b / gcd(a, b)
}

/// Proof of `[a, b]`'s properties.
pub proof fn axiom_lcm_properties(a: nat, b: nat)
    requires 
        a > 0 && b > 0,
    ensures 
        is_factor_of(lcm(a, b), a) && is_factor_of(lcm(a, b), b),
        lcm(a, b) != 0,
        forall|m: nat| m > 0 && is_factor_of(m, a) && is_factor_of(m, b) ==> m >= lcm(a, b),
        lcm(a, b) == lcm(b, a),
{
    let m = lcm(a, b);
    let d = gcd(a, b);
    let a1 = a / d;
    let b1 = b / d;
    let m1 = m / d;
    axiom_gcd_properties(a, b);

    // Goal 1: a|[a, b] and b|[a, b]
    assert(is_factor_of(m, a)) by {
        calc!{
            (==)
            m; {}
            a * b / d; { broadcast use lemma_fundamental_div_mod; }
            a * (d * b1 + 0) / d; {}
            a * (d * b1) / d; { broadcast use lemma_mul_is_associative; }
            a * d * b1 / d; { broadcast use lemma_mul_is_commutative; }
            d * a * b1 / d; { broadcast use lemma_mul_is_associative; }
            d * (a * b1) / d; { broadcast use lemma_div_multiples_vanish; }
            a * b1; {}
            b1 * a;
        }
        lemma_mod_multiples_basic(b1 as int, a as int);
    }
    assert(is_factor_of(m, b)) by {
        calc!{
            (==)
            m; {}
            a * b / d; { broadcast use lemma_fundamental_div_mod; }
            (d * a1 + 0) * b / d; {}
            d * a1 * b / d; { broadcast use lemma_mul_is_associative; }
            d * (a1 * b) / d; { broadcast use lemma_div_multiples_vanish; }
            a1 * b;
        }
        lemma_mod_multiples_basic(a1 as int, b as int);
    }

    // Goal w: [a, b] != 0
    assert_by_contradiction!(m != 0, {
        assert(is_factor_of(a * b, d)) by {
            assert(is_factor_of(a * b, b)) by { broadcast use lemma_mod_multiples_basic; }
            lemma_is_factor_transitive(d, b, a * b);
        }
        calc!{
            (==)
            a * b; { broadcast use lemma_fundamental_div_mod; }
            d * m + 0; { broadcast use group_mul_basics; }
            0 + 0; {}
            0;
        }
        assert(a * b != 0) by { broadcast use group_mul_properties; }
    });

    // Goal 3: [a, b] is the *least*
    assert forall|m0: nat| m0 > 0 && is_factor_of(m0, a) && is_factor_of(m0, b)
    implies m0 >= lcm(a, b)
    by {
        lemma_lcm_is_factor(a, b, m0); // lcm(a, b) | m0
        lemma_is_factor_bound(m0, lcm(a, b));
    }

    // Goal 4: [a, b] = [b, a]
    assert(lcm(a, b) == lcm(b, a)) by {
        calc!{
            (==)
            lcm(a, b); {}
            a * b / gcd(a, b); { broadcast use lemma_mul_is_commutative; }
            b * a / gcd(a, b); { axiom_gcd_properties(a, b); }
            b * a / gcd(b, a); {}
            lcm(b, a);
        }
    }
}

/// Proof that `[a, b] == a * b` is equivalent to coprimeness.
pub proof fn axiom_coprime_lcm(a: nat, b: nat)
    ensures a > 0 && b > 0 && lcm(a, b) == a * b <==> is_coprime(a, b),
{
    // ..the not so obvious step
    if a > 0 && b > 0 && lcm(a, b) == a * b / 1 {
        axiom_lcm_properties(a, b);
        assert(is_factor_of(a * b, gcd(a, b))) by {
            axiom_gcd_properties(a, b);
            assert(is_factor_of(b, gcd(a, b)));
            assert(is_factor_of(a * b, b)) by { broadcast use lemma_mod_multiples_basic; } 
            lemma_is_factor_transitive(gcd(a, b), b, a * b);
        }
        assert(a * b == gcd(a, b) * lcm(a, b) + 0) by { broadcast use lemma_fundamental_div_mod; }
        assert(a * b == lcm(a, b) * gcd(a, b));
        assert(a * b == lcm(a, b) * 1);
        lemma_mul_equality_converse(lcm(a, b) as int, gcd(a, b) as int, 1);
        assert(gcd(a, b) == 1);
    }
    calc!{
        (<==>)
        is_coprime(a, b); { axiom_coprime_gcd(a, b); }
        a > 0 && b > 0 && gcd(a, b) == 1; {}
        a > 0 && b > 0 && lcm(a, b) == a * b / 1; {}
        a > 0 && b > 0 && lcm(a, b) == a * b;
    }
}

/// Proof that `[a, b]` is a factor of any common multiple `n` of `a` and `b`.
pub proof fn lemma_lcm_is_factor(a: nat, b: nat, n: nat)
    requires
        is_factor_of(n, a),
        is_factor_of(n, b),
    ensures
        is_factor_of(n, a * b / gcd(a, b)),
{
    let d = gcd(a, b);
    let a1 = a / d;
    let b1 = b / d;
    let n1 = n / d;
    axiom_gcd_properties(a, b);
    calc!{
        (==)
        a; { lemma_fundamental_div_mod(a as int, d as int); }
        d * a1 + 0; {}
        a1 * d;
    }
    calc!{
        (==)
        b; { lemma_fundamental_div_mod(b as int, d as int); }
        d * b1 + 0; {}
        b1 * d;
    }
    calc!{
        (==)
        a * b / d; {}
        (a1 * d) * b / d; { lemma_mul_is_commutative(a1 as int, d as int); }
        d * a1 * b / d; { lemma_mul_is_associative(d as int, a1 as int, b as int); }
        d * (a1 * b) / d; { lemma_div_multiples_vanish((a1 * b) as int, d as int); }
        a1 * b;
    }

    lemma_is_factor_transitive(d, a, n);
    calc!{
        (==)
        n; { lemma_fundamental_div_mod(n as int, d as int); }
        d * n1 + 0; {}
        n1 * d;
    }
    assert(a1 > 0) by {
        lemma_is_factor_bound(a, d);
        lemma_div_non_zero(a as int, d as int);
    }
    assert(b1 > 0) by {
        lemma_is_factor_bound(b, d);
        lemma_div_non_zero(b as int, d as int);
    }
    assert(is_factor_of(n1 * d, a1 * d));
    assert(is_factor_of(n1 * d, b1 * d));
    lemma_is_factor_multiples(n1, a1, d); // a1 | n1
    lemma_is_factor_multiples(n1, b1, d); // b1 | n1

    let n2 = n1 / a1;
    assert(n1 == a1 * n2 + 0) by { lemma_fundamental_div_mod(n1 as int, a1 as int); }
    
    assert(a1 * b > 0) by { broadcast use group_mul_properties; }
    if n == 0 {
        // ..trivial
    } else {
        assert(n1 > 0) by {
            lemma_is_factor_bound(n, d);
            lemma_div_non_zero(n as int, d as int);
        }
        assert(n2 > 0) by {
            lemma_is_factor_bound(n1, a1);
            lemma_div_non_zero(n1 as int, a1 as int);
        }
        assert(is_coprime(b1, a1)) by {
            lemma_gcd_div(b, a, d);
            assert(gcd(b1, a1) == 1);
            axiom_coprime_gcd(b1, a1);
        }
        assert(is_factor_of(n2, b1)) by {
            lemma_coprime_factor(b1, a1, n2);
        }
        let n3 = n2 / b1;
        calc!{
            (==)
            n; {}
            n1 * d; {}
            a1 * n2 * d; { lemma_fundamental_div_mod(n2 as int, b1 as int); }
            a1 * (b1 * n3 + 0) * d; {}
            a1 * (b1 * n3) * d; { lemma_mul_is_associative(a1 as int, (b1 * n3) as int, d as int); }
            a1 * (b1 * n3 * d); { lemma_mul_is_associative(b1 as int, n3 as int, d as int); }
            a1 * (b1 * (n3 * d)); { lemma_mul_is_commutative(n3 as int, d as int); }
            a1 * (b1 * (d * n3)); { lemma_mul_is_associative(b1 as int, d as int, n3 as int); }
            a1 * (b1 * d * n3); { lemma_mul_is_associative(a1 as int, (b1 * d) as int, n3 as int); }
            a1 * (b1 * d) * n3; { lemma_mul_is_associative(a1 as int, b1 as int, d as int); }
            (a1 * b1 * d) * n3; { lemma_mul_is_commutative(n3 as int, (a1 * b1 * d) as int); }
            n3 * (a1 * b1 * d); { lemma_mul_is_associative(a1 as int, b1 as int, d as int); }
            n3 * (a1 * (b1 * d)); {}
            n3 * (a1 * b);
        }
        lemma_mod_multiples_basic(n3 as int, (a1 * b) as int);
    }
}

/// This function computes `gcd(a, b)` via the Euclidean method, in executable code.
pub fn gcd_exec(a: usize, b: usize) -> (ret: usize)
    ensures a > 0 && b > 0 ==> ret == gcd(a as nat, b as nat),
{
    if a == 0 || b == 0 {
        return 0;
    }

    let mut ea = a;
    let mut eb = b;
    let ghost d = gcd(a as nat, b as nat);
    while eb % ea != 0 
        invariant
            ea > 0 && eb > 0,
            gcd(ea as nat, eb as nat) == d,
        decreases ea, eb, 
    {
        let ghost a = ea as nat;
        let ghost b = eb as nat;
        if ea > eb {
            let tmp = ea;
            ea = eb;
            eb = tmp;
            proof { // invariant
                assert(ea == b && eb == a);
                axiom_gcd_properties(a, b); 
            }
        } else {
            let tmp = ea;
            ea = eb % ea;
            eb = tmp;
            proof { // invariant
                assert(ea == b % a && eb == a);
                assert(decreases_to!(a, b => ea, eb)) by {
                    lemma_mod_bound(b as int, a as int);
                    assert(ea < a);
                }
                gcd_exec_proof(a, b);
            }
        }
    }
    
    proof { // post invariants
        assert(ea == d) by {
            assert(gcd(ea as nat, eb as nat) == d && eb % ea == 0);
            lemma_gcd_is_gcd_rec(ea as nat, eb as nat);
            assert(eb >= ea) by { lemma_is_factor_bound(eb as nat, ea as nat); }
            reveal_with_fuel(gcd_rec, 2);
            assert(gcd_rec(ea as nat, eb as nat) == ea); 
        }
    }
    ea
}

proof fn gcd_exec_proof(a: nat, b: nat) 
    requires a > 0 && b > 0 && b % a != 0,
    ensures gcd(b % a, a) == gcd(a, b),
{
    let d = gcd(a, b);
    let d1 = gcd(b % a, a);
    axiom_gcd_properties(a, b);
    axiom_gcd_properties(b % a, a);

    assert(d1 <= d) by {
        calc!{
            (==)
            b; { broadcast use lemma_fundamental_div_mod; }
            a * (b/a) + b % a; { broadcast use group_mul_basics; }
            a * (b/a) + (b % a) * 1; 
        }
        lemma_is_factor_lincomb(a, (b/a) as int, b % a, 1, d1);
        let pred = |x: nat| is_factor_of(x, d1);
        assert forall|a0: nat, b0: nat, x: int, y: int| 
            pred(a0) && pred(b0) && a0 * x + b0 * y >= 0
        implies
            #[trigger] pred((a0 * x + b0 * y) as nat)
        by { lemma_is_factor_lincomb(a0, x, b0, y, d1); }
        assert(pred(d)) by { lemma_euclidean_induct(a, b, pred); }
        lemma_is_factor_bound(d, d1);
    }

    assert(d <= d1) by {
        calc!{
            (==)
            (b % a) as int; { lemma_fundamental_div_mod(b as int, a as int); }
            b - a * (b/a); { broadcast use group_mul_basics; }
            b * 1 - a * (b/a);
        }
        assert(is_factor_of(b % a, d)) by {
            lemma_is_factor_lincomb2(b, 1, a, (b/a) as int, d);
        }
        let pred = |x: nat| is_factor_of(x, d);
        assert forall|a0: nat, b0: nat, x: int, y: int| 
            pred(a0) && pred(b0) && a0 * x + b0 * y >= 0
        implies
            #[trigger] pred((a0 * x + b0 * y) as nat)
        by { lemma_is_factor_lincomb(a0, x, b0, y, d); }
        assert(pred(d1)) by { lemma_euclidean_induct(b % a, a, pred); }
        lemma_is_factor_bound(d1, d);
    }  
}

} // verus!