//! Definitions and lemmas for (N)umber (T)heory in Verus.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power::*;
use vstd::seq::*;
use vstd::set::fold::*;
use vstd::set_lib::*;
use vstd::math::{min, max, clip};
use vstd::{assert_by_contradiction, calc};
use vstd::relations::{injective_on, is_minimal, sorted_by};

pub mod gcd;
pub mod totient;
mod util;

pub use gcd::{
    gcd, lcm, gcd_exec,
    axiom_gcd_properties, axiom_lcm_properties, axiom_coprime_gcd, axiom_coprime_lcm,
    lemma_euclidean_induct, lemma_gcd_mul, lemma_gcd_div,
    lemma_gcd_common_factor, lemma_lcm_is_factor,
};

pub use totient::{totient, totients};

verus! {

/// An expansion of `div_mod::group_mod_properties` with commonly used lemmas 
/// in number theory.
/// WARNING: avoid using this and `mul::group_mul_properties` together; it likely 
/// blows up error diagnostics.
broadcast group group_mod_properties_nt {
    group_mod_properties,
    group_fundamental_div_mod_converse,
    lemma_fundamental_div_mod,
    lemma_mod_multiples_basic,
    lemma_mod_is_zero,
}

/// This function defines the natural number range [lo, hi).
/// It is useful in this module as a substitute of `set_lib::set_int_range`, 
/// with the elements being `nat` instead of `int`.
pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::<nat>::new(|p: nat| lo <= p < hi)
}

/// Proof of `set_nat_range`'s basic properties.
pub broadcast proof fn lemma_nat_range(lo: nat, hi: nat)
    ensures
        #[trigger] set_nat_range(lo, hi).finite(),
        #[trigger] set_nat_range(lo, hi).len() == clip(hi - lo),
{
    if lo > hi {
        // Case 1: Empty
        let empty = Set::<nat>::empty();
        assert_sets_equal!(set_nat_range(lo, hi) == empty, elem => {});
    } else {
        // Case 2: Non-empty
        let f = |e: int| e as nat;
        let set1 = set_int_range(lo as int, hi as int);
        let set1f = set_int_range(lo as int, hi as int).map(f);
        let set2 = set_nat_range(lo, hi);

        lemma_int_range(lo as int, hi as int);
        assert_sets_equal!(set1f == set2, elem => {
            if set1f.contains(elem) {
                let g = |a: nat| { exists|x: int| set1.contains(x) && a == f(x) };
                assert(g(elem));
                let elem1 = choose|x: int| set1.contains(x) && elem == f(x);
                assert(elem == elem1);
                assert(lo as int <= elem1 < hi as int);
                assert(lo <= elem < hi);
                assert(set2.contains(elem));
            } 
            if set2.contains(elem) {
                assert(lo <= elem < hi);
                let elem1 = elem as int;
                assert(set1.contains(elem1) && elem == f(elem1));
                assert(elem == elem1);
                assert(set1f.contains(elem));
            }
        });
        assert(injective_on(f, Set::<int>::new(|x: int| x >= 0)));
        lemma_map_size(set1, set2, f);
    }
}

/// This predicate determines whether `d` is a factor of `n` (`d|n`).
/// It can be used as a trigger term.
pub open spec fn is_factor_of(n: nat, d: nat) -> bool {
    n % d == 0 && d > 0
}

/// Proof that `d|n` implies either `n == 0` or `n >= d`.
pub broadcast proof fn lemma_is_factor_bound(n: nat, d: nat) 
    requires 
        #[trigger] is_factor_of(n, d),
    ensures n == 0 || n >= d,
{
    broadcast use group_mod_properties_nt;
}

/// Proof that if `d|n1` and `d|n2`, then `d|(n1 * a1 + n2 * a2)` for any integer coefficients
/// `a1` and `a2`.
pub proof fn lemma_is_factor_lincomb(n1: nat, a1: int, n2: nat, a2: int, d: nat)
    requires 
        is_factor_of(n1, d),
        is_factor_of(n2, d),
        n1 * a1 + n2 * a2 >= 0,
    ensures 
        is_factor_of((n1 * a1 + n2 * a2) as nat, d),
{
    assert(n1 * a1 % (d as int) == 0) by {
        broadcast use group_mod_properties_nt;
        assert(n1 == d * (n1/d) + 0);
        assert(n1 * a1 == (n1/d) * a1 * d) by { broadcast use group_mul_properties; };
    };
    assert(n2 * a2 % (d as int) == 0) by {
        broadcast use group_mod_properties_nt;
        assert(n2 == d * (n2/d) + 0);
        assert(n2 * a2 == (n2/d) * a2 * d) by { broadcast use group_mul_properties; };
    };
    broadcast use lemma_mod_adds;
    assert((n1 * a1 + n2 * a2) % (d as int) == 0);
}

/// Proof that if `d|n1` and `d|n2`, then `d|(n1 * a1 - n2 * a2)` for any integer coefficients
/// `a1` and `a2`.
/// This is an alternative form of `lemma_is_factor_lincomb`, useful when the linear
/// combination comes in the substraction form.
pub proof fn lemma_is_factor_lincomb2(n1: nat, a1: int, n2: nat, a2: int, d: nat)
    requires 
        is_factor_of(n1, d),
        is_factor_of(n2, d),
        n1 * a1 - n2 * a2 >= 0,
    ensures 
        is_factor_of((n1 * a1 - n2 * a2) as nat, d),
{
    calc!{
        (==)
        n1 * a1 - n2 * a2; { lemma_mul_unary_negation(n2 as int, a2); }
        n1 * a1 + n2 * (-a2);
    }
    lemma_is_factor_lincomb(n1, a1, n2, -a2, d);
}

/// Proof that if `a | b` and `b | c`, then `a | c`.
pub proof fn lemma_is_factor_transitive(a: nat, b: nat, c: nat)
    requires
        is_factor_of(b, a) && is_factor_of(c, b)
    ensures
        is_factor_of(c, a),
{
    calc!{
        (==)
        c; { broadcast use lemma_fundamental_div_mod; }
        b * (c/b) + 0; {}
        b * (c/b); { broadcast use lemma_fundamental_div_mod; }
        (a * (b/a) + 0) * (c/b); {}
        a * (b/a) * (c/b); { broadcast use lemma_mul_is_associative; }
        a * ((b/a) * (c/b)); { broadcast use lemma_mul_is_commutative; }
        ((b/a) * (c/b)) * a;
    }
    lemma_mod_multiples_basic(((b/a) * (c/b)) as int, a as int);
}

/// This function determines whether `p` is a prime number.
/// Note: this is but one of many ways to uniquely define primeness.
pub open spec fn is_prime(p: nat) -> bool {
    p > 1 && forall|d: nat| #[trigger] is_factor_of(p, d) ==> d == 1 || d == p
}

/// This function determines whether `n` is a composite number.
pub open spec fn is_composite(n: nat) -> bool {
    n > 1 && exists|a: nat, b: nat| 1 < a < n && 1 < b < n && #[trigger] (a * b) == n
}

/// This predicate determines whether `d` is a common factor of `a` and `b`.
pub open spec fn is_common_factor(a: nat, b: nat, d: nat) -> bool {
    is_factor_of(a, d) && is_factor_of(b, d)
}

/// This predicate determines whether `a` and `b` are coprime.
pub open spec fn is_coprime(a: nat, b: nat) -> bool {
    &&& a > 0
    &&& b > 0
    &&& !exists|d: nat| d > 1 && #[trigger] is_common_factor(a, b, d)
}

/// This function defines the set of prime factors of `n`.
pub open spec fn prime_factors(n: nat) -> Set<nat>
    recommends n > 0
{
    Set::<nat>::new(|p: nat| is_prime(p) && is_factor_of(n, p))
}

/// This function defines the "p-adic" valuation of `n` for a prime number `p` (denoted as `v_p(n)`); 
/// equivalently, it defines the exponent of the highest power of `p` that divides `n`.
pub closed spec fn vp(n: nat, p: nat) -> nat 
    recommends 
        n > 0,
        is_prime(p),
{
    let s = Set::<nat>::new(|k: nat| is_factor_of(n, pow(p as int, k) as nat));
    let r = |x: nat, y: nat| x <= y;
    s.find_unique_maximal(r)
}

/// Proof of `is_coprime`'s basic properties.
pub proof fn axiom_is_coprime(a: nat, b: nat)
    requires is_coprime(a, b),
    ensures is_coprime(b, a),
{
    axiom_coprime_gcd(a, b);
    axiom_coprime_gcd(b, a);
    axiom_gcd_properties(a, b);
}

/// Proof of `v_p(n)`'s basic properties.
pub proof fn axiom_vp_properties(n: nat, p: nat)
    requires 
        n > 0,
        is_prime(p),
    ensures 
        is_factor_of(n, pow(p as int, vp(n, p)) as nat),
        forall|k: nat| is_factor_of(n, pow(p as int, k) as nat) ==> k <= #[trigger] vp(n, p),
        vp(n, p) > 0 <==> is_factor_of(n, p),
        !is_factor_of(n / pow(p as int, vp(n, p)) as nat, p),
        prime_factors(n / pow(p as int, vp(n, p)) as nat) == prime_factors(n).remove(p),
{
    let s = Set::<nat>::new(|k: nat| is_factor_of(n, pow(p as int, k) as nat));
    let r = |x: nat, y: nat| x <= y;
    assert(s.finite()) by {
        assert forall|l: nat| #[trigger] s.contains(l) 
        implies set_nat_range(0, n).contains(l) 
        by { 
            assert_by_contradiction!(l < n, {
                util::lemma_pow_n_gt_n(p, n);
                lemma_pow_increases(p, n, l);
                lemma_is_factor_bound(n, pow(p as int, l) as nat);
            });
        };
        assert(s.subset_of(set_nat_range(0, n)));
        lemma_nat_range(0, n);
        lemma_len_subset(s, set_nat_range(0, n));
    };
    assert(s.len() > 0) by {
        lemma_pow0(p as int);
        assert(s.contains(0));
    };
    s.find_unique_maximal_ensures(r);

    // Goal 1
    assert(is_factor_of(n, pow(p as int, vp(n, p)) as nat)) by {
        s.contains(vp(n, p));
    }
    // Goal 2
    assert forall|k: nat| is_factor_of(n, pow(p as int, k) as nat)
    implies k <= #[trigger] vp(n, p)
    by { 
        assert_by_contradiction!(r(k, vp(n, p)), { assert(r(vp(n, p), k)); }); 
    };
    // Goal 3
    let e = vp(n, p);
    let p_to_e = pow(p as int, vp(n, p)) as nat;
    assert(e > 0 <==> is_factor_of(n, p)) by {
        if is_factor_of(n, p) {
            assert(p == pow(p as int, 1)) by { lemma_pow1(p as int); }
            assert(3 >= 1);
        }
        if e > 0 {
            let k = pow(p as int, (e - 1) as nat);
            assert(p_to_e == p * k) by { 
                lemma_pow_positive(p as int, e);
                reveal(pow); 
            };
            assert(p * k == k * p) by { broadcast use lemma_mul_is_commutative; }
            assert(is_factor_of(p_to_e, p)) by { lemma_mod_multiples_basic(k, p as int); }
            assert(is_factor_of(n, p)) by { lemma_is_factor_transitive(p, p_to_e, n); }
        }
    }
    // Goal 4
    let n1 = n / p_to_e;
    assert(n == p_to_e * n1 + 0) by { broadcast use lemma_fundamental_div_mod; }
    assert_by_contradiction!(!is_factor_of(n1, p), {
        let n2 = n1 / p;
        assert(n1 == p * n2 + 0) by { broadcast use lemma_fundamental_div_mod; }
        calc!{
            (==)
            n; {}
            n1 * p_to_e; {}
            p * n2 * p_to_e; {}
            n2 * p * p_to_e; { broadcast use lemma_mul_is_associative; }
            n2 * (p * p_to_e); {
                let p = p as int;
                let p_to_e = p_to_e as int;
                calc!{
                    (==)
                    p * p_to_e; { lemma_pow_positive(p, e); }
                    p * pow(p, e); { lemma_pow1(p); }
                    pow(p, 1) * pow(p, e); { lemma_pow_adds(p, 1, e); }
                    pow(p, 1 + e);
                }
            }
            n2 * (pow(p as int, e + 1) as nat);
        }
        assert(is_factor_of(n, pow(p as int, e + 1) as nat)) by { 
            lemma_pow_positive(p as int, e + 1);
            lemma_mod_multiples_basic(n2 as int, pow(p as int, e + 1));
        }
    });
    // Goal 5
    if is_factor_of(n, p) {
        assert(e > 0);
        assert(prime_factors(n1).insert(p) == prime_factors(n)) by {
            let set1 = prime_factors(n1).insert(p);
            let set2 = prime_factors(n);
            assert(set1.subset_of(set2)) by {
                assert forall|p0: nat| set1.contains(p0)
                implies set2.contains(p0)
                by {
                    if p0 == p {}
                    else {
                        assert(is_factor_of(n1, p0));
                        assert(is_factor_of(n, n1)) by { lemma_mod_multiples_basic(p_to_e as int, n1 as int); }
                        lemma_is_factor_transitive(p0, n1, n);
                    }
                }
            }
            assert(set2.subset_of(set1)) by {
                assert forall|p0: nat| set2.contains(p0)
                implies set1.contains(p0)
                by {
                    assert(is_factor_of(p_to_e, p0) || is_factor_of(n1, p0)) by {
                        assert(is_factor_of(n1 * p_to_e, p0));
                        axiom_prime_mul_union(p0);
                    }
                    if is_factor_of(p_to_e, p0) {
                        lemma_prime_factors_prime_pow(p, e);
                        assert(p0 == p) by {
                            assert(prime_factors(p_to_e).contains(p0));
                        }
                        assert(set1.contains(p0));
                    }
                    if is_factor_of(n1, p0) {
                        assert(is_factor_of(n, n1)) by {
                            assert(n == p_to_e * n1);
                            lemma_mod_multiples_basic(p_to_e as int, n1 as int);
                        }
                        lemma_is_factor_transitive(p0, n1, n);
                        assert(set1.contains(p0));
                    }
                }
            }
        }
        assert(prime_factors(n1) == prime_factors(n).remove(p));
    } else {
        assert(!prime_factors(n).contains(p));
        assert(e == 0);
        assert(p_to_e == 1) by { lemma_pow0(p as int); }
        calc!{ (==) n1; {} n / 1; {} n; }
    }
}

/// Proof that `p` is prime iff `p > 1` and `p` is not composite.
/// Note: this is also an alternative definition of `is_prime`.
pub broadcast proof fn axiom_prime_not_composite(p: nat)
    ensures 
        #[trigger] is_prime(p) 
        <==> p > 1 && !is_composite(p)
{
    if is_prime(p) {
        assert_by_contradiction!(!is_composite(p), {
            let (a, b) = choose|a: nat, b: nat| 1 < a < p && 1 < b < p && #[trigger] (a * b) == p;
            assert(is_factor_of(p, b)) by {
                assert(p == a * b + 0);
                lemma_fundamental_div_mod_converse(p as int, b as int, a as int, 0);
            };
        });
    }
    if p > 1 && !is_composite(p) {
        assert_by_contradiction!(is_prime(p), {
            let a = choose|d: nat| is_factor_of(p, d) && d != 1 && d != p;
            let b = p / a;
            broadcast use group_mod_properties_nt;
            assert(a * b + 0 == p);
            assert(1 < a < p) by { lemma_is_factor_bound(p, a); };
            assert(1 < b < p) by {
                lemma_div_by_multiple_is_strongly_ordered(a as int, p as int, b as int, a as int); // 1 < b
                lemma_div_is_ordered_by_denominator(p as int, 1, a as int); // b <= p
                assert_by_contradiction!(b != p, {
                    lemma_mul_equality_converse(b as int, a as int, 1);
                });
            };
        });
    }
}

/// Proof that `p` is prime iff `p|ab` implies `p|a` or `p|b`.
/// Note: this is also an alternative definition of `is_prime`.
pub broadcast proof fn axiom_prime_mul_union(p: nat)
    ensures 
        #[trigger] is_prime(p) 
        <==> p > 1 && forall|a: nat, b: nat| #[trigger] 
            is_factor_of(a * b, p) ==> is_factor_of(a, p) || is_factor_of(b, p),
{
    if is_prime(p) {
        assert forall|a: nat, b: nat| #[trigger] is_factor_of(a * b, p)
        implies is_factor_of(a, p) || is_factor_of(b, p)
        by {
            if !is_factor_of(a, p) {
                assert_by_contradiction!(is_coprime(p, a), {
                    let d = choose|d: nat| d > 1 && #[trigger] is_common_factor(p, a, d);
                    assert(d == p);
                });
                if b > 0 {
                    lemma_coprime_factor(p, a, b);
                    assert(is_factor_of(b, p));
                } else {
                    assert(is_factor_of(0, p));
                }
                
            }
        };
    }

    if p > 1 && forall|a: nat, b: nat| #[trigger] 
        is_factor_of(a * b, p) ==> is_factor_of(a, p) || is_factor_of(b, p) 
    {
        assert_by_contradiction!(is_prime(p), {
            assert(is_composite(p)) by { lemma_prime_or_composite(p); };
            let (a, b) = choose|a: nat, b: nat| 1 < a < p && 1 < b < p && #[trigger] (a * b) == p;
            assert(is_factor_of(a * b, p)) by(compute);
            assert_by_contradiction!(!is_factor_of(a, p), { lemma_is_factor_bound(a, p); });
            assert_by_contradiction!(!is_factor_of(b, p), { lemma_is_factor_bound(b, p); });
        });
    }
}

/// Proof that `b * c | a * c` implies `b | a`.
pub proof fn lemma_is_factor_multiples(a: nat, b: nat, c: nat)
    requires 
        b > 0 && c > 0,
        is_factor_of(a * c, b * c),
    ensures
        is_factor_of(a, b),
{
    let r = a % b;
    assert(is_factor_of(r * c, b * c)) by {
        assert(r * c == a * c * 1 + b * c * (-(a / b))) by {
            lemma_fundamental_div_mod(a as int, b as int);
            assert(a == b * (a / b) + r);
            assert(a * c == (b * (a / b) + r) * c);
            assert(a * c == a * c * 1);
            broadcast use group_mul_properties;
            assert((b * (a / b) + r) * c == b * (a / b) * c + r * c);
            assert(r * c == a * c + -(b * (a / b) * c));
            assert(b * (a / b) * c == b * c * (a / b));
            assert(-(b * c * (a / b)) == b * c * (-(a / b)));
        }
        lemma_is_factor_lincomb(a * c, 1, b * c, -(a / b), b * c);
    };
    
    assert(r * c < b * c) by {
        lemma_mod_bound(a as int, b as int);
        lemma_mul_strict_inequality(r as int, b as int, c as int);
    }

    assert(r == 0) by {
        lemma_is_factor_bound(r * c, b * c);
        broadcast use group_mul_properties;
    }
}

/// Proof that `a * b / c == a / c * b` if `c|a`.
pub proof fn lemma_is_factor_mul_div(a: nat, b: nat, c: nat)
    requires is_factor_of(a, c),
    ensures a * b / c == a / c * b,
{
    let a1 = a / c;
    assert(a == c * a1 + 0) by { lemma_fundamental_div_mod(a as int, c as int); }
    calc!{
        (==)
        a * b / c; {}
        c * a1 * b / c; { lemma_mul_is_associative(c as int, a1 as int, b as int); }
        c * (a1 * b) / c; { lemma_div_multiples_vanish((a1 * b) as int, c as int); }
        a1 * b; {}
        a / c * b;
    }
}

/// Proof that if `a|bc` and `(a, b) == 1`, then `a|c`.
pub proof fn lemma_coprime_factor(a: nat, b: nat, c: nat) 
    requires
        c > 0,
        is_factor_of(b * c, a),
        is_coprime(a, b),
    ensures
        is_factor_of(c, a),
{
    assert(is_factor_of(a * c, a)) by {
        broadcast use { lemma_mod_multiples_basic, group_mul_properties };
    }

    assert(is_factor_of(gcd(a * c, b * c), a)) by {
        let pred = |n: nat| is_factor_of(n, a);
        assert forall|a0: nat, b0: nat, x: int, y: int| pred(a0) && pred(b0) && a0 * x + b0 * y >= 0 
        implies #[trigger] pred((a0 * x + b0 * y) as nat)
        by { lemma_is_factor_lincomb(a0, x, b0, y, a); }
        assert(a * c > 0 && b * c > 0) by { broadcast use group_mul_properties; }
        lemma_euclidean_induct(a * c, b * c, pred);
    }

    assert(gcd(a * c, b * c) == c) by {
        lemma_gcd_mul(a, b, c);
        axiom_coprime_gcd(a, b);
    }
}

/// Proof of the Bézout's Identity (https://en.wikipedia.org/wiki/B%C3%A9zout%27s_identity).
pub proof fn lemma_bezout_identity(a: nat, b: nat, d: nat)
    requires
        a > 0 && b > 0,
        d == gcd(a, b),
    ensures 
        exists|x: int, y: int| 0 <= x < b / d && #[trigger] (a * x + b * y) == d,
{
    let a1 = a / d;
    let b1 = b / d;
    axiom_gcd_properties(a, b);
    assert(a == d * a1 + 0 && b == d * b1 + 0) by {
        broadcast use lemma_fundamental_div_mod;
    }
    assert(a1 > 0 && b1 > 0) by {
        lemma_is_factor_bound(a, d);
        lemma_is_factor_bound(b, d);
        lemma_div_non_zero(a as int, d as int);
        lemma_div_non_zero(b as int, d as int);
    }
    // Goal: exists|x, y| 0 <= x < b1 && a1 * x + b1 * y == 1
    assert(is_coprime(a1, b1)) by {
        lemma_gcd_div(a, b, d);
        assert(gcd(a1, b1) == 1);
        axiom_coprime_gcd(a1, b1);
    }

    // Main Idea: {0a1, 1a1, ..., (b1-1)a1} mod b1 == {0, 1, ..., b1-1}
    let a1 = a1 as int;
    let b1 = b1 as int;
    let f = |k: nat| ((k * a1) % b1) as nat;
    let dom = set_nat_range(0, b1 as nat);
    let img = dom.map(f);
    lemma_nat_range(0, b1 as nat);
    assert(injective_on(f, dom)) by {
        assert forall |x1: nat, x2: nat| 
            dom.contains(x1) && dom.contains(x2) && #[trigger] f(x1) == #[trigger] f(x2)
        implies 
            x1 == x2
        by {
            assert_by_contradiction!(x1 == x2, {
                let (x1, x2) = (max(x1 as int, x2 as int), min(x1 as int, x2 as int));
                assert(0 < x1 - x2 < b1);
                assert(x1 * a1 - x2 * a1 == a1 * (x1 - x2)) by {
                    assert(x1 * a1 - x2 * a1  == (x1 - x2) * a1) by (nonlinear_arith);
                    assert((x1 - x2) * a1 == a1 * (x1 - x2)) by (nonlinear_arith);
                }
                assert(is_factor_of((x1 - x2) as nat, b1 as nat)) by {
                    lemma_mod_equivalence((x1 * a1) as int, (x2 * a1) as int, b1 as int);
                    axiom_is_coprime(a1 as nat, b1 as nat);
                    lemma_coprime_factor(b1 as nat, a1 as nat, (x1 - x2) as nat);
                }
                lemma_is_factor_bound((x1 - x2) as nat, b1 as nat);
                assert(x1 - x2 <= b1);
            });
        }
    }
    lemma_map_size(dom, img, f);
    assert(img.subset_of(dom)) by {
        assert forall|y: nat| img.contains(y)
        implies dom.contains(y)
        by {
            let x = choose|x: nat| dom.contains(x) && y == f(x);
            assert(y == (x * a1) % b1);
            lemma_mod_bound((x * a1) as int, b1 as int);
        }
    }
    lemma_subset_equality(img, dom);

    // ..avoids blow-up
    util::lemma_bezout_identity_epilogue1(a1, b1, d as int);
    util::lemma_bezout_identity_epilogue2(a1, b1, d as int);
}

/// Proof of more properties about the Bezout identity. Specifically, for any 
/// `a > 0`, `b > 0`, and `m` such that `(a, b) | m`, `ax + by = m` as a *unique* 
/// solution such that `0 <= x < b / (a, b)`.
pub proof fn lemma_bezout_identity_ext(a: nat, b: nat, m: int)
    requires
        a > 0 && b > 0,
        m % (gcd(a, b) as int) == 0,
    ensures 
        exists|x: int, y: int| 0 <= x < b / gcd(a, b) && #[trigger] (a * x + b * y) == m,
        !exists|x1: int, y1: int, x2: int, y2: int| 
            0 <= x1 < x2 < b / gcd(a, b)
            && #[trigger] (a * x1 + b * y1) == m
            && #[trigger] (a * x2 + b * y2) == m,
{
    util::lemma_bezout_identity_ext1(a, b, m);
    util::lemma_bezout_identity_ext2(a, b, m);
}

/// Proof that all positive natural numbers are either prime, composite, or 1.
pub proof fn lemma_prime_or_composite(n: nat)
    requires n > 0,
    ensures n == 1 || is_prime(n) || is_composite(n),
{
    axiom_prime_not_composite(n);
}

/// Proof that 2 is the minimal prime.
pub proof fn lemma_prime_minimal()
    ensures
        is_prime(2),
        forall|p: nat| #[trigger] is_prime(p) ==> p >= 2,
{
    assert(is_prime(2)) by {
        assert forall|d: nat| is_factor_of(2, d)
        implies d == 1 || d == 2
        by { lemma_is_factor_bound(2, d); };
    };
}

/// Proof that there are infinitely many primes.
pub proof fn lemma_prime_infinite() 
    ensures
        !Set::<nat>::new(|n: nat| is_prime(n)).finite(),
{
    let all_primes = Set::<nat>::new(|n: nat| is_prime(n));
    assert_by_contradiction!(!all_primes.finite(), {
        let f = |prod: nat, p: nat| prod * p;
        let n = all_primes.fold(1, f) + 1;
        
        // n >= 1 by Induction
        let pred = |s: Set<nat>| s.subset_of(all_primes) ==> s.fold(1, f) >= 1;
        assert forall|a1, a2, b| #[trigger] f(f(b, a2), a1) == f(f(b, a1), a2)
        by { // is_fun_commutative(f)
            lemma_mul_is_associative(b as int, a2 as int, a1 as int);
            lemma_mul_is_commutative(a1 as int, a2 as int);
            lemma_mul_is_associative(b as int, a1 as int, a2 as int);
        };
        assert(pred(Set::<nat>::empty())) by { lemma_fold_empty(1, f); };
        assert forall |s, a| pred(s) && s.finite() && !s.contains(a) 
        implies #[trigger] pred(s.insert(a)) 
        by {
            if !s.subset_of(all_primes) || !all_primes.contains(a) {
                // ..bad case
            } else {
                lemma_fold_insert(s, 1, f, a);
                assert(f(s.fold(1, f), a) == s.fold(1, f) * a);
                lemma_mul_strictly_positive(s.fold(1, f) as int, a as int);
                assert(s.insert(a).fold(1, f) >= 1);
            }
        };
        assert(n >= 2) by { lemma_finite_set_induct(all_primes, pred); };

        assert_by_contradiction!(is_prime(n), {
            assert(is_composite(n)) by { lemma_prime_or_composite(n); };
            lemma_prime_factor_exists(n);
            let p = choose|p: nat| #[trigger] is_prime(p) && is_factor_of(n, p);
            assert(all_primes.contains(p));
            assert(is_factor_of((n - 1) as nat, p)) by {
                let other_primes = all_primes.remove(p);
                let k = other_primes.fold(1, f);
                lemma_fold_insert(other_primes, 1, f, p);
                assert((n - 1) as nat == k * p);
                lemma_is_factor_lincomb(p, k as int, 0, 0, p);
                lemma_mul_is_commutative(k as int, p as int);
            };
            assert(is_factor_of(1, p)) by {
                lemma_is_factor_lincomb(n, 1, (n - 1) as nat, -1, p);
            }
            lemma_is_factor_bound(1, p);
        });

        // Famous contradiction
        assert(forall|p: nat| is_prime(p) ==> #[trigger] all_primes.contains(p));
        assert_by_contradiction!(!all_primes.contains(n), {
            let other_primes = all_primes.remove(n);
            let k = other_primes.fold(1, f);
            lemma_fold_insert(other_primes, 1, f, n);
            assert((n - 1) as nat == k * n);
            assert(k * n >= n) by { 
                lemma_finite_set_induct(other_primes, pred); 
                lemma_mul_ordering(k as int, n as int);
            };
        });
    });
}

/// Proof that every `n > 1` has a prime factor.
pub proof fn lemma_prime_factor_exists(n: nat)
    requires n > 1,
    ensures !prime_factors(n).is_empty(),
    decreases n - 2,
{
    if n == 2 {
        assert(is_factor_of(2, 2));
        assert(is_prime(2)) by { lemma_prime_minimal() };
        assert(prime_factors(2).contains(2));
    } else {
        lemma_prime_or_composite(n);
        if is_prime(n) {
            assert(is_factor_of(n, n));
            assert(prime_factors(n).contains(n));
        } else {
            let (n1, n2) = choose|a: nat, b: nat| 1 < a < n && 1 < b < n && #[trigger] (a * b) == n;
            assert(is_factor_of(n, n2)) by { broadcast use lemma_mod_multiples_basic; }
            lemma_prime_factor_exists(n2);
            let p = choose|p: nat| #[trigger] is_prime(p) && is_factor_of(n2, p);
            lemma_is_factor_transitive(p, n2, n);
            assert(prime_factors(n).contains(p));
        }
    }
}

/// Proof that `1` has no prime factors.
pub proof fn lemma_prime_factors_one() 
    ensures prime_factors(1).is_empty(),
{
    assert_by_contradiction!(forall|p: nat| !prime_factors(1).contains(p), {
        let p = choose|p: nat| prime_factors(1).contains(p);
        lemma_is_factor_bound(1, p);
        lemma_prime_minimal();
    });
}

/// Proof that the only prime factor of a prime `p` is `p`.
pub proof fn lemma_prime_factors_prime(p: nat) 
    requires is_prime(p),
    ensures prime_factors(p) =~= set!{p},
{
    let set1 = prime_factors(p);
    let set2 = set!{p};
    assert_sets_equal!(set1 == set2, d => {
        if set2.contains(d) {
            assert(d == p);
            assert(set1.contains(p));
        }
        if set1.contains(d) {
            lemma_prime_minimal();
            assert(d == p);
            assert(set2.contains(p));
        }
    });
}

/// Proof that the only prime factor of a power of prime `p` is `p`.
pub proof fn lemma_prime_factors_prime_pow(p: nat, e: nat) 
    requires 
        is_prime(p),
        e > 0,
    ensures
        prime_factors(pow(p as int, e) as nat) =~= set!{p},
    decreases e,
{
    if e == 1 {
        lemma_pow1(p as int);
        lemma_prime_factors_prime(p);
    } else {
        reveal(pow);
        calc!{
            (==)
            pow(p as int, e); {}
            p * pow(p as int, (e - 1) as nat); { broadcast use lemma_mul_is_commutative; }
            pow(p as int, (e - 1) as nat) * p;
        }
        lemma_prime_factors_prime_pow(p, (e - 1) as nat);

        assert_sets_equal!(prime_factors(pow(p as int, e) as nat) == set!{p}, p0 => {
            if set!{p}.contains(p0) {
                assert(p0 == p);
                assert(is_factor_of(pow(p as int, e) as nat, p)) by { 
                    lemma_pow_positive(p as int, e);
                    lemma_pow_mod(p, e);
                }
            }
            if prime_factors(pow(p as int, e) as nat).contains(p0) {
                assert_by_contradiction!(p0 == p, {
                    assert(
                        is_factor_of(pow(p as int, (e - 1) as nat) as nat, p0) || is_factor_of(p, p0)
                    ) by {
                        lemma_pow_positive(p as int, e);
                        lemma_pow_positive(p as int, (e - 1) as nat);
                        assert(is_factor_of((pow(p as int, (e - 1) as nat) as nat) * p, p0));
                        axiom_prime_mul_union(p0);
                    }
                    if is_factor_of(p, p0) { assert(p == p0); }
                    else { 
                        assert(is_factor_of(pow(p as int, (e - 1) as nat) as nat, p0));
                        assert(set!{p}.contains(p0));
                    }
                });
            }
        });
    }
}

/// Proof that the prime factors of `n` is bounded.
pub proof fn lemma_prime_factors_bound(n: nat) 
    requires n > 0,
    ensures
        forall|p: nat| prime_factors(n).contains(p) ==> 2 <= p <= n,
        prime_factors(n).finite(),
{
    let ps = prime_factors(n);
    let range = set_nat_range(2, n + 1);
    assert(ps.subset_of(range)) by {
        assert forall|p: nat| ps.contains(p) 
        implies range.contains(p) 
        by {
            lemma_is_factor_bound(n, p);
            lemma_prime_minimal();
        }
    }
    lemma_nat_range(2, n + 1);
}

/// Proof that if `d | n`, then the set of prime factors of `d` is the subset of that of `n`.
pub proof fn lemma_prime_factors_is_factor_subset(n: nat, d: nat)
    requires n > 0 && d > 0 && is_factor_of(n, d),
    ensures prime_factors(d).subset_of(prime_factors(n))
{
    assert forall|p: nat| prime_factors(d).contains(p) 
    implies prime_factors(n).contains(p)
    by {
        lemma_is_factor_transitive(p, d, n);
    }
}

/// Proof that the prime factors of `(a, b)` is the intersection of the prime factors 
/// of `a` and the prime factors of `b`.
pub proof fn lemma_prime_factors_gcd_intersect(a: nat, b: nat)
    requires a > 0 && b > 0,
    ensures prime_factors(gcd(a, b)) =~= prime_factors(a) * prime_factors(b),
{
    let d = gcd(a, b);
    axiom_gcd_properties(a, b);

    assert(prime_factors(d).subset_of(prime_factors(a) * prime_factors(b))) by {
        lemma_prime_factors_is_factor_subset(a, d);
        lemma_prime_factors_is_factor_subset(b, d);
    }
    assert((prime_factors(a) * prime_factors(b)).subset_of(prime_factors(d))) by {
        assert forall|p: nat| prime_factors(a).contains(p) && prime_factors(b).contains(p)
        implies prime_factors(d).contains(p)
        by {
            lemma_bezout_identity(a, b, d);
            let (x, y) = choose|x: int, y: int| 0 <= x < b / d && #[trigger] (a * x + b * y) == d;
            lemma_is_factor_lincomb(a, x, b, y, p);
        }
    }
}

/// Proof that the prime factors of `[a, b]` is the union of the prime factors 
/// of `a` and the prime factors of `b`.
pub proof fn lemma_prime_factors_lcm_union(a: nat, b: nat)
    requires a > 0 && b > 0,
    ensures prime_factors(lcm(a, b)) =~= prime_factors(a) + prime_factors(b),
{
    let m = lcm(a, b);
    axiom_lcm_properties(a, b);

    assert((prime_factors(a) + prime_factors(b)).subset_of(prime_factors(m))) by {
        lemma_prime_factors_is_factor_subset(m, a);
        lemma_prime_factors_is_factor_subset(m, b);
    }
    assert(prime_factors(m).subset_of(prime_factors(a) + prime_factors(b))) by {
        assert forall|p: nat| prime_factors(m).contains(p)
        implies prime_factors(a).contains(p) || prime_factors(b).contains(p)
        by {
            assert(is_factor_of(a * b, m)) by { 
                assert(is_factor_of(a * b, b)) by { broadcast use lemma_mod_multiples_basic; }
                assert(is_factor_of(b * a, a)) by { broadcast use lemma_mod_multiples_basic; }
                assert(a * b == b * a);
                lemma_lcm_is_factor(a, b, a * b);
            }
            lemma_is_factor_transitive(p, m, a * b);
            axiom_prime_mul_union(p);
            assert(is_factor_of(a, p) || is_factor_of(b, p));
        }
    }
}

/// Proof that the prime factors of `a` and the prime factors of `b` are disjoint
/// iff they are coprime.
pub proof fn lemma_prime_factors_disjoint_iff_coprime(a: nat, b: nat)
    requires a > 0 && b > 0,
    ensures prime_factors(a).disjoint(prime_factors(b)) <==> is_coprime(a, b),
{
    // ..the not so obvious step
    assert forall|n: nat| n > 0 && #[trigger] prime_factors(n).is_empty()
    implies n == 1
    by { 
        assert_by_contradiction!(n == 1, {
            lemma_prime_factor_exists(n);
        });
    }
    
    calc!{
        (<==>)
        is_coprime(a, b); { axiom_coprime_gcd(a, b); }
        gcd(a, b) == 1; {
            axiom_gcd_properties(a, b);
            assert(prime_factors(gcd(a, b)).is_empty() ==> gcd(a, b) == 1);
            lemma_prime_factors_one();
        }
        prime_factors(gcd(a, b)).is_empty(); { lemma_prime_factors_gcd_intersect(a, b); }
        (prime_factors(a) * prime_factors(b)).is_empty(); { 
            lemma_disjoint_iff_empty_intersection(prime_factors(a), prime_factors(b));
        }
        prime_factors(a).disjoint(prime_factors(b));
    }
}

/// Proof of induction over factorization of `n`. 
/// Specifically, if `g(a * b) == g(a) * g(b)` when `a` and `b` are coprime, then
/// `g(n) = prime_factors(n).fold(g(1), x g(pow(p, vp(n, p))))`. 
pub proof fn lemma_factorization_induct(n: nat, g: spec_fn(nat) -> nat) 
    requires
        n > 0,
        forall|a: nat, b: nat| #[trigger] is_coprime(a, b) ==> g(a * b) == g(a) * g(b),
    ensures
        g(n) == prime_factors(n).fold(g(1), |prod: nat, p: nat| prod * g((pow(p as int, vp(n, p)) as nat))),
    decreases n,
{
    let f = |prod: nat, p: nat| prod * g((pow(p as int, vp(n, p)) as nat));
    lemma_factorization_fun_comm(n, g);

    if n == 1 {
        lemma_prime_factors_one();
        lemma_fold_empty(g(1), f);
    } else {
        lemma_prime_factor_exists(n);
        let p = prime_factors(n).choose();
        let e = vp(n, p);
        axiom_vp_properties(n, p);
        let p_to_e = pow(p as int, e) as nat;
        assert(e >= 1 && 1 < p_to_e <= n) by {
            assert(e >= 1) by { assert(is_factor_of(n, p)); }
            assert(p_to_e >= p) by { 
                lemma_pow_increases(p, 1, e); 
                lemma_pow1(p as int);
            }
            lemma_is_factor_bound(n, p_to_e);
        }

        // ..induction step
        let n1 = n / p_to_e;
        let f1 = |prod: nat, p: nat| prod * g((pow(p as int, vp(n1, p)) as nat));
        assert(n == p_to_e * n1 + 0) by { lemma_fundamental_div_mod(n as int, p_to_e as int); }
        assert(0 < n1 < n) by {
            lemma_div_non_zero(n as int, p_to_e as int);
            lemma_mul_strict_inequality(1, p_to_e as int, n1 as int);
            lemma_mul_strict_inequality_converse(1, p_to_e as int, n1 as int);
        }
        lemma_factorization_fun_comm(n1, g);
        
        assert(g(n1) == prime_factors(n1).fold(g(1), f1)) by {
            lemma_factorization_induct(n1, g);
        }

        // Goals: 
        // (1) prime_factors(n1).insert(p) == prime_factors(n)
        // (2) prime_factors(n1).fold(g(1), f1) == prime_factors(n1).fold(g(1), f)
        assert(!is_factor_of(n1, p));
        assert(prime_factors(n1).insert(p) == prime_factors(n)) by {
            let set1 = prime_factors(n1).insert(p);
            let set2 = prime_factors(n);
            assert(set1.subset_of(set2)) by {
                assert forall|p0: nat| set1.contains(p0)
                implies set2.contains(p0)
                by {
                    if p0 == p {}
                    else {
                        assert(is_factor_of(n1, p0));
                        assert(is_factor_of(n, n1)) by { broadcast use lemma_mod_multiples_basic; }
                        lemma_is_factor_transitive(p0, n1, n);
                    }
                }
            }
            assert(set2.subset_of(set1)) by {
                assert forall|p0: nat| set2.contains(p0)
                implies set1.contains(p0)
                by {
                    assert(is_factor_of(p_to_e, p0) || is_factor_of(n1, p0)) by {
                        assert(is_factor_of(n1 * p_to_e, p0));
                        axiom_prime_mul_union(p0);
                    }
                    if is_factor_of(p_to_e, p0) {
                        lemma_prime_factors_prime_pow(p, e);
                        assert(p0 == p) by {
                            assert(prime_factors(p_to_e).contains(p0));
                        }
                        assert(set1.contains(p0));
                    }
                    if is_factor_of(n1, p0) {
                        assert(is_factor_of(n, n1)) by {
                            assert(n == p_to_e * n1);
                            lemma_mod_multiples_basic(p_to_e as int, n1 as int);
                        }
                        lemma_is_factor_transitive(p0, n1, n);
                        assert(set1.contains(p0));
                    }
                }
            }
        } // ..(1)

        assert(prime_factors(n1).fold(g(1), f1) == prime_factors(n1).fold(g(1), f)) by {
            assert(is_factor_of(n, n1)) by { lemma_mod_multiples_basic(p_to_e as int, n1 as int); }
            lemma_factorization_fun_fold(n, p, n1, prime_factors(n1), g);
        } // ..(2)
        
        // ..and we are done!
        calc!{
            (==)
            g(n); {}
            g(p_to_e * n1); { broadcast use lemma_mul_is_commutative; }
            g(n1 * p_to_e); {
                assert(prime_factors(p_to_e) == set!{p}) by { lemma_prime_factors_prime_pow(p, e); }
                assert(prime_factors(n1).disjoint(set!{p}));
                lemma_prime_factors_disjoint_iff_coprime(n1, p_to_e);
                assert(is_coprime(n1, p_to_e));
            }
            g(n1) * g(p_to_e); {}
            prime_factors(n1).fold(g(1), f1) * g(p_to_e); {}
            prime_factors(n1).fold(g(1), f) * g(p_to_e); {}
            f(prime_factors(n1).fold(g(1), f), p); { 
                lemma_prime_factors_bound(n1);
                lemma_fold_insert(prime_factors(n1), g(1), f, p);
            }
            prime_factors(n1).insert(p).fold(g(1), f); {}
            prime_factors(n).fold(g(1), f);
        }
    }
}

proof fn lemma_factorization_fun_comm(n: nat, g: spec_fn(nat) -> nat)
    requires n > 0,
    ensures
        ({
            let f = |prod: nat, p: nat| prod * g((pow(p as int, vp(n, p)) as nat));
            is_fun_commutative(f)
        })
{
    let f = |prod: nat, p: nat| prod * g((pow(p as int, vp(n, p)) as nat));
    assert forall |a1: nat, a2: nat, b: nat| #[trigger] f(f(b, a2), a1) == f(f(b, a1), a2) 
    by {
        let g1 = g(pow(a1 as int, vp(n, a1)) as nat);
        let g2 = g(pow(a2 as int, vp(n, a2)) as nat);
        calc!{
            (==)
            f(f(b, a1), a2); {}
            b * g1 * g2; { broadcast use lemma_mul_is_associative; }
            b * (g1 * g2); { broadcast use lemma_mul_is_commutative; }
            b * (g2 * g1); { broadcast use lemma_mul_is_associative; }
            b * g2 * g1; {}
            f(f(b, a2), a1);
        }
    }
}

proof fn lemma_factorization_fun_fold(n: nat, p: nat, n1: nat, ps: Set<nat>, g: spec_fn(nat) -> nat) 
    requires
        is_prime(p),
        n > 0,
        vp(n, p) > 0,
        n == pow(p as int, vp(n, p)) as nat * n1,
        is_factor_of(n, n1),
        !is_factor_of(n1, p),
        ps.subset_of(prime_factors(n1)),
    ensures
        ({
            let f = |prod: nat, p: nat| prod * g((pow(p as int, vp(n, p)) as nat));
            let f1 = |prod: nat, p: nat| prod * g((pow(p as int, vp(n1, p)) as nat));
            ps.fold(g(1), f1) == ps.fold(g(1), f)
        })
    decreases ps.len(),
{
    let f = |prod: nat, p: nat| prod * g((pow(p as int, vp(n, p)) as nat));
    let f1 = |prod: nat, p: nat| prod * g((pow(p as int, vp(n1, p)) as nat));
    
    lemma_prime_factors_bound(n1);
    assert(ps.finite());

    if ps.is_empty() {
        // ..base
        lemma_fold_empty(g(1), f);
        lemma_fold_empty(g(1), f1);
    } else {
        // ..induct
        let p0 = ps.choose();
        let z = ps.remove(p0).fold(g(1), f);
        let z1 = ps.remove(p0).fold(g(1), f1);
       
        assert(f(z, p0) == f1(z1, p0)) by {
            assert(z == z1) by {
                lemma_factorization_fun_fold(n, p, n1, ps.remove(p0), g);
            }
            assert(vp(n, p0) == vp(n1, p0)) by {
                assert(p0 != p) by {
                    assert(!prime_factors(n1).contains(p));
                }
                assert(is_factor_of(n, p0)) by {
                    lemma_is_factor_transitive(p0, n1, n);
                }

                let e = vp(n, p0);
                let e1 = vp(n1, p0);
                axiom_vp_properties(n, p0);
                axiom_vp_properties(n1, p0);
                assert(e >= 1) by { assert(is_factor_of(n, p0)); }
                assert(e1 >= 1) by { assert(is_factor_of(n1, p0)); }

                assert(e1 <= e) by {
                    let p0_to_e1 = pow(p0 as int, e1) as nat;
                    assert(is_factor_of(n, p0_to_e1)) by {
                        lemma_is_factor_transitive(p0_to_e1, n1, n);
                    }
                }
                assert(e <= e1) by {
                    let p0_to_e = pow(p0 as int, e) as nat;
                    let p_exp = pow(p as int, vp(n, p)) as nat;
                    lemma_pow_positive(p0 as int, e);
                    lemma_pow_positive(p as int, vp(n, p));
                    assert(is_factor_of(n1, p0_to_e)) by {
                        assert(is_coprime(p0_to_e, p_exp)) by {
                            assert(prime_factors(p0_to_e) == set!{p0}) by { lemma_prime_factors_prime_pow(p0, e); }
                            assert(prime_factors(p_exp) == set!{p}) by { lemma_prime_factors_prime_pow(p, vp(n, p)); }
                            lemma_prime_factors_disjoint_iff_coprime(p0_to_e, p_exp);
                        }
                        lemma_coprime_factor(p0_to_e, p_exp, n1);
                    }
                }
            }
            assert(pow(p0 as int, vp(n, p0)) == pow(p0 as int, vp(n1, p0)));
            assert(f(z, p0) == f1(z1, p0));
        }
        lemma_factorization_fun_comm(n, g);
        lemma_factorization_fun_comm(n1, g);
        lemma_fold_insert(ps.remove(p0), g(1), f, p0);
        lemma_fold_insert(ps.remove(p0), g(1), f1, p0);
    }
}

/// Proof of the fundamental principle of arithmetics, or the factorization
/// of positive integer `n`.
pub proof fn lemma_factorization(n: nat) 
    requires
        n > 0,
    ensures
        n == prime_factors(n).fold(1, |prod: nat, p: nat| prod * (pow(p as int, vp(n, p)) as nat)),
{
    let id = |x: nat| x;
    lemma_factorization_induct(n, id);
    assert(id(1) == 1);

    let fold_fn = |g: spec_fn(nat) -> nat| {
        |prod: nat, p: nat| prod * g((pow(p as int, vp(n, p)) as nat))
    };
    let trivial_fn = |prod: nat, p: nat| prod * (pow(p as int, vp(n, p)) as nat);
    assert(fold_fn(id) == trivial_fn);
}

} // verus!