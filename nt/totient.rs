//! Proofs and specifications for the [Euler's totient function](https://en.wikipedia.org/wiki/Euler%27s_totient_function), 
//! also denoted as `phi(n)`.

use super::{
    set_nat_range, is_factor_of, is_common_factor, is_coprime, is_prime, prime_factors, vp, gcd,
    axiom_prime_mul_union, axiom_coprime_gcd, axiom_gcd_properties, axiom_vp_properties,
    lemma_nat_range, lemma_is_factor_bound, lemma_is_factor_lincomb, lemma_is_factor_transitive, 
    lemma_coprime_factor, 
    lemma_prime_factor_exists, lemma_prime_factors_bound, lemma_prime_factors_one, 
    lemma_prime_factors_prime, lemma_prime_factors_prime_pow,
    lemma_prime_factors_disjoint_iff_coprime, 
    lemma_bezout_identity_ext, lemma_factorization,
};
use crate::cart::{
    cart, lemma_cart_len, lemma_cart_intersect,
};

use vstd::prelude::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power::*;
use vstd::set::*;
use vstd::set::fold::*;
use vstd::set_lib::*;
use vstd::math::{min, max};
use vstd::{assert_by_contradiction, calc};
use vstd::relations::injective_on;

verus! {

/// This function defines the prime numbers in range [lo, hi).
pub open spec fn set_prime_range(lo: nat, hi: nat) -> Set<nat> {
    Set::<nat>::new(|p: nat| is_prime(p) && lo <= p < hi)
}

closed spec fn coprime_set(n: nat) -> Set<nat> {
    set_nat_range(1, n + 1).filter(|m: nat| is_coprime(n, m))
}

closed spec fn noncoprime_set(n: nat) -> Set<nat> {
    set_nat_range(1, n + 1).filter(|m: nat| !is_coprime(n, m))
}

proof fn axiom_coprime_set(n: nat)
    requires n > 0,
    ensures 
        #[trigger] coprime_set(n).finite(),
        #[trigger] noncoprime_set(n).finite(),
        #[trigger] coprime_set(n).len() == n - noncoprime_set(n).len(),
{
    lemma_nat_range(1, n + 1);
    let s1 = coprime_set(n);
    let s2 = noncoprime_set(n);
    assert(s1 + s2 == set_nat_range(1, n + 1));
    assert(s1 * s2 == Set::<nat>::empty());
    lemma_set_intersect_union_lens(s1, s2);
}

/// This function defines the totient function `phi(n)`, which computes
/// the number of integers in `1..=n` that is coprime with `n`,
pub closed spec fn totient(n: nat) -> nat {
    coprime_set(n).len()
}

/// Proof that `1 <= phi(n) <= n-1` for `n > 1`.
pub proof fn lemma_totient_bound(n: nat)
    requires n > 1,
    ensures 1 <= totient(n) <= (n - 1) as nat,
{
    axiom_coprime_set(n);
    assert(totient(n) >= 1) by {
        let m = (n - 1) as nat;
        assert_by_contradiction!(is_coprime(n, m), {
            let d = choose|d: nat| d > 1 && #[trigger] is_common_factor(n, m, d);
            assert(is_factor_of(1, d)) by {
                lemma_is_factor_lincomb(n, 1, m, -1, d);
            }
            lemma_is_factor_bound(1, d);
        });
        assert(coprime_set(n).contains(m));
        lemma_set_empty_equivalency_len(coprime_set(n));
    }
    assert(totient(n) <= n - 1) by {
        assert(noncoprime_set(n).contains(n)) by {
            assert(is_common_factor(n, n, n));
        }
    }
}

/// Proof that `phi(0) = 0`.
pub proof fn lemma_totient_zero()
    ensures totient(0) == 0,
{
    lemma_nat_range(1, 1);
    assert(coprime_set(0).is_empty());
}

/// Proof that `phi(1) = 1`.
pub proof fn lemma_totient_one()
    ensures totient(1) == 1,
{
    assert(set_nat_range(1, 2) == set!{1nat});
    assert(coprime_set(1).subset_of(set_nat_range(1,2)));
    assert(set!{1nat}.subset_of(coprime_set(1))) by {
        assert_by_contradiction!(is_coprime(1, 1), {
            let d = choose|d: nat| d > 1 && #[trigger] is_common_factor(1, 1, d);
            lemma_is_factor_bound(1, d);
        });
    }
    assert(coprime_set(1) == set!{1nat});
}

/// Proof that `phi(p) = p - 1`.
pub proof fn lemma_totient_prime(p: nat)
    requires is_prime(p),
    ensures totient(p) == p - 1,
{
    axiom_coprime_set(p);
    assert_sets_equal!(noncoprime_set(p) == set!{p}, m => {
        assert forall|m: nat| noncoprime_set(p).contains(m) 
        implies m == p 
        by {
            assert_by_contradiction!(m == p, {
                assert(m < p);
                let d = choose|d: nat| d > 1 && #[trigger] is_common_factor(p, m, d);
                lemma_is_factor_bound(m, d);
            });
        }
        assert(noncoprime_set(p).contains(p)) by {
            assert(is_common_factor(p, p, p));
        }
    }); 
}

/// Proof that `phi(p^e) = (p - 1) * p^(e-1)`.
pub proof fn lemma_totient_prime_pow(p: nat, e: nat)
    requires 
        e > 0,
        is_prime(p),
    ensures 
        totient(pow(p as int, e) as nat) == ((p - 1) * pow(p as int, (e - 1) as nat)) as nat,
{
    let n = pow(p as int, e) as nat;
    let n1 = pow(p as int, (e - 1) as nat) as nat;
    let r1 = set_nat_range(1, n1 + 1);
    let r1p = r1.map(|m: nat| p * m);

    // Basic properties
    lemma_nat_range(1, n1 + 1);
    lemma_pow_positive(p as int, (e - 1) as nat);
    lemma_pow_positive(p as int, e);
    assert(n == p * n1) by { reveal(pow); }
    assert(n1 * p == n) by { broadcast use lemma_mul_is_commutative; }

    assert(r1p.finite() && r1p.len() == n1) by {
        let f = |m: nat| p * m;
        assert(injective_on(f, r1)) by {
            assert forall |x1: nat, x2: nat| 
                r1.contains(x1) && r1.contains(x2) && #[trigger] f(x1) == #[trigger] f(x2)
            implies
                x1 == x2
            by {
               lemma_mul_equality_converse(p as int, x1 as int, x2 as int);
            }
        };
        lemma_map_size(r1, r1p, f);
    }

    assert_sets_equal!(noncoprime_set(n) == r1p, m => {
        // ==>
        if noncoprime_set(n).contains(m) {
            assert(1 <= m <= n) by { lemma_nat_range(1, n + 1); }

            let d = choose|d: nat| d > 1 && #[trigger] is_common_factor(n, m, d);
            lemma_prime_factor_exists(d);
            let p0 = prime_factors(d).choose();
            assert(p0 == p) by {
                lemma_prime_factors_prime_pow(p, e);
                lemma_is_factor_transitive(p0, d, n);
                assert(prime_factors(n).contains(p0));
            }
            assert(is_factor_of(m, p)) by {
                lemma_is_factor_transitive(p, d, m);
            }
            assert(r1p.contains(m)) by {
                let m1 = m / p;
                assert(m == p * m1 + 0) by { broadcast use lemma_fundamental_div_mod; }
                assert_by_contradiction!(r1.contains(m1), {
                    if m1 == 0 {
                        assert(m == 0) by { broadcast use group_mul_basics; }
                    } else {
                        assert(m1 > n1);
                        assert(m > n) by {
                            assert(m1 * p == m) by { broadcast use lemma_mul_is_commutative; }
                            lemma_mul_strict_inequality(n1 as int, m1 as int, p as int);
                        }
                    }
                });
            }
        }
        // <==
        if r1p.contains(m) {
            let m1 = choose|m1: nat| r1.contains(m1) && p * m1 == m;
            assert(is_factor_of(m, p)) by {
                assert(m == m1 * p) by { broadcast use lemma_mul_is_commutative; }
                lemma_mod_multiples_basic(m1 as int, p as int);
            }
            assert(noncoprime_set(n).contains(m)) by {
                assert(prime_factors(n).contains(p)) by {
                    lemma_prime_factors_prime_pow(p, e);
                }
                assert(is_common_factor(n, m, p));
                assert(0 < m) by { lemma_mul_strictly_positive(p as int, m1 as int); }
                assert(m <= n) by { lemma_mul_inequality(m1 as int, n1 as int, p as int); }
            }
        }
    });

    assert(totient(n) == (p - 1) * n1) by {
        axiom_coprime_set(n);
        lemma_mul_is_distributive_sub_other_way(n1 as int, p as int, 1);
    }
}

/// Proof that `phi(a * b) = phi(a) * phi(b)` if `a` and `b` are coprime.
pub proof fn lemma_totient_coprime_mul(a: nat, b: nat)
    requires 
        is_coprime(a, b),
    ensures 
        totient(a * b) == totient(a) * totient(b),
{
    if a == 1 {
        calc!{
            (==)
            totient(a * b); {}
            totient(1 * b); { broadcast use group_mul_basics; }
            totient(b); { broadcast use group_mul_basics; }
            1 * totient(b); { lemma_totient_one(); }
            totient(1) * totient(b);
        }
        return
    }
    if b == 1 {
        calc!{
            (==)
            totient(a * b); {}
            totient(a * 1); { broadcast use group_mul_basics; }
            totient(a); { broadcast use group_mul_basics; }
            totient(a) * 1; { lemma_totient_one(); }
            totient(a) * totient(1);
        }
        return
    }

    // Main Idea: [0, a * b] ~ [0, a) x [0, b) by `f`;
    // Thus the set `noncoprime(a * b)` can be dissected
    assert(a > 1 && b > 1);
    assert(a * b > 1) by { lemma_mul_increases(a as int, b as int); };

    let f = |m: nat| (m % a, m % b);
    let sa = set_nat_range(0, a);
    let sb = set_nat_range(0, b);
    assert(noncoprime_set(a).contains(a)) by { assert(is_common_factor(a, a, a)); }
    assert(noncoprime_set(b).contains(b)) by { assert(is_common_factor(b, b, b)); }
    assert(noncoprime_set(a * b).contains(a * b)) by { assert(is_common_factor(a * b, a * b, a * b)); }
    // ..unfortunately, have to tweak it a little bit
    let da = noncoprime_set(a).remove(a).insert(0);
    let db = noncoprime_set(b).remove(b).insert(0);

    let dom = noncoprime_set(a * b).remove(a * b).insert(0);
    let img = cart::<nat, nat>(da, sb) + cart::<nat, nat>(sa, db);

    // Step 1: noncoprime(a * b).map(f) == cart(da, sb) + cart(sa, db)
    assert(dom.map(f) == img) by { lemma_totient_coprime_mul_part1(a, b); }

    // Step 2: cart(da, sb) * cart(sa, db) == cart(sa, sb)
    assert(injective_on(f, dom)) by { lemma_totient_coprime_mul_part2(a, b); }
    
    // Step 3: cardinality
    axiom_coprime_set(a);
    axiom_coprime_set(b);
    axiom_coprime_set(a * b);
    calc!{
        (==)
        da.len(); {}
        noncoprime_set(a).len(); { axiom_coprime_set(a); }
        (a - totient(a)) as nat;
    }
    calc!{
        (==)
        db.len(); {}
        noncoprime_set(b).len(); { axiom_coprime_set(b); }
        (b - totient(b)) as nat;
    }

    lemma_nat_range(0, a);
    lemma_nat_range(0, b);
    lemma_cart_len(da, sb);
    lemma_cart_len(sa, db);
    calc!{
        (==)
        noncoprime_set(a * b).len() as int; {}
        dom.len() as int; { lemma_map_size(dom, img, f); }
        img.len() as int; {
            lemma_set_intersect_union_lens(cart::<nat, nat>(da, sb), cart::<nat, nat>(sa, db));
        }
        cart::<nat, nat>(da, sb).len() + cart::<nat, nat>(sa, db).len()
            - (cart::<nat, nat>(da, sb) * cart::<nat, nat>(sa, db)).len(); {
            lemma_cart_intersect(da, sb, sa, db);
            calc!{
                (==)
                cart::<nat, nat>(da, sb) * cart::<nat, nat>(sa, db); {}
                cart::<nat, nat>(da * sa, sb * db); {}
                cart::<nat, nat>(da, db);
            }
        }
        cart::<nat, nat>(da, sb).len() + cart::<nat, nat>(sa, db).len() 
            - cart::<nat, nat>(da, db).len(); {
            lemma_cart_len(da, db);
        }
        da.len() * sb.len() + sa.len() * db.len() - da.len() * db.len(); {}
        (a - totient(a)) * b + a * (b - totient(b)) - (a - totient(a)) * (b - totient(b)); {
            assert((a - totient(a)) * b == a * b - totient(a) * b) by { broadcast use lemma_mul_is_distributive_sub_other_way; }
            assert(a * (b - totient(b)) == a * b - a * totient(b)) by { broadcast use lemma_mul_is_distributive_sub; }
            calc!{
                (==)
                (a - totient(a)) * (b - totient(b)); { broadcast use lemma_mul_is_distributive_sub_other_way; }
                a * (b - totient(b)) - totient(a) * (b - totient(b)); { broadcast use lemma_mul_is_distributive_sub; }
                a * b - a * totient(b) - (totient(a) * b - totient(a) * totient(b)); {}
                a * b - a * totient(b) - totient(a) * b + totient(a) * totient(b);
            }
        }
        a * b - totient(a) * b + a * b - a * totient(b) 
            - (a * b - a * totient(b) - totient(a) * b + totient(a) * totient(b)); {}
        (a * b - totient(a) * totient(b)) as int;
    }
    assert(totient(a * b) == totient(a) * totient(b));
}

proof fn lemma_totient_coprime_mul_part1(a: nat, b: nat)
    requires 
        a > 1 && b > 1,
        a * b > 1,
        is_coprime(a, b),
    ensures 
        noncoprime_set(a * b).remove(a * b).insert(0).map(|m: nat| (m % a, m % b)) 
            == cart::<nat, nat>(noncoprime_set(a).remove(a).insert(0), set_nat_range(0, b)) 
                + cart::<nat, nat>(set_nat_range(0, a), noncoprime_set(b).remove(b).insert(0)),
{
    let f = |m: nat| (m % a, m % b);
    let sa = set_nat_range(0, a);
    let sb = set_nat_range(0, b);
    assert(noncoprime_set(a).contains(a)) by { assert(is_common_factor(a, a, a)); }
    assert(noncoprime_set(b).contains(b)) by { assert(is_common_factor(b, b, b)); }
    assert(noncoprime_set(a * b).contains(a * b)) by { assert(is_common_factor(a * b, a * b, a * b)); }
    let da = noncoprime_set(a).remove(a).insert(0);
    let db = noncoprime_set(b).remove(b).insert(0);

    let dom = noncoprime_set(a * b).remove(a * b).insert(0);
    let img = cart::<nat, nat>(da, sb) + cart::<nat, nat>(sa, db);
    assert_sets_equal!(dom.map(f) == img, pair => {
        if dom.map(f).contains(pair) {
            let x = choose|x: nat| #[trigger] dom.contains(x) && f(x) == pair;
            let ra = pair.0;
            let rb = pair.1;
            if x == 0 {
                assert(ra == 0 && rb == 0) by {
                    lemma_small_mod(x, a);
                    lemma_small_mod(x, b);
                };
                assert(img.contains(pair));
            } else {
                assert(!is_coprime(a * b, x));
                let d = choose|d: nat| d > 1 && #[trigger] is_common_factor(a * b, x, d);
                lemma_prime_factor_exists(d);
                let p = prime_factors(d).choose();
                assert(is_factor_of(x, p)) by { lemma_is_factor_transitive(p, d, x); }
                assert(is_factor_of(a * b, p)) by { lemma_is_factor_transitive(p, d, a * b); }
                assert(is_factor_of(a, p) || is_factor_of(b, p)) by { 
                    axiom_prime_mul_union(p); 
                }
                assert(0 <= ra < a) by { lemma_mod_bound(x as int, a as int); }
                assert(0 <= rb < b) by { lemma_mod_bound(x as int, b as int); }

                assert_by_contradiction!(!is_coprime(a, ra) || !is_coprime(b, rb), {
                    if is_factor_of(a, p) {
                        let a1 = a / p;
                        assert(a == p * a1 + 0) by { lemma_fundamental_div_mod(a as int, p as int); }
                        calc!{
                            (==)
                            0; {}
                            x % p; { lemma_fundamental_div_mod(x as int, a as int); }
                            (a * (x/a) + ra) % p; { 
                                calc!{
                                    (==)
                                    (a * (x/a)) % p; {}
                                    (p * a1 * (x/a)) % p; { lemma_mul_is_associative(p as int, a1 as int, (x/a) as int); }
                                    (p * (a1 * (x/a))) % p;  { lemma_mul_is_commutative(p as int, (a1 * (x/a)) as int); }
                                    (a1 * (x/a) * p) % p; { lemma_mod_multiples_basic((a1 * (x/a)) as int, p as int); }
                                    0;
                                }
                                assert(ra % p < p) by { lemma_mod_bound(ra as int, p as int); }
                                assert((a * (x/a) + ra) % p == ra % p) by {
                                    lemma_mod_adds((a * (x/a)) as int, ra as int, p as int); 
                                }
                            }
                            ra % p;
                        }
                        assert(is_common_factor(a, ra, p));
                    }
                    if is_factor_of(b, p) {
                        let b1 = b / p;
                        assert(b == p * b1 + 0) by { lemma_fundamental_div_mod(b as int, p as int); }
                        calc!{
                            (==)
                            0; {}
                            x % p; { lemma_fundamental_div_mod(x as int, b as int); }
                            (b * (x/b) + rb) % p; { 
                                calc!{
                                    (==)
                                    (b * (x/b)) % p; {}
                                    (p * b1 * (x/b)) % p; { lemma_mul_is_associative(p as int, b1 as int, (x/b) as int); }
                                    (p * (b1 * (x/b))) % p;  { lemma_mul_is_commutative(p as int, (b1 * (x/b)) as int); }
                                    (b1 * (x/b) * p) % p; { lemma_mod_multiples_basic((b1 * (x/b)) as int, p as int); }
                                    0;
                                }
                                assert(rb % p < p) by { lemma_mod_bound(rb as int, p as int); }
                                assert((b * (x/b) + rb) % p == rb % p) by {
                                    lemma_mod_adds((b * (x/b)) as int, rb as int, p as int); 
                                }
                            }
                            rb % p;
                        }
                        assert(is_common_factor(b, rb, p));
                    }
                });

                assert(
                    cart::<nat, nat>(da, sb).contains(pair) 
                    || cart::<nat, nat>(sa, db).contains(pair) 
                ) by {
                    assert(da.contains(ra) || db.contains(rb));
                    assert(sa.contains(ra) && sb.contains(rb));
                }
            }
        } // ==>

        let ra = pair.0 as int;
        let rb = pair.1 as int;
        axiom_coprime_gcd(a, b);
        axiom_gcd_properties(a, b);
        if cart::<nat, nat>(da, sb).contains(pair) {
            lemma_bezout_identity_ext(a, b, rb - ra);
            let (qa, qb) = choose|x: int, y: int| 0 <= x < b / 1 && #[trigger] (a * x + b * y) == rb - ra;
            let x = qa * a + ra;
            calc!{
                (==)
                x; {}
                qa * a + ra; { lemma_mul_is_commutative(qa, a as int); }
                a * qa + ra; {}
                (rb - ra - b * qb) + ra; {}
                rb - b * qb; {}
                -(b * qb) + rb; { lemma_mul_unary_negation(qb, b as int); }
                (-qb) * b + rb;
            }
            assert(x % (a as int) == ra) by { lemma_fundamental_div_mod_converse(x as int, a as int, qa, ra); }
            assert(x % (b as int) == rb) by { lemma_fundamental_div_mod_converse(x as int, b as int, -qb, rb); }
            assert(f(x as nat) == pair);

            assert(dom.contains(x as nat)) by {
                assert(x >= 0) by {
                    lemma_mul_inequality(0, qa, a as int);
                }
                calc!{
                    (<)
                    x; (==) {}
                    qa * a + ra; (<=) { lemma_mul_inequality(qa, (b - 1) as int, a as int); }
                    (b - 1) * a + ra; {}
                    (b - 1) * a + a; (==) { broadcast use group_mul_basics; }
                    (b - 1) * a + 1 * a; (==) { lemma_mul_is_distributive_add_other_way(a as int, (b - 1) as int, 1); }
                    (b - 1 + 1) * a; (==) {}
                    (b * a) as int; (==) { lemma_mul_is_commutative(b as int, a as int); }
                    (a * b) as int;
                }
                assert(!is_coprime(a * b, x as nat)) by {
                    assert(is_factor_of(a * b, a)) by {
                        lemma_mul_is_commutative(a as int, b as int);
                        lemma_mod_multiples_basic(b as int, a as int);
                    }
                    if ra == 0 {
                        assert(is_factor_of(x as nat, a)) by { lemma_mod_multiples_basic(qa, a as int); }
                        assert(is_common_factor(a * b, x as nat, a));
                    } else {
                        assert(noncoprime_set(a).contains(ra as nat));
                        let d = choose|d: nat| d > 1 && #[trigger] is_common_factor(a, ra as nat, d);
                        assert(is_factor_of(a * b, d)) by { lemma_is_factor_transitive(d, a, a * b); }
                        assert(is_factor_of(x as nat, d)) by {
                            calc!{
                                (==)
                                x; {}
                                qa * a + ra; { lemma_mul_is_commutative(qa, a as int); }
                                a * qa + ra; { broadcast use group_mul_basics; }
                                a * qa + ra * 1; 
                            }
                            lemma_is_factor_lincomb(a, qa, ra as nat, 1, d);
                        }
                        assert(is_common_factor(a * b, x as nat, d));
                    }
                }
            }
            assert(dom.map(f).contains(pair));
        } // <==(1)

        if cart::<nat, nat>(sa, db).contains(pair) {
            lemma_bezout_identity_ext(b, a, ra - rb);
            let (qb, qa) = choose|x: int, y: int| 0 <= x < a / 1 && #[trigger] (b * x + a * y) == ra - rb;
            let x = qb * b + rb;
            calc!{
                (==)
                x; {}
                qb * b + rb; { lemma_mul_is_commutative(qb, b as int); }
                b * qb + rb; {}
                (ra - rb - a * qa) + rb; {}
                ra - a * qa; {}
                -(a * qa) + ra; { 
                    calc!{
                        (==)
                        -(a * qa); { lemma_mul_is_commutative(a as int, qa); }
                        -(qa * a); { lemma_mul_unary_negation(qa, a as int); }
                        (-qa) * a;
                    }
                }
                (-qa) * a + ra;
            }
            assert(x % (a as int) == ra) by { lemma_fundamental_div_mod_converse(x as int, a as int, -qa, ra); }
            assert(x % (b as int) == rb) by { lemma_fundamental_div_mod_converse(x as int, b as int, qb, rb); }
            assert(f(x as nat) == pair);

            assert(dom.contains(x as nat)) by {
                assert(x >= 0) by {
                    lemma_mul_inequality(0, qb, b as int);
                }
                calc!{
                    (<)
                    x; (==) {}
                    qb * b + rb; (<=) { lemma_mul_inequality(qb, (a - 1) as int, b as int); }
                    (a - 1) * b + rb; {}
                    (a - 1) * b + b; (==) { broadcast use group_mul_basics; }
                    (a - 1) * b + 1 * b; (==) { lemma_mul_is_distributive_add_other_way(b as int, (a - 1) as int, 1); }
                    (a - 1 + 1) * b; (==) {}
                    (a * b) as int;
                }
                assert(!is_coprime(a * b, x as nat)) by {
                    assert(is_factor_of(a * b, b)) by {
                        lemma_mod_multiples_basic(a as int, b as int);
                    }
                    if rb == 0 {
                        assert(is_factor_of(x as nat, b)) by { lemma_mod_multiples_basic(qb, b as int); }
                        assert(is_common_factor(a * b, x as nat, b));
                    } else {
                        assert(noncoprime_set(b).contains(rb as nat));
                        let d = choose|d: nat| d > 1 && #[trigger] is_common_factor(b, rb as nat, d);
                        assert(is_factor_of(a * b, d)) by { lemma_is_factor_transitive(d, b, a * b); }
                        assert(is_factor_of(x as nat, d)) by {
                            calc!{
                                (==)
                                x; {}
                                qb * b + rb; { lemma_mul_is_commutative(qb, b as int); }
                                b * qb + rb; { broadcast use group_mul_basics; }
                                b * qb + rb * 1; 
                            }
                            lemma_is_factor_lincomb(b, qb, rb as nat, 1, d);
                        }
                        assert(is_common_factor(a * b, x as nat, d));
                    }
                }
            }
            assert(dom.map(f).contains(pair));
        } // <==(2)
    });
}

proof fn lemma_totient_coprime_mul_part2(a: nat, b: nat)
    requires 
        a > 1 && b > 1,
        a * b > 1,
        is_coprime(a, b),
    ensures 
        injective_on(|m: nat| (m % a, m % b), noncoprime_set(a * b).remove(a * b).insert(0)),
{
    let f = |m: nat| (m % a, m % b);
    let dom = set_nat_range(0, a * b); // widening the dom here
    lemma_nat_range(0, a * b);
    assert forall |x1: nat, x2: nat| 
        dom.contains(x1) && dom.contains(x2) && #[trigger] f(x1) == #[trigger] f(x2)
    implies
        x1 == x2
    by {
        assert_by_contradiction!(x1 == x2, {
            let (x1, x2) = (min(x1 as int, x2 as int), max(x1 as int, x2 as int));
            assert(0 <= x1 < x2 < a * b);

            let qa1 = x1 / (a as int);
            let ra1 = x1 % (a as int);
            assert(x1 == a * qa1 + ra1) by { lemma_fundamental_div_mod(x1 as int, a as int); }
            let qb1 = x1 / (b as int);
            let rb1 = x1 % (b as int); 
            assert(x1 == b * qb1 + rb1) by { lemma_fundamental_div_mod(x1 as int, b as int); }
            let qa2 = x2 / (a as int);
            let ra2 = x2 % (a as int); 
            assert(x2 == a * qa2 + ra2) by { lemma_fundamental_div_mod(x2 as int, a as int); }
            let qb2 = x2 / (b as int);
            let rb2 = x2 % (b as int); 
            assert(x2 == b * qb2 + rb2) by { lemma_fundamental_div_mod(x2 as int, b as int); 
            }
            assert(ra1 == ra2 && rb1 == rb2);
            assert(qa1 < qa2) by { 
                lemma_div_is_ordered(x1, x2, a as int); 
                assert_by_contradiction!(qa1 != qa2, { x1 == x2; });
            }
            assert(0 <= qa1 < b && 0 <= qa2 < b) by {
                lemma_div_pos_is_pos(x1, a as int);
                lemma_div_pos_is_pos(x2, a as int);
                assert(a * b == b * a) by { broadcast use lemma_mul_is_commutative; }
                assert((a * b) / a == b) by { broadcast use lemma_div_multiples_vanish; }
                lemma_div_by_multiple_is_strongly_ordered(x1, (a * b) as int, b as int, a as int);
                lemma_div_by_multiple_is_strongly_ordered(x2, (a * b) as int, b as int, a as int);
            }
            assert(0 < qa2 - qa1 < b);

            // a * (qa2 - qa1) + b * (qb1 - qb2) == rb2 - rb1 + ra1 - ra2 == 0
            calc!{
                (==)
                a * (qa2 - qa1) + b * (qb1 - qb2); { broadcast use lemma_mul_is_distributive_sub; }
                a * qa2 - a * qa1 + b * qb1 - b * qb2; {}
                (x2 - ra2) - (x1 - ra1) + (x1 - rb1) - (x2 - rb2); {}
                0;
            }
            // a * 0 + b * 0 == 0
            assert(a * 0 + b * 0 == 0) by { broadcast use group_mul_basics; }

            assert(gcd(a, b) == 1) by { axiom_coprime_gcd(a, b); }
            assert(0 <= 0 < qa2 - qa1 < b / gcd(a, b));
            lemma_bezout_identity_ext(a, b, 0); // contradiction to the uniqueness
        });
    }
}

/// Proof that `phi(n)` is computed via factorization of `n`.
pub proof fn lemma_totient_factorization(n: nat)
    requires 
        n > 0,
    ensures 
        totient(n) == prime_factors(n).fold(1, |prod: nat, p: nat| 
            prod * totient(pow(p as int, vp(n, p)) as nat)),
    decreases n,
{
    let f = |prod: nat, p: nat| prod * totient(pow(p as int, vp(n, p)) as nat);
    lemma_totient_factorization_fun_comm(n);
    if n == 1 {
        assert(prime_factors(n).is_empty()) by { lemma_prime_factors_one(); }
        assert(prime_factors(n).fold(1, f) == 1) by { lemma_fold_empty(1, f); }
        assert(totient(1) == 1) by { lemma_totient_one(); }
    } else {
        lemma_prime_factor_exists(n);
        lemma_prime_factors_bound(n);
        let p1 = prime_factors(n).choose();
        let ps = prime_factors(n).remove(p1);
        let e1 = vp(n, p1);
        let p1_to_e1 = pow(p1 as int, e1) as nat;
        axiom_vp_properties(n, p1);
        assert(e1 >= 1) by {
            lemma_pow1(p1 as int);
            assert(is_factor_of(n, pow(p1 as int, 1) as nat));
        }
        assert(prime_factors(p1_to_e1) == set!{p1}) by { lemma_prime_factors_prime_pow(p1, e1); }

        let n1 = n / p1_to_e1;
        assert(n == p1_to_e1 * n1 + 0) by { broadcast use lemma_fundamental_div_mod; }
        assert(0 < n1 < n) by { 
            lemma_is_factor_bound(n, p1_to_e1);
            lemma_div_non_zero(n as int, p1_to_e1 as int);
            assert(p1_to_e1 > 1) by {
                lemma_pow1(p1 as int);
                lemma_pow_increases(p1, 1, e1);
            }
            lemma_div_decreases(n as int, p1_to_e1 as int);
        }
        assert(is_factor_of(n, n1)) by { lemma_mod_multiples_basic(p1_to_e1 as int, n1 as int); }

        assert_sets_equal!(prime_factors(n1) == ps, p => {
            if prime_factors(n1).contains(p) {
                assert(is_factor_of(n, p)) by { lemma_is_factor_transitive(p, n1, n); }
                assert_by_contradiction!(p != p1, {
                    let n2 = n1 / p1;
                    assert(n1 == p1 * n2 + 0) by { broadcast use lemma_fundamental_div_mod; }
                    calc!{
                        (==)
                        n; {}
                        p1_to_e1 * n1; {}
                        p1_to_e1 * (p1 * n2); { broadcast use lemma_mul_is_associative; }
                        p1_to_e1 * p1 * n2; {}
                        pow(p1 as int, e1) as nat * p1 * n2; { 
                            lemma_mul_is_commutative(pow(p1 as int, e1), p1 as int); 
                        }
                        p1 * pow(p1 as int, e1) as nat * n2; { 
                            lemma_pow_positive(p1 as int, e1);
                            lemma_pow_positive(p1 as int, e1 + 1);
                            reveal(pow);
                            assert(p1 * pow(p1 as int, e1) as nat == pow(p1 as int, e1 + 1) as nat);
                        }
                        pow(p1 as int, e1 + 1) as nat * n2; { 
                            lemma_mul_is_commutative(pow(p1 as int, e1 + 1), n2 as int);
                        }
                        n2 * pow(p1 as int, e1 + 1) as nat;
                    }
                    assert(is_factor_of(n, pow(p1 as int, e1 + 1) as nat)) by {
                        lemma_pow_positive(p1 as int, e1 + 1);
                        lemma_mod_multiples_basic(n2 as int, pow(p1 as int, e1 + 1));
                    }
                });
                assert(prime_factors(n).contains(p));
            }
            if ps.contains(p) {
                assert(is_factor_of(n, p));
                assert(is_coprime(p, p1_to_e1)) by {
                    assert(p != p1);
                    assert(set!{p}.disjoint(set!{p1}));
                    lemma_prime_factors_prime(p);
                    lemma_prime_factors_disjoint_iff_coprime(p, p1_to_e1);
                }
                assert(prime_factors(n1).contains(p)) by {
                    lemma_coprime_factor(p, p1_to_e1, n1);
                }
            }
        });
        assert(is_coprime(p1_to_e1, n1)) by { lemma_prime_factors_disjoint_iff_coprime(p1_to_e1, n1); }

        calc!{
            (==)
            prime_factors(n).fold(1, f); { lemma_fold_insert(ps, 1, f, p1); }
            f(ps.fold(1, f), p1); {}
            f(prime_factors(n1).fold(1, f), p1); {
                lemma_totient_factorization(n1);
                assert(!is_factor_of(n1, p1)) by { assert(!prime_factors(n1).contains(p1)); }
                lemma_totient_factorization_induct(n, p1, n1, ps);
            }
            f(totient(n1), p1); {}
            totient(n1) * totient(p1_to_e1); { lemma_mul_is_commutative(totient(n1) as int, totient(p1_to_e1) as int); }
            totient(p1_to_e1) * totient(n1); { lemma_totient_coprime_mul(p1_to_e1, n1); }
            totient(p1_to_e1 * n1); {}
            totient(n);
        }
    }
}

// TODO: redundant with lemma_factorization?
proof fn lemma_totient_factorization_fun_comm(n: nat)
    requires n > 0,
    ensures
        ({
            let f = |prod: nat, p: nat| prod * totient(pow(p as int, vp(n, p)) as nat);
            is_fun_commutative(f)
        })
{
    let f = |prod: nat, p: nat| prod * totient(pow(p as int, vp(n, p)) as nat);
    assert forall |a1: nat, a2: nat, b: nat| #[trigger] f(f(b, a2), a1) == f(f(b, a1), a2) 
    by {
        let tot1 = totient(pow(a1 as int, vp(n, a1)) as nat);
        let tot2 = totient(pow(a2 as int, vp(n, a2)) as nat);
        calc!{
            (==)
            f(f(b, a1), a2); {}
            b * tot1 * tot2; { broadcast use lemma_mul_is_associative; }
            b * (tot1 * tot2); { broadcast use lemma_mul_is_commutative; }
            b * (tot2 * tot1); { broadcast use lemma_mul_is_associative; }
            b * tot2 * tot1; {}
            f(f(b, a2), a1);
        }
    }
}

proof fn lemma_totient_factorization_induct(n: nat, p: nat, n1: nat, ps: Set<nat>) 
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
            let f = |prod: nat, p: nat| prod * totient(pow(p as int, vp(n, p)) as nat);
            let f1 = |prod: nat, p: nat| prod * totient(pow(p as int, vp(n1, p)) as nat);
            ps.fold(1, f1) == ps.fold(1, f)
        })
    decreases ps.len(),
{
    let f = |prod: nat, p: nat| prod * totient(pow(p as int, vp(n, p)) as nat);
    let f1 = |prod: nat, p: nat| prod * totient(pow(p as int, vp(n1, p)) as nat);
    
    lemma_prime_factors_bound(n1);
    assert(ps.finite());

    if ps.is_empty() {
        // ..base
        lemma_fold_empty(1, f);
        lemma_fold_empty(1, f1);
    } else {
        // ..induct
        let p0 = ps.choose();
        let z = ps.remove(p0).fold(1, f);
        let z1 = ps.remove(p0).fold(1, f1);
       
        assert(f(z, p0) == f1(z1, p0)) by {
            assert(z == z1) by {
                lemma_totient_factorization_induct(n, p, n1, ps.remove(p0));
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
                assert(e >= 1) by {
                    lemma_pow1(p0 as int);
                    assert(is_factor_of(n, pow(p0 as int, 1) as nat));
                }
                assert(e1 >= 1) by {
                    lemma_pow1(p0 as int);
                    assert(is_factor_of(n1, pow(p0 as int, 1) as nat));
                }

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
            assert(totient(pow(p0 as int, vp(n, p0)) as nat) == totient(pow(p0 as int, vp(n1, p0)) as nat));
            assert(f(z, p0) == f1(z1, p0));
        }
        lemma_totient_factorization_fun_comm(n);
        lemma_totient_factorization_fun_comm(n1);
        lemma_fold_insert(ps.remove(p0), 1, f, p0);
        lemma_fold_insert(ps.remove(p0), 1, f1, p0);
    }
}

// TODO: totient_exec

} // verus!