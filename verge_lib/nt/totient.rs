//! Proofs and specifications for the [Euler's totient function](https://en.wikipedia.org/wiki/Euler%27s_totient_function), 
//! also denoted as `phi(n)`.

use super::{
    set_nat_range, is_factor_of, is_common_factor, is_coprime, is_prime, prime_factors, vp, gcd, lcm,
    axiom_prime_mul_union, axiom_coprime_gcd, axiom_gcd_properties, axiom_vp_properties, axiom_coprime_lcm,
    lemma_nat_range, lemma_is_factor_bound, lemma_is_factor_lincomb, lemma_is_factor_lincomb2, 
    lemma_is_factor_transitive, lemma_is_factor_mul_div, lemma_prime_or_composite,
    lemma_prime_minimal, lemma_coprime_factor, lemma_prime_factors_lcm_union, lemma_lcm_is_factor,
    lemma_prime_factor_exists, lemma_prime_factors_bound, lemma_prime_factors_one, 
    lemma_prime_factors_prime, lemma_prime_factors_prime_pow,
    lemma_prime_factors_disjoint_iff_coprime, lemma_bezout_identity_ext, 
    lemma_factorization, lemma_factorization_induct, lemma_factorization_fun_comm,
};
use crate::set::cart::{
    cart, lemma_cart_len, lemma_cart_intersect,
};
use crate::set::fold::{lemma_fold_set_seq_eq, lemma_fold_fn_eq, lemma_fold_disjoint_union};

use vstd::prelude::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power::*;
use vstd::seq::*;
use vstd::seq_lib::*;
use vstd::set::*;
use vstd::set::fold::*;
use vstd::set_lib::*;
use vstd::math::{min, max};
use vstd::{assert_by_contradiction, assert_seqs_equal, calc};
use vstd::relations::{injective_on, sorted_by};

verus! {

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
            assert(m == m1 * p) by { broadcast use lemma_mul_is_commutative; }
            assert(is_factor_of(m, p)) by { lemma_mod_multiples_basic(m1 as int, p as int); }
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
                -(b * qb) + rb; { 
                    calc!{
                        (==)
                        -(b * qb); { lemma_mul_is_commutative(b as int, qb); }
                        -(qb * b); { lemma_mul_unary_negation(qb, b as int); }
                        (-qb) * b;
                    }
                }
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
/// Specifically, for `n = p1^e1 * ... * pk^ek`, `phi(n) = n * ((p1-1) * ... * (pk-1)) / (p1 * ... * pk)`.
/// 
/// XXX: Unfortunately, it is not possible to use the more direct form:
/// ```
/// let f = |prod: nat, p: nat| prod * (p - 1) as nat / p;
/// totient(n) == prime_factors(n).fold(n, f)
/// ```
/// because the `fold` function requires `f` to be commutative over all inputs, which it is not.
pub proof fn lemma_totient_factorization(n: nat)
    requires 
        n > 0,
    ensures 
        totient(n) == n 
            * prime_factors(n).fold(1, |prod: nat, p: nat| prod * (p - 1) as nat)
            / prime_factors(n).fold(1, |prod: nat, p: nat| prod * p),
{
    let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
    let f2 = |prod: nat, n: nat| prod * n;
    assert(is_fun_commutative(f1)) by {
        let g1 = |n: nat| (n - 1) as nat;
        lemma_totient_factorization_fun_comm(g1);
        assert(f1 == |prod: nat, n: nat| prod * g1(n));
    }
    assert(is_fun_commutative(f2)) by {
        let g2 = |n: nat| n;
        lemma_totient_factorization_fun_comm(g2);
        assert(f2 == |prod: nat, n: nat| prod * g2(n));
    }

    let fold_fn = |g: spec_fn(nat) -> nat| {
        |prod: nat, p: nat| prod * g(pow(p as int, vp(n, p)) as nat)
    };
    let tot = |x: nat| totient(x);
    let tot2 = |x: nat| x * prime_factors(x).fold(1, f1) / prime_factors(x).fold(1, f2);

    assert forall|prod: nat, p: nat| prime_factors(n).contains(p) 
    implies #[trigger] fold_fn(tot)(prod, p) == fold_fn(tot2)(prod, p)
    by {
        let e = vp(n, p);
        let x = pow(p as int, e) as nat;
        axiom_vp_properties(n, p);
        calc!{
            (==)
            fold_fn(tot)(prod, p); {}
            prod * totient(x); {
                calc!{
                    (==)
                    totient(x) as int; { 
                        lemma_totient_prime_pow(p, e); 
                        lemma_pow_positive(p as int, (e - 1) as nat);
                    }
                    (p - 1) * pow(p as int, (e - 1) as nat); {
                        lemma_div_by_multiple((p - 1) * pow(p as int, (e - 1) as nat), p as int);
                    }
                    ((p - 1) * pow(p as int, (e - 1) as nat) * p) / p as int; {
                        lemma_mul_is_associative(p - 1, pow(p as int, (e - 1) as nat), p as int);
                    }
                    ((p - 1) * (pow(p as int, (e - 1) as nat) * p)) / p as int; {
                        lemma_mul_is_commutative(pow(p as int, (e - 1) as nat), p as int);
                    }
                    ((p - 1) * (p * pow(p as int, (e - 1) as nat))) / p as int; { 
                        reveal(pow); 
                        lemma_pow_positive(p as int, (e - 1) as nat);
                    }
                    ((p - 1) * x) / p as int; { lemma_mul_is_commutative(p - 1, x as int); }
                    x * (p - 1) / p as int; {
                        assert(set!{p}.fold(1, f1) == p - 1) by {
                            lemma_fold_empty(1, f1);
                            lemma_fold_insert(Set::<nat>::empty(), 1, f1, p);
                            broadcast use group_mul_basics;
                        }
                        assert(set!{p}.fold(1, f2) == p) by {
                            lemma_fold_empty(1, f2);
                            lemma_fold_insert(Set::<nat>::empty(), 1, f2, p);
                            broadcast use group_mul_basics;
                        }
                    }
                    (x * set!{p}.fold(1, f1) / set!{p}.fold(1, f2)) as int; { 
                        lemma_prime_factors_prime_pow(p, e); 
                    }
                    (x * prime_factors(x).fold(1, f1) / prime_factors(x).fold(1, f2)) as int;
                }
            }
            prod * (x * prime_factors(x).fold(1, f1) / prime_factors(x).fold(1, f2)); {}
            fold_fn(tot2)(prod, p);
        }
    }

    calc!{
        (==)
        totient(n); {
            assert forall|a: nat, b: nat| #[trigger] is_coprime(a, b) 
            implies tot(a * b) == tot(a) * tot(b) 
            by { lemma_totient_coprime_mul(a, b); }
            lemma_factorization_induct(n, tot);
            assert(tot(1) == 1) by { lemma_totient_one(); };
        }
        prime_factors(n).fold(1, fold_fn(tot)); {
            lemma_prime_factors_bound(n);
            lemma_factorization_fun_comm(n, tot);
            lemma_factorization_fun_comm(n, tot2);
            lemma_fold_fn_eq(prime_factors(n), 1, fold_fn(tot), fold_fn(tot2));
        }
        prime_factors(n).fold(1, fold_fn(tot2)); {
            assert forall|a: nat, b: nat| #[trigger] is_coprime(a, b) 
            implies tot2(a * b) == tot2(a) * tot2(b) 
            by { lemma_totient_factorization_tot2(a, b); }
            lemma_factorization_induct(n, tot2);
            calc!{
                (==)
                tot2(1); {}
                1 * prime_factors(1).fold(1, f1) / prime_factors(1).fold(1, f2); {
                    lemma_prime_factors_one();
                    lemma_fold_empty(1, f1);
                    lemma_fold_empty(1, f2);
                }
                1 * 1 / 1; {}
                1;
            }
        }
        n * prime_factors(n).fold(1, f1) / prime_factors(n).fold(1, f2);
    }
}

proof fn lemma_totient_factorization_tot2(a: nat, b: nat)
    requires is_coprime(a, b),
    ensures 
        ({
            let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
            let f2 = |prod: nat, n: nat| prod * n;
            let tot2 = |x: nat| x * prime_factors(x).fold(1, f1) / prime_factors(x).fold(1, f2);
            tot2(a * b) == tot2(a) * tot2(b)
        }),
{
    let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
    let g1 = |n: nat| (n - 1) as nat;
    assert(f1 == |prod: nat, n: nat| prod * g1(n));
    let f2 = |prod: nat, n: nat| prod * n;
    let g2 = |n: nat| n;
    assert(f2 == |prod: nat, n: nat| prod * g2(n));
    let tot2 = |x: nat| x * prime_factors(x).fold(1, f1) / prime_factors(x).fold(1, f2);
    lemma_prime_factors_bound(a);
    lemma_prime_factors_bound(b);

    calc!{
        (==)
        tot2(a * b); {}
        (a * b) * prime_factors(a * b).fold(1, f1) / prime_factors(a * b).fold(1, f2); {
            assert(prime_factors(a * b) == prime_factors(a) + prime_factors(b)) by {
                axiom_coprime_lcm(a, b);
                lemma_prime_factors_lcm_union(a, b);
            }
            assert(prime_factors(a).disjoint(prime_factors(b))) by {
                lemma_prime_factors_disjoint_iff_coprime(a, b);
            }
            calc!{
                (==)
                prime_factors(a * b).fold(1, f1); {}
                (prime_factors(a) + prime_factors(b)).fold(1, f1); {
                    lemma_totient_factorization_fun_comm(g1);
                    lemma_fold_disjoint_union(prime_factors(a), prime_factors(b), 1, f1);
                }
                prime_factors(b).fold(prime_factors(a).fold(1, f1), f1); {
                    lemma_totient_factorization_fold(prime_factors(b), prime_factors(a).fold(1, f1), g1);
                }
                prime_factors(a).fold(1, f1) * prime_factors(b).fold(1, f1); 
            }
            calc!{
                (==)
                prime_factors(a * b).fold(1, f2); {}
                (prime_factors(a) + prime_factors(b)).fold(1, f2); {
                    lemma_totient_factorization_fun_comm(g2);
                    lemma_fold_disjoint_union(prime_factors(a), prime_factors(b), 1, f2);
                }
                prime_factors(b).fold(prime_factors(a).fold(1, f2), f2); {
                    lemma_totient_factorization_fold(prime_factors(b), prime_factors(a).fold(1, f2), g2);
                }
                prime_factors(a).fold(1, f2) * prime_factors(b).fold(1, f2); 
            }
        }
        (a * b) 
            * (prime_factors(a).fold(1, f1) * prime_factors(b).fold(1, f1)) 
            / (prime_factors(a).fold(1, f2) * prime_factors(b).fold(1, f2));
        {
            calc!{
                (==)
                a * b * (prime_factors(a).fold(1, f1) * prime_factors(b).fold(1, f1)); {
                    broadcast use lemma_mul_is_associative;
                }
                a * (b * (prime_factors(a).fold(1, f1) * prime_factors(b).fold(1, f1))); {
                    broadcast use lemma_mul_is_commutative;
                }
                a * (prime_factors(a).fold(1, f1) * prime_factors(b).fold(1, f1) * b); {
                    broadcast use lemma_mul_is_associative;
                }
                a * (prime_factors(a).fold(1, f1) * (prime_factors(b).fold(1, f1) * b)); {
                    broadcast use lemma_mul_is_commutative;
                }
                a * (prime_factors(a).fold(1, f1) * (b * prime_factors(b).fold(1, f1))); {
                    broadcast use lemma_mul_is_associative;
                }
                (a * prime_factors(a).fold(1, f1)) * (b * prime_factors(b).fold(1, f1));
            }
            assert(prime_factors(a).fold(1, f2) > 0) by {
                assert forall|n: nat| prime_factors(a).contains(n) 
                implies g2(n) > 0 
                by { lemma_prime_minimal(); }
                lemma_totient_factorization_fold(prime_factors(a), 1, g2);
            }
            assert(prime_factors(b).fold(1, f2) > 0) by {
                assert forall|n: nat| prime_factors(b).contains(n) 
                implies g2(n) > 0 
                by { lemma_prime_minimal(); }
                lemma_totient_factorization_fold(prime_factors(b), 1, g2);
            }
            lemma_div_denominator(
                ((a * prime_factors(a).fold(1, f1)) * (b * prime_factors(b).fold(1, f1))) as int,
                prime_factors(a).fold(1, f2) as int,
                prime_factors(b).fold(1, f2) as int,
            );
        }
        (a * prime_factors(a).fold(1, f1)) 
            * (b * prime_factors(b).fold(1, f1))
            / prime_factors(a).fold(1, f2) 
            / prime_factors(b).fold(1, f2);
        {
            assert(is_factor_of(a * prime_factors(a).fold(1, f1), prime_factors(a).fold(1, f2))) by {
                assert(is_factor_of(a * prime_factors(a).fold(1, f1), a)) by {
                    lemma_mod_multiples_vanish(prime_factors(a).fold(1, f1) as int, 0, a as int)
                }
                lemma_totient_factorization_factor(a, prime_factors(a));
                lemma_is_factor_transitive(prime_factors(a).fold(1, f2), a, a * prime_factors(a).fold(1, f1));
            }
            lemma_is_factor_mul_div(a * prime_factors(a).fold(1, f1), b * prime_factors(b).fold(1, f1), prime_factors(a).fold(1, f2));
        }
        (a * prime_factors(a).fold(1, f1)) / prime_factors(a).fold(1, f2) 
            * (b * prime_factors(b).fold(1, f1))
            / prime_factors(b).fold(1, f2);
        {
            broadcast use lemma_mul_is_commutative;
        }
        (b * prime_factors(b).fold(1, f1)) 
            * ((a * prime_factors(a).fold(1, f1)) / prime_factors(a).fold(1, f2))
            / prime_factors(b).fold(1, f2);
        {
            assert(is_factor_of(b * prime_factors(b).fold(1, f1), prime_factors(b).fold(1, f2))) by {
                assert(is_factor_of(b * prime_factors(b).fold(1, f1), b)) by {
                    lemma_mod_multiples_vanish(prime_factors(b).fold(1, f1) as int, 0, b as int)
                }
                lemma_totient_factorization_factor(b, prime_factors(b));
                lemma_is_factor_transitive(prime_factors(b).fold(1, f2), b, b * prime_factors(b).fold(1, f1));
            }
            lemma_is_factor_mul_div(
                b * prime_factors(b).fold(1, f1), 
                (a * prime_factors(a).fold(1, f1)) / prime_factors(a).fold(1, f2),
                prime_factors(b).fold(1, f2),
            );
        }
        (b * prime_factors(b).fold(1, f1) / prime_factors(b).fold(1, f2))
            * ((a * prime_factors(a).fold(1, f1)) / prime_factors(a).fold(1, f2)); {}
        tot2(b) * tot2(a); { broadcast use lemma_mul_is_commutative; }
        tot2(a) * tot2(b);
    }
}

proof fn lemma_totient_factorization_fun_comm(g: spec_fn(nat) -> nat)
    ensures
        ({
            let f = |prod: nat, n: nat| prod * g(n);
            is_fun_commutative(f)
        }),
{
    let f = |prod: nat, n: nat| prod * g(n);
    assert forall |a1: nat, a2: nat, b: nat| #[trigger] f(f(b, a2), a1) == f(f(b, a1), a2) 
    by {
        calc!{
            (==)
            f(f(b, a1), a2); {}
            b * g(a1) * g(a2); { broadcast use lemma_mul_is_associative; }
            b * (g(a1) * g(a2)); { broadcast use lemma_mul_is_commutative; }
            b * (g(a2) * g(a1)); { broadcast use lemma_mul_is_associative; }
            b * g(a2) * g(a1); {}
            f(f(b, a2), a1);
        }
    }
}

proof fn lemma_totient_factorization_fold(s: Set<nat>, z: nat, g: spec_fn(nat) -> nat)
    requires s.finite(),
    ensures
        ({
            let f = |prod: nat, n: nat| prod * g(n);
            &&& s.fold(z, f) == z * s.fold(1, f)
            &&& (forall|n: nat| s.contains(n) ==> #[trigger] g(n) > 0) ==> s.fold(1, f) > 0
        }),
    decreases s.len(),
{
    let f = |prod: nat, n: nat| prod * g(n);
    assert(is_fun_commutative(f)) by { lemma_totient_factorization_fun_comm(g); }
    if s.is_empty() {
        // ..base
        calc!{
            (==)
            s.fold(z, f); { lemma_fold_empty(z, f); }
            z; { broadcast use group_mul_basics; }
            z * 1; { lemma_fold_empty(1, f); }
            z * s.fold(1, f);
        }
        assert(s.fold(1, f) > 0) by { lemma_fold_empty(1, f); }
    } else {
        // ..induct
        let a = s.choose();
        calc!{
            (==)
            s.fold(z, f); { lemma_fold_insert(s.remove(a), z, f, a); }
            f(s.remove(a).fold(z, f), a); {}
            s.remove(a).fold(z, f) * g(a); { lemma_totient_factorization_fold(s.remove(a), z, g); }
            z * s.remove(a).fold(1, f) * g(a); { broadcast use lemma_mul_is_associative; }
            z * (s.remove(a).fold(1, f) * g(a)); {}
            z * f(s.remove(a).fold(1, f), a); { lemma_fold_insert(s.remove(a), 1, f, a); }
            z * s.fold(1, f);
        }
        if forall|n: nat| s.contains(n) ==> #[trigger] g(n) > 0 {
            calc!{
                (>)
                s.fold(1, f); (==) { lemma_fold_insert(s.remove(a), 1, f, a); }
                f(s.remove(a).fold(1, f), a); (==) {}
                s.remove(a).fold(1, f) * g(a); {
                    assert(s.remove(a).fold(1, f) > 0) by { lemma_totient_factorization_fold(s.remove(a), 1, g); }
                    assert(g(a) > 0);
                    broadcast use lemma_mul_strictly_positive;
                }
                0;
            }
        }
    }
}

proof fn lemma_totient_factorization_factor(n: nat, set: Set<nat>)
    requires 
        n > 0,
        set.subset_of(prime_factors(n)),
    ensures 
        is_factor_of(n, set.fold(1, |prod: nat, p: nat| prod * p)),
{
    let f = |prod: nat, p: nat| prod * p;
    assert(is_fun_commutative(f)) by {
        let g = |p: nat| p;
        assert(f == |prod: nat, p: nat| prod * g(p));
        lemma_totient_factorization_fun_comm(g);
    }

    let pred = |s: Set<nat>| s.subset_of(prime_factors(n)) 
        ==> is_factor_of(n, s.fold(1, f)) && prime_factors(s.fold(1, f)) == s;
    lemma_prime_factors_bound(n);
    assert(pred(Set::<nat>::empty())) by { 
        lemma_fold_empty(1, f);
        assert(is_factor_of(n, 1)) by (compute);
        lemma_prime_factors_one();
    }

    assert forall |s: Set<nat>, p: nat| pred(s) && s.finite() && !s.contains(p)
    implies #[trigger] pred(s.insert(p))
    by {
        if !prime_factors(n).contains(p) || !s.subset_of(prime_factors(n)) {
            // ..bad case
            assert(!s.insert(p).subset_of(prime_factors(n)));
        } else {
            lemma_prime_factors_prime(p);
            calc!{
                (==)
                s.insert(p).fold(1, f); { lemma_fold_insert(s, 1, f, p); }
                f(s.fold(1, f), p); {}
                s.fold(1, f) * p; {
                    assert(is_coprime(s.fold(1, f), p)) by {
                        lemma_prime_factors_disjoint_iff_coprime(s.fold(1, f), p);
                    }
                    axiom_coprime_lcm(s.fold(1, f), p);
                }
                lcm(s.fold(1, f), p);
            }
            assert(is_factor_of(n, s.insert(p).fold(1, f))) by {
                lemma_lcm_is_factor(s.fold(1, f), p, n);
            }
            assert(prime_factors(s.insert(p).fold(1, f)) == s.insert(p)) by {
                lemma_prime_factors_lcm_union(s.fold(1, f), p);
            }
        }
    }
    lemma_finite_set_induct(set, pred);
}

mod lemma_totients {
    use super::*;

    pub(super) closed spec fn pf(n: nat, hi: nat) -> Set<nat>
    {
        if n > 0 {
            prime_factors(n).filter(|p: nat| p < hi)
        } else {
            Set::<nat>::empty()
        }
    }

    pub(super) proof fn pf_properties(n: nat, hi: nat)
        ensures
            pf(n, hi).finite(),
            forall|p: nat| #[trigger] pf(n, hi).contains(p) ==> prime_factors(n).contains(p) && p >= 2 && p < hi && p <= n,
    {
        if n == 0 { return; }
        lemma_prime_factors_bound(n);
        assert(pf(n, hi).subset_of(prime_factors(n)));
        lemma_set_subset_finite(prime_factors(n), pf(n, hi));

        assert forall|p: nat| #[trigger] pf(n, hi).contains(p)
        implies prime_factors(n).contains(p) && p >= 2 && p < hi && p <= n
        by { lemma_prime_minimal(); }
    }

    pub(super) proof fn pf_is_empty(n: nat)
        ensures pf(n, 2) == Set::<nat>::empty(),
    {
        assert_by_contradiction!(pf(n, 2).is_empty(), {
            let k = pf(n, 2).choose();
            lemma_prime_minimal();
        });
    }

    pub(super) proof fn pf_prime_is_empty(p: nat)
        requires is_prime(p),
        ensures pf(p, p) == Set::<nat>::empty(),
    {
        assert_by_contradiction!(pf(p, p).is_empty(), {
            let k = pf(p, p).choose();
            assert(is_factor_of(p, k) && 1 < k < p);
        });
    }

    pub(super) proof fn pf_inc_equal(k: nat, p: nat)
        requires !is_prime(p),
        ensures pf(k, p + 1) == pf(k, p),
    {
        assert(pf(k, p + 1) == pf(k, p as nat)) by { 
            lemma_totients::pf_properties(k, p + 1); 
            lemma_totients::pf_properties(k, p); 
            assert(!pf(k, p + 1).contains(p));
        }
    }

    pub(super) proof fn pf_is_full(n: nat, hi: nat)
        requires 
            n > 0,
            hi > n,
        ensures 
            pf(n, hi) == prime_factors(n),
    {
        assert(pf(n, hi).subset_of(prime_factors(n)));
        assert(prime_factors(n).subset_of(pf(n, hi))) by {
            assert forall |p: nat| prime_factors(n).contains(p)
            implies #[trigger] pf(n, hi).contains(p) 
            by { lemma_prime_factors_bound(n); }
        }
    }

    proof fn f1_f2_commutative()
        ensures 
            ({
                let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
                let f2 = |prod: nat, n: nat| prod * n;
                is_fun_commutative(f1) && is_fun_commutative(f2)
            }),
    {
        let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
        let f2 = |prod: nat, n: nat| prod * n;
        assert(is_fun_commutative(f1)) by {
            let g1 = |n: nat| (n - 1) as nat;
            lemma_totient_factorization_fun_comm(g1);
            assert(f1 == |prod: nat, n: nat| prod * g1(n));
        }
        assert(is_fun_commutative(f2)) by {
            let g2 = |n: nat| n;
            lemma_totient_factorization_fun_comm(g2);
            assert(f2 == |prod: nat, n: nat| prod * g2(n));
        }
    }

    proof fn fold_f1_f2_positive(s: Set<nat>)
        requires
            s.finite(),
            s.all(|n: nat| n >= 2),
        ensures 
            ({
                let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
                let f2 = |prod: nat, n: nat| prod * n;
                s.fold(1, f1) > 0 && s.fold(1, f2) > 0
            }),
        decreases s.len(),
    {
        let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
        let f2 = |prod: nat, n: nat| prod * n;
        if s.is_empty() {
            lemma_fold_empty(1, f1);
            lemma_fold_empty(1, f2);
        } else {
            f1_f2_commutative();
            let n = s.choose();
            fold_f1_f2_positive(s.remove(n));
            calc!{
                (>)
                s.fold(1, f1); (==) { lemma_fold_insert(s.remove(n), 1, f1, n); }
                s.remove(n).fold(1, f1) * (n - 1) as nat; { lemma_mul_strictly_positive(s.remove(n).fold(1, f1) as int, n - 1); }
                0;
            }
            calc!{
                (>)
                s.fold(1, f2); (==) { lemma_fold_insert(s.remove(n), 1, f2, n); }
                s.remove(n).fold(1, f2) * n; { lemma_mul_strictly_positive(s.remove(n).fold(1, f2) as int, n as int); }
                0;
            }
        }
    }

    proof fn fold_f1_lt_f2(s: Set<nat>)
        requires
            s.finite() && !s.is_empty(),
            s.all(|n: nat| n >= 2),
        ensures
            ({
                let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
                let f2 = |prod: nat, n: nat| prod * n;
                s.fold(1, f1) < s.fold(1, f2)
            }),
        decreases s.len(),
    {
        let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
        let f2 = |prod: nat, n: nat| prod * n;
        assert(s.len() > 0);
        f1_f2_commutative();
        if s.len() == 1 {
            let n = s.choose();
            let empty = Set::<nat>::empty();
            assert(s == empty.insert(n)) by { Set::<nat>::lemma_is_singleton(s); }
            calc!{
                (<)
                s.fold(1, f1); (==) { 
                    lemma_fold_insert(empty, 1, f1, n); 
                    lemma_fold_empty(1, f1);
                }
                (n - 1) as nat; {}
                n; (==) {
                    lemma_fold_insert(empty, 1, f2, n); 
                    lemma_fold_empty(1, f2);
                }
                s.fold(1, f2);
            }
        } else {
            let n = s.choose();
            calc!{
                (<)
                s.fold(1, f1); (==) { 
                    lemma_fold_insert(s.remove(n), 1, f1, n); 
                }
                s.remove(n).fold(1, f1) * (n - 1) as nat; {
                    fold_f1_lt_f2(s.remove(n));
                    lemma_mul_strict_inequality(
                        s.remove(n).fold(1, f1) as int, 
                        s.remove(n).fold(1, f2) as int, 
                        n - 1,
                    );
                }
                s.remove(n).fold(1, f2) * (n - 1) as nat; (==) { broadcast use lemma_mul_is_commutative; }
                (n - 1) as nat * s.remove(n).fold(1, f2); (<=) {
                    lemma_mul_inequality(n - 1, n as int, s.remove(n).fold(1, f2) as int);
                }
                n * s.remove(n).fold(1, f2); (==) { broadcast use lemma_mul_is_commutative; } 
                s.remove(n).fold(1, f2) * n; (==) { 
                    lemma_fold_insert(s.remove(n), 1, f2, n); 
                }
                s.fold(1, f2);
            }
        }
    }

    proof fn inequality_mul_div(a: nat, b: nat, c: nat)
        requires a > 0 && 0 < b < c,
        ensures a * b / c < a,
    {
        calc!{
            (<=)
            a * b / c; { lemma_div_is_ordered_by_denominator((a * b) as int, b as int, c as int); }
            a * b / b; (==) { lemma_div_by_multiple(a as int, b as int); }
            a;
        }
        assert_by_contradiction!(a * b / c != a, {
            calc!{
                (<=)
                (c * a) as int; (==) {}
                (c * (a * b / c)) as int; (==) { lemma_fundamental_div_mod((a * b) as int, c as int); }
                a * b - a * b % c; { lemma_mod_bound((a * b) as int, c as int); }
                (a * b) as int; (==) { broadcast use lemma_mul_is_commutative; }
                (b * a) as int;
            }
            lemma_mul_strict_inequality(b as int, c as int, a as int);
        });
    }

    proof fn inequality_div_mul(n: nat, p: nat)
        requires p >= 2,
        ensures n / p * (p - 1) <= n,
    {
        calc!{
            (<=)
            n / p * (p - 1); (==) { lemma_mul_is_distributive_sub((n / p) as int, p as int, 1); }
            n / p * p - n / p; {}
            (n / p * p) as int; (==) {
                lemma_fundamental_div_mod(n as int, p as int);
                lemma_mul_is_commutative((n / p) as int, p as int);
            }
            n - n % p; { lemma_mod_bound(n as int, p as int); }
            n as int;
        }
    }

    pub(super) proof fn p_is_prime(p: nat)
        requires 
            p >= 2,
        ensures
            ({
                let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
                let f2 = |prod: nat, n: nat| prod * n;
                is_prime(p) <==> p == p * pf(p, p).fold(1, f1) / pf(p, p).fold(1, f2)
            }),
    {
        let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
        let f2 = |prod: nat, n: nat| prod * n;
        if p == p * pf(p, p).fold(1, f1) / pf(p, p).fold(1, f2) {
            assert_by_contradiction!(is_prime(p), {
                lemma_prime_factor_exists(p);
                let p0 = prime_factors(p).choose();
                assert(p0 < p) by { lemma_prime_factors_bound(p); };
                assert(pf(p, p).contains(p0));
                assert(pf(p, p).fold(1, f1) < pf(p, p).fold(1, f2)) by {
                    pf_properties(p, p);
                    fold_f1_lt_f2(pf(p, p));
                }
                assert(pf(p, p).fold(1, f1) < pf(p, p).fold(1, f2));
                inequality_mul_div(p, pf(p, p).fold(1, f1), pf(p, p).fold(1, f2));
            });
        }
        if is_prime(p) {
            calc!{
                (==)
                p * pf(p, p).fold(1, f1) / pf(p, p).fold(1, f2); { 
                    pf_prime_is_empty(p);
                    lemma_fold_empty(1, f1);
                    lemma_fold_empty(1, f2);
                }
                p * 1 / 1; { assert(p * 1 / 1 == p) by (compute); }
                p;
            }
        }
        
    }

    pub(super) proof fn outer_inv_preloop(k: nat)
        ensures
            ({
                let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
                let f2 = |prod: nat, n: nat| prod * n;
                k == k * pf(k, 2).fold(1, f1) / pf(k, 2).fold(1, f2)
            }),
    {
        let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
        let f2 = |prod: nat, n: nat| prod * n;
        lemma_totients::pf_is_empty(k);
        calc!{
            (==)
            k * pf(k, 2).fold(1, f1) / pf(k, 2).fold(1, f2); {
                lemma_fold_empty(1, f1);
                lemma_fold_empty(1, f2);
            }
            k * 1 / 1; { assert(k * 1 / 1 == k) by (compute); }
            k;
        }
    }

    pub(super) proof fn inner_inv_preloop(l: nat, p: nat)
        requires
            0 <= l < p,
        ensures
            ({
                let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
                let f2 = |prod: nat, n: nat| prod * n;
                l * pf(l, p).fold(1, f1) / pf(l, p).fold(1, f2) 
                == l * pf(l, p+1).fold(1, f1) / pf(l, p+1).fold(1, f2)
            }),
    {
        let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
        let f2 = |prod: nat, n: nat| prod * n;
        if l == 0 {
            assert(l * pf(l, p).fold(1, f1) / pf(l, p).fold(1, f2) == 0) by {
                lemma_fold_empty(1, f1);
                lemma_fold_empty(1, f2);
                broadcast use { group_mul_basics, group_div_basics };
            }
            assert(l * pf(l, p+1).fold(1, f1) / pf(l, p+1).fold(1, f2) == 0) by {
                lemma_fold_empty(1, f1);
                lemma_fold_empty(1, f2);
                broadcast use { group_mul_basics, group_div_basics };
            }
        } else {
            assert(!pf(l, p+1).contains(p)) by {
                assert_by_contradiction!(!is_factor_of(l, p), {
                    lemma_is_factor_bound(l, p);
                });
            }
            assert(pf(l, p+1) == pf(l, p));
        }
    }         
    
    pub(super) proof fn overflow_safety(v: usize, p: usize, k: usize, n: usize)
        requires
            isize::MAX > n >= 2,
            2 <= p <= n + 1,
            p <= k <= n + p,
            v <= k,
        ensures 
            v / p * (p - 1) <= usize::MAX,
    {
        inequality_div_mul(v as nat, p as nat);
        assert(v <= usize::MAX);
    }

    pub(super) proof fn inner_inv_postloop(
        old_k: usize, k: usize, p: usize, n: usize, old_phi: Seq<usize>, phi: Seq<usize>
    )
        requires
            isize::MAX > n >= 2,
            2 <= p <= n + 1,
            is_prime(p as nat),
            old_k % p == 0,
            p <= old_k <= n,
            k == old_k + p,
            old_phi.len() == n + 1,
            forall|l: nat| 0 <= l <= n ==> 
                #[trigger] old_phi[l as int] <= l,
            ({
                let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
                let f2 = |prod: nat, n: nat| prod * n;
                &&& forall|l: nat| 0 <= l < old_k && l <= n ==> #[trigger]
                    old_phi[l as int] == l * pf(l, p as nat+1).fold(1, f1) / pf(l, p as nat+1).fold(1, f2)
                &&& forall|l: nat| old_k <= l <= n ==> #[trigger]
                    old_phi[l as int] == l * pf(l, p as nat).fold(1, f1) / pf(l, p as nat).fold(1, f2)
            }),
            phi =~= old_phi.update(old_k as int, (old_phi[old_k as int] / p * (p - 1)) as usize), 
        ensures
            k % p == 0,
            p <= k <= n + p,
            phi.len() == n + 1,
            forall|l: nat| 0 <= l <= n ==> 
                #[trigger] phi[l as int] <= l,
            ({
                let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
                let f2 = |prod: nat, n: nat| prod * n;
                &&& forall|l: nat| 0 <= l < k && l <= n ==> #[trigger]
                    phi[l as int] == l * pf(l, p as nat+1).fold(1, f1) / pf(l, p as nat+1).fold(1, f2)
                &&& forall|l: nat| k <= l <= n ==> #[trigger]
                    phi[l as int] == l * pf(l, p as nat).fold(1, f1) / pf(l, p as nat).fold(1, f2)
            }),
    {
        let f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
        let f2 = |prod: nat, n: nat| prod * n;
        // Goal 1
        assert(k % p == 0) by {
            lemma_mod_self_0(p as int);
            lemma_is_factor_lincomb(old_k as nat, 1, p as nat, 1, p as nat);
            assert(k == old_k * 1 + p * 1) by (compute);
        }
        // Goal 2
        assert(p <= k <= n + p);
        // Goal 3
        assert(phi.len() == n + 1);
        // Goal 4
        assert forall|l: nat| 0 <= l <= n 
        implies #[trigger] phi[l as int] <= l
        by {
            if l == old_k {
                let v = phi[l as int];
                assert(v == (old_phi[old_k as int] / p * (p - 1)) as usize);
                inequality_div_mul(old_phi[old_k as int] as nat, p as nat);
                assert(v <= old_phi[old_k as int] <= old_k);
            } 
        }
        // Goal 5
        assert forall|l: nat| 0 <= l < k && l <= n
        implies #[trigger] phi[l as int] == l * pf(l, p as nat+1).fold(1, f1) / pf(l, p as nat+1).fold(1, f2)
        by {
            if l < old_k {
                // ..trivial
            } else if old_k < l < k {
                // ..similar to preloop invariant
                assert(!pf(l, p as nat+1).contains(p as nat)) by {
                    assert_by_contradiction!(!is_factor_of(l, p as nat), {
                        lemma_is_factor_lincomb2(l, 1, old_k as nat, 1, p as nat);
                        assert(l * 1 - old_k * 1 == l - old_k) by (compute);
                        assert(0 < l - old_k < p);
                        lemma_is_factor_bound((l - old_k) as nat, p as nat);
                    });
                }
                assert(pf(l, p as nat+1) == pf(l, p as nat));
            } else {
                // Key of the proof!

                let p = p as nat;
                assert(old_k == l);
                f1_f2_commutative();
                pf_properties(l, p);
                fold_f1_f2_positive(pf(l, p));
                assert(pf(l, p).insert(p) == pf(l, p + 1)) by {
                    assert(pf(l, p + 1).contains(p));
                }

                calc!{
                    (==)
                    phi[l as int] as int; { overflow_safety(old_phi[old_k as int], p as usize, old_k, n); }
                    old_phi[l as int] / p as usize * (p - 1); {}
                    l * pf(l, p).fold(1, f1) / pf(l, p).fold(1, f2) / p * (p - 1); {
                        lemma_div_denominator((l * pf(l, p).fold(1, f1)) as int, pf(l, p).fold(1, f2) as int, p as int);
                    }
                    l * pf(l, p).fold(1, f1) / (pf(l, p).fold(1, f2) * p) * (p - 1); {
                        calc!{
                            (==)
                            pf(l, p).fold(1, f2) * p; { lemma_fold_insert(pf(l, p), 1, f2, p); }
                            pf(l, p).insert(p).fold(1, f2); {}
                            pf(l, p + 1).fold(1, f2);
                        }
                    }
                    l * pf(l, p).fold(1, f1) / pf(l, p + 1).fold(1, f2) * (p - 1); {
                        assert(is_factor_of(l * pf(l, p).fold(1, f1), pf(l, p + 1).fold(1, f2))) by {
                            assert(is_factor_of(l, pf(l, p + 1).fold(1, f2))) by {
                                assert(pf(l, p + 1).subset_of(prime_factors(l)));
                                lemma_totient_factorization_factor(l, pf(l, p + 1));
                            }
                            assert(is_factor_of(l * pf(l, p).fold(1, f1), l)) by {
                                lemma_mod_multiples_vanish(pf(l, p).fold(1, f1) as int, 0, l as int);
                            }
                            lemma_is_factor_transitive(pf(l, p + 1).fold(1, f2), l, l * pf(l, p).fold(1, f1));
                        }
                        lemma_is_factor_mul_div(l * pf(l, p).fold(1, f1), (p - 1) as nat, pf(l, p + 1).fold(1, f2));
                    }
                    l * pf(l, p).fold(1, f1) * (p - 1) / pf(l, p + 1).fold(1, f2) as int; {
                        broadcast use lemma_mul_is_associative;
                    }
                    l * (pf(l, p).fold(1, f1) * (p - 1)) / pf(l, p + 1).fold(1, f2) as int; {
                        lemma_fold_insert(pf(l, p), 1, f1, p);
                    }
                    (l * pf(l, p).insert(p).fold(1, f1) / pf(l, p + 1).fold(1, f2)) as int; {}
                    (l * pf(l, p + 1).fold(1, f1) / pf(l, p + 1).fold(1, f2)) as int;
                }
            }
        }
    }
}

use lemma_totients::pf;

/// This function computes `phi(i)` for `i` in `0..=n`, in executable code.
pub fn totients(n: usize) -> (ret: Vec<usize>)
    requires isize::MAX > n >= 2,
    ensures
        ret@.len() == n + 1,
        forall|i: nat| #![auto] 0 <= i <= n ==> ret@[i as int] == totient(i),
{
    // Init ghost states
    let ghost f1 = |prod: nat, n: nat| prod * (n - 1) as nat;
    let ghost f2 = |prod: nat, n: nat| prod * n;

    // Init `phi`
    let mut phi = vec![0usize; n + 1];
    for i in 0..(n+1)
        invariant 
            0 <= i <= n + 1,
            phi@.len() == n + 1,
            forall|k: nat| 0 <= k < i ==> phi[k as int] == k,
    {
        phi[i] = i;
    }
    
    // Update `phi`
    proof { 
        // Proof of pre-loop invariant (outer)
        // n == n * pf(n, 2).fold(1, f1) / pf(n, 2).fold(1, f2)
        assert forall |k: nat| 0 <= k <= n 
        implies #[trigger] phi[k as int] == k * pf(k, 2).fold(1, f1) / pf(k, 2).fold(1, f2)
        by { lemma_totients::outer_inv_preloop(k); }
    }

    #[verifier::loop_isolation(false)]
    for p in 2..(n+1) 
        invariant
            2 <= p <= n + 1,
            phi@.len() == n + 1,
            forall|k: nat| 0 <= k <= n ==> #[trigger] phi[k as int] <= k,
            forall|k: nat| 0 <= k <= n ==> #[trigger] phi[k as int] == k * pf(k, p as nat).fold(1, f1) / pf(k, p as nat).fold(1, f2),
    {
        // Proof that p is prime iff phi[p] == p 
        proof { lemma_totients::p_is_prime(p as nat); }

        if phi[p] == p {
            let mut k = p;
            // Proof of pre-loop invariant (inner)
            // For 0 <= l < p, pf(l, p+1) == pf(l, p) 
            proof {
                let p = p as nat;
                assert forall|l: nat| 0 <= l < p
                implies phi[l as int] == l * pf(l, p+1).fold(1, f1) / pf(l, p+1).fold(1, f2)
                by { lemma_totients::inner_inv_preloop(l, p); }
            }
            #[verifier::loop_isolation(false)]
            while k <= n 
                invariant
                    k % p == 0,
                    p <= k <= n + p,
                    phi@.len() == n + 1,
                    forall|l: nat|
                        0 <= l <= n ==> #[trigger] phi[l as int] <= l,
                    forall|l: nat|
                        0 <= l < k && l <= n ==> #[trigger]
                        phi[l as int] == l * pf(l, p as nat+1).fold(1, f1) / pf(l, p as nat+1).fold(1, f2),
                    forall|l: nat|
                        k <= l <= n ==> #[trigger]
                        phi[l as int] == l * pf(l, p as nat).fold(1, f1) / pf(l, p as nat).fold(1, f2)
                decreases n + p - k,
            {
                let ghost old_k = k;
                let ghost old_phi = phi@;
                
                // Proof of overflow-safety
                proof { lemma_totients::overflow_safety(phi[k as int], p, k, n); }
                phi[k] = phi[k] / p * (p - 1);
                k += p;

                // Proof of post-loop invariant (inner)
                proof { lemma_totients::inner_inv_postloop(old_k, k, p, n, old_phi, phi@); }
            }
        } else {
            // Proof of post-loop invariant (outer)
            // p is not prime
            proof { 
                assert forall |k: nat| 0 <= k <= n 
                implies #[trigger] phi[k as int] == k * pf(k, p as nat+1).fold(1, f1) / pf(k, p as nat+1).fold(1, f2)
                by { lemma_totients::pf_inc_equal(k, p as nat); }
            }
        }
    }

    // Proof of postcond
    // k * pf(k, n+1).fold(1, f1) / pf(k, n+1).fold(1, f2) == totient(k)
    proof {
        assert forall|i: nat| #![auto] 0 <= i <= n 
        implies phi[i as int] == totient(i)
        by {
            if i == 0 {
                lemma_fold_empty(1, f1);
                lemma_fold_empty(1, f2);
                assert(0 * 1 / 1 == 0) by (compute);
                lemma_totient_zero();
            } else {
                lemma_totients::pf_is_full(i, (n + 1) as nat);
                lemma_totient_factorization(i);
            }
        }
    }
    phi
}

} // verus!