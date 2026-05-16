# `verge::nt`

Specifications and lemmas for (N)umber (T)heory in Verus.


## Functions


### `set_nat_range`

This function defines the natural number range [lo, hi).
It is useful in this module as a substitute of `set_lib::set_int_range`,
with the elements being `nat` instead of `int`.

```rust
pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::<nat>::new(|p: nat| lo <= p < hi)
    }
```


### `lemma_nat_range`

Proof of `set_nat_range`'s basic properties.

```rust
pub broadcast proof fn lemma_nat_range(lo: nat, hi: nat)
    ensures
        #[trigger] set_nat_range(lo, hi).finite(),
        #[trigger] set_nat_range(lo, hi).len() == clip(hi - lo),
```


### `is_factor_of`

This predicate determines whether `d` is a factor of `n` (`d|n`).
It can be used as a trigger term.

```rust
pub open spec fn is_factor_of(n: nat, d: nat) -> bool {
    n % d == 0 && d > 0
    }
```


### `lemma_is_factor_bound`

Proof that `d|n` implies either `n == 0` or `n >= d`.

```rust
pub broadcast proof fn lemma_is_factor_bound(n: nat, d: nat)
    requires
        #[trigger] is_factor_of(n, d),
    ensures n == 0 || n >= d,
```


### `lemma_is_factor_lincomb`

Proof that if `d|n1` and `d|n2`, then `d|(n1 * a1 + n2 * a2)` for any integer coefficients
`a1` and `a2`.

```rust
pub proof fn lemma_is_factor_lincomb(n1: nat, a1: int, n2: nat, a2: int, d: nat)
    requires
        is_factor_of(n1, d),
        is_factor_of(n2, d),
        n1 * a1 + n2 * a2 >= 0,
    ensures
        is_factor_of((n1 * a1 + n2 * a2) as nat, d),
```


### `lemma_is_factor_lincomb2`

Proof that if `d|n1` and `d|n2`, then `d|(n1 * a1 - n2 * a2)` for any integer coefficients
`a1` and `a2`.
This is an alternative form of `lemma_is_factor_lincomb`, useful when the linear
combination comes in the substraction form.

```rust
pub proof fn lemma_is_factor_lincomb2(n1: nat, a1: int, n2: nat, a2: int, d: nat)
    requires
        is_factor_of(n1, d),
        is_factor_of(n2, d),
        n1 * a1 - n2 * a2 >= 0,
    ensures
        is_factor_of((n1 * a1 - n2 * a2) as nat, d),
```


### `lemma_is_factor_transitive`

Proof that if `a | b` and `b | c`, then `a | c`.

```rust
pub proof fn lemma_is_factor_transitive(a: nat, b: nat, c: nat)
    requires
        is_factor_of(b, a) && is_factor_of(c, b)
    ensures
        is_factor_of(c, a),
```


### `is_prime`

This function determines whether `p` is a prime number.
Note: this is but one of many ways to uniquely define primeness.

```rust
pub open spec fn is_prime(p: nat) -> bool {
    p > 1 && forall|d: nat| #[trigger] is_factor_of(p, d) ==> d == 1 || d == p
    }
```


### `is_composite`

This function determines whether `n` is a composite number.

```rust
pub open spec fn is_composite(n: nat) -> bool {
    n > 1 && exists|a: nat, b: nat| 1 < a < n && 1 < b < n && #[trigger] (a * b) == n
    }
```


### `is_common_factor`

This predicate determines whether `d` is a common factor of `a` and `b`.

```rust
pub open spec fn is_common_factor(a: nat, b: nat, d: nat) -> bool {
    is_factor_of(a, d) && is_factor_of(b, d)
    }
```


### `is_coprime`

This predicate determines whether `a` and `b` are coprime.

```rust
pub open spec fn is_coprime(a: nat, b: nat) -> bool {
    &&& a > 0
    &&& b > 0
    &&& !exists|d: nat| d > 1 && #[trigger] is_common_factor(a, b, d)
    }
```


### `prime_factors`

This function defines the set of prime factors of `n`.

```rust
pub open spec fn prime_factors(n: nat) -> Set<nat>
    recommends n > 0
        {
        Set::<nat>::new(|p: nat| is_prime(p) && is_factor_of(n, p))
        }
```


### `vp`

This function defines the "p-adic" valuation of `n` for a prime number `p` (denoted as `v_p(n)`);
equivalently, it defines the exponent of the highest power of `p` that divides `n`.

```rust
pub closed spec fn vp(n: nat, p: nat) -> nat
    recommends
        n > 0,
        is_prime(p),
```


### `axiom_is_coprime`

Proof of `is_coprime`'s basic properties.

```rust
pub proof fn axiom_is_coprime(a: nat, b: nat)
    requires is_coprime(a, b),
    ensures is_coprime(b, a),
```


### `axiom_vp_properties`

Proof of `v_p(n)`'s basic properties.

```rust
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
```


### `axiom_prime_not_composite`

Proof that `p` is prime iff `p > 1` and `p` is not composite.
Note: this is also an alternative definition of `is_prime`.

```rust
pub broadcast proof fn axiom_prime_not_composite(p: nat)
    ensures
        #[trigger] is_prime(p)
        <==> p > 1 && !is_composite(p)
```


### `axiom_prime_mul_union`

Proof that `p` is prime iff `p|ab` implies `p|a` or `p|b`.
Note: this is also an alternative definition of `is_prime`.

```rust
pub broadcast proof fn axiom_prime_mul_union(p: nat)
    ensures
        #[trigger] is_prime(p)
        <==> p > 1 && forall|a: nat, b: nat| #[trigger]
            is_factor_of(a * b, p) ==> is_factor_of(a, p) || is_factor_of(b, p),
```


### `lemma_is_factor_multiples`

Proof that `b * c | a * c` implies `b | a`.

```rust
pub proof fn lemma_is_factor_multiples(a: nat, b: nat, c: nat)
    requires
        b > 0 && c > 0,
        is_factor_of(a * c, b * c),
    ensures
        is_factor_of(a, b),
```


### `lemma_is_factor_mul_div`

Proof that `a * b / c == a / c * b` if `c|a`.

```rust
pub proof fn lemma_is_factor_mul_div(a: nat, b: nat, c: nat)
    requires is_factor_of(a, c),
    ensures a * b / c == a / c * b,
```


### `lemma_coprime_factor`

Proof that if `a|bc` and `(a, b) == 1`, then `a|c`.

```rust
pub proof fn lemma_coprime_factor(a: nat, b: nat, c: nat)
    requires
        c > 0,
        is_factor_of(b * c, a),
        is_coprime(a, b),
    ensures
        is_factor_of(c, a),
```


### `lemma_bezout_identity`

Proof of the Bézout's Identity (https://en.wikipedia.org/wiki/B%C3%A9zout%27s_identity).

```rust
pub proof fn lemma_bezout_identity(a: nat, b: nat, d: nat)
    requires
        a > 0 && b > 0,
        d == gcd(a, b),
    ensures
        exists|x: int, y: int| 0 <= x < b / d && #[trigger] (a * x + b * y) == d,
```


### `lemma_bezout_identity_ext`

Proof of more properties about the Bezout identity. Specifically, for any
`a > 0`, `b > 0`, and `m` such that `(a, b) | m`, `ax + by = m` as a *unique*
solution such that `0 <= x < b / (a, b)`.

```rust
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
```


### `lemma_prime_or_composite`

Proof that all positive natural numbers are either prime, composite, or 1.

```rust
pub proof fn lemma_prime_or_composite(n: nat)
    requires n > 0,
    ensures n == 1 || is_prime(n) || is_composite(n),
```


### `lemma_prime_minimal`

Proof that 2 is the minimal prime.

```rust
pub proof fn lemma_prime_minimal()
    ensures
        is_prime(2),
        forall|p: nat| #[trigger] is_prime(p) ==> p >= 2,
```


### `lemma_prime_infinite`

Proof that there are infinitely many primes.

```rust
pub proof fn lemma_prime_infinite()
    ensures
        !Set::<nat>::new(|n: nat| is_prime(n)).finite(),
```


### `lemma_prime_factor_exists`

Proof that every `n > 1` has a prime factor.

```rust
pub proof fn lemma_prime_factor_exists(n: nat)
    requires n > 1,
    ensures !prime_factors(n).is_empty(),
    decreases n - 2,
```


### `lemma_prime_factors_one`

Proof that `1` has no prime factors.

```rust
pub proof fn lemma_prime_factors_one()
    ensures prime_factors(1).is_empty(),
```


### `lemma_prime_factors_prime`

Proof that the only prime factor of a prime `p` is `p`.

```rust
pub proof fn lemma_prime_factors_prime(p: nat)
    requires is_prime(p),
    ensures prime_factors(p) =~= set!{p},
```


### `lemma_prime_factors_prime_pow`

Proof that the only prime factor of a power of prime `p` is `p`.

```rust
pub proof fn lemma_prime_factors_prime_pow(p: nat, e: nat)
    requires
        is_prime(p),
        e > 0,
    ensures
        prime_factors(pow(p as int, e) as nat) =~= set!{p},
    decreases e,
```


### `lemma_prime_factors_bound`

Proof that the prime factors of `n` is bounded.

```rust
pub proof fn lemma_prime_factors_bound(n: nat)
    requires n > 0,
    ensures
        forall|p: nat| prime_factors(n).contains(p) ==> 2 <= p <= n,
        prime_factors(n).finite(),
```


### `lemma_prime_factors_is_factor_subset`

Proof that if `d | n`, then the set of prime factors of `d` is the subset of that of `n`.

```rust
pub proof fn lemma_prime_factors_is_factor_subset(n: nat, d: nat)
    requires n > 0 && d > 0 && is_factor_of(n, d),
    ensures prime_factors(d).subset_of(prime_factors(n))
```


### `lemma_prime_factors_gcd_intersect`

Proof that the prime factors of `(a, b)` is the intersection of the prime factors
of `a` and the prime factors of `b`.

```rust
pub proof fn lemma_prime_factors_gcd_intersect(a: nat, b: nat)
    requires a > 0 && b > 0,
    ensures prime_factors(gcd(a, b)) =~= prime_factors(a) * prime_factors(b),
```


### `lemma_prime_factors_lcm_union`

Proof that the prime factors of `[a, b]` is the union of the prime factors
of `a` and the prime factors of `b`.

```rust
pub proof fn lemma_prime_factors_lcm_union(a: nat, b: nat)
    requires a > 0 && b > 0,
    ensures prime_factors(lcm(a, b)) =~= prime_factors(a) + prime_factors(b),
```


### `lemma_prime_factors_disjoint_iff_coprime`

Proof that the prime factors of `a` and the prime factors of `b` are disjoint
iff they are coprime.

```rust
pub proof fn lemma_prime_factors_disjoint_iff_coprime(a: nat, b: nat)
    requires a > 0 && b > 0,
    ensures prime_factors(a).disjoint(prime_factors(b)) <==> is_coprime(a, b),
```


### `lemma_factorization_induct`

Proof of induction over factorization of `n`.
Specifically, if `g(a * b) == g(a) * g(b)` when `a` and `b` are coprime, then
`g(n) = prime_factors(n).fold(g(1), x g(pow(p, vp(n, p))))`.

```rust
pub proof fn lemma_factorization_induct(n: nat, g: spec_fn(nat) -> nat)
    requires
        n > 0,
        forall|a: nat, b: nat| #[trigger] is_coprime(a, b) ==> g(a * b) == g(a) * g(b),
    ensures
        g(n) == prime_factors(n).fold(g(1), |prod: nat, p: nat| prod * g((pow(p as int, vp(n, p)) as nat))),
    decreases n,
```


### `lemma_factorization`

Proof of the fundamental principle of arithmetics, or the factorization
of positive integer `n`.

```rust
pub proof fn lemma_factorization(n: nat)
    requires
        n > 0,
    ensures
        n == prime_factors(n).fold(1, |prod: nat, p: nat| prod * (pow(p as int, vp(n, p)) as nat)),
```
