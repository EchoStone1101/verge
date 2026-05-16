# `verge::nt::gcd`

Proofs and specifications for `gcd`-related properties.
Also contains lemmas about the [Euclidean method](https://en.wikipedia.org/wiki/Euclidean_algorithm).


## Functions


### `gcd`

This function computes the greatest common divisor of `a` and `b`
(denoted as `(a, b)`).

```rust
pub closed spec fn gcd(a: nat, b: nat) -> nat
    recommends a > 0 && b > 0,
```


### `axiom_gcd_properties`

Proof of `(a, b)`'s properties.

```rust
pub proof fn axiom_gcd_properties(a: nat, b: nat)
    requires
        a > 0 && b > 0,
    ensures
        is_common_factor(a, b, gcd(a, b)),
        forall|d: nat| is_common_factor(a, b, d) ==> d <= #[trigger] gcd(a, b),
        gcd(a, b) == gcd(b, a),
```


### `axiom_coprime_gcd`

Proof that `(a, b) == 1` is equivalent to coprimeness.

```rust
pub proof fn axiom_coprime_gcd(a: nat, b: nat)
    ensures a > 0 && b > 0 && gcd(a, b) == 1 <==> is_coprime(a, b),
```


### `lemma_euclidean_induct`

Proof that if the predicate `pred` is preserved by linear combination,
then `pred(a) && pred(b)` implies `pred(gcd(a, b))`.

```rust
pub proof fn lemma_euclidean_induct(a: nat, b: nat, pred: spec_fn(nat) -> bool)
    requires
        a > 0 && b > 0,
        pred(a) && pred(b),
        forall|a0: nat, b0: nat, x: int, y: int|
            pred(a0) && pred(b0) && a0 * x + b0 * y >= 0
                ==> #[trigger] pred((a0 * x + b0 * y) as nat),
    ensures
        pred(gcd(a, b)),
```


### `lemma_gcd_common_factor`

Proof that any common factor `d` of `a` and `b` is also a factor of `(a, b)`.

```rust
pub proof fn lemma_gcd_common_factor(a: nat, b: nat, d: nat)
    requires
        a > 0 && b > 0,
        is_common_factor(a, b, d),
    ensures
        is_factor_of(gcd(a, b), d),
```


### `lemma_gcd_mul`

Proof that `(a * c, b * c) == (a, b) * c`.

```rust
pub proof fn lemma_gcd_mul(a: nat, b: nat, c: nat)
    requires a > 0 && b > 0 && c > 0,
    ensures gcd(a * c, b * c) == gcd(a, b) * c,
```


### `lemma_gcd_div`

Proof that `(a / d, b / d) = (a, b) / d` for any common factor `d` of `a` and `b`.

```rust
pub proof fn lemma_gcd_div(a: nat, b: nat, d: nat)
    requires
        a > 0 && b > 0 && d > 0,
        is_common_factor(a, b, d),
    ensures
        gcd(a / d, b / d) == gcd(a, b) / d,
```


### `lcm`

This function computes the least common multiple of `a` and `b`
(denoted as `[a, b]`).

```rust
pub open spec fn lcm(a: nat, b: nat) -> nat
    recommends a > 0 && b > 0,
        {
        a * b / gcd(a, b)
        }
```


### `axiom_lcm_properties`

Proof of `[a, b]`'s properties.

```rust
pub proof fn axiom_lcm_properties(a: nat, b: nat)
    requires
        a > 0 && b > 0,
    ensures
        is_factor_of(lcm(a, b), a) && is_factor_of(lcm(a, b), b),
        lcm(a, b) != 0,
        forall|m: nat| m > 0 && is_factor_of(m, a) && is_factor_of(m, b) ==> m >= lcm(a, b),
        lcm(a, b) == lcm(b, a),
```


### `axiom_coprime_lcm`

Proof that `[a, b] == a * b` is equivalent to coprimeness.

```rust
pub proof fn axiom_coprime_lcm(a: nat, b: nat)
    ensures a > 0 && b > 0 && lcm(a, b) == a * b <==> is_coprime(a, b),
```


### `lemma_lcm_is_factor`

Proof that `[a, b]` is a factor of any common multiple `n` of `a` and `b`.

```rust
pub proof fn lemma_lcm_is_factor(a: nat, b: nat, n: nat)
    requires
        is_factor_of(n, a),
        is_factor_of(n, b),
    ensures
        is_factor_of(n, a * b / gcd(a, b)),
```


### `gcd_exec`

This function computes `gcd(a, b)` via the Euclidean method, in executable code.

```rust
pub fn gcd_exec(a: usize, b: usize) -> (ret: usize)
    ensures a > 0 && b > 0 ==> ret == gcd(a as nat, b as nat),
```
