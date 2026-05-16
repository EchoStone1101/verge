# `verge::nt::totient`

Proofs and specifications for the [Euler's totient function](https://en.wikipedia.org/wiki/Euler%27s_totient_function),
also denoted as `phi(n)`.


## Functions


### `totient`

This function defines the totient function `phi(n)`, which computes
the number of integers in `1..=n` that is coprime with `n`,

```rust
pub closed spec fn totient(n: nat) -> nat
```


### `lemma_totient_bound`

Proof that `1 <= phi(n) <= n-1` for `n > 1`.

```rust
pub proof fn lemma_totient_bound(n: nat)
    requires n > 1,
    ensures 1 <= totient(n) <= (n - 1) as nat,
```


### `lemma_totient_zero`

Proof that `phi(0) = 0`.

```rust
pub proof fn lemma_totient_zero()
    ensures totient(0) == 0,
```


### `lemma_totient_one`

Proof that `phi(1) = 1`.

```rust
pub proof fn lemma_totient_one()
    ensures totient(1) == 1,
```


### `lemma_totient_prime`

Proof that `phi(p) = p - 1`.

```rust
pub proof fn lemma_totient_prime(p: nat)
    requires is_prime(p),
    ensures totient(p) == p - 1,
```


### `lemma_totient_prime_pow`

Proof that `phi(p^e) = (p - 1) * p^(e-1)`.

```rust
pub proof fn lemma_totient_prime_pow(p: nat, e: nat)
    requires
        e > 0,
        is_prime(p),
    ensures
        totient(pow(p as int, e) as nat) == ((p - 1) * pow(p as int, (e - 1) as nat)) as nat,
```


### `lemma_totient_coprime_mul`

Proof that `phi(a * b) = phi(a) * phi(b)` if `a` and `b` are coprime.

```rust
pub proof fn lemma_totient_coprime_mul(a: nat, b: nat)
    requires
        is_coprime(a, b),
    ensures
        totient(a * b) == totient(a) * totient(b),
```


### `lemma_totient_factorization`

Proof that `phi(n)` is computed via factorization of `n`.
Specifically, for `n = p1^e1 * ... * pk^ek`, `phi(n) = n * ((p1-1) * ... * (pk-1)) / (p1 * ... * pk)`.

XXX: Unfortunately, it is not possible to use the more direct form:
```
let f = |prod: nat, p: nat| prod * (p - 1) as nat / p;
totient(n) == prime_factors(n).fold(n, f)
```
because the `fold` function requires `f` to be commutative over all inputs, which it is not.

```rust
pub proof fn lemma_totient_factorization(n: nat)
    requires
        n > 0,
    ensures
        totient(n) == n
            * prime_factors(n).fold(1, |prod: nat, p: nat| prod * (p - 1) as nat)
            / prime_factors(n).fold(1, |prod: nat, p: nat| prod * p),
```


### `totients`

This function computes `phi(i)` for `i` in `0..=n`, in executable code.

```rust
pub fn totients(n: usize) -> (ret: Vec<usize>)
    requires isize::MAX > n >= 2,
    ensures
        ret@.len() == n + 1,
        forall|i: nat| #![auto] 0 <= i <= n ==> ret@[i as int] == totient(i),
```
