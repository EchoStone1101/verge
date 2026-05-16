# `verge::nt::util`

Utility proofs and specifications for number theory.


## Functions


### `lemma_pow_n_gt_n`

Proof that `b^n > n` for `b > 1`.

```rust
pub(crate) proof fn lemma_pow_n_gt_n(b: nat, n: nat)
    requires b > 1,
    ensures pow(b as int, n) > n,
    decreases n,
```


### `lemma_bezout_identity_epilogue1`

```rust
pub(crate) proof fn lemma_bezout_identity_epilogue1(a1: int, b1: int, d: int)
    requires
        a1 > 0 && b1 > 0 && d > 0,
        set_nat_range(0, b1 as nat).map(|k: nat| ((k * a1) % b1) as nat) == set_nat_range(0, b1 as nat),
    ensures
        exists|x: int, y: int| 0 <= x < b1 && #[trigger] (a1 * d * x - b1 * d * y) == d,
```


### `lemma_bezout_identity_epilogue2`

```rust
pub(crate) proof fn lemma_bezout_identity_epilogue2(a1: int, b1: int, d: int)
    requires
        exists|x: int, y: int| 0 <= x < b1 && #[trigger] (a1 * d * x - b1 * d * y) == d,
    ensures
        exists|x: int, y: int| 0 <= x < b1 && #[trigger] (a1 * d * x + b1 * d * y) == d,
```


### `lemma_bezout_identity_ext1`

```rust
pub proof fn lemma_bezout_identity_ext1(a: nat, b: nat, m: int)
    requires
        a > 0 && b > 0,
        m % (gcd(a, b) as int) == 0,
    ensures
        exists|x: int, y: int| 0 <= x < b / gcd(a, b) && #[trigger] (a * x + b * y) == m,
```


### `lemma_bezout_identity_ext2`

```rust
pub proof fn lemma_bezout_identity_ext2(a: nat, b: nat, m: int)
    requires
        a > 0 && b > 0,
        m % (gcd(a, b) as int) == 0,
    ensures
        !exists|x1: int, y1: int, x2: int, y2: int|
            0 <= x1 < x2 < b / gcd(a, b)
            && #[trigger] (a * x1 + b * y1) == m
            && #[trigger] (a * x2 + b * y2) == m,
```
