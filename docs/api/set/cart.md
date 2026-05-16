# `verge::set::cart`

Definitions and lemmas for the Cartesian product of sets in Verus.


## Functions


### `cart`

This function defines the Cartesian product of sets `a` and `b`.

```rust
pub open spec fn cart<A, B>(a: Set<A>, b: Set<B>) -> Set<(A, B)> {
    Set::<(A, B)>::new(|p: (A, B)| a.contains(p.0) && b.contains(p.1))
    }
```


### `lemma_cart_empty`

Proof that `a x b` is empty iff `a` is empty or `b` is empty.

```rust
pub proof fn lemma_cart_empty<A, B>(a: Set<A>, b: Set<B>)
    ensures cart(a, b).is_empty() <==> a.is_empty() || b.is_empty()
```


### `lemma_cart_equality`

Proof that (for non-empty sets) `a1 x b1 == a2 x b2` iff `a1 == a2` and `b1 == b2`.

```rust
pub proof fn lemma_cart_equality<A, B>(a1: Set<A>, b1: Set<B>, a2: Set<A>, b2: Set<B>)
    ensures
        a1 == a2 && b1 == b2 ==> cart(a1, b1) == cart(a2, b2),
        !a1.is_empty() && !b1.is_empty() && !a2.is_empty() && !b2.is_empty()
            && cart(a1, b1) == cart(a2, b2) ==> a1 == a2 && b1 == b2,
```


### `lemma_cart_subset`

Proof that (for non-empty sets) `a1 x b1 <= a2 x b2` iff `a1 <= a2` and `b1 <= b2`.

```rust
pub proof fn lemma_cart_subset<A, B>(a1: Set<A>, b1: Set<B>, a2: Set<A>, b2: Set<B>)
    ensures
        a1.subset_of(a2) && b1.subset_of(b2) ==> cart(a1, b1).subset_of(cart(a2, b2)),
        !a1.is_empty() && !b1.is_empty() && !a2.is_empty() && !b2.is_empty()
            && cart(a1, b1).subset_of(cart(a2, b2)) ==> a1.subset_of(a2) && b1.subset_of(b2),
```


### `lemma_cart_intersect`

Proof that `(a1 x b1) * (a2 x b2)` is equal to `(a1 * a2) x (b1 * b2)`.

```rust
pub proof fn lemma_cart_intersect<A, B>(a1: Set<A>, b1: Set<B>, a2: Set<A>, b2: Set<B>)
    ensures cart(a1, b1) * cart(a2, b2) == cart(a1 * a2, b1 * b2)
```


### `lemma_cart_union_left`

Proof that for sets `a1`, `a2`, and `b`, `a1 x b + a2 x b` is equal to
`(a1 + a2) x b`.

```rust
pub proof fn lemma_cart_union_left<A, B>(a1: Set<A>, a2: Set<A>, b: Set<B>)
    ensures cart(a1, b) + cart(a2, b) == cart(a1 + a2, b)
```


### `lemma_cart_union_right`

Proof that for sets `a`, `b1`, and `b2`, `a x b1 + a x b2` is equal to
`a x (b1 + b2)`.

```rust
pub proof fn lemma_cart_union_right<A, B>(a: Set<A>, b1: Set<B>, b2: Set<B>)
    ensures cart(a, b1) + cart(a, b2) == cart(a, b1 + b2)
```


### `lemma_cart_difference_left`

Proof that for sets `a1`, `a2`, and `b`, `a1 x b - a2 x b` is equal to
`(a1 - a2) x b`.

```rust
pub proof fn lemma_cart_difference_left<A, B>(a1: Set<A>, a2: Set<A>, b: Set<B>)
    ensures cart(a1, b) - cart(a2, b) == cart(a1 - a2, b)
```


### `lemma_cart_difference_right`

Proof that for sets `a`, `b1`, and `b2`, `a x b1 - a x b2` is equal to
`a x (b1 - b2)`.

```rust
pub proof fn lemma_cart_difference_right<A, B>(a: Set<A>, b1: Set<B>, b2: Set<B>)
    ensures cart(a, b1) - cart(a, b2) == cart(a, b1 - b2)
```


### `lemma_cart_len`

Proof that the Cartesian product of sets `a` and `b` is finite if
`a` and `b` are both finite, and that its size is `a.len() * b.len()`.

```rust
pub broadcast proof fn lemma_cart_len<A, B>(a: Set<A>, b: Set<B>)
    requires
        a.finite() && b.finite(),
    ensures
        #[trigger] cart(a, b).finite(),
        #[trigger] cart(a, b).len() == a.len() * b.len(),
    decreases a.len(),
```
