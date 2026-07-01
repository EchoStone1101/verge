# `verge::seq`

Extended sequence specifications and lemmas for `Seq` in vstd.


## Traits


### `SeqAdditionalSpec`

```rust
pub trait SeqAdditionalSpec
```


#### `A`

```rust
type A; // element type
    spec fn is_infix_of(self, other: Self) -> bool;
```


#### `is_subrange_of`

```rust
spec fn is_subrange_of(self, other: Self) -> bool;
```


#### `count`

```rust
spec fn count(self, pred: spec_fn(Self::A) -> bool) -> nat;
```


#### `skip_while`

```rust
spec fn skip_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<Self::A>;
```


#### `rskip_while`

```rust
spec fn rskip_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<Self::A>;
```


#### `take_while`

```rust
spec fn take_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<Self::A>;
```


#### `rtake_while`

```rust
spec fn rtake_while(self, pred: spec_fn(Self::A) -> bool) -> Seq<Self::A>;
```


#### `count_while`

```rust
spec fn count_while(self, pred: spec_fn(Self::A) -> bool) -> nat;
```


#### `rcount_while`

```rust
spec fn rcount_while(self, pred: spec_fn(Self::A) -> bool) -> nat;
```


#### `deep_view`

```rust
spec fn deep_view(self) -> Seq<<Self::A as View>::V>
    where Self::A: View;
```


## Functions


### `lemma_seq_flatten_same_length`

```rust
pub proof fn lemma_seq_flatten_same_length<A>(s: Seq<Seq<A>>, l: nat)
    requires
        forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i].len() == l,
    ensures
        s.flatten().len() == s.len() * l,
        forall |i: int| 0 <= i < s.len()
            ==> s.flatten().subrange(i * l, (i + 1) * l) == #[trigger] s[i],
    decreases
        s.len(),
```


### `lemma_seq_is_infix_subrange`

Proof that if `s1` is an infix of `s`, then any subrange of `s1` is also an infix of `s`.

```rust
pub broadcast proof fn lemma_seq_is_infix_subrange<A>(s: Seq<A>, s1: Seq<A>, i: int, j: int)
    requires
        s1.is_infix_of(s),
        0 <= i <= j <= s1.len(),
    ensures
        #[trigger] s1.subrange(i, j).is_infix_of(s),
```


### `lemma_seq_is_subrange_subrange`

Proof that if `s1` is a subrange of `s`, then any subrange of `s1` is also a subrange of `s`.

```rust
pub broadcast proof fn lemma_seq_is_subrange_subrange<A>(s: Seq<A>, s1: Seq<A>, i: int, j: int)
    requires
        s1.is_subrange_of(s),
        0 <= i <= j <= s1.len(),
    ensures
        #[trigger] s1.subrange(i, j).is_subrange_of(s),
```


### `lemma_seq_is_subrange_alt`

Proof that if `s1` is a subrange of `s`, then `s1` is a prefix, suffix, or infix.

```rust
pub broadcast proof fn lemma_seq_is_subrange_alt<A>(s: Seq<A>, s1: Seq<A>)
    ensures
        #[trigger] s1.is_subrange_of(s) <==> {
            ||| s1.is_prefix_of(s)
            ||| s1.is_suffix_of(s)
            ||| s1.is_infix_of(s)
        },
```


### `lemma_seq_concat_while`

Proof that `s.take_while(pred)` and `s.skip_while(pred)` add back to `s`.

```rust
pub broadcast proof fn lemma_seq_concat_while<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #[trigger] (s.take_while(pred) + s.skip_while(pred)) == s,
```


### `lemma_seq_skip_while_ensures`

Proof of `s.skip_while(pred)`'s properties.

```rust
pub broadcast proof fn lemma_seq_skip_while_ensures<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #![trigger s.skip_while(pred)]
        s.skip_while(pred).is_suffix_of(s),
        s.skip_while(pred).len() > 0 ==> !pred(s.skip_while(pred).first()),
        forall|i: int| 0 <= i < s.len() - s.skip_while(pred).len()
            ==> #[trigger] pred(s[i]),
```


### `lemma_seq_take_while_ensures`

Proof of `s.take_while(pred)`'s properties.

```rust
pub broadcast proof fn lemma_seq_take_while_ensures<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #![trigger s.take_while(pred)]
        s.take_while(pred).is_prefix_of(s),
        s.take_while(pred).len() < s.len() ==> !pred(s[s.take_while(pred).len() as int]),
        forall|i: int| 0 <= i < s.take_while(pred).len() ==> #[trigger] pred(s.take_while(pred)[i]),
```


### `lemma_seq_skip_while_defines`

Proof of an alternative way to define `skip_while`.

```rust
pub proof fn lemma_seq_skip_while_defines<A>(s: Seq<A>, pred: spec_fn(A) -> bool, s1: Seq<A>)
    requires
        s1.is_suffix_of(s),
        s1.len() > 0 ==> !pred(s1.first()),
        forall|i: int| 0 <= i < s.len() - s1.len() ==> #[trigger] pred(s[i]),
    ensures
        s1 == s.skip_while(pred),
```


### `lemma_seq_take_while_defines`

Proof of an alternative way to define `take_while`.

```rust
pub proof fn lemma_seq_take_while_defines<A>(s: Seq<A>, pred: spec_fn(A) -> bool, s1: Seq<A>)
    requires
        s1.is_prefix_of(s),
        s1.len() < s.len() ==> !pred(s[s1.len() as int]),
        forall|i: int| 0 <= i < s1.len() ==> #[trigger] pred(s1[i]),
    ensures
        s1 == s.take_while(pred),
```


### `lemma_seq_skip_skip_while`

Proof that `s.skip(n).skip_while(pred) == s.skip_while(pred)` if `0 <= n <= s.take_while(pred).len()`.

```rust
pub broadcast proof fn lemma_seq_skip_skip_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.take_while(pred).len(),
    ensures
        #[trigger] s.skip(n).skip_while(pred) == s.skip_while(pred),
```


### `lemma_seq_skip_take_while`

Proof that `s.skip(n).take_while(pred) == s.take_while(pred).skip(n)`
if `0 <= n <= s.take_while(pred).len()`.

```rust
pub broadcast proof fn lemma_seq_skip_take_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.take_while(pred).len(),
    ensures
        #[trigger] s.skip(n).take_while(pred) == s.take_while(pred).skip(n),
```


### `lemma_seq_take_skip_while`

Proof that `s.take(n).skip_while(pred)` is
(1) empty, if `n <= s.take_while(pred).len()`
(2) `s.skip_while(pred).take(n - s.take_while(pred).len())`, otherwise

```rust
pub broadcast proof fn lemma_seq_take_skip_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.len(),
    ensures
        #![trigger s.take(n).skip_while(pred)]
        n <= s.take_while(pred).len() ==> s.take(n).skip_while(pred).len() == 0,
        n > s.take_while(pred).len() ==>
            s.take(n).skip_while(pred) == s.skip_while(pred).take(n - s.take_while(pred).len()),
```


### `lemma_seq_take_take_while`

Proof that `s.take(n).take_while(pred)` is
(1) `s.take(n)`, if `n <= s.take_while(pred).len()`
(2) `s.take_while(pred)`, otherwise

```rust
pub broadcast proof fn lemma_seq_take_take_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.len(),
    ensures
        #![trigger s.take(n).take_while(pred)]
        n <= s.take_while(pred).len() ==> s.take(n).take_while(pred) == s.take(n),
        n > s.take_while(pred).len() ==> s.take(n).take_while(pred) == s.take_while(pred),
```


### `lemma_seq_rconcat_while`

Proof that `s.rskip_while(pred)` and `s.rtake_while(pred)` add back to `s`.

```rust
pub broadcast proof fn lemma_seq_rconcat_while<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #[trigger] (s.rskip_while(pred) + s.rtake_while(pred)) == s,
```


### `lemma_seq_rskip_while_ensures`

Proof of `s.rskip_while(pred)`'s properties.

```rust
pub broadcast proof fn lemma_seq_rskip_while_ensures<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #![trigger s.rskip_while(pred)]
        s.rskip_while(pred).is_prefix_of(s),
        s.rskip_while(pred).len() > 0 ==> !pred(s.rskip_while(pred).last()),
        forall|i: int| s.rskip_while(pred).len() <= i < s.len()
            ==> #[trigger] pred(s[i]),
```


### `lemma_seq_rtake_while_ensures`

Proof of `s.rtake_while(pred)`'s properties.

```rust
pub broadcast proof fn lemma_seq_rtake_while_ensures<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #![trigger s.rtake_while(pred)]
        s.rtake_while(pred).is_suffix_of(s),
        s.rtake_while(pred).len() < s.len() ==> !pred(s[s.len() - 1 - s.rtake_while(pred).len()]),
        forall|i: int| 0 <= i < s.rtake_while(pred).len() ==> #[trigger] pred(s.rtake_while(pred)[i]),
```


### `lemma_seq_rskip_while_defines`

Proof of an alternative way to define `rskip_while`.

```rust
pub proof fn lemma_seq_rskip_while_defines<A>(s: Seq<A>, pred: spec_fn(A) -> bool, s1: Seq<A>)
    requires
        s1.is_prefix_of(s),
        s1.len() > 0 ==> !pred(s1.last()),
        forall|i: int| s1.len() <= i < s.len() ==> #[trigger] pred(s[i]),
    ensures
        s1 == s.rskip_while(pred),
```


### `lemma_seq_rtake_while_defines`

Proof of an alternative way to define `take_while`.

```rust
pub proof fn lemma_seq_rtake_while_defines<A>(s: Seq<A>, pred: spec_fn(A) -> bool, s1: Seq<A>)
    requires
        s1.is_suffix_of(s),
        s1.len() < s.len() ==> !pred(s[s.len() - 1 - s1.len()]),
        forall|i: int| 0 <= i < s1.len() ==> #[trigger] pred(s1[i]),
    ensures
        s1 == s.rtake_while(pred),
```


### `lemma_seq_take_rskip_while`

Proof that `s.take(n).rskip_while(pred) == s.rskip_while(pred)` if `n >= s.rskip_while(pred).len()`.

```rust
pub broadcast proof fn lemma_seq_take_rskip_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        s.rskip_while(pred).len() <= n <= s.len(),
    ensures
        #[trigger] s.take(n).rskip_while(pred) == s.rskip_while(pred),
```


### `lemma_seq_take_rtake_while`

Proof that `s.take(n).rtake_while(pred) == s.rtake_while(pred).take(n - s.rskip_while(pred).len())`
if `n >= s.rskip_while(pred).len()`.

```rust
pub broadcast proof fn lemma_seq_take_rtake_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        s.rskip_while(pred).len() <= n <= s.len(),
    ensures
        #[trigger] s.take(n).rtake_while(pred) == s.rtake_while(pred).take(n - s.rskip_while(pred).len()),
```


### `lemma_seq_skip_rskip_while`

Proof that `s.skip(n).rskip_while(pred)` is
(1) empty, if `n >= s.rskip_while(pred).len()`
(2) `s.rskip_while(pred).skip(n)`, otherwise

```rust
pub broadcast proof fn lemma_seq_skip_rskip_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.len(),
    ensures
        #![trigger s.skip(n).rskip_while(pred)]
        n >= s.rskip_while(pred).len() ==> s.skip(n).rskip_while(pred).len() == 0,
        n < s.rskip_while(pred).len() ==>
            s.skip(n).rskip_while(pred) == s.rskip_while(pred).skip(n),
```


### `lemma_seq_skip_rtake_while`

Proof that `s.skip(n).rtake_while(pred)` is
(1) `s.skip(n)`, if `n >= s.rskip_while(pred).len()`
(2) `s.rtake_while(pred)`, otherwise

```rust
pub broadcast proof fn lemma_seq_skip_rtake_while<A>(s: Seq<A>, n: int, pred: spec_fn(A) -> bool)
    requires
        0 <= n <= s.len(),
    ensures
        #![trigger s.skip(n).rtake_while(pred)]
        n >= s.rskip_while(pred).len() ==> s.skip(n).rtake_while(pred) == s.skip(n),
        n < s.rskip_while(pred).len() ==> s.skip(n).rtake_while(pred) == s.rtake_while(pred),
```


### `lemma_seq_rskip_while_reverse`

Proof that `s.rskip_while(pred)` is equal to `s.reverse().skip_while(pred).reverse()`.

```rust
pub broadcast proof fn lemma_seq_rskip_while_reverse<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #[trigger] s.rskip_while(pred) == s.reverse().skip_while(pred).reverse(),
```


### `lemma_seq_rtake_while_reverse`

Proof that `s.rtake_while(pred)` is equal to `s.reverse().rtake_while(pred).reverse()`.

```rust
pub broadcast proof fn lemma_seq_rtake_while_reverse<A>(s: Seq<A>, pred: spec_fn(A) -> bool)
    ensures
        #[trigger] s.rtake_while(pred) == s.reverse().take_while(pred).reverse(),
```


### `lemma_seq_count_while_upper_bound`

Proof that a negative witness (`!pred(s[i])`) gives an upper bound
to the size of `s.take_while(pred)`.

```rust
pub broadcast proof fn lemma_seq_count_while_upper_bound<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int)
    requires
        0 <= i < s.len(),
        !pred(s[i]),
    ensures
        #![trigger s.take_while(pred).len(), pred(s[i])]
        #![trigger s.skip_while(pred).len(), pred(s[i])]
        s.take_while(pred).len() <= i,
        s.skip_while(pred).len() >= s.len() - i,
```


### `lemma_seq_count_while_lower_bound`

Proof that a postive witness (`forall|i| 0 <= i < k ==> pred(s[i])`)
gives a lower bound to the size of `s.take_while(pred)`.

```rust
pub broadcast proof fn lemma_seq_count_while_lower_bound<A>(s: Seq<A>, pred: spec_fn(A) -> bool, k: int)
    requires
        0 <= k <= s.len(),
        forall|i: int| 0 <= i < k ==> #[trigger] pred(s[i]),
    ensures
        #![trigger s.take_while(pred).len(), pred(s[k])]
        #![trigger s.skip_while(pred).len(), pred(s[k])]
        s.take_while(pred).len() >= k,
        s.skip_while(pred).len() <= s.len() - k,
```


### `lemma_seq_rcount_while_upper_bound`

Proof that a negative witness (`!pred(s[i])`) gives an upper bound
to the size of `s.rtake_while(pred)`.

```rust
pub broadcast proof fn lemma_seq_rcount_while_upper_bound<A>(s: Seq<A>, pred: spec_fn(A) -> bool, i: int)
    requires
        0 <= i < s.len(),
        !pred(s[i]),
    ensures
        #![trigger s.rtake_while(pred).len(), pred(s[i])]
        #![trigger s.rskip_while(pred).len(), pred(s[i])]
        s.rtake_while(pred).len() <= s.len() - i - 1,
        s.rskip_while(pred).len() >= i + 1,
```


### `lemma_seq_rcount_while_lower_bound`

Proof that a postive witness (`forall|i| k <= i < s.len() ==> pred(s[i])`)
gives a lower bound to the size of `s.rtake_while(pred)`.

```rust
pub broadcast proof fn lemma_seq_rcount_while_lower_bound<A>(s: Seq<A>, pred: spec_fn(A) -> bool, k: int)
    requires
        0 <= k <= s.len(),
        forall|i: int| k <= i < s.len() ==> #[trigger] pred(s[i]),
    ensures
        #![trigger s.rtake_while(pred).len(), pred(s[k])]
        #![trigger s.rskip_while(pred).len(), pred(s[k])]
        s.rtake_while(pred).len() >= s.len() - k,
        s.rskip_while(pred).len() <= k,
```
