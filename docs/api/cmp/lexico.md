# `verge::cmp::lexico`

Generic lexicographic comparison specs and lemmas.


## Functions


### `lexico_eq`

This function encodes lexicographic equality over two sequences.

```rust
pub open spec fn lexico_eq<T: PartialEq>(s1: Seq<T>, s2: Seq<T>) -> bool
    decreases s1.len(),
        {
        if s1.len() == 0 || s2.len() == 0 {
        s1.len() == 0 && s2.len() == 0
        } else {
        s1[0].eq_spec(&s2[0]) && lexico_eq(s1.drop_first(), s2.drop_first())
        }
        }
```


### `lexico_cmp`

This function compares two sequences in the lexicographic order.

```rust
pub open spec fn lexico_cmp<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>) -> Option<Ordering>
    decreases s1.len(),
        {
        if s1.len() == 0 && s2.len() == 0 {
        Some(Ordering::Equal)
        } else if s1.len() == 0 {
        Some(Ordering::Less)
        } else if s2.len() == 0 {
        Some(Ordering::Greater)
        } else {
        match PartialOrdSpec::partial_cmp_spec(&s1[0], &s2[0]) {
            Some(Ordering::Equal) => lexico_cmp(s1.drop_first(), s2.drop_first()),
            cmp => cmp,
        }
        }
        }
```


### `lemma_lexico_eq_symmetric`

Proof that `lexico_eq` is symmetric for `PartialEqVerified` elements.

```rust
pub proof fn lemma_lexico_eq_symmetric<T: PartialEqVerified>(s1: Seq<T>, s2: Seq<T>)
    ensures
        lexico_eq(s1, s2) <==> lexico_eq(s2, s1),
    decreases s1.len() + s2.len(),
```


### `lemma_lexico_eq_transitive`

Proof that `lexico_eq` is transitive for `PartialEqVerified` elements.

```rust
pub proof fn lemma_lexico_eq_transitive<T: PartialEqVerified>(
    s1: Seq<T>,
    s2: Seq<T>,
    s3: Seq<T>,
    )
    requires
        lexico_eq(s1, s2),
        lexico_eq(s2, s3),
    ensures
        lexico_eq(s1, s3),
    decreases s1.len() + s2.len() + s3.len(),
```


### `lemma_lexico_eq_reflexive`

Proof that `lexico_eq` is reflexive for `EqVerified` elements.

```rust
pub proof fn lemma_lexico_eq_reflexive<T: EqVerified>(s: Seq<T>)
    ensures
        lexico_eq(s, s),
    decreases s.len(),
```


### `lexico_cmp_by_prefix`

This function compares two sequences in lexicographic order using the
first non-`Equal` comparison in the common prefix.

```rust
pub open spec fn lexico_cmp_by_prefix<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>) -> Option<Ordering> {
    let head = Seq::<Option<Ordering>>::new(
    min(s1.len() as int, s2.len() as int) as nat,
    |i: int| PartialOrdSpec::partial_cmp_spec(&s1[i], &s2[i])
    );
    if lexico_less(head) {
    Some(Ordering::Less)
    } else if lexico_greater(head) {
    Some(Ordering::Greater)
    } else if lexico_incomparable(head) {
    None
    } else {
    if s1.len() < s2.len() {
    Some(Ordering::Less)
    } else if s1.len() > s2.len() {
    Some(Ordering::Greater)
    } else {
    Some(Ordering::Equal)
    }
    }
    }
```


### `lexico_less`

This function encodes the lexicographic Less: the first non-Equal entry is Less.

```rust
pub open spec fn lexico_less(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
    && s[i] == Some(Ordering::Less)
    && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
    }
```


### `lexico_greater`

This function encodes the lexicographic Greater: the first non-Equal entry is Greater.

```rust
pub open spec fn lexico_greater(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
    && s[i] == Some(Ordering::Greater)
    && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
    }
```


### `lexico_incomparable`

This function encodes the lexicographic Incomparable: the first non-Equal entry is None.

```rust
pub open spec fn lexico_incomparable(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
    && s[i] == None
    && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
    }
```


### `lexico_equal`

This function encodes the lexicographic Equal: all entries are Equal.

```rust
pub open spec fn lexico_equal(s: Seq<Option<Ordering>>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == Some(Ordering::Equal)
    }
```


### `lemma_lexico_cmp_tetrachotomy`

Proof that exactly one of `lexico_less(s)`, `lexico_greater(s)`, `lexico_incomparable(s)`, and
`lexico_equal(s)` holds.

```rust
pub proof fn lemma_lexico_cmp_tetrachotomy(s: Seq<Option<Ordering>>)
    ensures
        ({
            match (
                lexico_less(s),
                lexico_greater(s),
                lexico_incomparable(s),
                lexico_equal(s),
            ) {
                (true, false, false, false)
                | (false, true, false, false)
                | (false, false, true, false)
                | (false, false, false, true)
                    => true,
                _
                    => false,
            }
        }),
```


### `lemma_lexico_cmp_by_prefix`

Proof that the recursive `lexico_cmp` agrees with the equivalent
first-non-`Equal` formulation.

```rust
pub proof fn lemma_lexico_cmp_by_prefix<T: PartialOrd>(s1: Seq<T>, s2: Seq<T>)
    ensures
        lexico_cmp(s1, s2) == lexico_cmp_by_prefix(s1, s2),
    decreases s1.len(),
```


### `lemma_lexico_cmp_eq_consistent`

Proof that `lexico_cmp` returning `Equal` is consistent with `lexico_eq`,
and that equal prefixes are substitutable on the left of a comparison.

```rust
pub proof fn lemma_lexico_cmp_eq_consistent<T: PartialOrdVerified>(s1: Seq<T>, s2: Seq<T>)
    ensures
        lexico_cmp(s1, s2) == Some(Ordering::Equal) <==> lexico_eq(s1, s2),
        lexico_cmp(s1, s2) == Some(Ordering::Equal) ==>
            forall|s3: Seq<T>| lexico_cmp(s1, s3) == lexico_cmp(s2, s3),
    decreases s1.len(),
```


### `lemma_lexico_cmp_dual`

Proof that `lexico_cmp` upholds duality.

```rust
pub proof fn lemma_lexico_cmp_dual<T: PartialOrdVerified>(
    s1: Seq<T>,
    s2: Seq<T>,
    )
    ensures
        ({
            match lexico_cmp(s1, s2) {
                Some(Ordering::Equal) => lexico_cmp(s2, s1) == Some(Ordering::Equal),
                Some(Ordering::Less) => lexico_cmp(s2, s1) == Some(Ordering::Greater),
                Some(Ordering::Greater) => lexico_cmp(s2, s1) == Some(Ordering::Less),
                None => lexico_cmp(s2, s1) == None,
            }
        }),
    decreases s1.len() + s2.len(),
```


### `lemma_lexico_cmp_total`

Proof that `lexico_cmp` is total for `OrdVerified` elements.

```rust
pub proof fn lemma_lexico_cmp_total<T: OrdVerified>(s1: Seq<T>, s2: Seq<T>)
    ensures
        lexico_cmp(s1, s2) is Some,
    decreases s1.len(),
```


### `lemma_lexico_cmp_transitive`

Proof that `lexico_cmp` upholds transitivity for `PartialOrdVerified` elements.

```rust
pub proof fn lemma_lexico_cmp_transitive<T: PartialOrdVerified>(
    s1: Seq<T>,
    s2: Seq<T>,
    s3: Seq<T>,
    )
    requires
        lexico_cmp(s1, s2) == lexico_cmp(s2, s3),
        lexico_cmp(s1, s2) == Some(Ordering::Less)
            || lexico_cmp(s1, s2) == Some(Ordering::Greater),
    ensures
        lexico_cmp(s1, s3) == lexico_cmp(s1, s2),
    decreases s1.len() + s2.len() + s3.len(),
```
