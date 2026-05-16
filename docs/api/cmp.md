# `verge::cmp`

Verified trait invariants for comparison traits.

## Trait-Level Invariants
Rust's comparison traits (`PartialEq`, `Eq`, `PartialOrd`, `Ord`) carry implicit
invariants that the compiler does not enforce. For example, `PartialEq` should be
symmetric and transitive, and `Eq` should additionally be reflexive. `vstd` provides
the spec scaffolding (`eq_spec`, `obeys_eq_spec`, etc.) but does not mandate that
these invariants are proven for user-defined types.

Verge addresses this with "verified" sub-traits (e.g., `PartialEqVerified`) that
require the user to provide proofs of the relevant invariants as trait methods.
Implementing these traits is the recommended way to establish trait correctness
for custom types in verified Rust code.

## Known Limitations
Tuples implement `PartialEq`, `Eq`, `PartialOrd`, and `Ord` in `std`; however their
specs are not in `vstd` yet, and Verge cannot provide that implementaton (since the spec
extension traits are defined in `vstd`).
The current recommended workaround is to explictly define the tuple as a *tuple struct*,
then use the `derive_*` macros provided by Verge to get the derived trait implementation
as well as proof of invariants.

For example:

```ignore
#[verge_macros::derive_eq]
struct Pair(u8, i32);

fn compare_pairs(p1: &Pair, p2: &Pair) -> (ret: bool)
    returns
        PartialEqSpec::eq_spec(p1, p2),
{
    proof { PartialEqVerified::lemma_eq_symmetric(p1, p2); }
    p2 == p1
}
```


## Traits


### `PartialEqVerified`

A verified `PartialEq` that requires proofs of symmetry and transitivity
for the type's `eq_spec`.

Implementing this trait certifies that the type's `PartialEq` implementation satisfies
the expected mathematical properties.

# Usage

```ignore
impl PartialEqVerified for MyType {
    proof fn lemma_eq_symmetric(a: &Self, b: &Self) {
        // prove a.eq_spec(b) <==> b.eq_spec(a)
    }
    proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {
        // prove a.eq_spec(b) && b.eq_spec(c) ==> a.eq_spec(c)
    }
}
```

```rust
pub trait PartialEqVerified: PartialEq
```


#### `lemma_eq_symmetric`

Proof that `eq_spec` is symmetric.

```rust
proof fn lemma_eq_symmetric(a: &Self, b: &Self)
    requires
        Self::obeys_eq_spec(),
    ensures
        a.eq_spec(b) <==> b.eq_spec(a);
```


#### `lemma_eq_transitive`

Proof that `eq_spec` is transitive.

```rust
proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self)
    requires
        Self::obeys_eq_spec(),
        a.eq_spec(b),
        b.eq_spec(c),
    ensures
        a.eq_spec(c);
```


### `EqVerified`

A verified `Eq` that additionally requires a proof of reflexivity for `eq_spec`.

```rust
pub trait EqVerified: Eq + PartialEqVerified
```


#### `lemma_eq_reflexive`

Proof that `eq_spec` is reflexive.

```rust
proof fn lemma_eq_reflexive(a: &Self)
    requires Self::obeys_eq_spec(),
    ensures a.eq_spec(a);
```


### `PartialOrdVerified`

A verified `PartialOrd` that requires proofs of the ordering invariants for
`partial_cmp_spec`.

The proof obligations correspond to `vstd::laws_cmp::obeys_partial_cmp_spec_properties`:
- Consistency with `eq_spec`
- Duality between `Less` and `Greater`
- Transitivity of `Less`
- Transitivity of `Greater`

```rust
pub trait PartialOrdVerified: PartialOrd + PartialEqVerified
```


#### `lemma_cmp_eq_consistent`

Proof that `partial_cmp_spec` returning `Equal` is equivalent to `eq_spec`.

```rust
proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self)
    requires
        Self::obeys_eq_spec(),
        Self::obeys_partial_cmp_spec(),
    ensures
        a.partial_cmp_spec(b) == Some(Ordering::Equal) <==> a.eq_spec(b);
```


#### `lemma_cmp_dual`

Proof that `Less` in one direction means `Greater` in the other.

```rust
proof fn lemma_cmp_dual(a: &Self, b: &Self)
    requires
        Self::obeys_partial_cmp_spec(),
    ensures
        a.partial_cmp_spec(b) == Some(Ordering::Less)
            <==> b.partial_cmp_spec(a) == Some(Ordering::Greater);
```


#### `lemma_cmp_less_transitive`

Proof that `Less` is transitive.

```rust
proof fn lemma_cmp_less_transitive(a: &Self, b: &Self, c: &Self)
    requires
        Self::obeys_partial_cmp_spec(),
        a.partial_cmp_spec(b) == Some(Ordering::Less),
        b.partial_cmp_spec(c) == Some(Ordering::Less),
    ensures
        a.partial_cmp_spec(c) == Some(Ordering::Less);
```


#### `lemma_cmp_greater_transitive`

Proof that `Greater` is transitive.

```rust
proof fn lemma_cmp_greater_transitive(a: &Self, b: &Self, c: &Self)
    requires
        Self::obeys_partial_cmp_spec(),
        a.partial_cmp_spec(b) == Some(Ordering::Greater),
        b.partial_cmp_spec(c) == Some(Ordering::Greater),
    ensures
        a.partial_cmp_spec(c) == Some(Ordering::Greater);
```


#### `lemma_cmp_comparable`

Proof that comparability is transitive: if `a` is comparable to `b` and
`b` is comparable to `c`, then `a` is comparable to `c`.

```rust
proof fn lemma_cmp_comparable(a: &Self, b: &Self, c: &Self)
    requires
        Self::obeys_partial_cmp_spec(),
        a.partial_cmp_spec(b).is_some(),
        b.partial_cmp_spec(c).is_some(),
    ensures
        a.partial_cmp_spec(c).is_some();
```


#### `lemma_less_eq_subst`

`Less` is substitutive on the right with respect to `eq_spec`.
Default proof: by ruling out `Equal` and `Greater` using eq-consistency,
eq-transitivity, duality, less-transitivity, and comparability.

```rust
proof fn lemma_less_eq_subst(a: &Self, b: &Self, c: &Self)
    requires
        Self::obeys_eq_spec(),
        Self::obeys_partial_cmp_spec(),
        a.partial_cmp_spec(b) == Some(Ordering::Less),
        b.eq_spec(c),
    ensures
        a.partial_cmp_spec(c) == Some(Ordering::Less),
```


#### `lemma_eq_less_subst`

`Less` is substitutive on the left with respect to `eq_spec`.

```rust
proof fn lemma_eq_less_subst(a: &Self, b: &Self, c: &Self)
    requires
        Self::obeys_eq_spec(),
        Self::obeys_partial_cmp_spec(),
        a.eq_spec(b),
        b.partial_cmp_spec(c) == Some(Ordering::Less),
    ensures
        a.partial_cmp_spec(c) == Some(Ordering::Less),
```


#### `lemma_greater_eq_subst`

`Greater` is substitutive on the right with respect to `eq_spec`.

```rust
proof fn lemma_greater_eq_subst(a: &Self, b: &Self, c: &Self)
    requires
        Self::obeys_eq_spec(),
        Self::obeys_partial_cmp_spec(),
        a.partial_cmp_spec(b) == Some(Ordering::Greater),
        b.eq_spec(c),
    ensures
        a.partial_cmp_spec(c) == Some(Ordering::Greater),
```


#### `lemma_eq_greater_subst`

`Greater` is substitutive on the left with respect to `eq_spec`.

```rust
proof fn lemma_eq_greater_subst(a: &Self, b: &Self, c: &Self)
    requires
        Self::obeys_eq_spec(),
        Self::obeys_partial_cmp_spec(),
        a.eq_spec(b),
        b.partial_cmp_spec(c) == Some(Ordering::Greater),
    ensures
        a.partial_cmp_spec(c) == Some(Ordering::Greater),
```


### `OrdVerified`

A verified `Ord` that requires a proof that `cmp_spec` is consistent with
`partial_cmp_spec` (and therefore total).

```rust
pub trait OrdVerified: Ord + EqVerified + PartialOrdVerified
```


#### `lemma_cmp_consistent`

Proof that `partial_cmp_spec` always equals `Some(cmp_spec(...))`.

```rust
proof fn lemma_cmp_consistent(a: &Self, b: &Self)
    requires
        Self::obeys_cmp_spec(),
        Self::obeys_partial_cmp_spec(),
    ensures
        a.partial_cmp_spec(b) == Some(a.cmp_spec(b));
```


## Functions


### `lemma_partial_eq_verified`

For any type implementing `PartialEqVerified`, the full `laws_eq::obeys_eq_spec`
predicate holds.

```rust
pub proof fn lemma_partial_eq_verified<T: PartialEqVerified>()
    requires T::obeys_eq_spec(),
    ensures laws_eq::obeys_eq_spec::<T>(),
```


### `lemma_partial_ord_verified`

For any type implementing `PartialOrdVerified`, the
`laws_cmp::obeys_partial_cmp_spec_properties` predicate holds.

```rust
pub proof fn lemma_partial_ord_verified<T: PartialOrdVerified>()
    requires
        T::obeys_eq_spec(),
        T::obeys_partial_cmp_spec(),
    ensures
        laws_cmp::obeys_partial_cmp_spec_properties::<T>(),
```


### `lemma_ord_verified`

For any type implementing `OrdVerified`, the full `laws_cmp::obeys_cmp_spec`
predicate holds.

```rust
pub proof fn lemma_ord_verified<T: OrdVerified>()
    requires
        T::obeys_eq_spec(),
        T::obeys_partial_cmp_spec(),
        T::obeys_cmp_spec(),
    ensures
        laws_cmp::obeys_cmp_spec::<T>(),
```


### `lexico_less`

Lexicographic Less: the first non-Equal entry is Less.

```rust
pub open spec fn lexico_less(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
    && s[i] == Some(Ordering::Less)
    && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
    }
```


### `lexico_greater`

Lexicographic Greater: the first non-Equal entry is Greater.

```rust
pub open spec fn lexico_greater(s: Seq<Option<Ordering>>) -> bool {
    exists|i: int| 0 <= i < s.len()
    && s[i] == Some(Ordering::Greater)
    && forall|j: int| 0 <= j < i ==> s[j] == Some(Ordering::Equal)
    }
```


### `lexico_equal`

Lexicographic Equal: all entries are Equal.

```rust
pub open spec fn lexico_equal(s: Seq<Option<Ordering>>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == Some(Ordering::Equal)
    }
```
