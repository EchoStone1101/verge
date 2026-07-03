# `verge::cmp::pointer`

Verified comparison impls for owning pointer types.


## Functions


### `<Box<T, A> as PartialEq>::eq`

Enable `Box<T>` equality.

```rust
pub assume_specification<T: MetaSized + PartialEq, A: Allocator>[ <Box<T, A> as PartialEq>::eq ](a: &Box<T, A>, b: &Box<T, A>) -> bool;
```


### `<Box<T, A> as PartialEq>::ne`

Enable `Box<T>` inequality.

```rust
pub assume_specification<T: MetaSized + PartialEq, A: Allocator>[ <Box<T, A> as PartialEq>::ne ](a: &Box<T, A>, b: &Box<T, A>) -> bool;
```


### `<Box<T, A> as PartialOrd>::partial_cmp`

Enable `Box<T>` partial comparison.

```rust
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Box<T, A> as PartialOrd>::partial_cmp ](a: &Box<T, A>, b: &Box<T, A>) -> Option<Ordering>;
```


### `<Box<T, A> as PartialOrd>::lt`

Enable `Box<T>` less-than comparison.

```rust
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Box<T, A> as PartialOrd>::lt ](a: &Box<T, A>, b: &Box<T, A>) -> bool;
```


### `<Box<T, A> as PartialOrd>::le`

Enable `Box<T>` less-than-or-equal comparison.

```rust
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Box<T, A> as PartialOrd>::le ](a: &Box<T, A>, b: &Box<T, A>) -> bool;
```


### `<Box<T, A> as PartialOrd>::gt`

Enable `Box<T>` greater-than comparison.

```rust
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Box<T, A> as PartialOrd>::gt ](a: &Box<T, A>, b: &Box<T, A>) -> bool;
```


### `<Box<T, A> as PartialOrd>::ge`

Enable `Box<T>` greater-than-or-equal comparison.

```rust
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Box<T, A> as PartialOrd>::ge ](a: &Box<T, A>, b: &Box<T, A>) -> bool;
```


### `<Box<T, A> as Ord>::cmp`

Enable `Box<T>` total comparison.

```rust
pub assume_specification<T: MetaSized + Ord, A: Allocator>[ <Box<T, A> as Ord>::cmp ](a: &Box<T, A>, b: &Box<T, A>) -> Ordering;
```


### `<Rc<T, A> as PartialEq>::eq`

Enable `Rc<T>` equality.

```rust
pub assume_specification<T: MetaSized + PartialEq, A: Allocator>[ <Rc<T, A> as PartialEq>::eq ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;
```


### `<Rc<T, A> as PartialEq>::ne`

Enable `Rc<T>` inequality.

```rust
pub assume_specification<T: MetaSized + PartialEq, A: Allocator>[ <Rc<T, A> as PartialEq>::ne ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;
```


### `<Rc<T, A> as PartialOrd>::partial_cmp`

Enable `Rc<T>` partial comparison.

```rust
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Rc<T, A> as PartialOrd>::partial_cmp ](a: &Rc<T, A>, b: &Rc<T, A>) -> Option<Ordering>;
```


### `<Rc<T, A> as PartialOrd>::lt`

Enable `Rc<T>` less-than comparison.

```rust
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Rc<T, A> as PartialOrd>::lt ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;
```


### `<Rc<T, A> as PartialOrd>::le`

Enable `Rc<T>` less-than-or-equal comparison.

```rust
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Rc<T, A> as PartialOrd>::le ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;
```


### `<Rc<T, A> as PartialOrd>::gt`

Enable `Rc<T>` greater-than comparison.

```rust
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Rc<T, A> as PartialOrd>::gt ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;
```


### `<Rc<T, A> as PartialOrd>::ge`

Enable `Rc<T>` greater-than-or-equal comparison.

```rust
pub assume_specification<T: MetaSized + PartialOrd, A: Allocator>[ <Rc<T, A> as PartialOrd>::ge ](a: &Rc<T, A>, b: &Rc<T, A>) -> bool;
```


### `<Rc<T, A> as Ord>::cmp`

Enable `Rc<T>` total comparison.

```rust
pub assume_specification<T: MetaSized + Ord, A: Allocator>[ <Rc<T, A> as Ord>::cmp ](a: &Rc<T, A>, b: &Rc<T, A>) -> Ordering;
```


### `lemma_box_obeys_eq_spec`

Proof that links `Box<T>` `PartialEq` obedience to `T`.

```rust
pub broadcast axiom fn lemma_box_obeys_eq_spec<T: PartialEq>()
    ensures
        #[trigger] <Box<T> as PartialEqSpec>::obeys_eq_spec() == <T as PartialEqSpec>::obeys_eq_spec();
```


### `lemma_box_eq_spec`

Proof that links `Box<T>` equality with the pointee equality.

```rust
pub broadcast axiom fn lemma_box_eq_spec<T: PartialEq>(a: &Box<T>, b: &Box<T>)
    ensures
        #![trigger <Box<T> as PartialEqSpec>::eq_spec(a, b)]
        <Box<T> as PartialEqSpec>::eq_spec(a, b) == <T as PartialEqSpec>::eq_spec(&**a, &**b);
```


### `lemma_box_obeys_partial_cmp_spec`

Proof that links `Box<T>` `PartialOrd` obedience to `T`.

```rust
pub broadcast axiom fn lemma_box_obeys_partial_cmp_spec<T: PartialOrd>()
    ensures
        #[trigger] <Box<T> as PartialOrdSpec>::obeys_partial_cmp_spec() == <T as PartialOrdSpec>::obeys_partial_cmp_spec();
```


### `lemma_box_partial_cmp_spec`

Proof that links `Box<T>` partial comparison with the pointee comparison.

```rust
pub broadcast axiom fn lemma_box_partial_cmp_spec<T: PartialOrd>(a: &Box<T>, b: &Box<T>)
    ensures
        #![trigger <Box<T> as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <Box<T> as PartialOrdSpec>::partial_cmp_spec(a, b) == <T as PartialOrdSpec>::partial_cmp_spec(&**a, &**b);
```


### `lemma_box_obeys_cmp_spec`

Proof that links `Box<T>` `Ord` obedience to `T`.

```rust
pub broadcast axiom fn lemma_box_obeys_cmp_spec<T: Ord>()
    ensures
        #[trigger] <Box<T> as OrdSpec>::obeys_cmp_spec() == <T as OrdSpec>::obeys_cmp_spec();
```


### `lemma_box_cmp_spec`

Proof that links `Box<T>` total comparison with the pointee comparison.

```rust
pub broadcast axiom fn lemma_box_cmp_spec<T: Ord>(a: &Box<T>, b: &Box<T>)
    ensures
        #![trigger <Box<T> as OrdSpec>::cmp_spec(a, b)]
        <Box<T> as OrdSpec>::cmp_spec(a, b) == <T as OrdSpec>::cmp_spec(&**a, &**b);
```


### `lemma_rc_obeys_eq_spec`

Proof that links `Rc<T>` `PartialEq` obedience to `T`.

```rust
pub broadcast axiom fn lemma_rc_obeys_eq_spec<T: PartialEq>()
    ensures
        #[trigger] <Rc<T> as PartialEqSpec>::obeys_eq_spec() == <T as PartialEqSpec>::obeys_eq_spec();
```


### `lemma_rc_eq_spec`

Proof that links `Rc<T>` equality with the pointee equality.

```rust
pub broadcast axiom fn lemma_rc_eq_spec<T: PartialEq>(a: &Rc<T>, b: &Rc<T>)
    ensures
        #![trigger <Rc<T> as PartialEqSpec>::eq_spec(a, b)]
        <Rc<T> as PartialEqSpec>::eq_spec(a, b) == <T as PartialEqSpec>::eq_spec(&**a, &**b);
```


### `lemma_rc_obeys_partial_cmp_spec`

Proof that links `Rc<T>` `PartialOrd` obedience to `T`.

```rust
pub broadcast axiom fn lemma_rc_obeys_partial_cmp_spec<T: PartialOrd>()
    ensures
        #[trigger] <Rc<T> as PartialOrdSpec>::obeys_partial_cmp_spec() == <T as PartialOrdSpec>::obeys_partial_cmp_spec();
```


### `lemma_rc_partial_cmp_spec`

Proof that links `Rc<T>` partial comparison with the pointee comparison.

```rust
pub broadcast axiom fn lemma_rc_partial_cmp_spec<T: PartialOrd>(a: &Rc<T>, b: &Rc<T>)
    ensures
        #![trigger <Rc<T> as PartialOrdSpec>::partial_cmp_spec(a, b)]
        <Rc<T> as PartialOrdSpec>::partial_cmp_spec(a, b) == <T as PartialOrdSpec>::partial_cmp_spec(&**a, &**b);
```


### `lemma_rc_obeys_cmp_spec`

Proof that links `Rc<T>` `Ord` obedience to `T`.

```rust
pub broadcast axiom fn lemma_rc_obeys_cmp_spec<T: Ord>()
    ensures
        #[trigger] <Rc<T> as OrdSpec>::obeys_cmp_spec() == <T as OrdSpec>::obeys_cmp_spec();
```


### `lemma_rc_cmp_spec`

Proof that links `Rc<T>` total comparison with the pointee comparison.

```rust
pub broadcast axiom fn lemma_rc_cmp_spec<T: Ord>(a: &Rc<T>, b: &Rc<T>)
    ensures
        #![trigger <Rc<T> as OrdSpec>::cmp_spec(a, b)]
        <Rc<T> as OrdSpec>::cmp_spec(a, b) == <T as OrdSpec>::cmp_spec(&**a, &**b);
```
