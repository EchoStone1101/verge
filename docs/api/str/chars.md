# `verge::str::chars`

Character-related string specifications.

## Non-ASCII characters in `spec`-mode
Except for Unicode whitespace, non-ASCII characters are only categorized in Verge specs.
For example, you can directly `assert(!'①'.is_ascii())` (because it is
obvious from the `char` value range), but not `assert('①'.is_numeric())`.
The `exec`-mode `'①'.is_numeric()` will still evaluate to true, giving
`'①'.is_non_ascii_numeric()` - which is `uninterp` and cannot be established
in `spec`-mode otherwise. Unicode whitespace is fully specified by `vstd`.


## Functions


### `is_non_ascii_alphabetic`

```rust
pub uninterp spec fn is_non_ascii_alphabetic(this: char) -> bool;
```


### `is_non_ascii_lowercase`

```rust
pub uninterp spec fn is_non_ascii_lowercase(this: char) -> bool;
```


### `is_non_ascii_uppercase`

```rust
pub uninterp spec fn is_non_ascii_uppercase(this: char) -> bool;
```


### `is_non_ascii_whitespace`

Whether `this` is a non-ASCII character with Unicode's `White_Space` property.

```rust
pub open spec fn is_non_ascii_whitespace(this: char) -> bool {
    !this.is_ascii() && vstd::std_specs::char::is_white_space(this)
    }
```


### `is_non_ascii_control`

```rust
pub uninterp spec fn is_non_ascii_control(this: char) -> bool;
```


### `is_non_ascii_numeric`

```rust
pub uninterp spec fn is_non_ascii_numeric(this: char) -> bool;
```


### `axiom_non_ascii_categories`

Axiom that asserts the implications and exclusivity between the non-ASCII predicates.

Note that the exclusivity stated here is complete - for example, it is possible that
`c.is_alphabetic() && c.is_numeric()` and `c.is_whitespace() && c.is_control()`,
because these combinations are not prohibited by the exclusivity.

```rust
pub axiom fn axiom_non_ascii_categories(c: char)
    ensures
        // implications
        is_non_ascii_lowercase(c) ==> is_non_ascii_alphabetic(c),
        is_non_ascii_uppercase(c) ==> is_non_ascii_alphabetic(c),
        // mutual exclusivity
        is_non_ascii_alphabetic(c) ==> {
            &&& !is_non_ascii_whitespace(c)
            &&& !is_non_ascii_control(c)
            &&& !is_non_ascii_numeric(c)
        },
        is_non_ascii_lowercase(c) ==> {
            &&& !is_non_ascii_uppercase(c)
            &&& !is_non_ascii_whitespace(c)
            &&& !is_non_ascii_control(c)
            &&& !is_non_ascii_numeric(c)
        },
        is_non_ascii_uppercase(c) ==> {
            &&& !is_non_ascii_whitespace(c)
            &&& !is_non_ascii_control(c)
            &&& !is_non_ascii_numeric(c)
        },
        is_non_ascii_whitespace(c) ==> !is_non_ascii_numeric(c),
        is_non_ascii_control(c) ==> !is_non_ascii_numeric(c),
        ;
```
