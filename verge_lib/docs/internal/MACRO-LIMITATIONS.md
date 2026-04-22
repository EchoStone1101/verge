# Derive Macro Limitations

Internal reference for known limitations. To be incorporated into user-facing documentation.

## Enum Ordering

`derive_partial_ord` and `derive_ord` do not support enums. Enum ordering requires discriminant handling and the proof machinery is significantly more complex. Users must implement manually, which involves:
- `PartialEq`, `PartialOrd` (and `Eq`, `Ord` for total order)
- `PartialEqSpecImpl`, `PartialOrdSpecImpl` (and `OrdSpecImpl`)
- `PartialEqVerified`, `PartialOrdVerified` (and `EqVerified`, `OrdVerified`)
- Transitivity proofs for `Less` and `Greater` directions

See `end_to_end.rs` (`CachedResult`) for a manual implementation example.

## Generic Types

The macros do not emit trait bounds (e.g., `where T: PartialEqVerified`). For generic structs like `struct Wrapper<T>(T)`, the macro expands successfully but Verus verification will fail with errors about missing trait implementations on `T`. Users must ensure field types satisfy the required traits.

## `hash_key` Clone Ban Error

`#[hash_key]` emits `impl CloneImpl for T { type Impl = CloneNo; }`, which prevents `Clone` from being implemented via Rust's coherence rules. If a user tries to impl `Clone`, they get a coherence error about `CloneImpl` — not a friendly message. The workaround is `#[hash_key_with_clone]`.

## `#[ignored]` in `derive_clone`

An `#[ignored]` field is still cloned in exec (`self.field.clone()`), but the spec makes no claim about the cloned field's value. This is correct (the clone postcondition simply doesn't mention the field) but may be surprising. If the intent is to reset the field to a default value, use `#[ignored_with_default]` instead.

## Field Attribute Support Matrix

| Macro | `#[ignored]` | `#[ignored_with_default]` |
|-------|:---:|:---:|
| `derive_partial_eq` | filters field from eq | filters field from eq |
| `derive_eq` | filters field from eq | filters field from eq |
| `derive_partial_ord` | filters field from cmp | filters field from cmp |
| `derive_ord` | filters field from cmp | filters field from cmp |
| `derive_clone` | field cloned, no spec constraint | field set to `Default`, spec uses `call_ensures` |
| `derive_copy` | **rejected** | **rejected** |
| `derive_default` | **rejected** | **rejected** |
| `hash_key` | filters from eq + hash | filters from eq + hash |
| `hash_key_with_clone` | filters from eq + hash; field cloned, no spec constraint | filters from eq + hash; field set to Default in clone |

Both attributes on the same field is rejected in all macros that check for it.

## Tuple Support

Rust's orphan rules prevent Verge from implementing vstd's `PartialEqSpecImpl` for tuples (both the trait and the type are foreign). Bare tuples cannot be used in contexts requiring verified comparison specs. Workaround: define a tuple struct instead.

## Copy Semantics Gap

`derive_copy`'s `strictly_cloned` spec uses `*a == *b` (ghost-mode equality), which is not strictly bitwise equality. For immutable references (`&T`), spec `==` compares pointed-to values rather than pointer addresses.
