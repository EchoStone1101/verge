# `verge::cmp` Test Coverage

This directory contains downstream-style tests for the public executable
comparison APIs exported through `verge::cmp`, with concrete proof assertions
kept adjacent to executable `exec_assert` checks where applicable. Each Rust
module exposes a normal Rust `pub fn run()` hook with progress prints, and
`cmp::run()` calls all migrated cmp modules for the external executable driver.

## Common Public API Families

Proof-only `cmp` submodules that contain no `assume_specification` items are not
listed here. They implement verified traits only, so these downstream tests focus
on modules that expose executable APIs through Verge assumptions.

| Module | Availability | Usability | Soundness / Status |
| --- | --- | --- | --- |
| `array.rs` | Calls `[T; N]` equality, inequality, `PartialOrd::{partial_cmp,lt,le,gt,ge}`, `Ord::cmp`, and `Ord::{min,max,clamp}` on fixed arrays. | Good for equality, inequality, relational ordering, `partial_cmp`, `cmp`, and linking lemmas; WIP for selected-result proofs for `Ord::{min,max,clamp}`. | Executable checks compare equality, inequality, direct relational ordering, and `cmp` results. `TODO(issue)`: `Ord::{min,max,clamp}` are callable, but current downstream proof support does not establish the selected result. `XXX(Verus)`: the array `Ord` impl inherits `min`, `max`, and `clamp` from trait defaults, so those impl-default methods cannot be assume-specified directly. |
| `pointer.rs` | Calls `Box<T>` and `Rc<T>` equality, inequality, relational operators, `partial_cmp`, `cmp`, and `Ord::{min,max,clamp}`. | Good; downstream proofs use `group_pointer_ordering` for concrete pointer ordering checks. | Representative executable checks cover pointer ordering and `min`/`max`/`clamp`; no blocked pointer cmp API noted. |
| `result.rs` | Calls `Result<T, E>` equality, same-variant and cross-variant relational operators, `partial_cmp`, `cmp`, and `Ord::{min,max,clamp}`. | Good for same-variant ordering and Rust's cross-variant `Ok(_) < Err(_)` ordering. | Representative executable checks cover same-variant `Err`/`Ok` ordering, cross-variant ordering, and clamp boundaries. |
| `slice.rs` | Calls `[T]` equality, `PartialOrd::{partial_cmp,lt,le,gt,ge}`, and `cmp` for first-difference and prefix cases. | Good for `eq`, relational ordering, `partial_cmp`, and `cmp`; concrete checks use lexicographic specs where needed. | Representative executable checks cover equality, relational ordering, and direct comparison results. `XXX(Verus)`: the slice `PartialEq` impl inherits `ne` from the trait default, so direct `!=`/`.ne` cannot be assume-specified. |
| `string.rs` | Calls `str` and `String` equality, inequality, relational operators, `partial_cmp`, `cmp`, and `Ord::{min,max,clamp}`. | Good; downstream proofs use string ordering broadcasts and string literal reveals for concrete executable checks. | Representative executable checks cover `str`/`String` ordering and selected-result APIs. |
| `tuple.rs` | Calls tuple and unit `()` equality, inequality, relational operators that Verus accepts, `cmp`, and `Ord::{min,max,clamp}`. | Good for accepted tuple APIs and unit ordering. | Representative executable checks cover accepted tuple ordering. `XXX(Verus)`: tuple `partial_cmp`, `le`, and `ge` attempts remain commented because the needed specs create a cyclic broadcast issue. |
| `vec.rs` | Calls `Vec<T>` equality, `ne`, `partial_cmp`, `cmp`, and `Ord::{min,max,clamp}` for first-difference and prefix cases. | Good; downstream proofs use vstd vector axioms, `group_vec_ordering`, `lexico_eq`, `lexico_cmp`, and vector linking lemmas. | Representative executable checks cover equality, direct ordering, and length sanity for `min`/`max`/`clamp`. `XXX(Verus)`: the `Vec<T>` `PartialOrd` impl inherits relational methods from trait defaults, so `<`, `<=`, `>`, `>=`, `.lt`, `.le`, `.gt`, and `.ge` cannot be assume-specified directly. |
| `vec_deque.rs` | Calls `VecDeque<T>` equality, `partial_cmp`, `cmp`, and `Ord::{min,max,clamp}` for first-difference and prefix cases. | Good; downstream proofs use vstd `VecDeque` axioms, `group_vec_deque_ordering`, `lexico_eq`, `lexico_cmp`, and linking lemmas. | Representative executable checks cover equality, direct ordering, and length sanity for `min`/`max`/`clamp`. `XXX(Verus)`: the `VecDeque<T>` impls inherit `ne` and relational methods from trait defaults, so `!=`, `<`, `<=`, `>`, `>=`, `.ne`, `.lt`, `.le`, `.gt`, and `.ge` cannot be assume-specified directly. |

## Shared Specs and Lemmas

- `lexico_eq`, `lexico_cmp`, `lemma_lexico_eq_reflexive`, and
  `lemma_lexico_cmp_eq_consistent` are exercised through arrays, slices, `Vec`,
  `VecDeque`, and strings.
- WIP: direct downstream coverage is still missing for `lexico_cmp_by_prefix`,
  `lexico_less`, `lexico_greater`, `lexico_incomparable`, `lexico_equal`,
  `lemma_lexico_cmp_tetrachotomy`, `lemma_lexico_cmp_by_prefix`,
  `lemma_lexico_cmp_dual`, `lemma_lexico_cmp_total`, and
  `lemma_lexico_cmp_transitive`, especially `None`/incomparable cases.
- Generic bridge lemmas `lemma_partial_eq_verified`, `lemma_partial_ord_verified`,
  and `lemma_ord_verified` are intentionally not covered here for now; cmp tests
  focus on executable API availability and concrete runtime/spec agreement.
- `Ordering` equality linking lemmas are exercised throughout executable checks by
  direct assertions such as `partial == Some(Ordering::Less)` and
  `cmp == Ordering::Less`.
- Type-specific linking lemmas for arrays, slices, `Vec`, `VecDeque`, and `String`
  are exercised where public APIs expose lexicographic specs.
