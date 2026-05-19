# Verus Mutable Reference Migration Plan

**Context**: Verus `0.2026.05.13` requires explicit disambiguation of mutable reference
parameters in postconditions. Bare `*x` / `x@` / `x.method()` in `ensures` for `&mut`
parameters now errors — you must wrap in `old(...)` (pre-state) or `final(...)` (post-state).

Additionally, `&mut` at return position is now fully supported, enabling API upgrades
that were previously impossible.

---

## Part 1 — Syntax Migration (DONE)

### Rule

In any `ensures` clause, every reference to a `&mut` parameter that refers to the
**post-state** must be wrapped in `final(...)`:

```rust
// BEFORE (old Verus)
fn push(s: &mut String, ch: char)
    ensures s@ =~= old(s)@.push(ch);

// AFTER (new Verus)
fn push(s: &mut String, ch: char)
    ensures final(s)@ =~= old(s)@.push(ch);
```

References to **pre-state** already use `old(...)` and are unchanged.

---

## Part 2 — API Upgrades (Opportunities)

### 2a. Remove `ReadBuf` workaround in `io.rs`

**Current state**: The `Read::read()` signature is:
```rust
fn read<B: ReadBuf + ?Sized>(&mut self, buf: &mut B, range: Option<Range<usize>>) -> Result<usize>
```

This exists because Verus previously couldn't handle `&mut [u8]` return from index operations,
making the standard `fn read(&mut self, buf: &mut [u8]) -> Result<usize>` unusable.

**New capability**: Verus now supports `&mut` at return position. The vstd already has:
- `vec_index_mut` returning `&mut T` with `final()` specs
- `Option::as_mut` returning `Option<&mut T>`
- `index_set` for `IndexMut`

**Proposed change**: Replace the `ReadBuf` trait with the standard signature:
```rust
fn read(&mut self, buf: &mut [u8]) -> Result<usize>
```

Callers that need to write to a subrange can use `&mut buf[start..end]` directly,
which is now expressible in Verus.

**Impact**: This is a **breaking API change** affecting:
- `Read` trait definition
- All `Read` implementations (`File`, `Empty`, `Repeat`, `BufReader`, `Cursor`, stdin)
- All callers (downstream users pass `&mut buf` instead of `&mut buf, Some(range)`)
- The `ReadBuf` trait and its impls can be removed entirely

**Verification needed**: Confirm that `&mut buf[start..end]` (producing `&mut [u8]` from
`&mut [u8]` / `&mut Vec<u8>` / `&mut [u8; N]`) works in Verus ensures clauses with `final()`.
Specifically, the spec for `slice_subrange` or equivalent must exist for mutable slices.

**Risk**: Medium. The spec for mutable slice subranging may not yet exist in vstd.
Need to check `vstd::slice` for `slice_index_mut` or similar.

### 2b. Unify iterator design on vstd's `IteratorSpecImpl`

**Current state**: Verge has two iterator patterns:
- `impl_iterator_default!` — for std types (CharIndices, Lines, Args, etc.) used directly
  with `assume_specification` on next() and a custom `IteratorView` trait
- `impl_iterator_verge!` — for Verge-defined wrapper types (Split, SplitN, etc.)
  with `external_body` on next() and the same `IteratorView` trait

Both use a custom `IteratorView` trait returning `(int, Seq<Item>)` and hand-written
ensures on `next()`.

**New capability**: vstd now provides `IteratorSpecImpl` with prophetic `remaining()`,
automatic ensures on `next()`, and for-loop integration (`for x in iter: expr`).

**Proposed change**: Wrap ALL iterator types (including currently-unwrapped ones like
`CharIndices`, `Lines`, `Args`) and implement `IteratorSpecImpl` on each.

This is necessary because:
- Rust's orphan rule prevents implementing `IteratorSpecImpl` for std types directly
- But if every type has a Verge wrapper, we own the type and can implement anything
- This makes Verge a clean downstream consumer of vstd, not a parallel abstraction

**What changes**:
- Remove `IteratorView` trait entirely
- Remove both `impl_iterator_default!` and `impl_iterator_verge!` macros
- Replace with a single `impl_iterator!` macro (or manual impls) that generates:
  1. Wrapper struct + `external_type_specification`
  2. `Iterator` impl with `external_body` next()
  3. `IteratorSpecImpl` impl (remaining, decrease, obeys_prophetic_iter_laws, etc.)
  4. Constructor with `#[verifier::when_used_as_spec(...)]`
- Gains: for-loop syntax, automatic termination, vstd-standard interface
- Types affected: CharIndices, SplitAsciiWhitespace, Lines, Args, Vars,
  Split, SplitInclusive, SplitTerminator, SplitN, MatchIndices, Ancestors, ReadDir

**Verified experimentally**: See `experiments/iter_new_design_3.rs` (wrapper type with
IteratorSpecImpl verifies and integrates with for-loops) and `experiments/iter_soundness.rs`
(design is defensive — lying `remaining()` is caught by vstd's ensures on next()).

**Soundness note**: The design is defensive. If `obeys_prophetic_iter_laws() = true` and
`remaining()` doesn't match the actual exec behavior, Verus rejects the `next()` impl.
The only bypass is `external_body` on `next()`, which is the standard trust boundary.

### 2c. Explore `IndexMut` support

**Current state**: Verge doesn't expose `IndexMut` for any types.

**New capability**: vstd now provides `index_set` and `IndexSetTrustedSpec`. Vec already
has `vec_index_mut` returning `&mut T`.

**Opportunity**: If Verge wraps types that support indexing (currently none do directly),
this could be leveraged. **Low priority** — no current types need this.

### 2d. Explore returning `&mut` from trait methods

**Current state**: Some trait methods are constrained by the old limitation. For instance,
`BufRead::fill_buf()` returns `Result<&[u8]>` (immutable) — the standard `std::io::BufRead`
also returns immutable, so no change needed there.

**Opportunity**: Review if any Verge trait methods would benefit from returning `&mut`.
Currently none identified beyond the `ReadBuf` case.

---

## Execution Order

1. **Syntax migration** (Part 1) — mechanical, module by module:
   1. `mem.rs` (2 errors, simplest, good warmup)
   2. `str/string.rs` (9 errors, mechanical)
   3. `iter.rs` (11 errors, macro changes affect all iterator users)
   4. `fs/path.rs` (4 errors)
   5. `io.rs` (4 errors, trait definitions)
   6. `fs.rs` (16 errors)
   7. `io/impls.rs` (41 errors, most tedious)
   8. `io/stdio.rs` (1 error)
   9. `cmp.rs` (deprecation warnings)
   10. `fs.rs:361`, `io/stdio.rs:152` (redundant attribute warnings)

2. **Verify each module** after migration with `cargo-verus focus`.

3. **ReadBuf removal** (Part 2a) — requires:
   1. Experimental verification that `&mut buf[range]` works in Verus specs
   2. If confirmed: redesign Read trait, update all impls and tests
   3. If not confirmed: defer to future Verus version

4. **Full verification** of the entire crate.
