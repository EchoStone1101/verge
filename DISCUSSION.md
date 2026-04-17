# Discussions

### Modeling other `Iterator` methods

Currently `Iterator::next` is the only exposed API in `vstd` and Verge for most `Iterator` types, and it is also done on a per-type basis (using `assume_specification`). It would be helpful to allow access to at least some of the other provided methods in `Iterator` (e.g., `take`, `skip`, `collect`), done in an ergonomic way in Verge.

### Trait invariant proofs 

Can we enforce invariants on important custom trait implementation?

- `PartialEq`: `T::obeys_eq_spec` for derived impls, or proving it for custom types? Does the `vstd` design suffice? Or is it not defensive?

- `Eq`: Can we facilitate proofs for reflexivity?

- `PartialOrd` & `Ord`: similar to `PartialEq`

- Consistency between `PartialOrd`, `Ord`, and `PartialEq`?

- `Clone` - check implementation soundness?
