## Specifying types, functions and methods
By default, Verge uses `#[verifier::external_type_specification]` to introduce types, 
and `assume_specification` to introduce both function calls and associated methods.
However, in certain cases it is necessary to rename a function or alter its signature for Verus. In this case, Verge adds a new function with `#[verifier::external_body]`, whose body contains minimal code that delegates the call to the actual function.
For associated methods, this is done by adding a helper trait that declares the 
altered method signature, then implementing the trait using `#[verifier::external_body]`.

## Specifying traits

When the external trait signature can be specified directly, prefer the `via` pattern:
combine `#[verifier::external_trait_specification]` with
`#[verifier::external_trait_extension(SpecTrait via SpecImplTrait)]`. The external trait spec
keeps calls on the original Rust trait, while the `SpecImplTrait` lets concrete types provide
the spec helper functions used in the method postconditions. `str::fmt::ToStringSpec` and
`str::parse::FromStrSpec` use this style.

Unfortunately, sometimes the `Spec` traits cannot be implemented in Verge directly (often due to Rust's orphan rules when the `Spec` trait is defined in `vstd`). In that case, Verge adopts the **linking lemma** pattern - introduce broadcast lemmas to help Verus interpret the implicit `spec` functions from the `Spec` trait, so that the `Spec` traits can still be used. This works because with the `Spec` trait defined in `vstd`, when it is not explicitly implemented for a certain type `T`, Verus effectively sees specs like `<T as SpecTrait>::xxx` as `uninterp` specs. 

Some trait methods still need concrete `assume_specification` entries for Verus to accept the
external call form, especially associated functions on standard-library impls. Keep those assumes
as thin bridges to the same helper predicates used by the trait extension; do not create a second
semantic model for the concrete implementation (i.e., the `assume_specification` items need no new `requires` or `ensures` clauses attached to them, because the functions already inherit specs from trait specifications).

Use implementation-specific `assume_specification` when a generic external trait spec is not viable
or would create excessive proof load. This remains useful for traits like `core::iter::Iterator`,
where core language constructs must resolve to exactly the original `Iterator::next()` method.

Use a new delegating Verge trait only when the Rust trait signature must change or the external
trait lacks the abstract state needed in its own bounds. This is the case for `verge::io` traits
(e.g., `Read` and `Write`), where the spec needs reader/writer state unavailable from the standard
trait alone.

In all cases, Verge uses macros to minimize boilerplate code.
