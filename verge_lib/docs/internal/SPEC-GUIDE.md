## Specifying types, functions and methods
By default, Verge uses `#[verifier::external_type_specification]` to introduce types, 
and `assume_specification` to introduce both function calls and associated methods.
However, in certain cases it makes more sense to rename a function or alter its
signature for Verus. In this case, Verge adds a new function with `#[verifier::external_body]`, 
whose body contains minimal code that delegates the call to the actual function.
For associated methods, this is done by adding a helper trait that declares the 
altered method signature, then implementing the trait using `#[verifier::external_body]`.

We give some examples that demonstrate the need for altering signature.
For one, `str::from_utf8_unchecked` is `unsafe` in `std` because it relies on 
a pre-condition that cannot be checked by the compiler, whereas Verus is fully 
capable of proving soundness given proper conditions. Thus, the API is renamed
to `str::from_utf8_verified` in Verge and is no longer `unsafe`.
For another, `str::find` takes a `pat: P where P: Pattern` argument in `std`, 
but specifying this API form adds unnecessary burden to the prover. Verge changes `str::find` 
to accept `pat: &str` - the most common case. 

## Specifying traits
Traits are introduced with `#[verifier::external_trait_specification]`. 
To add specifications, Verge then adds a new trait that contains only `spec` and
`proof` methods, then implement it as needed. For example, to specifiy `std::io::Read`, 
Verge adds the `ReadSpec` trait which crucially contains a `bytes()` spec function representing 
the byte sequence left in any reader instance. 

When it comes to actually introducing trait methods, there are also two ways.
However, neither is the default here, because there are trade-offs for both of them.

The first way is using `assume_specification` on specific implementations of
a trait method. The trade-off: calls to a trait method are resolved to 
the original trait, but the specification is not associated with the trait method, 
only to the implemetation. 
This is useful for traits like `core::iter::Iterator`, which is depended on by
core language constructs like the `for` loop - it is crucial that Verge introduces 
exactly the `core::iter::Iterator::next()` method. However, the downside is that `Iterator::next` 
remains unspecified (only implementations like `<Vec<T> as Iterator>::next` are), 
so specifying generic functions based on the `Iterator` trait is not possible.

The second way is adding a new trait with matching methods, then have the implementations 
delegate the actual calls. This works the exact opposite way: the specification can now 
exist at the trait method level, but the trait method is no longer the original one. 
This is the case for `verge::io` traits (e.g., `Read` and `Write`).
It is also the only viable option when the signature needs to change.

In both cases, Verge uses macros to minimize boilerplace code. 
Note again that the specification is not associated with the original trait method either way;
`#[verifier::external_trait_specification]` requires trait bounds to be identical, 
so it is generally impossible to write useful specification given only the external traits 
(e.g., Verge cannot specify `std::io::Read::read`, because the trait knows nothing about `ReadSpec` 
at the trait level). 