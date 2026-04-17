use proc_macro::TokenStream;

mod hash_key;

/// Attribute macro that derives `Hash`, `PartialEq`, `Eq` for a struct or enum
/// and generates a broadcast axiom establishing `obeys_key_model` for the type.
///
/// The generated axiom requires `obeys_key_model` for each field type as preconditions.
/// A short name must be provided; the generated lemma will be `lemma_{name}_obeys_key_model`.
///
/// # Usage
///
/// ```ignore
/// #[verge_macros::hash_key(my_key)]
/// pub struct MyKey {
///     id: u64,
///     name_hash: u32,
/// }
///
/// // Then in a verus! block:
/// fn example() {
///     broadcast use vstd::std_specs::hash::group_hash_axioms;
///     broadcast use lemma_my_key_obeys_key_model;
///     // obeys_key_model::<MyKey>() is now available
/// }
/// ```
#[proc_macro_attribute]
pub fn hash_key(attr: TokenStream, item: TokenStream) -> TokenStream {
    hash_key::hash_key_impl(attr.into(), item.into()).into()
}
