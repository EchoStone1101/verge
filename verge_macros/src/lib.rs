use proc_macro::TokenStream;

mod eq_common;
mod hash_key;
mod derive_clone;
mod derive_copy;
mod derive_default;
mod derive_eq;
mod derive_ord;
mod derive_partial_eq;
mod derive_partial_ord;

#[proc_macro_attribute]
pub fn hash_key(attr: TokenStream, item: TokenStream) -> TokenStream {
    hash_key::hash_key_impl(attr.into(), item.into()).into()
}

#[proc_macro_attribute]
pub fn hash_key_with_clone(attr: TokenStream, item: TokenStream) -> TokenStream {
    hash_key::hash_key_with_clone_impl(attr.into(), item.into()).into()
}

#[proc_macro_attribute]
pub fn derive_partial_eq(attr: TokenStream, item: TokenStream) -> TokenStream {
    derive_partial_eq::derive_partial_eq_impl(attr.into(), item.into()).into()
}

#[proc_macro_attribute]
pub fn derive_eq(attr: TokenStream, item: TokenStream) -> TokenStream {
    derive_eq::derive_eq_impl(attr.into(), item.into()).into()
}

#[proc_macro_attribute]
pub fn derive_partial_ord(attr: TokenStream, item: TokenStream) -> TokenStream {
    derive_partial_ord::derive_partial_ord_impl(attr.into(), item.into()).into()
}

#[proc_macro_attribute]
pub fn derive_ord(attr: TokenStream, item: TokenStream) -> TokenStream {
    derive_ord::derive_ord_impl(attr.into(), item.into()).into()
}

#[proc_macro_attribute]
pub fn derive_clone(attr: TokenStream, item: TokenStream) -> TokenStream {
    derive_clone::derive_clone_impl(attr.into(), item.into()).into()
}

#[proc_macro_attribute]
pub fn derive_copy(attr: TokenStream, item: TokenStream) -> TokenStream {
    derive_copy::derive_copy_impl(attr.into(), item.into()).into()
}

#[proc_macro_attribute]
pub fn derive_default(attr: TokenStream, item: TokenStream) -> TokenStream {
    derive_default::derive_default_impl(attr.into(), item.into()).into()
}
