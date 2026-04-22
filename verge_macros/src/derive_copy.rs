use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse2, Fields, Ident, Item, ItemStruct, ItemEnum};
use crate::eq_common;

pub fn derive_copy_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new_spanned(attr, "derive_copy takes no arguments")
            .to_compile_error();
    }
    let item: Item = match parse2(item) {
        Ok(item) => item,
        Err(e) => return e.to_compile_error(),
    };
    match item {
        Item::Struct(s) => gen_struct(s),
        Item::Enum(e) => gen_enum(e),
        _ => syn::Error::new(proc_macro2::Span::call_site(),
            "derive_copy can only be applied to structs and enums").to_compile_error(),
    }
}

fn gen_struct(input: ItemStruct) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;
    let fields = &input.fields;
    if eq_common::has_any_verge_attr(fields) {
        return syn::Error::new(proc_macro2::Span::call_site(),
            "derive_copy does not support #[ignored] or #[ignored_with_default] fields. Copy types must copy all fields.")
            .to_compile_error();
    }
    let (_impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let struct_def = match fields {
        Fields::Named(_) => quote! { #(#attrs)* #vis struct #name #generics #where_clause #fields },
        Fields::Unnamed(_) => quote! { #(#attrs)* #vis struct #name #generics #fields #where_clause ; },
        Fields::Unit => quote! { #(#attrs)* #vis struct #name #generics #where_clause ; },
    };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    emit_output(struct_def, name, &g, &tg)
}

fn gen_enum(input: ItemEnum) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;
    let variants = &input.variants;
    let (_impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let enum_def = quote! { #(#attrs)* #vis enum #name #generics #where_clause { #variants } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    emit_output(enum_def, name, &g, &tg)
}

fn emit_output(type_def: TokenStream, name: &Ident, g: &TokenStream, tg: &TokenStream) -> TokenStream {
    quote! {
        ::vstd::prelude::verus! {
            #type_def
            impl #g Copy for #name #tg {}
            impl #g Clone for #name #tg {
                fn clone(&self) -> (ret: Self)
                    ensures Self::strictly_cloned(self, &ret),
                { *self }
            }
            impl #g #name #tg {
                #[allow(unused_parens)]
                pub open spec fn strictly_cloned(a: &Self, b: &Self) -> bool {
                    *a == *b
                }
            }
            impl #g verge::clone::CopyVerified for #name #tg {
                proof fn lemma_clone_identical(a: &Self) {}
            }
        }
    }
}
