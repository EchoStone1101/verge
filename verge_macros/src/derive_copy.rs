use proc_macro2::TokenStream;
use quote::{quote, format_ident};
use syn::{parse2, Fields, Ident, Item, ItemStruct, ItemEnum};
use crate::eq_common;

pub fn derive_copy_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    let short_name: Ident = match parse2(attr) {
        Ok(name) => name,
        Err(_) => return syn::Error::new(proc_macro2::Span::call_site(),
            "derive_copy requires a name: #[derive_copy(my_type)]").to_compile_error(),
    };
    let item: Item = match parse2(item) {
        Ok(item) => item,
        Err(e) => return e.to_compile_error(),
    };
    match item {
        Item::Struct(s) => gen_struct(short_name, s),
        Item::Enum(e) => gen_enum(short_name, e),
        _ => syn::Error::new(proc_macro2::Span::call_site(),
            "derive_copy can only be applied to structs and enums").to_compile_error(),
    }
}

fn gen_struct(short_name: Ident, input: ItemStruct) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;
    let fields = &input.fields;
    if eq_common::has_any_ignored(fields) {
        return syn::Error::new(proc_macro2::Span::call_site(),
            "derive_copy does not support #[ignored] fields. Copy types must copy all fields.")
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
    let cloned_fn_name = format_ident!("{}_strictly_cloned", short_name);
    emit_output(struct_def, name, &g, &tg, &cloned_fn_name)
}

fn gen_enum(short_name: Ident, input: ItemEnum) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;
    let variants = &input.variants;
    let (_impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let enum_def = quote! { #(#attrs)* #vis enum #name #generics #where_clause { #variants } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    let cloned_fn_name = format_ident!("{}_strictly_cloned", short_name);
    emit_output(enum_def, name, &g, &tg, &cloned_fn_name)
}

fn emit_output(type_def: TokenStream, name: &Ident, g: &TokenStream, tg: &TokenStream, cloned_fn_name: &Ident) -> TokenStream {
    quote! {
        ::vstd::prelude::verus! {
            #type_def
            impl #g Copy for #name #tg {}
            impl #g Clone for #name #tg {
                fn clone(&self) -> (ret: Self)
                    ensures #cloned_fn_name(self, &ret),
                { *self }
            }
            #[allow(unused_parens)]
            pub open spec fn #cloned_fn_name #g (a: &#name #tg, b: &#name #tg) -> bool {
                *a == *b
            }
            impl #g verge::clone::CopyVerified for #name #tg {
                proof fn lemma_clone_identical(a: &Self) {}
            }
        }
    }
}
