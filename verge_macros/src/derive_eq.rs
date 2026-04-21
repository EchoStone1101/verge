use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse2, Fields, Ident, Item, ItemEnum, ItemStruct};

use crate::eq_common::{self, *};

pub fn derive_eq_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new_spanned(attr, "derive_eq takes no arguments").to_compile_error();
    }
    let item: Item = match parse2(item) {
        Ok(item) => item,
        Err(e) => return e.to_compile_error(),
    };
    match item {
        Item::Struct(s) => gen_struct(s),
        Item::Enum(e) => gen_enum(e),
        _ => syn::Error::new(proc_macro2::Span::call_site(),
            "derive_eq can only be applied to structs and enums").to_compile_error(),
    }
}

fn gen_struct(input: ItemStruct) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;
    let fields = &input.fields;
    let (_impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let stripped = eq_common::strip_ignored_attrs(fields);
    let struct_def = match fields {
        Fields::Named(_) => quote! { #(#attrs)* #vis struct #name #generics #where_clause #stripped },
        Fields::Unnamed(_) => quote! { #(#attrs)* #vis struct #name #generics #stripped #where_clause ; },
        Fields::Unit => quote! { #(#attrs)* #vis struct #name #generics #where_clause ; },
    };
    let code = gen_struct_field_code(fields);
    let openness = if all_fields_pub(fields) { quote! { open } } else { quote! { closed } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    emit_eq(struct_def, name, &g, &tg, &openness, &code)
}

fn gen_enum(input: ItemEnum) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;
    let variants = &input.variants;
    let (_impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let enum_def = quote! { #(#attrs)* #vis enum #name #generics #where_clause { #variants } };
    let all_pub = variants.iter().all(|v| all_fields_pub(&v.fields));
    let mut exec_arms = Vec::new();
    let mut spec_arms = Vec::new();
    let mut sym_arms = Vec::new();
    let mut trans_arms = Vec::new();
    let mut refl_arms = Vec::new();
    for variant in variants {
        let arms = gen_enum_variant_arms(name, variant);
        exec_arms.extend(arms.exec_arms);
        spec_arms.extend(arms.spec_arms);
        sym_arms.extend(arms.sym_arms);
        trans_arms.extend(arms.trans_arms);
        refl_arms.extend(arms.refl_arms);
    }
    let code = StructFieldCode {
        eq_body: quote! { match (self, other) { #(#exec_arms,)* _ => false, } },
        eq_spec_body: quote! { match (self, other) { #(#spec_arms,)* _ => false, } },
        sym_body: quote! { match (a, b) { #(#sym_arms,)* _ => {}, } },
        trans_body: quote! { match (a, b, c) { #(#trans_arms,)* _ => {}, } },
        refl_body: quote! { match a { #(#refl_arms,)* } },
    };
    let openness = if all_pub { quote! { open } } else { quote! { closed } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    emit_eq(enum_def, name, &g, &tg, &openness, &code)
}

fn emit_eq(
    type_def: TokenStream, name: &Ident, generics: &TokenStream,
    ty_generics: &TokenStream, openness: &TokenStream, code: &StructFieldCode,
) -> TokenStream {
    let eq_body = &code.eq_body;
    let eq_spec_body = &code.eq_spec_body;
    let sym_body = &code.sym_body;
    let trans_body = &code.trans_body;
    let refl_body = &code.refl_body;
    quote! {
        ::vstd::prelude::verus! {
            #type_def
            impl #generics PartialEq for #name #ty_generics {
                fn eq(&self, other: &Self) -> (r: bool) { #eq_body }
            }
            impl #generics Eq for #name #ty_generics {}
            impl #generics vstd::std_specs::cmp::PartialEqSpecImpl for #name #ty_generics {
                open spec fn obeys_eq_spec() -> bool { true }
                #openness spec fn eq_spec(&self, other: &Self) -> bool { #eq_spec_body }
            }
            impl #generics verge::cmp::PartialEqVerified for #name #ty_generics {
                proof fn lemma_eq_symmetric(a: &Self, b: &Self) { #sym_body }
                proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) { #trans_body }
            }
            impl #generics verge::cmp::EqVerified for #name #ty_generics {
                proof fn lemma_eq_reflexive(a: &Self) { #refl_body }
            }
        }
    }
}
