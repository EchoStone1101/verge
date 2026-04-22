use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse2, Fields, Ident, Item, ItemEnum, ItemStruct};

use crate::eq_common::{self, *};
use crate::derive_eq::emit_eq;

pub fn hash_key_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new_spanned(attr, "hash_key takes no arguments").to_compile_error();
    }
    let item: Item = match parse2(item) {
        Ok(item) => item,
        Err(e) => return e.to_compile_error(),
    };
    match item {
        Item::Struct(s) => gen_hash_key_struct(s, false),
        Item::Enum(e) => gen_hash_key_enum(e, false),
        _ => syn::Error::new(proc_macro2::Span::call_site(),
            "hash_key can only be applied to structs and enums").to_compile_error(),
    }
}

pub fn hash_key_with_clone_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new_spanned(attr, "hash_key_with_clone takes no arguments").to_compile_error();
    }
    let item: Item = match parse2(item) {
        Ok(item) => item,
        Err(e) => return e.to_compile_error(),
    };
    match item {
        Item::Struct(s) => gen_hash_key_struct(s, true),
        Item::Enum(e) => gen_hash_key_enum(e, true),
        _ => syn::Error::new(proc_macro2::Span::call_site(),
            "hash_key_with_clone can only be applied to structs and enums").to_compile_error(),
    }
}

fn gen_hash_key_struct(input: ItemStruct, with_clone: bool) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;
    let fields = &input.fields;
    if eq_common::has_conflicting_attrs(fields) {
        return syn::Error::new(proc_macro2::Span::call_site(),
            "a field cannot have both #[ignored] and #[ignored_with_default].")
            .to_compile_error();
    }
    let (_impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let stripped = eq_common::strip_ignored_attrs(fields);
    let struct_def = match fields {
        Fields::Named(_) => quote! { #(#attrs)* #vis struct #name #generics #where_clause #stripped },
        Fields::Unnamed(_) => quote! { #(#attrs)* #vis struct #name #generics #stripped #where_clause ; },
        Fields::Unit => quote! { #(#attrs)* #vis struct #name #generics #where_clause ; },
    };
    let eq_code = gen_struct_field_code(fields);
    let openness = if all_fields_pub(fields) { quote! { open } } else { quote! { closed } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    let eq_output = emit_eq(struct_def, name, &g, &tg, &openness, &eq_code);
    let hash_impl = build_struct_hash_impl(name, &g, &tg, fields);
    let key_model_proof = build_key_model_proof(name, &g, &tg);
    let clone_or_ban = if with_clone {
        build_clone_and_clone_partial_eq_struct(name, &g, &tg, &openness, vis, fields)
    } else {
        build_clone_ban(name, &g, &tg)
    };
    quote! { #eq_output #hash_impl #clone_or_ban #key_model_proof }
}

fn gen_hash_key_enum(input: ItemEnum, with_clone: bool) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;
    let variants = &input.variants;
    for v in variants {
        if eq_common::has_conflicting_attrs(&v.fields) {
            return syn::Error::new(proc_macro2::Span::call_site(),
                "a field cannot have both #[ignored] and #[ignored_with_default].")
                .to_compile_error();
        }
    }
    let (_impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let enum_def = quote! { #(#attrs)* #vis enum #name #generics #where_clause { #variants } };
    let all_pub = variants.iter().all(|v| eq_common::all_fields_pub(&v.fields));
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
    let eq_code = StructFieldCode {
        eq_body: quote! { match (self, other) { #(#exec_arms,)* _ => false, } },
        eq_spec_body: quote! { match (self, other) { #(#spec_arms,)* _ => false, } },
        sym_body: quote! { match (a, b) { #(#sym_arms,)* _ => {}, } },
        trans_body: quote! { match (a, b, c) { #(#trans_arms,)* _ => {}, } },
        refl_body: quote! { match a { #(#refl_arms,)* } },
    };
    let openness = if all_pub { quote! { open } } else { quote! { closed } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    let eq_output = emit_eq(enum_def, name, &g, &tg, &openness, &eq_code);
    let hash_impl = build_enum_hash_impl(name, &g, &tg, variants);
    let key_model_proof = build_key_model_proof(name, &g, &tg);
    let clone_or_ban = if with_clone {
        build_clone_and_clone_partial_eq_enum(name, &g, &tg, &openness, vis, variants)
    } else {
        build_clone_ban(name, &g, &tg)
    };
    quote! { #eq_output #hash_impl #clone_or_ban #key_model_proof }
}

// --- Hash impl generation ---

fn build_struct_hash_impl(name: &Ident, g: &TokenStream, tg: &TokenStream, fields: &Fields) -> TokenStream {
    let hash_body = match fields {
        Fields::Named(f) => {
            let stmts: Vec<TokenStream> = f.named.iter()
                .filter(|f| !eq_common::is_field_filtered(f))
                .map(|field| {
                    let fname = field.ident.as_ref().unwrap();
                    quote! { self.#fname.hash(state); }
                }).collect();
            quote! { #(#stmts)* }
        },
        Fields::Unnamed(f) => {
            let stmts: Vec<TokenStream> = f.unnamed.iter().enumerate()
                .filter(|(_, f)| !eq_common::is_field_filtered(f))
                .map(|(i, _)| {
                    let idx = syn::Index::from(i);
                    quote! { self.#idx.hash(state); }
                }).collect();
            quote! { #(#stmts)* }
        },
        Fields::Unit => quote! {},
    };
    quote! {
        #[verifier::external]
        impl #g ::core::hash::Hash for #name #tg {
            fn hash<H: ::core::hash::Hasher>(&self, state: &mut H) {
                #hash_body
            }
        }
    }
}

fn build_enum_hash_impl(
    name: &Ident, g: &TokenStream, tg: &TokenStream,
    variants: &syn::punctuated::Punctuated<syn::Variant, syn::token::Comma>,
) -> TokenStream {
    let arms: Vec<TokenStream> = variants.iter().map(|v| {
        let vname = &v.ident;
        match &v.fields {
            Fields::Named(f) => {
                let field_names: Vec<&Ident> = f.named.iter()
                    .map(|f| f.ident.as_ref().unwrap()).collect();
                let binds: Vec<Ident> = field_names.iter()
                    .map(|n| Ident::new(&format!("f_{}", n), n.span())).collect();
                let pat: Vec<TokenStream> = field_names.iter().zip(binds.iter())
                    .map(|(n, b)| quote! { #n: #b }).collect();
                let stmts: Vec<TokenStream> = f.named.iter().zip(binds.iter())
                    .filter(|(f, _)| !eq_common::is_field_filtered(f))
                    .map(|(_, b)| quote! { #b.hash(state); })
                    .collect();
                quote! { #name::#vname { #(#pat),* } => { #(#stmts)* } }
            },
            Fields::Unnamed(f) => {
                let binds: Vec<Ident> = (0..f.unnamed.len())
                    .map(|i| Ident::new(&format!("f_{}", i), proc_macro2::Span::call_site())).collect();
                let stmts: Vec<TokenStream> = f.unnamed.iter().zip(binds.iter())
                    .filter(|(f, _)| !eq_common::is_field_filtered(f))
                    .map(|(_, b)| quote! { #b.hash(state); })
                    .collect();
                quote! { #name::#vname(#(#binds),*) => { #(#stmts)* } }
            },
            Fields::Unit => {
                quote! { #name::#vname => {} }
            },
        }
    }).collect();
    quote! {
        #[verifier::external]
        impl #g ::core::hash::Hash for #name #tg {
            fn hash<H: ::core::hash::Hasher>(&self, state: &mut H) {
                ::core::mem::discriminant(self).hash(state);
                match self { #(#arms,)* }
            }
        }
    }
}

// --- Clone ban ---

fn build_clone_ban(name: &Ident, g: &TokenStream, tg: &TokenStream) -> TokenStream {
    quote! {
        impl #g verge::clone::CloneImpl for #name #tg {
            type Impl = verge::clone::CloneNo;
        }
    }
}

// --- Clone + ClonePartialEq generation ---

fn build_clone_and_clone_partial_eq_struct(
    name: &Ident, g: &TokenStream, tg: &TokenStream,
    openness: &TokenStream, vis: &syn::Visibility, fields: &Fields,
) -> TokenStream {
    let clone_body = build_struct_clone_exec(name, fields);
    let cloned_spec = build_struct_cloned_spec(fields);
    let clone_eq_proof = build_struct_clone_eq_proof(fields);
    quote! {
        ::vstd::prelude::verus! {
            impl #g Clone for #name #tg {
                fn clone(&self) -> (ret: Self)
                    ensures Self::strictly_cloned(self, &ret),
                { #clone_body }
            }
            impl #g #name #tg {
                #vis #openness spec fn strictly_cloned(a: &Self, b: &Self) -> bool {
                    #cloned_spec
                }
            }
            impl #g verge::clone::ClonePartialEq for #name #tg {
                proof fn lemma_clone_preserves_eq(a: &Self) {
                    #clone_eq_proof
                }
            }
        }
    }
}

fn build_clone_and_clone_partial_eq_enum(
    name: &Ident, g: &TokenStream, tg: &TokenStream,
    openness: &TokenStream, vis: &syn::Visibility,
    variants: &syn::punctuated::Punctuated<syn::Variant, syn::token::Comma>,
) -> TokenStream {
    let (clone_arms, spec_arms) = crate::derive_clone::build_enum_clone_arms_pub(name, variants);
    let clone_body = quote! { match self { #(#clone_arms,)* } };
    let cloned_body = quote! { match (a, b) { #(#spec_arms,)* _ => false, } };
    let clone_eq_proof = build_enum_clone_eq_proof(name, variants);
    quote! {
        ::vstd::prelude::verus! {
            impl #g Clone for #name #tg {
                fn clone(&self) -> (ret: Self)
                    ensures Self::strictly_cloned(self, &ret),
                { #clone_body }
            }
            impl #g #name #tg {
                #vis #openness spec fn strictly_cloned(a: &Self, b: &Self) -> bool {
                    #cloned_body
                }
            }
            impl #g verge::clone::ClonePartialEq for #name #tg {
                proof fn lemma_clone_preserves_eq(a: &Self) {
                    #clone_eq_proof
                }
            }
        }
    }
}

// --- Struct clone helpers ---

fn build_struct_clone_exec(name: &Ident, fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(f) => {
            let clones: Vec<TokenStream> = f.named.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                if eq_common::is_field_ignored_with_default(field) {
                    let ty = &field.ty;
                    quote! { #fname: <#ty as Default>::default() }
                } else {
                    quote! { #fname: self.#fname.clone() }
                }
            }).collect();
            quote! { #name { #(#clones),* } }
        },
        Fields::Unnamed(f) => {
            let clones: Vec<TokenStream> = f.unnamed.iter().enumerate().map(|(i, field)| {
                if eq_common::is_field_ignored_with_default(field) {
                    let ty = &field.ty;
                    quote! { <#ty as Default>::default() }
                } else {
                    let idx = syn::Index::from(i);
                    quote! { self.#idx.clone() }
                }
            }).collect();
            quote! { #name(#(#clones),*) }
        },
        Fields::Unit => quote! { #name },
    }
}

fn build_struct_cloned_spec(fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(f) => {
            let parts: Vec<TokenStream> = f.named.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                if eq_common::is_field_ignored(field) {
                    return quote! {};
                }
                if eq_common::is_field_ignored_with_default(field) {
                    let ty = &field.ty;
                    quote! { call_ensures(<#ty as Default>::default, (), b.#fname) }
                } else {
                    quote! { vstd::pervasive::strictly_cloned(a.#fname, b.#fname) }
                }
            }).filter(|t| !t.is_empty()).collect();
            eq_common::conjunction(&parts)
        },
        Fields::Unnamed(f) => {
            let parts: Vec<TokenStream> = f.unnamed.iter().enumerate().map(|(i, field)| {
                let idx = syn::Index::from(i);
                if eq_common::is_field_ignored(field) {
                    return quote! {};
                }
                if eq_common::is_field_ignored_with_default(field) {
                    let ty = &field.ty;
                    quote! { call_ensures(<#ty as Default>::default, (), b.#idx) }
                } else {
                    quote! { vstd::pervasive::strictly_cloned(a.#idx, b.#idx) }
                }
            }).filter(|t| !t.is_empty()).collect();
            eq_common::conjunction(&parts)
        },
        Fields::Unit => quote! { true },
    }
}

fn build_struct_clone_eq_proof(fields: &Fields) -> TokenStream {
    // For each non-ignored field, call ClonePartialEq::lemma_clone_preserves_eq on &a.field
    let calls: Vec<TokenStream> = match fields {
        Fields::Named(f) => f.named.iter()
            .filter(|f| !eq_common::is_field_filtered(f))
            .map(|field| {
                let fname = field.ident.as_ref().unwrap();
                let ty = &field.ty;
                quote! { <#ty as verge::clone::ClonePartialEq>::lemma_clone_preserves_eq(&a.#fname); }
            }).collect(),
        Fields::Unnamed(f) => f.unnamed.iter().enumerate()
            .filter(|(_, f)| !eq_common::is_field_filtered(f))
            .map(|(i, field)| {
                let idx = syn::Index::from(i);
                let ty = &field.ty;
                quote! { <#ty as verge::clone::ClonePartialEq>::lemma_clone_preserves_eq(&a.#idx); }
            }).collect(),
        Fields::Unit => vec![],
    };
    quote! { #(#calls)* }
}

fn build_enum_clone_eq_proof(
    name: &Ident,
    variants: &syn::punctuated::Punctuated<syn::Variant, syn::token::Comma>,
) -> TokenStream {
    let arms: Vec<TokenStream> = variants.iter().map(|v| {
        let vname = &v.ident;
        match &v.fields {
            Fields::Named(f) => {
                let field_names: Vec<&Ident> = f.named.iter()
                    .map(|f| f.ident.as_ref().unwrap()).collect();
                let binds: Vec<Ident> = field_names.iter()
                    .map(|n| Ident::new(&format!("f_{}", n), n.span())).collect();
                let pat: Vec<TokenStream> = field_names.iter().zip(binds.iter())
                    .map(|(n, b)| quote! { #n: #b }).collect();
                let calls: Vec<TokenStream> = f.named.iter().zip(binds.iter())
                    .filter(|(f, _)| !eq_common::is_field_filtered(f))
                    .map(|(field, b)| {
                        let ty = &field.ty;
                        quote! { <#ty as verge::clone::ClonePartialEq>::lemma_clone_preserves_eq(#b); }
                    }).collect();
                quote! { #name::#vname { #(#pat),* } => { #(#calls)* } }
            },
            Fields::Unnamed(f) => {
                let binds: Vec<Ident> = (0..f.unnamed.len())
                    .map(|i| Ident::new(&format!("f_{}", i), proc_macro2::Span::call_site())).collect();
                let calls: Vec<TokenStream> = f.unnamed.iter().zip(binds.iter())
                    .filter(|(f, _)| !eq_common::is_field_filtered(f))
                    .map(|(field, b)| {
                        let ty = &field.ty;
                        quote! { <#ty as verge::clone::ClonePartialEq>::lemma_clone_preserves_eq(#b); }
                    }).collect();
                quote! { #name::#vname(#(#binds),*) => { #(#calls)* } }
            },
            Fields::Unit => {
                quote! { #name::#vname => {} }
            },
        }
    }).collect();
    quote! { match a { #(#arms,)* } }
}

// --- obeys_key_model proof ---

fn build_key_model_proof(name: &Ident, g: &TokenStream, tg: &TokenStream) -> TokenStream {
    quote! {
        ::vstd::prelude::verus! {
            impl #g #name #tg {
                #[verifier::external_body]
                pub broadcast proof fn lemma_obeys_key_model()
                    ensures
                        #[trigger] obeys_key_model::<#name #tg>(),
                {
                }
            }
        }
    }
}
