//! Shared utilities for verified trait macros.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Fields, Ident, Visibility};

/// Check if a field has the `#[ignored]` attribute.
pub fn is_field_ignored(field: &syn::Field) -> bool {
    field.attrs.iter().any(|a| is_ignored_attr(a))
}

fn is_ignored_attr(attr: &syn::Attribute) -> bool {
    let path = attr.path();
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    segs == ["ignored"]
}

/// Check if any field in the Fields has `#[ignored]`.
pub fn has_any_ignored(fields: &Fields) -> bool {
    match fields {
        Fields::Named(f) => f.named.iter().any(|f| is_field_ignored(f)),
        Fields::Unnamed(f) => f.unnamed.iter().any(|f| is_field_ignored(f)),
        Fields::Unit => false,
    }
}

/// Strip `#[ignored]` attributes from fields for struct emission.
pub fn strip_ignored_attrs(fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(f) => {
            let stripped: Vec<TokenStream> = f.named.iter().map(|field| {
                let attrs: Vec<&syn::Attribute> = field.attrs.iter()
                    .filter(|a| !is_ignored_attr(a)).collect();
                let vis = &field.vis;
                let ident = &field.ident;
                let ty = &field.ty;
                quote! { #(#attrs)* #vis #ident: #ty }
            }).collect();
            quote! { { #(#stripped),* } }
        },
        Fields::Unnamed(f) => {
            let stripped: Vec<TokenStream> = f.unnamed.iter().map(|field| {
                let attrs: Vec<&syn::Attribute> = field.attrs.iter()
                    .filter(|a| !is_ignored_attr(a)).collect();
                let vis = &field.vis;
                let ty = &field.ty;
                quote! { #(#attrs)* #vis #ty }
            }).collect();
            quote! { ( #(#stripped),* ) }
        },
        Fields::Unit => quote! {},
    }
}

pub fn all_fields_pub(fields: &Fields) -> bool {
    match fields {
        Fields::Named(f) => f.named.iter().all(|f| matches!(f.vis, Visibility::Public(_))),
        Fields::Unnamed(f) => f.unnamed.iter().all(|f| matches!(f.vis, Visibility::Public(_))),
        Fields::Unit => true,
    }
}

pub fn conjunction(parts: &[TokenStream]) -> TokenStream {
    if parts.is_empty() {
        quote! { true }
    } else {
        let mut iter = parts.iter();
        let first = iter.next().unwrap();
        iter.fold(quote! { #first }, |acc, next| quote! { #acc && #next })
    }
}

/// Per-field code generation results for struct fields.
pub struct StructFieldCode {
    pub eq_body: TokenStream,
    pub eq_spec_body: TokenStream,
    pub sym_body: TokenStream,
    pub trans_body: TokenStream,
    pub refl_body: TokenStream,
}

/// Per-variant code generation results for enum variants.
pub struct EnumVariantArms {
    pub exec_arms: Vec<TokenStream>,
    pub spec_arms: Vec<TokenStream>,
    pub sym_arms: Vec<TokenStream>,
    pub trans_arms: Vec<TokenStream>,
    pub refl_arms: Vec<TokenStream>,
}

/// Generate field-level code for a struct. Fields with `#[ignored]` are excluded.
pub fn gen_struct_field_code(fields: &Fields) -> StructFieldCode {
    match fields {
        Fields::Named(f) => {
            let active: Vec<&syn::Field> = f.named.iter().filter(|f| !is_field_ignored(f)).collect();
            let exec_eqs: Vec<TokenStream> = active.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                quote! { self.#fname == other.#fname }
            }).collect();
            let spec_eqs: Vec<TokenStream> = active.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                quote! { vstd::std_specs::cmp::PartialEqSpec::eq_spec(&self.#fname, &other.#fname) }
            }).collect();
            let sym_calls: Vec<TokenStream> = active.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                let ty = &field.ty;
                quote! { <#ty as verge::cmp::PartialEqVerified>::lemma_eq_symmetric(&a.#fname, &b.#fname); }
            }).collect();
            let trans_calls: Vec<TokenStream> = active.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                let ty = &field.ty;
                quote! { <#ty as verge::cmp::PartialEqVerified>::lemma_eq_transitive(&a.#fname, &b.#fname, &c.#fname); }
            }).collect();
            let refl_calls: Vec<TokenStream> = active.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                let ty = &field.ty;
                quote! { <#ty as verge::cmp::EqVerified>::lemma_eq_reflexive(&a.#fname); }
            }).collect();
            StructFieldCode {
                eq_body: conjunction(&exec_eqs),
                eq_spec_body: conjunction(&spec_eqs),
                sym_body: quote! { #(#sym_calls)* },
                trans_body: quote! { #(#trans_calls)* },
                refl_body: quote! { #(#refl_calls)* },
            }
        },
        Fields::Unnamed(f) => {
            let active: Vec<(usize, &syn::Field)> = f.unnamed.iter().enumerate()
                .filter(|(_, f)| !is_field_ignored(f)).collect();
            let exec_eqs: Vec<TokenStream> = active.iter().map(|(i, _)| {
                let idx = syn::Index::from(*i);
                quote! { self.#idx == other.#idx }
            }).collect();
            let spec_eqs: Vec<TokenStream> = active.iter().map(|(i, _)| {
                let idx = syn::Index::from(*i);
                quote! { vstd::std_specs::cmp::PartialEqSpec::eq_spec(&self.#idx, &other.#idx) }
            }).collect();
            let sym_calls: Vec<TokenStream> = active.iter().map(|(i, field)| {
                let idx = syn::Index::from(*i);
                let ty = &field.ty;
                quote! { <#ty as verge::cmp::PartialEqVerified>::lemma_eq_symmetric(&a.#idx, &b.#idx); }
            }).collect();
            let trans_calls: Vec<TokenStream> = active.iter().map(|(i, field)| {
                let idx = syn::Index::from(*i);
                let ty = &field.ty;
                quote! { <#ty as verge::cmp::PartialEqVerified>::lemma_eq_transitive(&a.#idx, &b.#idx, &c.#idx); }
            }).collect();
            let refl_calls: Vec<TokenStream> = active.iter().map(|(i, field)| {
                let idx = syn::Index::from(*i);
                let ty = &field.ty;
                quote! { <#ty as verge::cmp::EqVerified>::lemma_eq_reflexive(&a.#idx); }
            }).collect();
            StructFieldCode {
                eq_body: conjunction(&exec_eqs),
                eq_spec_body: conjunction(&spec_eqs),
                sym_body: quote! { #(#sym_calls)* },
                trans_body: quote! { #(#trans_calls)* },
                refl_body: quote! { #(#refl_calls)* },
            }
        },
        Fields::Unit => StructFieldCode {
            eq_body: quote! { true },
            eq_spec_body: quote! { true },
            sym_body: quote! {},
            trans_body: quote! {},
            refl_body: quote! {},
        },
    }
}

/// Generate match arms for an enum variant (for all proof types).
pub fn gen_enum_variant_arms(name: &Ident, variant: &syn::Variant) -> EnumVariantArms {
    let vname = &variant.ident;
    let mut result = EnumVariantArms {
        exec_arms: Vec::new(),
        spec_arms: Vec::new(),
        sym_arms: Vec::new(),
        trans_arms: Vec::new(),
        refl_arms: Vec::new(),
    };

    match &variant.fields {
        Fields::Named(f) => {
            let field_names: Vec<&Ident> = f.named.iter()
                .map(|f| f.ident.as_ref().unwrap()).collect();
            let a_binds: Vec<Ident> = field_names.iter()
                .map(|n| Ident::new(&format!("a_{}", n), n.span())).collect();
            let b_binds: Vec<Ident> = field_names.iter()
                .map(|n| Ident::new(&format!("b_{}", n), n.span())).collect();
            let c_binds: Vec<Ident> = field_names.iter()
                .map(|n| Ident::new(&format!("c_{}", n), n.span())).collect();

            let a_pat: Vec<TokenStream> = field_names.iter().zip(a_binds.iter())
                .map(|(n, b)| quote! { #n: #b }).collect();
            let b_pat: Vec<TokenStream> = field_names.iter().zip(b_binds.iter())
                .map(|(n, b)| quote! { #n: #b }).collect();
            let c_pat: Vec<TokenStream> = field_names.iter().zip(c_binds.iter())
                .map(|(n, b)| quote! { #n: #b }).collect();

            let exec_eqs: Vec<TokenStream> = a_binds.iter().zip(b_binds.iter())
                .map(|(a, b)| quote! { *#a == *#b }).collect();
            let spec_eqs: Vec<TokenStream> = a_binds.iter().zip(b_binds.iter())
                .map(|(a, b)| quote! { vstd::std_specs::cmp::PartialEqSpec::eq_spec(#a, #b) }).collect();
            let sym_calls: Vec<TokenStream> = f.named.iter().zip(a_binds.iter().zip(b_binds.iter()))
                .map(|(field, (a, b))| {
                    let ty = &field.ty;
                    quote! { <#ty as verge::cmp::PartialEqVerified>::lemma_eq_symmetric(#a, #b); }
                }).collect();
            let trans_calls: Vec<TokenStream> = f.named.iter()
                .zip(a_binds.iter().zip(b_binds.iter().zip(c_binds.iter())))
                .map(|(field, (a, (b, c)))| {
                    let ty = &field.ty;
                    quote! { <#ty as verge::cmp::PartialEqVerified>::lemma_eq_transitive(#a, #b, #c); }
                }).collect();
            let refl_calls: Vec<TokenStream> = f.named.iter().zip(a_binds.iter())
                .map(|(field, a)| {
                    let ty = &field.ty;
                    quote! { <#ty as verge::cmp::EqVerified>::lemma_eq_reflexive(#a); }
                }).collect();

            let exec_body = conjunction(&exec_eqs);
            let spec_body = conjunction(&spec_eqs);

            result.exec_arms.push(quote! {
                (#name::#vname { #(#a_pat),* }, #name::#vname { #(#b_pat),* }) => { #exec_body }
            });
            result.spec_arms.push(quote! {
                (#name::#vname { #(#a_pat),* }, #name::#vname { #(#b_pat),* }) => { #spec_body }
            });
            result.sym_arms.push(quote! {
                (#name::#vname { #(#a_pat),* }, #name::#vname { #(#b_pat),* }) => { #(#sym_calls)* }
            });
            result.trans_arms.push(quote! {
                (#name::#vname { #(#a_pat),* }, #name::#vname { #(#b_pat),* }, #name::#vname { #(#c_pat),* }) => { #(#trans_calls)* }
            });
            result.refl_arms.push(quote! {
                (#name::#vname { #(#a_pat),* }) => { #(#refl_calls)* }
            });
        },
        Fields::Unnamed(f) => {
            let a_binds: Vec<Ident> = (0..f.unnamed.len())
                .map(|i| Ident::new(&format!("a_{}", i), proc_macro2::Span::call_site())).collect();
            let b_binds: Vec<Ident> = (0..f.unnamed.len())
                .map(|i| Ident::new(&format!("b_{}", i), proc_macro2::Span::call_site())).collect();
            let c_binds: Vec<Ident> = (0..f.unnamed.len())
                .map(|i| Ident::new(&format!("c_{}", i), proc_macro2::Span::call_site())).collect();

            let exec_eqs: Vec<TokenStream> = a_binds.iter().zip(b_binds.iter())
                .map(|(a, b)| quote! { *#a == *#b }).collect();
            let spec_eqs: Vec<TokenStream> = a_binds.iter().zip(b_binds.iter())
                .map(|(a, b)| quote! { vstd::std_specs::cmp::PartialEqSpec::eq_spec(#a, #b) }).collect();
            let sym_calls: Vec<TokenStream> = f.unnamed.iter().zip(a_binds.iter().zip(b_binds.iter()))
                .map(|(field, (a, b))| {
                    let ty = &field.ty;
                    quote! { <#ty as verge::cmp::PartialEqVerified>::lemma_eq_symmetric(#a, #b); }
                }).collect();
            let trans_calls: Vec<TokenStream> = f.unnamed.iter()
                .zip(a_binds.iter().zip(b_binds.iter().zip(c_binds.iter())))
                .map(|(field, (a, (b, c)))| {
                    let ty = &field.ty;
                    quote! { <#ty as verge::cmp::PartialEqVerified>::lemma_eq_transitive(#a, #b, #c); }
                }).collect();
            let refl_calls: Vec<TokenStream> = f.unnamed.iter().zip(a_binds.iter())
                .map(|(field, a)| {
                    let ty = &field.ty;
                    quote! { <#ty as verge::cmp::EqVerified>::lemma_eq_reflexive(#a); }
                }).collect();

            let exec_body = conjunction(&exec_eqs);
            let spec_body = conjunction(&spec_eqs);

            result.exec_arms.push(quote! {
                (#name::#vname(#(#a_binds),*), #name::#vname(#(#b_binds),*)) => { #exec_body }
            });
            result.spec_arms.push(quote! {
                (#name::#vname(#(#a_binds),*), #name::#vname(#(#b_binds),*)) => { #spec_body }
            });
            result.sym_arms.push(quote! {
                (#name::#vname(#(#a_binds),*), #name::#vname(#(#b_binds),*)) => { #(#sym_calls)* }
            });
            result.trans_arms.push(quote! {
                (#name::#vname(#(#a_binds),*), #name::#vname(#(#b_binds),*), #name::#vname(#(#c_binds),*)) => { #(#trans_calls)* }
            });
            result.refl_arms.push(quote! {
                (#name::#vname(#(#a_binds),*)) => { #(#refl_calls)* }
            });
        },
        Fields::Unit => {
            result.exec_arms.push(quote! { (#name::#vname, #name::#vname) => { true } });
            result.spec_arms.push(quote! { (#name::#vname, #name::#vname) => { true } });
            result.sym_arms.push(quote! { (#name::#vname, #name::#vname) => {} });
            result.trans_arms.push(quote! { (#name::#vname, #name::#vname, #name::#vname) => {} });
            result.refl_arms.push(quote! { (#name::#vname) => {} });
        },
    }
    result
}
