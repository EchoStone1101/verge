use proc_macro2::TokenStream;
use quote::{quote, format_ident};
use syn::{parse2, Fields, Ident, Item, ItemEnum, ItemStruct};

use crate::eq_common;

pub fn derive_default_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    let short_name: Ident = match parse2(attr) {
        Ok(name) => name,
        Err(_) => return syn::Error::new(proc_macro2::Span::call_site(),
            "derive_default requires a name: #[derive_default(my_type)]").to_compile_error(),
    };
    let item: Item = match parse2(item) {
        Ok(item) => item,
        Err(e) => return e.to_compile_error(),
    };
    match item {
        Item::Struct(s) => gen_struct(short_name, s),
        Item::Enum(e) => gen_enum(short_name, e),
        _ => syn::Error::new(proc_macro2::Span::call_site(),
            "derive_default can only be applied to structs and enums").to_compile_error(),
    }
}


fn gen_struct(short_name: Ident, input: ItemStruct) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;
    let fields = &input.fields;
    if eq_common::has_any_verge_attr(fields) {
        return syn::Error::new(proc_macro2::Span::call_site(),
            "derive_default does not support #[ignored] or #[ignored_with_default] on struct fields.")
            .to_compile_error();
    }
    let (_impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let struct_def = match fields {
        Fields::Named(_) => quote! { #(#attrs)* #vis struct #name #generics #where_clause #fields },
        Fields::Unnamed(_) => quote! { #(#attrs)* #vis struct #name #generics #fields #where_clause ; },
        Fields::Unit => quote! { #(#attrs)* #vis struct #name #generics #where_clause ; },
    };
    let openness = if eq_common::all_fields_pub(fields) { quote! { open } } else { quote! { closed } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    let is_default_fn = format_ident!("{}_is_default", short_name);
    let default_body = build_struct_default_body(name, fields);
    let spec_body = build_struct_is_default_body(fields);
    quote! {
        ::vstd::prelude::verus! {
            #struct_def
            impl #g Default for #name #tg {
                fn default() -> (ret: Self)
                    ensures #is_default_fn(&ret),
                { #default_body }
            }
            #vis #openness spec fn #is_default_fn #g (a: &#name #tg) -> bool {
                #spec_body
            }
        }
    }
}

fn gen_enum(short_name: Ident, input: ItemEnum) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;
    let variants = &input.variants;
    let (_impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    // Find the variant marked #[default]
    let default_variants: Vec<&syn::Variant> = variants.iter()
        .filter(|v| v.attrs.iter().any(|a| {
            let segs: Vec<String> = a.path().segments.iter().map(|s| s.ident.to_string()).collect();
            segs == ["default"]
        }))
        .collect();
    if default_variants.is_empty() {
        return syn::Error::new(proc_macro2::Span::call_site(),
            "derive_default on enums requires exactly one variant marked #[default]").to_compile_error();
    }
    if default_variants.len() > 1 {
        return syn::Error::new(proc_macro2::Span::call_site(),
            "derive_default on enums requires exactly one variant marked #[default], found multiple").to_compile_error();
    }
    let default_variant = default_variants[0];

    // Check no verge field attributes on any variant fields
    for v in variants.iter() {
        if eq_common::has_any_verge_attr(&v.fields) {
            return syn::Error::new(proc_macro2::Span::call_site(),
                "derive_default does not support #[ignored] or #[ignored_with_default] on variant fields.")
                .to_compile_error();
        }
    }

    // Strip #[default] attribute from variant for output
    let stripped_variants: Vec<TokenStream> = variants.iter().map(|v| {
        let vattrs: Vec<&syn::Attribute> = v.attrs.iter()
            .filter(|a| {
                let segs: Vec<String> = a.path().segments.iter().map(|s| s.ident.to_string()).collect();
                segs != ["default"]
            }).collect();
        let vname = &v.ident;
        let vfields = &v.fields;
        let disc = v.discriminant.as_ref().map(|(eq, expr)| quote! { #eq #expr });
        match vfields {
            Fields::Named(_) => quote! { #(#vattrs)* #vname #vfields #disc },
            Fields::Unnamed(_) => quote! { #(#vattrs)* #vname #vfields #disc },
            Fields::Unit => quote! { #(#vattrs)* #vname #disc },
        }
    }).collect();

    let enum_def = quote! { #(#attrs)* #vis enum #name #generics #where_clause { #(#stripped_variants),* } };

    let all_pub = variants.iter().all(|v| eq_common::all_fields_pub(&v.fields));
    let openness = if all_pub { quote! { open } } else { quote! { closed } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    let is_default_fn = format_ident!("{}_is_default", short_name);

    // Build exec default body for the default variant
    let default_body = build_variant_default_body(name, default_variant);
    // Build spec body: match on the default variant, check call_ensures for each field
    let spec_body = build_enum_is_default_body(name, default_variant);

    quote! {
        ::vstd::prelude::verus! {
            #enum_def
            impl #g Default for #name #tg {
                fn default() -> (ret: Self)
                    ensures #is_default_fn(&ret),
                { #default_body }
            }
            #vis #openness spec fn #is_default_fn #g (a: &#name #tg) -> bool {
                #spec_body
            }
        }
    }
}

fn build_struct_default_body(name: &Ident, fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(f) => {
            let inits: Vec<TokenStream> = f.named.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                let ty = &field.ty;
                quote! { #fname: <#ty as Default>::default() }
            }).collect();
            quote! { #name { #(#inits),* } }
        },
        Fields::Unnamed(f) => {
            let inits: Vec<TokenStream> = f.unnamed.iter().map(|field| {
                let ty = &field.ty;
                quote! { <#ty as Default>::default() }
            }).collect();
            quote! { #name(#(#inits),*) }
        },
        Fields::Unit => quote! { #name },
    }
}

fn build_struct_is_default_body(fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(f) => {
            let parts: Vec<TokenStream> = f.named.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                let ty = &field.ty;
                quote! { call_ensures(<#ty as Default>::default, (), a.#fname) }
            }).collect();
            eq_common::conjunction(&parts)
        },
        Fields::Unnamed(f) => {
            let parts: Vec<TokenStream> = f.unnamed.iter().enumerate().map(|(i, field)| {
                let idx = syn::Index::from(i);
                let ty = &field.ty;
                quote! { call_ensures(<#ty as Default>::default, (), a.#idx) }
            }).collect();
            eq_common::conjunction(&parts)
        },
        Fields::Unit => quote! { true },
    }
}

fn build_variant_default_body(name: &Ident, variant: &syn::Variant) -> TokenStream {
    let vname = &variant.ident;
    match &variant.fields {
        Fields::Named(f) => {
            let inits: Vec<TokenStream> = f.named.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                let ty = &field.ty;
                quote! { #fname: <#ty as Default>::default() }
            }).collect();
            quote! { #name::#vname { #(#inits),* } }
        },
        Fields::Unnamed(f) => {
            let inits: Vec<TokenStream> = f.unnamed.iter().map(|field| {
                let ty = &field.ty;
                quote! { <#ty as Default>::default() }
            }).collect();
            quote! { #name::#vname(#(#inits),*) }
        },
        Fields::Unit => quote! { #name::#vname },
    }
}

fn build_enum_is_default_body(name: &Ident, variant: &syn::Variant) -> TokenStream {
    let vname = &variant.ident;
    match &variant.fields {
        Fields::Named(f) => {
            let field_names: Vec<&Ident> = f.named.iter().map(|f| f.ident.as_ref().unwrap()).collect();
            let binds: Vec<Ident> = field_names.iter()
                .map(|n| Ident::new(&format!("f_{}", n), n.span())).collect();
            let pat: Vec<TokenStream> = field_names.iter().zip(binds.iter())
                .map(|(n, b)| quote! { #n: #b }).collect();
            let parts: Vec<TokenStream> = f.named.iter().zip(binds.iter())
                .map(|(field, b)| {
                    let ty = &field.ty;
                    quote! { call_ensures(<#ty as Default>::default, (), *#b) }
                }).collect();
            let body = eq_common::conjunction(&parts);
            quote! { match a { #name::#vname { #(#pat),* } => { #body }, _ => false, } }
        },
        Fields::Unnamed(f) => {
            let binds: Vec<Ident> = (0..f.unnamed.len())
                .map(|i| Ident::new(&format!("f_{}", i), proc_macro2::Span::call_site())).collect();
            let parts: Vec<TokenStream> = f.unnamed.iter().zip(binds.iter())
                .map(|(field, b)| {
                    let ty = &field.ty;
                    quote! { call_ensures(<#ty as Default>::default, (), *#b) }
                }).collect();
            let body = eq_common::conjunction(&parts);
            quote! { match a { #name::#vname(#(#binds),*) => { #body }, _ => false, } }
        },
        Fields::Unit => {
            quote! { match a { #name::#vname => true, _ => false, } }
        },
    }
}
