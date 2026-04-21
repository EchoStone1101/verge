use proc_macro2::TokenStream;
use quote::{quote, format_ident};
use syn::{parse2, Fields, Ident, Item, ItemEnum, ItemStruct, Visibility};

use crate::eq_common::{self, conjunction};

pub fn derive_clone_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    let short_name: Ident = match parse2(attr) {
        Ok(name) => name,
        Err(_) => return syn::Error::new(proc_macro2::Span::call_site(),
            "derive_clone requires a name: #[derive_clone(my_type)]").to_compile_error(),
    };
    let item: Item = match parse2(item) {
        Ok(item) => item,
        Err(e) => return e.to_compile_error(),
    };
    match item {
        Item::Struct(s) => gen_struct(short_name, s),
        Item::Enum(e) => gen_enum(short_name, e),
        _ => syn::Error::new(proc_macro2::Span::call_site(),
            "derive_clone can only be applied to structs and enums").to_compile_error(),
    }
}

fn all_fields_pub(fields: &Fields) -> bool {
    match fields {
        Fields::Named(f) => f.named.iter().all(|f| matches!(f.vis, Visibility::Public(_))),
        Fields::Unnamed(f) => f.unnamed.iter().all(|f| matches!(f.vis, Visibility::Public(_))),
        Fields::Unit => true,
    }
}

fn gen_struct(short_name: Ident, input: ItemStruct) -> TokenStream {
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
    let openness = if all_fields_pub(fields) { quote! { open } } else { quote! { closed } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    let cloned_fn_name = format_ident!("{}_strictly_cloned", short_name);
    let cloned_body = build_struct_cloned_body(fields);
    let clone_body = build_struct_clone_body(name, fields);
    quote! {
        ::vstd::prelude::verus! {
            #struct_def
            impl #g Clone for #name #tg {
                fn clone(&self) -> (ret: Self)
                    ensures #cloned_fn_name(self, &ret),
                { #clone_body }
            }
            #vis #openness spec fn #cloned_fn_name #g (a: &#name #tg, b: &#name #tg) -> bool {
                #cloned_body
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
    let enum_def = quote! { #(#attrs)* #vis enum #name #generics #where_clause { #variants } };
    let all_pub = variants.iter().all(|v| all_fields_pub(&v.fields));
    let openness = if all_pub { quote! { open } } else { quote! { closed } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    let cloned_fn_name = format_ident!("{}_strictly_cloned", short_name);

    // Build clone body and spec body for enum
    let (clone_arms, spec_arms) = build_enum_clone_arms(name, variants);
    let clone_body = quote! { match self { #(#clone_arms,)* } };
    let cloned_body = quote! { match (a, b) { #(#spec_arms,)* _ => false, } };

    quote! {
        ::vstd::prelude::verus! {
            #enum_def
            impl #g Clone for #name #tg {
                fn clone(&self) -> (ret: Self)
                    ensures #cloned_fn_name(self, &ret),
                { #clone_body }
            }
            #vis #openness spec fn #cloned_fn_name #g (a: &#name #tg, b: &#name #tg) -> bool {
                #cloned_body
            }
        }
    }
}

fn build_struct_clone_body(name: &Ident, fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(f) => {
            let clones: Vec<TokenStream> = f.named.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                quote! { #fname: self.#fname.clone() }
            }).collect();
            quote! { #name { #(#clones),* } }
        },
        Fields::Unnamed(f) => {
            let clones: Vec<TokenStream> = (0..f.unnamed.len()).map(|i| {
                let idx = syn::Index::from(i);
                quote! { self.#idx.clone() }
            }).collect();
            quote! { #name(#(#clones),*) }
        },
        Fields::Unit => quote! { #name },
    }
}

fn build_struct_cloned_body(fields: &Fields) -> TokenStream {
    match fields {
        Fields::Named(f) => {
            let parts: Vec<TokenStream> = f.named.iter().map(|field| {
                let fname = field.ident.as_ref().unwrap();
                quote! { vstd::pervasive::strictly_cloned(a.#fname, b.#fname) }
            }).collect();
            conjunction(&parts)
        },
        Fields::Unnamed(f) => {
            let parts: Vec<TokenStream> = (0..f.unnamed.len()).map(|i| {
                let idx = syn::Index::from(i);
                quote! { vstd::pervasive::strictly_cloned(a.#idx, b.#idx) }
            }).collect();
            conjunction(&parts)
        },
        Fields::Unit => quote! { true },
    }
}

fn build_enum_clone_arms(name: &Ident, variants: &syn::punctuated::Punctuated<syn::Variant, syn::token::Comma>) -> (Vec<TokenStream>, Vec<TokenStream>) {
    let mut clone_arms = Vec::new();
    let mut spec_arms = Vec::new();
    for variant in variants {
        let vname = &variant.ident;
        match &variant.fields {
            Fields::Named(f) => {
                let field_names: Vec<&Ident> = f.named.iter().map(|f| f.ident.as_ref().unwrap()).collect();
                let binds: Vec<Ident> = field_names.iter().map(|n| Ident::new(&format!("f_{}", n), n.span())).collect();
                let pat: Vec<TokenStream> = field_names.iter().zip(binds.iter()).map(|(n, b)| quote! { #n: #b }).collect();
                let clones: Vec<TokenStream> = field_names.iter().zip(binds.iter()).map(|(n, b)| quote! { #n: #b.clone() }).collect();
                let a_binds: Vec<Ident> = field_names.iter().map(|n| Ident::new(&format!("a_{}", n), n.span())).collect();
                let b_binds: Vec<Ident> = field_names.iter().map(|n| Ident::new(&format!("b_{}", n), n.span())).collect();
                let a_pat: Vec<TokenStream> = field_names.iter().zip(a_binds.iter()).map(|(n, b)| quote! { #n: #b }).collect();
                let b_pat: Vec<TokenStream> = field_names.iter().zip(b_binds.iter()).map(|(n, b)| quote! { #n: #b }).collect();
                let field_cloneds: Vec<TokenStream> = a_binds.iter().zip(b_binds.iter())
                    .map(|(a, b)| quote! { vstd::pervasive::strictly_cloned(*#a, *#b) }).collect();
                let spec_body = conjunction(&field_cloneds);
                clone_arms.push(quote! { #name::#vname { #(#pat),* } => #name::#vname { #(#clones),* } });
                spec_arms.push(quote! { (#name::#vname { #(#a_pat),* }, #name::#vname { #(#b_pat),* }) => { #spec_body } });
            },
            Fields::Unnamed(f) => {
                let binds: Vec<Ident> = (0..f.unnamed.len()).map(|i| Ident::new(&format!("f_{}", i), proc_macro2::Span::call_site())).collect();
                let clones: Vec<TokenStream> = binds.iter().map(|b| quote! { #b.clone() }).collect();
                let a_binds: Vec<Ident> = (0..f.unnamed.len()).map(|i| Ident::new(&format!("a_{}", i), proc_macro2::Span::call_site())).collect();
                let b_binds: Vec<Ident> = (0..f.unnamed.len()).map(|i| Ident::new(&format!("b_{}", i), proc_macro2::Span::call_site())).collect();
                let field_cloneds: Vec<TokenStream> = a_binds.iter().zip(b_binds.iter())
                    .map(|(a, b)| quote! { vstd::pervasive::strictly_cloned(*#a, *#b) }).collect();
                let spec_body = conjunction(&field_cloneds);
                clone_arms.push(quote! { #name::#vname(#(#binds),*) => #name::#vname(#(#clones),*) });
                spec_arms.push(quote! { (#name::#vname(#(#a_binds),*), #name::#vname(#(#b_binds),*)) => { #spec_body } });
            },
            Fields::Unit => {
                clone_arms.push(quote! { #name::#vname => #name::#vname });
                spec_arms.push(quote! { (#name::#vname, #name::#vname) => { true } });
            },
        }
    }
    (clone_arms, spec_arms)
}
