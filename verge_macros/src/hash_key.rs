use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse2, Fields, Ident, Item, ItemEnum, ItemStruct, Type};
use quote::format_ident;

pub fn hash_key_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse the attribute as a short name; the lemma will be named lemma_{name}_obeys_key_model
    let short_name: Ident = match parse2(attr) {
        Ok(name) => name,
        Err(_) => {
            return syn::Error::new(
                proc_macro2::Span::call_site(),
                "hash_key requires a name: #[hash_key(my_type)]",
            )
            .to_compile_error();
        }
    };
    let lemma_name = format_ident!("lemma_{}_obeys_key_model", short_name);

    // Parse as either struct or enum
    let item: Item = match parse2(item) {
        Ok(item) => item,
        Err(e) => return e.to_compile_error(),
    };

    match item {
        Item::Struct(s) => hash_key_struct(lemma_name, s),
        Item::Enum(e) => hash_key_enum(lemma_name, e),
        _ => syn::Error::new(proc_macro2::Span::call_site(), "hash_key can only be applied to structs and enums")
            .to_compile_error(),
    }
}

fn hash_key_struct(lemma_name: Ident, input: ItemStruct) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;
    let fields = &input.fields;

    let field_types = collect_field_types(fields);
    let (requires_block, proof_fn_generics, ty_generics) =
        build_proof_parts(generics, &field_types);

    let (_impl_generics, _ty_generics, where_clause) = generics.split_for_impl();

    let struct_def = match fields {
        Fields::Named(_) => quote! {
            #(#attrs)*
            #[verifier::verify]
            #[derive(Hash, PartialEq, Eq)]
            #vis struct #name #generics #where_clause #fields
        },
        Fields::Unnamed(_) => quote! {
            #(#attrs)*
            #[verifier::verify]
            #[derive(Hash, PartialEq, Eq)]
            #vis struct #name #generics #fields #where_clause ;
        },
        Fields::Unit => quote! {
            #(#attrs)*
            #[verifier::verify]
            #[derive(Hash, PartialEq, Eq)]
            #vis struct #name #generics #where_clause ;
        },
    };

    emit_output(struct_def, vis, &lemma_name, &proof_fn_generics, &requires_block, name, &ty_generics)
}

fn hash_key_enum(lemma_name: Ident, input: ItemEnum) -> TokenStream {
    let name = &input.ident;
    let vis = &input.vis;
    let attrs = &input.attrs;
    let generics = &input.generics;

    // Collect field types from all variants
    let mut field_types: Vec<&Type> = Vec::new();
    for variant in &input.variants {
        field_types.extend(collect_field_types(&variant.fields));
    }

    let (requires_block, proof_fn_generics, ty_generics) =
        build_proof_parts(generics, &field_types);

    let (_impl_generics, _ty_generics, where_clause) = generics.split_for_impl();

    let variants = &input.variants;
    let enum_def = quote! {
        #(#attrs)*
        #[verifier::verify]
        #[derive(Hash, PartialEq, Eq)]
        #vis enum #name #generics #where_clause {
            #variants
        }
    };

    emit_output(enum_def, vis, &lemma_name, &proof_fn_generics, &requires_block, name, &ty_generics)
}

fn collect_field_types(fields: &Fields) -> Vec<&Type> {
    match fields {
        Fields::Named(f) => f.named.iter().map(|f| &f.ty).collect(),
        Fields::Unnamed(f) => f.unnamed.iter().map(|f| &f.ty).collect(),
        Fields::Unit => vec![],
    }
}

fn build_proof_parts(
    generics: &syn::Generics,
    field_types: &[&Type],
) -> (TokenStream, TokenStream, TokenStream) {
    let unique_field_types = dedup_types(field_types);

    let requires_clauses: Vec<TokenStream> = unique_field_types
        .iter()
        .map(|ty| quote! { obeys_key_model::<#ty>(), })
        .collect();

    let requires_block = if requires_clauses.is_empty() {
        quote! {}
    } else {
        quote! {
            requires
                #(#requires_clauses)*
        }
    };

    let proof_fn_generics = quote! { #generics };
    let (_impl_generics, ty_generics, _where_clause) = generics.split_for_impl();
    let ty_generics = quote! { #ty_generics };

    (requires_block, proof_fn_generics, ty_generics)
}

fn emit_output(
    type_def: TokenStream,
    vis: &syn::Visibility,
    lemma_name: &Ident,
    proof_fn_generics: &TokenStream,
    requires_block: &TokenStream,
    name: &Ident,
    ty_generics: &TokenStream,
) -> TokenStream {
    quote! {
        #type_def

        ::vstd::prelude::verus! {
            #[verifier::external_body]
            #vis broadcast axiom fn #lemma_name #proof_fn_generics ()
                #requires_block
                ensures
                    #[trigger] obeys_key_model::<#name #ty_generics>(),
            ;
        }
    }
}

/// Deduplicate types by their token representation.
fn dedup_types<'a>(types: &[&'a Type]) -> Vec<&'a Type> {
    let mut seen = std::collections::HashSet::new();
    let mut result = Vec::new();
    for ty in types {
        let key = quote!(#ty).to_string();
        if seen.insert(key) {
            result.push(*ty);
        }
    }
    result
}
