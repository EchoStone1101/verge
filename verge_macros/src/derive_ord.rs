use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse2, Fields, Ident, Item, ItemStruct};

use crate::eq_common::{self, *};
use crate::derive_partial_ord::{FieldInfo, pub_build_trans_proof_fn, pub_build_equiv_lemma};

pub fn derive_ord_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new_spanned(attr, "derive_ord takes no arguments")
            .to_compile_error();
    }
    let item: Item = match parse2(item) {
        Ok(item) => item,
        Err(e) => return e.to_compile_error(),
    };
    match item {
        Item::Struct(s) => gen_struct(s),
        Item::Enum(_) => syn::Error::new(proc_macro2::Span::call_site(),
            "derive_ord does not support enums.").to_compile_error(),
        _ => syn::Error::new(proc_macro2::Span::call_site(),
            "derive_ord can only be applied to structs").to_compile_error(),
    }
}

fn extract_field_info(fields: &Fields) -> Vec<FieldInfo> {
    match fields {
        Fields::Named(f) => f.named.iter().filter(|f| !eq_common::is_field_filtered(f)).map(|field| {
            let name = field.ident.as_ref().unwrap().to_string();
            let ty = field.ty.to_token_stream().to_string();
            FieldInfo { self_acc: format!("self.{}", name), other_acc: format!("other.{}", name),
                a_acc: format!("a.{}", name), b_acc: format!("b.{}", name), c_acc: format!("c.{}", name), ty_str: ty }
        }).collect(),
        Fields::Unnamed(f) => f.unnamed.iter().enumerate().filter(|(_, f)| !eq_common::is_field_filtered(f)).map(|(i, field)| {
            let ty = field.ty.to_token_stream().to_string();
            FieldInfo { self_acc: format!("self.{}", i), other_acc: format!("other.{}", i),
                a_acc: format!("a.{}", i), b_acc: format!("b.{}", i), c_acc: format!("c.{}", i), ty_str: ty }
        }).collect(),
        Fields::Unit => vec![],
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
    let eq_code = gen_struct_field_code(fields);
    let openness = if all_fields_pub(fields) { quote! { open } } else { quote! { closed } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    let field_info = extract_field_info(fields);
    let n = field_info.len();

    // Exec ord (returns Ordering)
    let entries_self_ord: Vec<(TokenStream, TokenStream, &syn::Type)> = match fields {
        Fields::Named(f) => f.named.iter().filter(|f| !eq_common::is_field_filtered(f)).map(|field| { let fname = field.ident.as_ref().unwrap(); (quote! { &self.#fname }, quote! { &other.#fname }, &field.ty) }).collect(),
        Fields::Unnamed(f) => f.unnamed.iter().enumerate().filter(|(_, f)| !eq_common::is_field_filtered(f)).map(|(i, field)| { let idx = syn::Index::from(i); (quote! { &self.#idx }, quote! { &other.#idx }, &field.ty) }).collect(),
        Fields::Unit => vec![],
    };
    let exec_ord = lexico_exec_ord(&entries_self_ord);
    let spec_ord = lexico_spec_ord(&entries_self_ord);

    // Spec cmp using PartialOrdSpec (for partial_cmp_spec)
    let entries_self_pcmp: Vec<(TokenStream, TokenStream, &syn::Type)> = entries_self_ord.iter()
        .map(|(sa, oa, ty)| (sa.clone(), oa.clone(), *ty)).collect();
    let spec_pcmp = lexico_spec_pcmp(&entries_self_pcmp);

    // Seq entries using PartialOrdSpec (Option<Ordering>) for trans proof compatibility
    let seq_entries: Vec<TokenStream> = match fields {
        Fields::Named(f) => f.named.iter().filter(|f| !eq_common::is_field_filtered(f)).map(|field| { let fname = field.ident.as_ref().unwrap(); let ty = &field.ty; quote! { <#ty as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.#fname, &b.#fname) } }).collect(),
        Fields::Unnamed(f) => f.unnamed.iter().enumerate().filter(|(_, f)| !eq_common::is_field_filtered(f)).map(|(i, field)| { let idx = syn::Index::from(i); let ty = &field.ty; quote! { <#ty as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.#idx, &b.#idx) } }).collect(),
        Fields::Unit => vec![],
    };

    let eq_con_calls = build_calls(fields, "lemma_cmp_eq_consistent", "PartialOrdVerified", true);
    let dual_calls = build_calls(fields, "lemma_cmp_dual", "PartialOrdVerified", true);
    let less_trans_fn = pub_build_trans_proof_fn(&field_info, &name.to_string(), n, "Less");
    let greater_trans_fn = pub_build_trans_proof_fn(&field_info, &name.to_string(), n, "Greater");
    let equiv_lemma = pub_build_equiv_lemma(&name.to_string(), &vis.to_token_stream().to_string(), n);

    let eq_body = &eq_code.eq_body;
    let eq_spec_body = &eq_code.eq_spec_body;
    let sym_body = &eq_code.sym_body;
    let trans_body = &eq_code.trans_body;
    let refl_body = &eq_code.refl_body;

    quote! {
        ::vstd::prelude::verus! {
            #struct_def
            impl #g PartialEq for #name #tg {
                fn eq(&self, other: &Self) -> (r: bool) { #eq_body }
            }
            impl #g Eq for #name #tg {}
            impl #g Ord for #name #tg {
                fn cmp(&self, other: &Self) -> (r: core::cmp::Ordering) { #exec_ord }
            }
            impl #g PartialOrd for #name #tg {
                fn partial_cmp(&self, other: &Self) -> (r: Option<core::cmp::Ordering>) { Some(self.cmp(other)) }
            }
            impl #g vstd::std_specs::cmp::PartialEqSpecImpl for #name #tg {
                open spec fn obeys_eq_spec() -> bool { true }
                #openness spec fn eq_spec(&self, other: &Self) -> bool { #eq_spec_body }
            }
            impl #g vstd::std_specs::cmp::OrdSpecImpl for #name #tg {
                open spec fn obeys_cmp_spec() -> bool { true }
                #openness spec fn cmp_spec(&self, other: &Self) -> core::cmp::Ordering { #spec_ord }
            }
            impl #g vstd::std_specs::cmp::PartialOrdSpecImpl for #name #tg {
                open spec fn obeys_partial_cmp_spec() -> bool { true }
                #openness spec fn partial_cmp_spec(&self, other: &Self) -> Option<core::cmp::Ordering> { #spec_pcmp }
            }
            impl #g #name #tg {
                #vis open spec fn partial_cmp_spec_seq(a: &Self, b: &Self) -> Seq<Option<core::cmp::Ordering>> {
                    seq![#(#seq_entries),*]
                }
            }
            #less_trans_fn
            #greater_trans_fn
            impl #g verge::cmp::PartialEqVerified for #name #tg {
                proof fn lemma_eq_symmetric(a: &Self, b: &Self) { #sym_body }
                proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) { #trans_body }
            }
            impl #g verge::cmp::EqVerified for #name #tg {
                proof fn lemma_eq_reflexive(a: &Self) { #refl_body }
            }
            impl #g verge::cmp::PartialOrdVerified for #name #tg {
                proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self) { #eq_con_calls }
                proof fn lemma_cmp_dual(a: &Self, b: &Self) { #dual_calls }
                proof fn lemma_cmp_comparable(a: &Self, b: &Self, c: &Self) {}
                proof fn lemma_cmp_less_transitive(a: &Self, b: &Self, c: &Self) { Self::__less_trans(a, b, c); }
                proof fn lemma_cmp_greater_transitive(a: &Self, b: &Self, c: &Self) { Self::__greater_trans(a, b, c); }
            }
            impl #g verge::cmp::OrdVerified for #name #tg {
                proof fn lemma_cmp_consistent(a: &Self, b: &Self) {}
            }
        }
        ::vstd::prelude::verus! { #equiv_lemma }
    }
}

fn build_calls(fields: &Fields, lemma: &str, trait_name: &str, with_eq_sym: bool) -> TokenStream {
    let lemma_id = Ident::new(lemma, proc_macro2::Span::call_site());
    let trait_id = Ident::new(trait_name, proc_macro2::Span::call_site());
    let calls: Vec<TokenStream> = match fields {
        Fields::Named(f) => f.named.iter().filter(|f| !eq_common::is_field_filtered(f)).map(|field| {
            let fname = field.ident.as_ref().unwrap(); let ty = &field.ty;
            let main = quote! { <#ty as verge::cmp::#trait_id>::#lemma_id(&a.#fname, &b.#fname); };
            if with_eq_sym { quote! { #main <#ty as verge::cmp::PartialEqVerified>::lemma_eq_symmetric(&a.#fname, &b.#fname); } } else { main }
        }).collect(),
        Fields::Unnamed(f) => f.unnamed.iter().enumerate().filter(|(_, f)| !eq_common::is_field_filtered(f)).map(|(i, field)| {
            let idx = syn::Index::from(i); let ty = &field.ty;
            let main = quote! { <#ty as verge::cmp::#trait_id>::#lemma_id(&a.#idx, &b.#idx); };
            if with_eq_sym { quote! { #main <#ty as verge::cmp::PartialEqVerified>::lemma_eq_symmetric(&a.#idx, &b.#idx); } } else { main }
        }).collect(),
        Fields::Unit => vec![],
    };
    quote! { #(#calls)* }
}

fn lexico_exec_ord(fields: &[(TokenStream, TokenStream, &syn::Type)]) -> TokenStream {
    if fields.is_empty() { return quote! { core::cmp::Ordering::Equal }; }
    let (ref sa, ref oa, _ty) = fields[0];
    if fields.len() == 1 { quote! { (#sa).cmp(#oa) } }
    else { let rest = lexico_exec_ord(&fields[1..]); quote! { match (#sa).cmp(#oa) { core::cmp::Ordering::Equal => #rest, c => c, } } }
}

fn lexico_spec_ord(fields: &[(TokenStream, TokenStream, &syn::Type)]) -> TokenStream {
    if fields.is_empty() { return quote! { core::cmp::Ordering::Equal }; }
    let (ref sa, ref oa, ty) = fields[0];
    if fields.len() == 1 { quote! { <#ty as vstd::std_specs::cmp::OrdSpec>::cmp_spec(#sa, #oa) } }
    else { let rest = lexico_spec_ord(&fields[1..]); quote! { if <#ty as vstd::std_specs::cmp::OrdSpec>::cmp_spec(#sa, #oa) != core::cmp::Ordering::Equal { <#ty as vstd::std_specs::cmp::OrdSpec>::cmp_spec(#sa, #oa) } else { #rest } } }
}

fn lexico_spec_pcmp(fields: &[(TokenStream, TokenStream, &syn::Type)]) -> TokenStream {
    if fields.is_empty() { return quote! { Some(core::cmp::Ordering::Equal) }; }
    let (ref sa, ref oa, ty) = fields[0];
    if fields.len() == 1 { quote! { <#ty as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(#sa, #oa) } }
    else { let rest = lexico_spec_pcmp(&fields[1..]); quote! { if <#ty as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(#sa, #oa) != Some(core::cmp::Ordering::Equal) { <#ty as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(#sa, #oa) } else { #rest } } }
}
