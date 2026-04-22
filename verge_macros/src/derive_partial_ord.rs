use proc_macro2::TokenStream;
use quote::{quote, format_ident, ToTokens};
use syn::{parse2, Fields, Ident, Item, ItemStruct};

use crate::eq_common::{self, *};

pub fn derive_partial_ord_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    let short_name: Ident = match parse2(attr) {
        Ok(name) => name,
        Err(_) => return syn::Error::new(proc_macro2::Span::call_site(),
            "derive_partial_ord requires a name: #[derive_partial_ord(my_type)]").to_compile_error(),
    };
    let item: Item = match parse2(item) {
        Ok(item) => item,
        Err(e) => return e.to_compile_error(),
    };
    match item {
        Item::Struct(s) => gen_struct(short_name, s),
        Item::Enum(_) => syn::Error::new(proc_macro2::Span::call_site(),
            "derive_partial_ord does not support enums. Implement manually.").to_compile_error(),
        _ => syn::Error::new(proc_macro2::Span::call_site(),
            "derive_partial_ord can only be applied to structs").to_compile_error(),
    }
}

#[allow(dead_code)]
pub(crate) struct FieldInfo {
    pub(crate) self_acc: String,
    pub(crate) other_acc: String,
    pub(crate) a_acc: String,
    pub(crate) b_acc: String,
    pub(crate) c_acc: String,
    pub(crate) ty_str: String,
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
    let eq_code = gen_struct_field_code(fields);
    let openness = if all_fields_pub(fields) { quote! { open } } else { quote! { closed } };
    let g = quote! { #generics };
    let tg = quote! { #ty_generics };
    let field_info = extract_field_info(fields);
    let n = field_info.len();
    let seq_fn_name = format_ident!("{}_partial_cmp_spec_seq", short_name);
    let equiv_lemma_name = format_ident!("lemma_{}_partial_cmp_spec_equiv", short_name);
    let less_trans_fn_name = format_ident!("__verge_{}_less_trans", short_name);
    let greater_trans_fn_name = format_ident!("__verge_{}_greater_trans", short_name);

    let entries_self: Vec<(TokenStream, TokenStream, &syn::Type)> = match fields {
        Fields::Named(f) => f.named.iter().filter(|f| !eq_common::is_field_filtered(f)).map(|field| { let fname = field.ident.as_ref().unwrap(); (quote! { &self.#fname }, quote! { &other.#fname }, &field.ty) }).collect(),
        Fields::Unnamed(f) => f.unnamed.iter().enumerate().filter(|(_, f)| !eq_common::is_field_filtered(f)).map(|(i, field)| { let idx = syn::Index::from(i); (quote! { &self.#idx }, quote! { &other.#idx }, &field.ty) }).collect(),
        Fields::Unit => vec![],
    };
    let exec_cmp = lexico_exec_cmp(&entries_self);
    let spec_cmp = lexico_spec_cmp(&entries_self);
    let seq_entries: Vec<TokenStream> = match fields {
        Fields::Named(f) => f.named.iter().filter(|f| !eq_common::is_field_filtered(f)).map(|field| { let fname = field.ident.as_ref().unwrap(); let ty = &field.ty; quote! { <#ty as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.#fname, &b.#fname) } }).collect(),
        Fields::Unnamed(f) => f.unnamed.iter().enumerate().filter(|(_, f)| !eq_common::is_field_filtered(f)).map(|(i, field)| { let idx = syn::Index::from(i); let ty = &field.ty; quote! { <#ty as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.#idx, &b.#idx) } }).collect(),
        Fields::Unit => vec![],
    };

    let eq_con_calls = build_calls(fields, "lemma_cmp_eq_consistent", "PartialOrdVerified", true);
    let dual_calls = build_calls(fields, "lemma_cmp_dual", "PartialOrdVerified", true);
    let comparable_calls = build_3arg_calls(fields, "lemma_cmp_comparable", "PartialOrdVerified");
    let less_trans_fn = pub_build_trans_proof_fn(&field_info, &name.to_string(), &seq_fn_name.to_string(), &equiv_lemma_name.to_string(), &less_trans_fn_name.to_string(), n, "Less");
    let greater_trans_fn = pub_build_trans_proof_fn(&field_info, &name.to_string(), &seq_fn_name.to_string(), &equiv_lemma_name.to_string(), &greater_trans_fn_name.to_string(), n, "Greater");
    let equiv_lemma = pub_build_equiv_lemma(&name.to_string(), &seq_fn_name.to_string(), &equiv_lemma_name.to_string(), &vis.to_token_stream().to_string(), n);

    let eq_body = &eq_code.eq_body;
    let eq_spec_body = &eq_code.eq_spec_body;
    let sym_body = &eq_code.sym_body;
    let trans_body = &eq_code.trans_body;

    quote! {
        ::vstd::prelude::verus! {
            #struct_def
            impl #g PartialEq for #name #tg {
                fn eq(&self, other: &Self) -> (r: bool) { #eq_body }
            }
            impl #g PartialOrd for #name #tg {
                fn partial_cmp(&self, other: &Self) -> (r: Option<core::cmp::Ordering>) { #exec_cmp }
            }
            impl #g vstd::std_specs::cmp::PartialEqSpecImpl for #name #tg {
                open spec fn obeys_eq_spec() -> bool { true }
                #openness spec fn eq_spec(&self, other: &Self) -> bool { #eq_spec_body }
            }
            impl #g vstd::std_specs::cmp::PartialOrdSpecImpl for #name #tg {
                open spec fn obeys_partial_cmp_spec() -> bool { true }
                #openness spec fn partial_cmp_spec(&self, other: &Self) -> Option<core::cmp::Ordering> { #spec_cmp }
            }
            #vis open spec fn #seq_fn_name #g (a: &#name #tg, b: &#name #tg) -> Seq<Option<core::cmp::Ordering>> {
                seq![#(#seq_entries),*]
            }
            #less_trans_fn
            #greater_trans_fn
            impl #g verge::cmp::PartialEqVerified for #name #tg {
                proof fn lemma_eq_symmetric(a: &Self, b: &Self) { #sym_body }
                proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) { #trans_body }
            }
            impl #g verge::cmp::PartialOrdVerified for #name #tg {
                proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self) { #eq_con_calls }
                proof fn lemma_cmp_dual(a: &Self, b: &Self) { #dual_calls }
                proof fn lemma_cmp_comparable(a: &Self, b: &Self, c: &Self) { #comparable_calls }
                proof fn lemma_cmp_less_transitive(a: &Self, b: &Self, c: &Self) {
                    #less_trans_fn_name(a, b, c);
                }
                proof fn lemma_cmp_greater_transitive(a: &Self, b: &Self, c: &Self) {
                    #greater_trans_fn_name(a, b, c);
                }
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
            if with_eq_sym { quote! { #main <#ty as verge::cmp::PartialEqVerified>::lemma_eq_symmetric(&a.#fname, &b.#fname); } }
            else { main }
        }).collect(),
        Fields::Unnamed(f) => f.unnamed.iter().enumerate().filter(|(_, f)| !eq_common::is_field_filtered(f)).map(|(i, field)| {
            let idx = syn::Index::from(i); let ty = &field.ty;
            let main = quote! { <#ty as verge::cmp::#trait_id>::#lemma_id(&a.#idx, &b.#idx); };
            if with_eq_sym { quote! { #main <#ty as verge::cmp::PartialEqVerified>::lemma_eq_symmetric(&a.#idx, &b.#idx); } }
            else { main }
        }).collect(),
        Fields::Unit => vec![],
    };
    quote! { #(#calls)* }
}

fn build_3arg_calls(fields: &Fields, lemma: &str, trait_name: &str) -> TokenStream {
    let lemma_id = Ident::new(lemma, proc_macro2::Span::call_site());
    let trait_id = Ident::new(trait_name, proc_macro2::Span::call_site());
    let calls: Vec<TokenStream> = match fields {
        Fields::Named(f) => f.named.iter().filter(|f| !eq_common::is_field_filtered(f)).map(|field| {
            let fname = field.ident.as_ref().unwrap(); let ty = &field.ty;
            quote! { <#ty as verge::cmp::#trait_id>::#lemma_id(&a.#fname, &b.#fname, &c.#fname); }
        }).collect(),
        Fields::Unnamed(f) => f.unnamed.iter().enumerate().filter(|(_, f)| !eq_common::is_field_filtered(f)).map(|(i, field)| {
            let idx = syn::Index::from(i); let ty = &field.ty;
            quote! { <#ty as verge::cmp::#trait_id>::#lemma_id(&a.#idx, &b.#idx, &c.#idx); }
        }).collect(),
        Fields::Unit => vec![],
    };
    quote! { #(#calls)* }
}

pub(crate) fn pub_build_trans_proof_fn(fields: &[FieldInfo], type_name: &str, seq_fn: &str, equiv_fn: &str, fn_name: &str, n: usize, dir: &str) -> TokenStream {
    if n == 0 { return quote! {}; }
    let dir_lower = dir.to_lowercase();
    let trans_lemma = format!("lemma_cmp_{}_transitive", dir_lower);
    let mut lines = Vec::new();
    for f in fields {
        for (x, y) in [("a", "b"), ("b", "c"), ("a", "c")] {
            let xa = f.a_acc.replace("a.", &format!("{}.", x));
            let ya = f.a_acc.replace("a.", &format!("{}.", y));
            lines.push(format!("<{ty} as verge::cmp::PartialOrdVerified>::lemma_cmp_eq_consistent(&{xa}, &{ya});", ty = f.ty_str));
            lines.push(format!("<{ty} as verge::cmp::PartialOrdVerified>::lemma_cmp_dual(&{xa}, &{ya});", ty = f.ty_str));
            lines.push(format!("<{ty} as verge::cmp::PartialEqVerified>::lemma_eq_symmetric(&{xa}, &{ya});", ty = f.ty_str));
        }
    }
    for f in fields {
        lines.push(format!(
            "if <{ty} as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&{a}, &{b}) == Some(core::cmp::Ordering::{dir}) \
             && <{ty} as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&{b}, &{c}) == Some(core::cmp::Ordering::{dir}) {{ \
                <{ty} as verge::cmp::PartialOrdVerified>::{trans}(&{a}, &{b}, &{c}); \
             }}", ty = f.ty_str, a = f.a_acc, b = f.b_acc, c = f.c_acc, dir = dir, trans = trans_lemma));
    }
    lines.push(format!("let s_ab = {seq_fn}(a, b);"));
    lines.push(format!("let s_bc = {seq_fn}(b, c);"));
    lines.push(format!("let s_ac = {seq_fn}(a, c);"));
    // Call equiv lemma to establish lexico_less(s_ab) and lexico_less(s_bc), which gives the exists witnesses for choose
    lines.push(format!("{equiv_fn}(a, b);"));
    lines.push(format!("{equiv_fn}(b, c);"));
    lines.push(format!("{equiv_fn}(a, c);"));
    let combos = [("Equal", "Equal", "Equal"), (dir, "Equal", dir), ("Equal", dir, dir), (dir, dir, dir)];
    for (ab, bc, ac) in &combos {
        lines.push(format!("assert forall|j: int| 0 <= j < {n} && s_ab[j] == Some(core::cmp::Ordering::{ab}) && s_bc[j] == Some(core::cmp::Ordering::{bc}) implies s_ac[j] == Some(core::cmp::Ordering::{ac}) by {{}};"));
    }
    lines.push(format!("let i1 = choose|i: int| 0 <= i < {n} && s_ab[i] == Some(core::cmp::Ordering::{dir}) && forall|j: int| 0 <= j < i ==> s_ab[j] == Some(core::cmp::Ordering::Equal);"));
    lines.push(format!("let i2 = choose|i: int| 0 <= i < {n} && s_bc[i] == Some(core::cmp::Ordering::{dir}) && forall|j: int| 0 <= j < i ==> s_bc[j] == Some(core::cmp::Ordering::Equal);"));
    lines.push("let k = if i1 <= i2 { i1 } else { i2 };".to_string());
    lines.push(format!("assert(s_ac[k] == Some(core::cmp::Ordering::{dir}));"));
    lines.push("assert forall|j: int| 0 <= j < k implies s_ac[j] == Some(core::cmp::Ordering::Equal) by {};".to_string());

    let body = lines.join("\n");
    let code = format!(
        "proof fn {fn_name}(a: &{ty}, b: &{ty}, c: &{ty}) \
            requires \
                vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(a, b) == Some(core::cmp::Ordering::{dir}), \
                vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(b, c) == Some(core::cmp::Ordering::{dir}), \
            ensures \
                vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(a, c) == Some(core::cmp::Ordering::{dir}), \
        {{ {body} }}", fn_name = fn_name, ty = type_name, dir = dir, body = body);
    pub_parse_verus_fn(&code)
}

pub(crate) fn pub_build_equiv_lemma(name: &str, seq_fn: &str, equiv_fn: &str, vis: &str, n: usize) -> TokenStream {
    if n == 0 { return quote! {}; }
    let mut body_lines = Vec::new();
    body_lines.push(format!("let s = {seq_fn}(a, b);"));
    for dir in ["Less", "Greater"] {
        let mut fwd = String::new();
        for i in 0..n { if i < n-1 { fwd.push_str(&format!("if i == {i} {{}} else ")); } else { fwd.push_str("{}"); } }
        body_lines.push(format!("if exists|i: int| 0 <= i < {n} && s[i] == Some(core::cmp::Ordering::{dir}) && forall|j: int| 0 <= j < i ==> s[j] == Some(core::cmp::Ordering::Equal) {{ let i = choose|i: int| 0 <= i < {n} && s[i] == Some(core::cmp::Ordering::{dir}) && forall|j: int| 0 <= j < i ==> s[j] == Some(core::cmp::Ordering::Equal); {fwd} }}"));
        let mut bwd = String::new();
        for i in 0..n { if i < n-1 { bwd.push_str(&format!("if s[{i}int] != Some(core::cmp::Ordering::Equal) {{ assert(s[{i}int] == Some(core::cmp::Ordering::{dir})); }} else ")); } else { bwd.push_str(&format!("{{ assert(s[{i}int] == Some(core::cmp::Ordering::{dir})); }}")); } }
        body_lines.push(format!("if vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(a, b) == Some(core::cmp::Ordering::{dir}) {{ {bwd} }}"));
    }
    let body = body_lines.join("\n");
    let code = format!(
        "{vis} proof fn {equiv_fn}(a: &{name}, b: &{name}) \
            ensures \
                verge::cmp::lexico_less({seq_fn}(a, b)) <==> vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(a, b) == Some(core::cmp::Ordering::Less), \
                verge::cmp::lexico_greater({seq_fn}(a, b)) <==> vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(a, b) == Some(core::cmp::Ordering::Greater), \
                verge::cmp::lexico_equal({seq_fn}(a, b)) <==> vstd::std_specs::cmp::PartialOrdSpec::partial_cmp_spec(a, b) == Some(core::cmp::Ordering::Equal), \
        {{ {body} }}", vis = vis, equiv_fn = equiv_fn, name = name, seq_fn = seq_fn, body = body);
    pub_parse_verus_fn(&code)
}

pub(crate) fn pub_parse_verus_fn(code: &str) -> TokenStream {
    let tokens: proc_macro2::TokenStream = match code.parse() {
        Ok(t) => t,
        Err(e) => return syn::Error::new(proc_macro2::Span::call_site(), format!("Tokenize error: {}", e)).to_compile_error(),
    };
    match verus_syn::parse2::<verus_syn::ItemFn>(tokens) {
        Ok(item) => item.to_token_stream(),
        Err(e) => return syn::Error::new(proc_macro2::Span::call_site(), format!("Parse error: {}", e)).to_compile_error(),
    }
}

fn lexico_exec_cmp(fields: &[(TokenStream, TokenStream, &syn::Type)]) -> TokenStream {
    if fields.is_empty() { return quote! { Some(core::cmp::Ordering::Equal) }; }
    let (ref sa, ref oa, _ty) = fields[0];
    if fields.len() == 1 { quote! { (#sa).partial_cmp(#oa) } }
    else { let rest = lexico_exec_cmp(&fields[1..]); quote! { match (#sa).partial_cmp(#oa) { Some(core::cmp::Ordering::Equal) => #rest, c => c, } } }
}

fn lexico_spec_cmp(fields: &[(TokenStream, TokenStream, &syn::Type)]) -> TokenStream {
    if fields.is_empty() { return quote! { Some(core::cmp::Ordering::Equal) }; }
    let (ref sa, ref oa, ty) = fields[0];
    if fields.len() == 1 { quote! { <#ty as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(#sa, #oa) } }
    else { let rest = lexico_spec_cmp(&fields[1..]); quote! { if <#ty as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(#sa, #oa) != Some(core::cmp::Ordering::Equal) { <#ty as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(#sa, #oa) } else { #rest } } }
}
