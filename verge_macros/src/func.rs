use proc_macro2::{Group, Ident, Span, TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{
    parenthesized, parse2, parse_quote, Attribute, Error, Expr, FnArg, ItemFn, Pat, PatIdent,
    PatType, Path, ReturnType, Stmt, Token, TraitItemFn, Type,
};

pub fn assume_surjective_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    if attr.is_empty() {
        return Error::new(
            Span::call_site(),
            "assume_surjective requires a proof function path",
        )
        .to_compile_error();
    }

    let proof: Path = match parse2(attr) {
        Ok(proof) => proof,
        Err(err) => return err.to_compile_error(),
    };

    if !cfg!(feature = "func_assume_lemmas") {
        return item;
    }

    expand(
        item,
        ExpansionKind::Surjective(LemmaKind::Assume {
            proof: proof.to_token_stream(),
        }),
    )
}

pub fn assume_injective_by_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    let args: AssumeInjectiveArgs = match parse2(attr) {
        Ok(args) => args,
        Err(err) => return err.to_compile_error(),
    };

    if !cfg!(feature = "func_assume_lemmas") {
        return item;
    }

    expand(
        item,
        ExpansionKind::Injective(args.injection, LemmaKind::Assume { proof: args.proof }),
    )
}

pub fn assert_surjective_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    if attr.is_empty() {
        return Error::new(
            Span::call_site(),
            "assert_surjective requires a proof function path",
        )
        .to_compile_error();
    }

    let proof: Path = match parse2(attr) {
        Ok(proof) => proof,
        Err(err) => return err.to_compile_error(),
    };

    expand(
        item,
        ExpansionKind::Surjective(LemmaKind::Assert {
            proof: proof.to_token_stream(),
        }),
    )
}

pub fn assert_injective_by_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    let args: AssertInjectiveArgs = match parse2(attr) {
        Ok(args) => args,
        Err(err) => return err.to_compile_error(),
    };

    expand(
        item,
        ExpansionKind::Injective(args.injection, LemmaKind::Assert { proof: args.proof }),
    )
}

enum ExpansionKind {
    Surjective(LemmaKind),
    Injective(InjectionArgs, LemmaKind),
}

enum LemmaKind {
    Assume { proof: TokenStream },
    Assert { proof: TokenStream },
}

fn expand(item: TokenStream, kind: ExpansionKind) -> TokenStream {
    if let Ok(input) = parse2::<TraitItemFn>(item.clone()) {
        let name = input.sig.ident.to_string();
        if name.starts_with("VERUS_SPEC__") && input.default.is_some() {
            let original = input.to_token_stream();
            let Some(func) = Function::from_trait_item(&input) else {
                return original;
            };
            return expand_function(original, func, kind);
        }
    }

    if let Ok(input) = parse2::<ItemFn>(item.clone()) {
        let original = input.to_token_stream();
        if !has_verus_internal_attr(&input.attrs, "verus_macro")
            || input.sig.ident.to_string().starts_with("VERUS_SPEC__")
        {
            return original;
        }
        return expand_function(original, Function::from_item(&input), kind);
    }

    if let Ok(input) = parse2::<TraitItemFn>(item.clone()) {
        let original = input.to_token_stream();
        let Some(func) = Function::from_trait_item(&input) else {
            return original;
        };
        return expand_function(original, func, kind);
    }

    Error::new(
        Span::call_site(),
        "function contract macros can only be applied to functions",
    )
    .to_compile_error()
}

fn expand_function(
    original: TokenStream,
    func: Result<Function<'_>, TokenStream>,
    kind: ExpansionKind,
) -> TokenStream {
    let func = match func {
        Ok(func) => func,
        Err(err) => return quote! { #original #err },
    };
    let lemma = match kind {
        ExpansionKind::Surjective(lemma_kind) => gen_surjective(&func, &lemma_kind),
        ExpansionKind::Injective(args, lemma_kind) => gen_injective(&func, &args, &lemma_kind),
    };

    quote! { #original #lemma }
}

struct Function<'a> {
    name: Ident,
    span: Span,
    generics: &'a syn::Generics,
    original_args: Vec<Arg>,
    ret: Option<Arg>,
    preconditions: Vec<Expr>,
    postconditions: Vec<Expr>,
}

#[derive(Clone)]
struct Arg {
    ident: Ident,
    ty: Type,
    is_receiver: bool,
}

impl<'a> Function<'a> {
    fn from_item(input: &'a ItemFn) -> Result<Self, TokenStream> {
        Self::from_parts(
            input.sig.ident.clone(),
            input.sig.ident.span(),
            &input.sig.generics,
            &input.sig.inputs,
            &input.sig.output,
            &input.block.stmts,
            &input.attrs,
        )
    }

    fn from_trait_item(input: &'a TraitItemFn) -> Option<Result<Self, TokenStream>> {
        let name = input.sig.ident.to_string();
        let name = name.strip_prefix("VERUS_SPEC__").unwrap_or(&name);
        let block = input.default.as_ref()?;
        Some(Self::from_parts(
            Ident::new(
                name,
                input.sig.ident.span(),
            ),
            input.sig.ident.span(),
            &input.sig.generics,
            &input.sig.inputs,
            &input.sig.output,
            &block.stmts,
            &input.attrs,
        ))
    }

    fn from_parts(
        name: Ident,
        span: Span,
        generics: &'a syn::Generics,
        inputs: &'a Punctuated<FnArg, Token![,]>,
        output: &'a ReturnType,
        stmts: &'a [Stmt],
        attrs: &'a [Attribute],
    ) -> Result<Self, TokenStream> {
        ensure_supported_mode(attrs, &name)?;
        ensure_no_mut_refs(inputs, output)?;

        let original_args = collect_args(inputs)?;
        let ret = return_arg(&name, output, stmts, span)?;
        let (preconditions, postconditions) = collect_contracts(stmts, ret.as_ref())?;

        Ok(Self {
            name,
            span,
            generics,
            original_args,
            ret,
            preconditions,
            postconditions,
        })
    }
}

fn ensure_supported_mode(attrs: &[Attribute], ident: &Ident) -> Result<(), TokenStream> {
    let is_proof = has_verus_internal_attr(attrs, "proof");
    let is_exec = !has_verus_internal_attr(attrs, "spec")
        && !has_verus_internal_attr(attrs, "proof")
        && !has_verus_internal_attr(attrs, "proof_axiom");

    if is_proof || is_exec {
        Ok(())
    } else {
        Err(Error::new_spanned(
            ident,
            "function contract macros only support proof fn or exec fn",
        )
        .to_compile_error())
    }
}

fn has_verus_internal_attr(attrs: &[Attribute], expected: &str) -> bool {
    attrs.iter().any(|attr| {
        let path = attr.path();
        if path.segments.len() != 2 {
            return false;
        }
        if path.segments[0].ident != "verus" || path.segments[1].ident != "internal" {
            return false;
        }
        match &attr.meta {
            syn::Meta::List(list) => list.tokens.to_string() == expected,
            _ => false,
        }
    })
}

fn ensure_no_mut_refs(
    inputs: &Punctuated<FnArg, Token![,]>,
    output: &ReturnType,
) -> Result<(), TokenStream> {
    let mut visitor = MutRefVisitor { found: None };
    for arg in inputs {
        visitor.visit_fn_arg(arg);
    }
    visitor.visit_return_type(output);

    if let Some(span) = visitor.found {
        Err(
            Error::new(span, "function contract macros do not support &mut types")
                .to_compile_error(),
        )
    } else {
        Ok(())
    }
}

struct MutRefVisitor {
    found: Option<Span>,
}

impl<'ast> Visit<'ast> for MutRefVisitor {
    fn visit_type_reference(&mut self, node: &'ast syn::TypeReference) {
        if node.mutability.is_some() && self.found.is_none() {
            self.found = Some(node.and_token.span);
        }
        syn::visit::visit_type_reference(self, node);
    }

    fn visit_receiver(&mut self, node: &'ast syn::Receiver) {
        if node.mutability.is_some() && self.found.is_none() {
            self.found = Some(node.self_token.span);
        }
        syn::visit::visit_receiver(self, node);
    }
}

fn collect_args(inputs: &Punctuated<FnArg, Token![,]>) -> Result<Vec<Arg>, TokenStream> {
    inputs.iter().map(arg_from_fn_arg).collect()
}

fn arg_from_fn_arg(arg: &FnArg) -> Result<Arg, TokenStream> {
    match arg {
        FnArg::Receiver(receiver) => Ok(Arg {
            ident: Ident::new("self", receiver.self_token.span),
            ty: (*receiver.ty).clone(),
            is_receiver: true,
        }),
        FnArg::Typed(PatType { pat, ty, .. }) => {
            let ident = ident_from_pat(pat).ok_or_else(|| {
                Error::new_spanned(pat, "function contract macros require identifier arguments")
                    .to_compile_error()
            })?;
            Ok(Arg {
                ident,
                ty: (**ty).clone(),
                is_receiver: false,
            })
        }
    }
}

fn ident_from_pat(pat: &Pat) -> Option<Ident> {
    match pat {
        Pat::Ident(PatIdent { ident, .. }) => Some(ident.clone()),
        Pat::Reference(reference) => ident_from_pat(&reference.pat),
        Pat::Type(typed) => ident_from_pat(&typed.pat),
        _ => None,
    }
}

fn return_arg(
    name: &Ident,
    output: &ReturnType,
    stmts: &[Stmt],
    span: Span,
) -> Result<Option<Arg>, TokenStream> {
    let ReturnType::Type(_, ty) = output else {
        return Ok(None);
    };

    let mut ret_ident = None;
    for stmt in stmts {
        if let Some(ident) = named_return_from_ensures(stmt, span) {
            ret_ident = Some(ident);
            break;
        }
    }

    let ident = if let Some(ident) = ret_ident {
        ident
    } else if has_contract_clause(stmts, "returns") {
        Ident::new("ret", span)
    } else {
        return Err(Error::new_spanned(
            name,
            "function contract macros require a named return value",
        )
        .to_compile_error());
    };

    Ok(Some(Arg {
        ident,
        ty: (**ty).clone(),
        is_receiver: false,
    }))
}

fn named_return_from_ensures(stmt: &Stmt, name_span: Span) -> Option<Ident> {
    let Stmt::Expr(Expr::Call(call), _) = stmt else {
        return None;
    };
    if !expr_path_ends_with(&call.func, "ensures") || call.args.len() != 1 {
        return None;
    }
    let Expr::Closure(closure) = call.args.first()? else {
        return None;
    };
    if closure.inputs.len() != 1 {
        return None;
    }
    let input = closure.inputs.first()?;
    let ident = ident_from_pat(input)?;
    let ident_str = ident.to_string();
    if ident_str.starts_with("_verge_ret") {
        return None;
    }
    let mut ret = Ident::new(&ident_str, name_span);
    ret.set_span(ident.span());
    Some(ret)
}

fn has_contract_clause(stmts: &[Stmt], name: &str) -> bool {
    stmts
        .iter()
        .any(|stmt| matches!(contract_call_exprs(stmt, name), Ok(Some(_))))
}

fn collect_contracts(
    stmts: &[Stmt],
    ret: Option<&Arg>,
) -> Result<(Vec<Expr>, Vec<Expr>), TokenStream> {
    let mut preconditions = Vec::new();
    let mut postconditions = Vec::new();

    for stmt in stmts {
        if let Some(exprs) = contract_call_exprs(stmt, "requires")? {
            preconditions.extend(exprs);
        } else if let Some(exprs) = ensures_call_exprs(stmt)? {
            postconditions.extend(exprs);
        } else if let Some(exprs) = contract_call_exprs(stmt, "returns")? {
            let Some(ret) = ret else {
                return Err(
                    Error::new_spanned(stmt, "returns clause requires a return value")
                        .to_compile_error(),
                );
            };
            let ret_ident = &ret.ident;
            postconditions.extend(exprs.into_iter().map(|expr| {
                parse_quote! {
                    ::vstd::prelude::spec_eq(#ret_ident, #expr)
                }
            }));
        } else if is_contract_prefix_stmt(stmt) {
            continue;
        } else {
            break;
        }
    }

    Ok((preconditions, postconditions))
}

fn contract_call_exprs(stmt: &Stmt, name: &str) -> Result<Option<Vec<Expr>>, TokenStream> {
    let Stmt::Expr(Expr::Call(call), _) = stmt else {
        return Ok(None);
    };
    if !expr_path_ends_with(&call.func, name) {
        return Ok(None);
    }
    if call.args.len() != 1 {
        return Err(Error::new_spanned(call, "malformed Verus contract clause").to_compile_error());
    }
    let arg = call.args.first().expect("len checked");
    expr_list(arg).map(Some)
}

fn ensures_call_exprs(stmt: &Stmt) -> Result<Option<Vec<Expr>>, TokenStream> {
    let Stmt::Expr(Expr::Call(call), _) = stmt else {
        return Ok(None);
    };
    if !expr_path_ends_with(&call.func, "ensures") {
        return Ok(None);
    }
    if call.args.len() != 1 {
        return Err(Error::new_spanned(call, "malformed Verus ensures clause").to_compile_error());
    }
    let arg = call.args.first().expect("len checked");
    flatten_ensures_arg(arg).map(Some)
}

fn expr_list(expr: &Expr) -> Result<Vec<Expr>, TokenStream> {
    match expr {
        Expr::Array(array) => Ok(array.elems.iter().cloned().collect()),
        _ => Err(
            Error::new_spanned(expr, "malformed Verus contract expression list").to_compile_error(),
        ),
    }
}

fn flatten_ensures_arg(expr: &Expr) -> Result<Vec<Expr>, TokenStream> {
    let exprs = match expr {
        Expr::Array(array) => array.elems.iter().cloned().collect(),
        Expr::Closure(closure) => match &*closure.body {
            Expr::Array(array) => array.elems.iter().cloned().collect(),
            body => vec![body.clone()],
        },
        _ => {
            return Err(
                Error::new_spanned(expr, "malformed Verus ensures clause").to_compile_error()
            );
        }
    };

    Ok(exprs
        .into_iter()
        .filter(|expr| !is_constrain_type(expr))
        .collect())
}

fn is_constrain_type(expr: &Expr) -> bool {
    let Expr::Call(call) = expr else { return false };
    expr_path_ends_with(&call.func, "constrain_type")
}

fn is_contract_prefix_stmt(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Expr(Expr::Call(call), _) => {
            expr_path_ends_with(&call.func, "requires")
                || expr_path_ends_with(&call.func, "ensures")
                || expr_path_ends_with(&call.func, "returns")
        }
        _ => false,
    }
}

fn expr_path_ends_with(expr: &Expr, name: &str) -> bool {
    let Expr::Path(path) = expr else { return false };
    path.path
        .segments
        .last()
        .is_some_and(|segment| segment.ident == name)
}

fn gen_surjective(func: &Function<'_>, kind: &LemmaKind) -> TokenStream {
    let lemma_name = lemma_name(func, kind, "surjective");
    let generics = func.generics;
    let where_clause = &func.generics.where_clause;
    let inputs = lemma_inputs(func, None);
    let call_args = lemma_call_args(func, None);
    let requires = clauses(&func.postconditions);
    let ensures = clauses(&func.preconditions);
    let requires_call = requires_call(&requires);
    let ensures_call = ensures_call(&ensures);
    let body = lemma_body(kind, &call_args);

    quote_spanned! { func.span =>
        #[verus::internal(verus_macro)]
        #[verus::internal(proof)]
        fn #lemma_name #generics (#(#inputs),*) #where_clause {
            #requires_call
            #ensures_call
            #body
        }
    }
}

fn gen_injective(func: &Function<'_>, args: &InjectionArgs, kind: &LemmaKind) -> TokenStream {
    let lemma_name = lemma_name(func, kind, "injective");
    let generics = func.generics;
    let where_clause = &func.generics.where_clause;
    let inputs1 = lemma_inputs(func, Some("1"));
    let inputs2 = lemma_inputs(func, Some("2"));
    let call_args1 = lemma_call_args(func, Some("1"));
    let call_args2 = lemma_call_args(func, Some("2"));
    let call_args: Vec<_> = call_args1.into_iter().chain(call_args2).collect();
    let pre1 = clauses_for_suffix(&func.preconditions, func, "1");
    let post1 = clauses_for_suffix(&func.postconditions, func, "1");
    let pre2 = clauses_for_suffix(&func.preconditions, func, "2");
    let post2 = clauses_for_suffix(&func.postconditions, func, "2");
    let left_equalities = args
        .left
        .iter()
        .map(|expr| injective_equality(expr, func, "1", "2"));
    let right_equalities = args
        .right
        .iter()
        .map(|expr| injective_equality(expr, func, "1", "2"));
    let requires: Vec<_> =
        quote! { #(#pre1,)* #(#post1,)* #(#pre2,)* #(#post2,)* #(#left_equalities,)* }
            .into_iter()
            .collect();
    let ensures: Vec<_> = quote! { #(#right_equalities,)* }.into_iter().collect();
    let requires_call = raw_contract_call("requires", requires);
    let ensures_call = raw_contract_call("ensures", ensures);
    let body = lemma_body(kind, &call_args);

    quote_spanned! { func.span =>
        #[verus::internal(verus_macro)]
        #[verus::internal(proof)]
        fn #lemma_name #generics (#(#inputs1,)* #(#inputs2),*) #where_clause {
            #requires_call
            #ensures_call
            #body
        }
    }
}

fn lemma_name(func: &Function<'_>, kind: &LemmaKind, suffix: &str) -> Ident {
    match kind {
        LemmaKind::Assume { .. } => {
            Ident::new(&format!("__assume_{}_{}", func.name, suffix), func.span)
        }
        LemmaKind::Assert { .. } => {
            Ident::new(&format!("__{}_{}", func.name, suffix), func.span)
        }
    }
}

fn lemma_body(kind: &LemmaKind, call_args: &[Ident]) -> TokenStream {
    match kind {
        LemmaKind::Assume { proof } => quote! { #proof(#(#call_args),*); },
        LemmaKind::Assert { proof } => quote! { #proof(#(#call_args),*); },
    }
}

fn requires_call(clauses: &[TokenStream]) -> TokenStream {
    if clauses.is_empty() {
        quote! {}
    } else {
        quote! { ::vstd::prelude::requires([#(#clauses,)*]); }
    }
}

fn ensures_call(clauses: &[TokenStream]) -> TokenStream {
    if clauses.is_empty() {
        quote! {}
    } else {
        quote! { ::vstd::prelude::ensures([#(#clauses,)*]); }
    }
}

fn raw_contract_call(name: &str, clauses: Vec<TokenTree>) -> TokenStream {
    if clauses.is_empty() {
        return quote! {};
    }

    let name = Ident::new(name, Span::call_site());
    let clauses: TokenStream = clauses.into_iter().collect();
    quote! { ::vstd::prelude::#name([#clauses]); }
}

fn lemma_inputs(func: &Function<'_>, suffix: Option<&str>) -> Vec<TokenStream> {
    func.original_args
        .iter()
        .chain(func.ret.iter())
        .map(|arg| {
            let ident = suffixed_ident(&arg.ident, suffix);
            let ty = &arg.ty;
            if arg.is_receiver && suffix.is_none() {
                quote! { #ident: #ty }
            } else {
                quote! { #ident: #ty }
            }
        })
        .collect()
}

fn lemma_call_args(func: &Function<'_>, suffix: Option<&str>) -> Vec<Ident> {
    func.original_args
        .iter()
        .chain(func.ret.iter())
        .map(|arg| suffixed_ident(&arg.ident, suffix))
        .collect()
}

fn clauses(exprs: &[Expr]) -> Vec<TokenStream> {
    exprs.iter().map(|expr| quote! { #expr }).collect()
}

fn clauses_for_suffix(exprs: &[Expr], func: &Function<'_>, suffix: &str) -> Vec<TokenStream> {
    exprs
        .iter()
        .map(|expr| {
            let expr = rename_expr(expr, func, suffix);
            quote! { #expr }
        })
        .collect()
}

fn injective_equality(
    expr: &TokenStream,
    func: &Function<'_>,
    suffix1: &str,
    suffix2: &str,
) -> TokenStream {
    let lhs = rename_injection_expr(expr, func, suffix1);
    let rhs = rename_injection_expr(expr, func, suffix2);
    quote! {
        ::vstd::prelude::verus_proof_expr!((#lhs) == (#rhs))
    }
}

fn rename_injection_expr(expr: &TokenStream, func: &Function<'_>, suffix: &str) -> TokenStream {
    let mapping = rename_mapping(func, suffix);
    rename_tokens(expr.clone(), &mapping)
}

fn rename_expr(expr: &Expr, func: &Function<'_>, suffix: &str) -> TokenStream {
    let mapping = rename_mapping(func, suffix);
    rename_tokens(expr.to_token_stream(), &mapping)
}

fn rename_mapping(func: &Function<'_>, suffix: &str) -> Vec<(String, Ident)> {
    func.original_args
        .iter()
        .chain(func.ret.iter())
        .map(|arg| {
            (
                arg.ident.to_string(),
                suffixed_ident(&arg.ident, Some(suffix)),
            )
        })
        .collect()
}

fn rename_tokens(tokens: TokenStream, mapping: &[(String, Ident)]) -> TokenStream {
    tokens
        .into_iter()
        .map(|token| match token {
            TokenTree::Ident(ident) => mapping
                .iter()
                .find(|(name, _)| ident == name)
                .map(|(_, replacement)| {
                    TokenTree::Ident(clone_with_span(replacement, ident.span()))
                })
                .unwrap_or(TokenTree::Ident(ident)),
            TokenTree::Group(group) => {
                let mut renamed =
                    Group::new(group.delimiter(), rename_tokens(group.stream(), mapping));
                renamed.set_span(group.span());
                TokenTree::Group(renamed)
            }
            other => other,
        })
        .collect()
}

fn clone_with_span(ident: &Ident, span: Span) -> Ident {
    let mut cloned = ident.clone();
    cloned.set_span(span);
    cloned
}

fn suffixed_ident(ident: &Ident, suffix: Option<&str>) -> Ident {
    match suffix {
        Some(suffix) => Ident::new(&format!("{}{}", ident, suffix), ident.span()),
        None => ident.clone(),
    }
}

struct InjectionArgs {
    left: Vec<TokenStream>,
    right: Vec<TokenStream>,
}

struct AssumeInjectiveArgs {
    proof: TokenStream,
    injection: InjectionArgs,
}

impl Parse for AssumeInjectiveArgs {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let proof: Path = input.parse()?;
        let content;
        parenthesized!(content in input);
        if !input.is_empty() {
            return Err(input.error("assume_injective_by expects a proof call expression"));
        }

        let tokens: TokenStream = content.parse()?;
        let injection = parse_injection_tokens(tokens, "assume_injective_by")
            .map_err(|message| content.error(message))?;

        Ok(Self {
            proof: proof.to_token_stream(),
            injection,
        })
    }
}

impl Parse for InjectionArgs {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let tokens: TokenStream = input.parse()?;
        parse_injection_tokens(tokens, "assume_injective_by")
            .map_err(|message| input.error(message))
    }
}

struct AssertInjectiveArgs {
    proof: TokenStream,
    injection: InjectionArgs,
}

impl Parse for AssertInjectiveArgs {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let proof: Path = input.parse()?;
        let content;
        parenthesized!(content in input);
        if !input.is_empty() {
            return Err(input.error("assert_injective_by expects a proof call expression"));
        }

        let tokens: TokenStream = content.parse()?;
        let injection = parse_injection_tokens(tokens, "assert_injective_by")
            .map_err(|message| content.error(message))?;

        Ok(Self {
            proof: proof.to_token_stream(),
            injection,
        })
    }
}

fn parse_injection_tokens(tokens: TokenStream, macro_name: &str) -> Result<InjectionArgs, String> {
    let mut left = TokenStream::new();
    let mut right = TokenStream::new();
    let mut semis = 0usize;

    for token in tokens {
        match &token {
            TokenTree::Punct(punct) if punct.as_char() == ';' => {
                if semis > 0 {
                    return Err(format!("{macro_name} requires exactly one `;` separator"));
                }
                semis += 1;
            }
            other => {
                if semis == 0 {
                    left.extend(std::iter::once(other.clone()));
                } else {
                    right.extend(std::iter::once(other.clone()));
                }
            }
        }
    }

    if semis != 1 {
        return Err(format!("{macro_name} requires exactly one `;` separator"));
    }

    let left = parse_injection_side(left, macro_name)?;
    let right = parse_injection_side(right, macro_name)?;

    if left.is_empty() || right.is_empty() {
        return Err(format!(
            "{macro_name} requires nonempty left and right expression lists"
        ));
    }

    Ok(InjectionArgs { left, right })
}

fn parse_injection_side(tokens: TokenStream, macro_name: &str) -> Result<Vec<TokenStream>, String> {
    if tokens.is_empty() {
        return Err(format!(
            "{macro_name} expression lists cannot contain empty entries"
        ));
    }
    let exprs = verus_syn::parse::Parser::parse2(
        verus_syn::punctuated::Punctuated::<verus_syn::Expr, verus_syn::Token![,]>::parse_terminated,
        tokens,
    )
    .map_err(|_| format!("{macro_name} expects comma-separated Verus expressions on each side"))?;

    if exprs.is_empty() {
        return Err(format!(
            "{macro_name} expression lists cannot contain empty entries"
        ));
    }

    Ok(exprs
        .into_iter()
        .map(|expr| expr.to_token_stream())
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    #[test]
    fn parses_assume_surjective_path() {
        let proof: Path = parse2(quote! { crate::proof::lemma_name }).unwrap();
        assert_eq!(proof.to_token_stream().to_string(), "crate :: proof :: lemma_name");
    }

    #[test]
    fn parses_assume_injective_proof_call() {
        let args: AssumeInjectiveArgs =
            parse2(quote! { crate::proof::lemma_name(x, y@; ret.seq()) }).unwrap();
        assert_eq!(args.proof.to_string(), "crate :: proof :: lemma_name");
        assert_eq!(args.injection.left.len(), 2);
        assert_eq!(args.injection.right.len(), 1);
    }

    #[test]
    fn parses_injection_separator() {
        let args =
            parse_injection_tokens(quote! { x, y@; ret.seq() }, "assume_injective_by").unwrap();
        assert_eq!(args.left.len(), 2);
        assert_eq!(args.right.len(), 1);
    }

    #[test]
    fn parses_assert_injective_proof_call() {
        let args: AssertInjectiveArgs =
            parse2(quote! { crate::proof::lemma(s@, ch; ret) }).unwrap();
        assert_eq!(args.proof.to_string(), "crate :: proof :: lemma");
        assert_eq!(args.injection.left.len(), 2);
        assert_eq!(args.injection.right.len(), 1);
    }

    #[test]
    fn rejects_missing_separator() {
        assert!(parse_injection_tokens(quote! { x, y }, "assume_injective_by").is_err());
    }

    #[test]
    fn rejects_duplicate_separator() {
        assert!(parse_injection_tokens(quote! { x; y; z }, "assume_injective_by").is_err());
    }

    #[test]
    fn rejects_assert_injective_without_call() {
        assert!(parse2::<AssertInjectiveArgs>(quote! { crate::proof::lemma }).is_err());
    }

    #[test]
    fn rejects_assume_injective_without_call() {
        assert!(parse2::<AssumeInjectiveArgs>(quote! { lemma_name }).is_err());
    }
}
