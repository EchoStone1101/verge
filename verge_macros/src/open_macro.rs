use proc_macro2::{TokenStream, Span};
use quote::quote;
use verus_syn::{
    visit_mut::{self, VisitMut},
    punctuated::Punctuated, token::Comma,
    Expr, ExprCall, ExprMethodCall, ExprMacro, Ident, 
    Path, PathSegment,
};

pub fn open_impl(mut expr: Expr) -> TokenStream {
    let mut rewriter = Rewriter;
    rewriter.visit_expr_mut(&mut expr);

    quote!(#expr)
}

fn open_calls() -> Vec<(Vec<&'static str>, Vec<&'static str>)> {
    let bytes_fn = [
        "spec_u16_from_le_bytes",
        "spec_u16_to_le_bytes",
        "spec_u32_from_le_bytes",
        "spec_u32_to_le_bytes",
        "spec_u64_from_le_bytes",
        "spec_u64_to_le_bytes_open",
        "spec_u128_from_le_bytes",
        "spec_u128_to_le_bytes",
    ];
    let mut map = Vec::new();
    for fname in bytes_fn.iter() {
        map.push((
            vec!["vstd", "bytes", fname],
            vec!["verge", "open", "bytes", fname],
        ));
    }
    map
}

fn open_macros() -> Vec<(Vec<&'static str>, Vec<&'static str>)> {
    vec![
        (
            vec!["vstd", "set", "set"],
            vec!["verge", "open", "set", "set_literal"],
        ),
    ]
}

struct Rewriter;

impl Rewriter {

    fn rewrite_call_path(&self, path: &mut Path) -> bool {
        for (src, dst) in open_calls() {
            if path_suffix_of(path, &src) {
                #[cfg(debug_assertions)]
                eprintln!("open! > {:?}", path);
                *path = make_path(&dst);
                #[cfg(debug_assertions)]
                eprintln!("     -> {:?}", path);
                return true;
            }
        }
        false
    }
    
    fn rewrite_macro_path(&self, path: &mut Path) {
        for (src, dst) in open_macros() {
            if path_suffix_of(path, &src) {
                #[cfg(debug_assertions)]
                eprintln!("open! > {:?}", path);
                *path = make_path(&dst);
                #[cfg(debug_assertions)]
                eprintln!("     -> {:?}", path);
                return;
            }
        }
    }

    fn rewrite_method_call(&self, mc: &ExprMethodCall) -> Option<Expr> {
        None
        // let method = mc.method.to_string();

        // for (src, dst) in fn_map() {
        //     if src.last().copied() == Some(method.as_str()) {
        //         let mut args: Punctuated<Expr, Comma> = Punctuated::new();
        //         args.push((*mc.receiver).clone());
        //         args.extend(mc.args.iter().cloned());

        //         return Some(Expr::Call(ExprCall {
        //             attrs: Vec::new(),
        //             func: Box::new(Expr::Path(make_path(&dst))),
        //             paren_token: Default::default(),
        //             args,
        //         }));
        //     }
        // }
        // None
    }
}

impl VisitMut for Rewriter {

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        match expr {
            // Method call (x.f(...))
            Expr::MethodCall(mc) => {
                self.visit_expr_mut(&mut mc.receiver);
                for arg in mc.args.iter_mut() {
                    self.visit_expr_mut(arg);
                }

                if let Some(new_expr) = self.rewrite_method_call(mc) {
                    *expr = new_expr;
                    visit_mut::visit_expr_mut(self, expr);
                }
            }

            // Free call + UFCS (f(...), a::b::f(...))
            Expr::Call(call) => {
                self.visit_expr_mut(&mut call.func);
                for arg in call.args.iter_mut() {
                    self.visit_expr_mut(arg);
                }

                if let Expr::Path(p) = &mut *call.func {
                    self.rewrite_call_path(&mut p.path);
                }
            }

            // Macro invocation
            Expr::Macro(mac) => {
                self.rewrite_macro_path(&mut mac.mac.path);
            }

            _ => visit_mut::visit_expr_mut(self, expr),
        }
    }
}

fn path_suffix_of(path: &Path, src: &[&str]) -> bool {
    let segs: Vec<_> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    segs.len() <= src.len()
        && segs == src[src.len() - segs.len()..]
}

fn make_path(segments: &[&str]) -> Path {
    Path {
        leading_colon: None,
        segments: segments
            .iter()
            .map(|s| {
                PathSegment {
                    ident: Ident::new(s, Span::call_site()),
                    arguments: verus_syn::PathArguments::None,
                }
            })
            .collect(),
    }
}