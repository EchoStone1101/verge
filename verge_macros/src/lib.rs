use proc_macro::TokenStream;
use verus_syn::{parse_macro_input, Expr};

mod open_macro;

#[proc_macro]
pub fn open(input: TokenStream) -> TokenStream {
    let expr = parse_macro_input!(input as Expr);
    open_macro::open_impl(expr).into()
}