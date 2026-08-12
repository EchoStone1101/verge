//! Function-contract attribute macros reserved for future use.
//!
//! Verge currently keeps the macro surface available but does not apply any of
//! these attributes or ship contract lemmas under `verge::func`. The available
//! macros are `assume_surjective`, `assume_injective_by`, `assert_surjective`,
//! and `assert_injective_by`.

pub use verge_macros::{
    assert_injective_by,
    assert_surjective,
    assume_injective_by,
    assume_surjective,
};
