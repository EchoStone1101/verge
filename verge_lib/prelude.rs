//! Verge library prelude.

// Verified trait invariants for comparison
pub use crate::cmp::{PartialEqVerified, EqVerified, PartialOrdVerified, OrdVerified};

// Verified trait invariants for clone/copy
pub use crate::clone::{ClonePartialEq, CopyVerified};

// Proc-macro attributes
pub use verge_macros::{
    hash_key,
    hash_key_with_clone,
    derive_partial_eq,
    derive_eq,
    derive_partial_ord,
    derive_ord,
    derive_clone,
    derive_copy,
    derive_default,
};
