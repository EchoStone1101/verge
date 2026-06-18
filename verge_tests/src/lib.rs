//! Integration tests for Verge public APIs.
//!
//! These modules intentionally live outside `verge_lib` so they exercise the same
//! visibility, imports, and broadcast defaults available to downstream users.

#![allow(incomplete_features)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(unused_doc_comments)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(rustdoc::invalid_rust_codeblocks)]
#![feature(allocator_api)]
#![feature(sized_hierarchy)]
#![feature(pattern)]
#![feature(specialization)]
#![feature(slice_index_methods)]

mod io;
mod str;
