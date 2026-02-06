// //! Utilities and workarounds for mutable references, until Verus adds better support.
// //! 
// //! Currently (as of Feb 2026) Verus's support of `&mut` remains limited, making it impossible 
// //! to verify some perfectly valid code. For example, `&mut` is not allowed at the return position, 
// //! so `IndexMut` or `<[T]>::split_at_mut` cannot be expressed. It is also essentially impossible 
// //! to obtain an `&mut [T]` (e.g., from `[T; N]` or `Vec<T>`).
// //!
// //! We provide access to some crucial trait methods by wrapping their application in an external
// //! block, while retaining the proof conditions by using higher-order functions.

// use vstd::prelude::*;
// use vstd::view::View;

// use core::marker::PointeeSized;
// use core::ops::Deref;

// verus! {

// #[verifier::external_trait_specification]
// pub trait ExAsMut<T: PointeeSized>: PointeeSized {
//     type ExternalTraitSpecificationFor: core::convert::AsMut<T>;
// }

// #[verifier::external_trait_specification]
// pub trait ExDerefMut: core::ops::Deref + PointeeSized {
//     type ExternalTraitSpecificationFor: core::ops::DerefMut;
// }

// #[verifier::external_body]
// pub fn app_as_mut<T: core::convert::AsMut<U> + View, U: ?Sized>(
//     t: &mut T, 
//     f: impl FnOnce(&mut U),
//     f_spec: Ghost<spec_fn(T::V) -> T::V>,
// )
//     ensures
//         t@ == f_spec@(old(t)@),
// {
//     f(<T as core::convert::AsMut<U>>::as_mut(t));
// }

// #[verifier::external_body]
// pub fn app_deref_mut<T: core::ops::DerefMut + View>(
//     t: &mut T, 
//     f: impl FnOnce(&mut T::Target),
//     f_spec: spec_fn(T::V) -> T::V,
// )
//     ensures
//         t@ == f_spec(old(t)@),
// {
//     f(<T as core::ops::DerefMut>::deref_mut(t))
// }

// // pub fn take_mut_slice(x: &mut [i32]) {}

// // #[verifier::external_body]
// // pub fn take_ref_slice(x: &[i32]) {
// //     unsafe { take_mut_slice(std::mem::transmute(x)) }
// // }

// // pub fn test() {
// //     let ghost f_spec = |pre: Seq<i32>| pre;
// //     assert(is_refinement::<[i32; 32], [i32]>(take_ref_slice, f_spec));
// // }



// // pub fn unsize() {
// //     let mut x = [0i32; 32];

// //     let ghost f_spec = |pre: Seq<i32>| pre;
// //     app_as_mut(&mut x, take_mut_slice, Ghost(f_spec));
// // }

// } // verus!