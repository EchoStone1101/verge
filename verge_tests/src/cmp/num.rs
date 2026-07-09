//! Tests for primitive number and boolean comparison APIs.

use core::cmp::Ordering;

use vstd::prelude::*;
use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};
use verge::cmp::*;
use verge::prelude::*;

verus! {

fn test_numeric_comparison_methods_are_callable() {
    let a: i32 = 3;
    let b: i32 = 5;

    let eq = a == a;
    let ne = a != b;
    let lt = a < b;
    let le = a <= b;
    let gt = b > a;
    let ge = b >= a;
    assert(eq);
    assert(ne);
    assert(lt);
    assert(le);
    assert(gt);
    assert(ge);
    assert(a != b);
    assert(a < b);
    assert(a <= b);
    assert(b > a);
    assert(b >= a);
    let partial = a.partial_cmp(&b);
    let cmp = a.cmp(&b);
    assert(partial == Some(Ordering::Less));
    assert(cmp == Ordering::Less);

    let method_eq = a.eq(&a);
    let method_ne = a.ne(&b);
    let method_lt = a.lt(&b);
    let method_le = a.le(&b);
    let method_gt = b.gt(&a);
    let method_ge = b.ge(&a);
    assert(method_eq);
    assert(method_ne);
    assert(method_lt);
    assert(method_le);
    assert(method_gt);
    assert(method_ge);

    let max = a.max(b);
    let min = a.min(b);
    assert(max == b);
    assert(min == a);
}

fn test_all_numeric_verified_families() {
    let u8_a: u8 = 3;
    let u8_b: u8 = 5;
    let u8_eq = u8_a == u8_a;
    let u8_ne = u8_a != u8_b;
    let u8_lt = u8_a < u8_b;
    let u8_le = u8_a <= u8_b;
    let u8_gt = u8_b > u8_a;
    let u8_ge = u8_b >= u8_a;
    let u8_partial = u8_a.partial_cmp(&u8_b);
    let u8_cmp = u8_a.cmp(&u8_b);
    let u8_max = u8_a.max(u8_b);
    let u8_min = u8_a.min(u8_b);
    assert(u8_eq);
    assert(u8_ne);
    assert(u8_lt);
    assert(u8_le);
    assert(u8_gt);
    assert(u8_ge);
    assert(u8_partial == Some(Ordering::Less));
    assert(u8_cmp == Ordering::Less);
    assert(u8_max == u8_b);
    assert(u8_min == u8_a);

    let u16_a: u16 = 3;
    let u16_b: u16 = 5;
    let u16_eq = u16_a == u16_a;
    let u16_ne = u16_a != u16_b;
    let u16_lt = u16_a < u16_b;
    let u16_le = u16_a <= u16_b;
    let u16_gt = u16_b > u16_a;
    let u16_ge = u16_b >= u16_a;
    let u16_partial = u16_a.partial_cmp(&u16_b);
    let u16_cmp = u16_a.cmp(&u16_b);
    let u16_max = u16_a.max(u16_b);
    let u16_min = u16_a.min(u16_b);
    assert(u16_eq);
    assert(u16_ne);
    assert(u16_lt);
    assert(u16_le);
    assert(u16_gt);
    assert(u16_ge);
    assert(u16_partial == Some(Ordering::Less));
    assert(u16_cmp == Ordering::Less);
    assert(u16_max == u16_b);
    assert(u16_min == u16_a);

    let u32_a: u32 = 3;
    let u32_b: u32 = 5;
    let u32_eq = u32_a == u32_a;
    let u32_ne = u32_a != u32_b;
    let u32_lt = u32_a < u32_b;
    let u32_le = u32_a <= u32_b;
    let u32_gt = u32_b > u32_a;
    let u32_ge = u32_b >= u32_a;
    let u32_partial = u32_a.partial_cmp(&u32_b);
    let u32_cmp = u32_a.cmp(&u32_b);
    let u32_max = u32_a.max(u32_b);
    let u32_min = u32_a.min(u32_b);
    assert(u32_eq);
    assert(u32_ne);
    assert(u32_lt);
    assert(u32_le);
    assert(u32_gt);
    assert(u32_ge);
    assert(u32_partial == Some(Ordering::Less));
    assert(u32_cmp == Ordering::Less);
    assert(u32_max == u32_b);
    assert(u32_min == u32_a);

    let u64_a: u64 = 3;
    let u64_b: u64 = 5;
    let u64_eq = u64_a == u64_a;
    let u64_ne = u64_a != u64_b;
    let u64_lt = u64_a < u64_b;
    let u64_le = u64_a <= u64_b;
    let u64_gt = u64_b > u64_a;
    let u64_ge = u64_b >= u64_a;
    let u64_partial = u64_a.partial_cmp(&u64_b);
    let u64_cmp = u64_a.cmp(&u64_b);
    let u64_max = u64_a.max(u64_b);
    let u64_min = u64_a.min(u64_b);
    assert(u64_eq);
    assert(u64_ne);
    assert(u64_lt);
    assert(u64_le);
    assert(u64_gt);
    assert(u64_ge);
    assert(u64_partial == Some(Ordering::Less));
    assert(u64_cmp == Ordering::Less);
    assert(u64_max == u64_b);
    assert(u64_min == u64_a);

    let u128_a: u128 = 3;
    let u128_b: u128 = 5;
    let u128_eq = u128_a == u128_a;
    let u128_ne = u128_a != u128_b;
    let u128_lt = u128_a < u128_b;
    let u128_le = u128_a <= u128_b;
    let u128_gt = u128_b > u128_a;
    let u128_ge = u128_b >= u128_a;
    let u128_partial = u128_a.partial_cmp(&u128_b);
    let u128_cmp = u128_a.cmp(&u128_b);
    let u128_max = u128_a.max(u128_b);
    let u128_min = u128_a.min(u128_b);
    assert(u128_eq);
    assert(u128_ne);
    assert(u128_lt);
    assert(u128_le);
    assert(u128_gt);
    assert(u128_ge);
    assert(u128_partial == Some(Ordering::Less));
    assert(u128_cmp == Ordering::Less);
    assert(u128_max == u128_b);
    assert(u128_min == u128_a);

    let usize_a: usize = 3;
    let usize_b: usize = 5;
    let usize_eq = usize_a == usize_a;
    let usize_ne = usize_a != usize_b;
    let usize_lt = usize_a < usize_b;
    let usize_le = usize_a <= usize_b;
    let usize_gt = usize_b > usize_a;
    let usize_ge = usize_b >= usize_a;
    let usize_partial = usize_a.partial_cmp(&usize_b);
    let usize_cmp = usize_a.cmp(&usize_b);
    let usize_max = usize_a.max(usize_b);
    let usize_min = usize_a.min(usize_b);
    assert(usize_eq);
    assert(usize_ne);
    assert(usize_lt);
    assert(usize_le);
    assert(usize_gt);
    assert(usize_ge);
    assert(usize_partial == Some(Ordering::Less));
    assert(usize_cmp == Ordering::Less);
    assert(usize_max == usize_b);
    assert(usize_min == usize_a);

    let i8_a: i8 = -5;
    let i8_b: i8 = 3;
    let i8_eq = i8_a == i8_a;
    let i8_ne = i8_a != i8_b;
    let i8_lt = i8_a < i8_b;
    let i8_le = i8_a <= i8_b;
    let i8_gt = i8_b > i8_a;
    let i8_ge = i8_b >= i8_a;
    let i8_partial = i8_a.partial_cmp(&i8_b);
    let i8_cmp = i8_a.cmp(&i8_b);
    let i8_max = i8_a.max(i8_b);
    let i8_min = i8_a.min(i8_b);
    assert(i8_eq);
    assert(i8_ne);
    assert(i8_lt);
    assert(i8_le);
    assert(i8_gt);
    assert(i8_ge);
    assert(i8_partial == Some(Ordering::Less));
    assert(i8_cmp == Ordering::Less);
    assert(i8_max == i8_b);
    assert(i8_min == i8_a);

    let i16_a: i16 = -5;
    let i16_b: i16 = 3;
    let i16_eq = i16_a == i16_a;
    let i16_ne = i16_a != i16_b;
    let i16_lt = i16_a < i16_b;
    let i16_le = i16_a <= i16_b;
    let i16_gt = i16_b > i16_a;
    let i16_ge = i16_b >= i16_a;
    let i16_partial = i16_a.partial_cmp(&i16_b);
    let i16_cmp = i16_a.cmp(&i16_b);
    let i16_max = i16_a.max(i16_b);
    let i16_min = i16_a.min(i16_b);
    assert(i16_eq);
    assert(i16_ne);
    assert(i16_lt);
    assert(i16_le);
    assert(i16_gt);
    assert(i16_ge);
    assert(i16_partial == Some(Ordering::Less));
    assert(i16_cmp == Ordering::Less);
    assert(i16_max == i16_b);
    assert(i16_min == i16_a);

    let i32_a: i32 = -5;
    let i32_b: i32 = 3;
    let i32_eq = i32_a == i32_a;
    let i32_ne = i32_a != i32_b;
    let i32_lt = i32_a < i32_b;
    let i32_le = i32_a <= i32_b;
    let i32_gt = i32_b > i32_a;
    let i32_ge = i32_b >= i32_a;
    let i32_partial = i32_a.partial_cmp(&i32_b);
    let i32_cmp = i32_a.cmp(&i32_b);
    let i32_max = i32_a.max(i32_b);
    let i32_min = i32_a.min(i32_b);
    assert(i32_eq);
    assert(i32_ne);
    assert(i32_lt);
    assert(i32_le);
    assert(i32_gt);
    assert(i32_ge);
    assert(i32_partial == Some(Ordering::Less));
    assert(i32_cmp == Ordering::Less);
    assert(i32_max == i32_b);
    assert(i32_min == i32_a);

    let i64_a: i64 = -5;
    let i64_b: i64 = 3;
    let i64_eq = i64_a == i64_a;
    let i64_ne = i64_a != i64_b;
    let i64_lt = i64_a < i64_b;
    let i64_le = i64_a <= i64_b;
    let i64_gt = i64_b > i64_a;
    let i64_ge = i64_b >= i64_a;
    let i64_partial = i64_a.partial_cmp(&i64_b);
    let i64_cmp = i64_a.cmp(&i64_b);
    let i64_max = i64_a.max(i64_b);
    let i64_min = i64_a.min(i64_b);
    assert(i64_eq);
    assert(i64_ne);
    assert(i64_lt);
    assert(i64_le);
    assert(i64_gt);
    assert(i64_ge);
    assert(i64_partial == Some(Ordering::Less));
    assert(i64_cmp == Ordering::Less);
    assert(i64_max == i64_b);
    assert(i64_min == i64_a);

    let i128_a: i128 = -5;
    let i128_b: i128 = 3;
    let i128_eq = i128_a == i128_a;
    let i128_ne = i128_a != i128_b;
    let i128_lt = i128_a < i128_b;
    let i128_le = i128_a <= i128_b;
    let i128_gt = i128_b > i128_a;
    let i128_ge = i128_b >= i128_a;
    let i128_partial = i128_a.partial_cmp(&i128_b);
    let i128_cmp = i128_a.cmp(&i128_b);
    let i128_max = i128_a.max(i128_b);
    let i128_min = i128_a.min(i128_b);
    assert(i128_eq);
    assert(i128_ne);
    assert(i128_lt);
    assert(i128_le);
    assert(i128_gt);
    assert(i128_ge);
    assert(i128_partial == Some(Ordering::Less));
    assert(i128_cmp == Ordering::Less);
    assert(i128_max == i128_b);
    assert(i128_min == i128_a);

    let isize_a: isize = -5;
    let isize_b: isize = 3;
    let isize_eq = isize_a == isize_a;
    let isize_ne = isize_a != isize_b;
    let isize_lt = isize_a < isize_b;
    let isize_le = isize_a <= isize_b;
    let isize_gt = isize_b > isize_a;
    let isize_ge = isize_b >= isize_a;
    let isize_partial = isize_a.partial_cmp(&isize_b);
    let isize_cmp = isize_a.cmp(&isize_b);
    let isize_max = isize_a.max(isize_b);
    let isize_min = isize_a.min(isize_b);
    assert(isize_eq);
    assert(isize_ne);
    assert(isize_lt);
    assert(isize_le);
    assert(isize_gt);
    assert(isize_ge);
    assert(isize_partial == Some(Ordering::Less));
    assert(isize_cmp == Ordering::Less);
    assert(isize_max == isize_b);
    assert(isize_min == isize_a);

    proof {
        lemma_ord_verified::<u8>();
        lemma_ord_verified::<u16>();
        lemma_ord_verified::<u32>();
        lemma_ord_verified::<u64>();
        lemma_ord_verified::<u128>();
        lemma_ord_verified::<usize>();
        lemma_ord_verified::<i8>();
        lemma_ord_verified::<i16>();
        lemma_ord_verified::<i32>();
        lemma_ord_verified::<i64>();
        lemma_ord_verified::<i128>();
        lemma_ord_verified::<isize>();
    }
}

fn test_bool_equality_methods_and_verified_lemmas() {
    let a = true;
    let b = false;

    assert(a != b);
    let eq = a == true;
    let ne = a != b;
    assert(eq);
    assert(ne);

    proof {
        lemma_partial_eq_verified::<bool>();
    }
}

} // verus!
