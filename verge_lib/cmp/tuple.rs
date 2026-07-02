//! Verified comparison impls for tuples.

use super::*;
use core::cmp::{Ord, Ordering, PartialEq, PartialOrd};
use vstd::math::min;

macro_rules! tuple_cmp_impl {
    ($($idx:tt $T:ident, )+) => {
        verus! {
        pub assume_specification<$($T: PartialEq),+>[ <($($T,)+) as PartialEq>::eq ](a: &($($T,)+), b: &($($T,)+)) -> bool;
        pub assume_specification<$($T: PartialEq),+>[ <($($T,)+) as PartialEq>::ne ](a: &($($T,)+), b: &($($T,)+)) -> bool;
        impl<$($T: PartialEqVerified),+> PartialEqVerified for ($($T,)+) {
            proof fn lemma_obeys_eq_spec() {
                $($T::lemma_obeys_eq_spec(); )+
            }
            proof fn lemma_eq_symmetric(a: &Self, b: &Self) {
                $($T::lemma_eq_symmetric(&a.$idx, &b.$idx); )+
            }
            proof fn lemma_eq_transitive(a: &Self, b: &Self, c: &Self) {
                $($T::lemma_eq_transitive(&a.$idx, &b.$idx, &c.$idx); )+
            }
        }
        impl<$($T: EqVerified),+> EqVerified for ($($T,)+) {
            proof fn lemma_eq_reflexive(a: &Self) {
                $($T::lemma_eq_reflexive(&a.$idx); )+
            }
        }
        // XXX: due to Verus's self-reference checks being overly conservative (#1487),
        // `partial_cmp`, `le`, and `ge` cannot be added.
        pub assume_specification<$($T: PartialOrd),+>[ <($($T,)+) as PartialOrd>::lt ](a: &($($T,)+), b: &($($T,)+)) -> bool;
        pub assume_specification<$($T: PartialOrd),+>[ <($($T,)+) as PartialOrd>::gt ](a: &($($T,)+), b: &($($T,)+)) -> bool;
        pub assume_specification<$($T: Ord),+>[ <($($T,)+) as Ord>::cmp ](a: &($($T,)+), b: &($($T,)+)) -> Ordering;
        impl<$($T: PartialOrdVerified),+> PartialOrdVerified for ($($T,)+) {
            proof fn lemma_obeys_partial_cmp_spec() {
                $($T::lemma_obeys_partial_cmp_spec(); )+
            }
            proof fn lemma_cmp_eq_consistent(a: &Self, b: &Self) {
                $($T::lemma_cmp_eq_consistent(&a.$idx, &b.$idx); )+
                $(<$T as PartialEqVerified>::lemma_eq_symmetric(&a.$idx, &b.$idx); )+
            }
            proof fn lemma_cmp_dual(a: &Self, b: &Self) {
                $($T::lemma_cmp_dual(&a.$idx, &b.$idx); )+
                $(<$T as PartialEqVerified>::lemma_eq_symmetric(&a.$idx, &b.$idx); )+
                $($T::lemma_cmp_eq_consistent(&a.$idx, &b.$idx); )+
                $($T::lemma_cmp_eq_consistent(&b.$idx, &a.$idx); )+
            }
            proof fn lemma_cmp_transitive(a: &Self, b: &Self, c: &Self) {
                let s_ab: Seq<Option<core::cmp::Ordering>> = seq![$(<$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.$idx, &b.$idx)),+];
                let s_bc: Seq<Option<core::cmp::Ordering>> = seq![$(<$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&b.$idx, &c.$idx)),+];
                let s_ac: Seq<Option<core::cmp::Ordering>> = seq![$(<$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.$idx, &c.$idx)),+];
                let n = s_ab.len() as int;
                if <Self as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(a, b) == Some(core::cmp::Ordering::Less) {
                    assert(lexico_less(s_ab)) by {
                        $(if s_ab[$idx as int] != Some(core::cmp::Ordering::Equal) { assert(s_ab[$idx as int] == Some(core::cmp::Ordering::Less)); } else)+ {}
                    }
                    assert(lexico_less(s_bc)) by {
                        $(if s_bc[$idx as int] != Some(core::cmp::Ordering::Equal) { assert(s_bc[$idx as int] == Some(core::cmp::Ordering::Less)); } else)+ {}
                    }
                    // Per-element substitutivity
                    assert forall|j: int| 0 <= j < n implies {
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Equal) && s_bc[j] == Some(core::cmp::Ordering::Equal) ==> s_ac[j] == Some(core::cmp::Ordering::Equal))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Less) && s_bc[j] == Some(core::cmp::Ordering::Equal) ==> s_ac[j] == Some(core::cmp::Ordering::Less))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Equal) && s_bc[j] == Some(core::cmp::Ordering::Less) ==> s_ac[j] == Some(core::cmp::Ordering::Less))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Less) && s_bc[j] == Some(core::cmp::Ordering::Less) ==> s_ac[j] == Some(core::cmp::Ordering::Less))
                    } by {
                        $(if j == $idx {
                            $T::lemma_cmp_eq_consistent(&a.$idx, &b.$idx);
                            $T::lemma_cmp_eq_consistent(&b.$idx, &c.$idx);
                            $T::lemma_cmp_dual(&b.$idx, &a.$idx);
                            $T::lemma_cmp_dual(&c.$idx, &a.$idx);
                            if <$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.$idx, &b.$idx) == Some(core::cmp::Ordering::Less)
                                && <$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&b.$idx, &c.$idx) == Some(core::cmp::Ordering::Less) {
                                $T::lemma_cmp_transitive(&a.$idx, &b.$idx, &c.$idx);
                            }
                        } else)+
                        {}
                    };
                    assert(lexico_less(s_ac)) by {
                        let i1 = choose|i: int| 0 <= i < s_ab.len()
                            && s_ab[i] == Some(core::cmp::Ordering::Less)
                            && forall|j: int| 0 <= j < i ==> s_ab[j] == Some(core::cmp::Ordering::Equal);
                        let i2 = choose|i: int| 0 <= i < s_bc.len()
                            && s_bc[i] == Some(core::cmp::Ordering::Less)
                            && forall|j: int| 0 <= j < i ==> s_bc[j] == Some(core::cmp::Ordering::Equal);
                        let k = min(i1, i2);
                        assert(s_ac[k] == Some(core::cmp::Ordering::Less));
                        assert forall |j: int| 0 <= j < k implies s_ac[j] == Some(core::cmp::Ordering::Equal) by {}
                    }
                } else {
                    assert(lexico_greater(s_ab)) by {
                        $(if s_ab[$idx as int] != Some(core::cmp::Ordering::Equal) { assert(s_ab[$idx as int] == Some(core::cmp::Ordering::Greater)); } else)+ {}
                    }
                    assert(lexico_greater(s_bc)) by {
                        $(if s_bc[$idx as int] != Some(core::cmp::Ordering::Equal) { assert(s_bc[$idx as int] == Some(core::cmp::Ordering::Greater)); } else)+ {}
                    }
                    // Per-element substitutivity
                    assert forall|j: int| 0 <= j < n implies {
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Equal) && s_bc[j] == Some(core::cmp::Ordering::Equal) ==> s_ac[j] == Some(core::cmp::Ordering::Equal))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Greater) && s_bc[j] == Some(core::cmp::Ordering::Equal) ==> s_ac[j] == Some(core::cmp::Ordering::Greater))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Equal) && s_bc[j] == Some(core::cmp::Ordering::Greater) ==> s_ac[j] == Some(core::cmp::Ordering::Greater))
                        &&& (s_ab[j] == Some(core::cmp::Ordering::Greater) && s_bc[j] == Some(core::cmp::Ordering::Greater) ==> s_ac[j] == Some(core::cmp::Ordering::Greater))
                    } by {
                        $(if j == $idx as int {
                            $T::lemma_cmp_eq_consistent(&a.$idx, &b.$idx);
                            $T::lemma_cmp_eq_consistent(&b.$idx, &c.$idx);
                            $T::lemma_cmp_dual(&b.$idx, &a.$idx);
                            $T::lemma_cmp_dual(&c.$idx, &a.$idx);
                            if <$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&a.$idx, &b.$idx) == Some(core::cmp::Ordering::Greater)
                                && <$T as vstd::std_specs::cmp::PartialOrdSpec>::partial_cmp_spec(&b.$idx, &c.$idx) == Some(core::cmp::Ordering::Greater) {
                                $T::lemma_cmp_transitive(&a.$idx, &b.$idx, &c.$idx);
                            }
                        } else)+
                        {}
                    };
                    assert(lexico_greater(s_ac)) by {
                        let i1 = choose|i: int| 0 <= i < s_ab.len()
                            && s_ab[i] == Some(core::cmp::Ordering::Greater)
                            && forall|j: int| 0 <= j < i ==> s_ab[j] == Some(core::cmp::Ordering::Equal);
                        let i2 = choose|i: int| 0 <= i < s_bc.len()
                            && s_bc[i] == Some(core::cmp::Ordering::Greater)
                            && forall|j: int| 0 <= j < i ==> s_bc[j] == Some(core::cmp::Ordering::Equal);
                        let k = min(i1, i2);
                        assert(s_ac[k] == Some(core::cmp::Ordering::Greater));
                        assert forall |j: int| 0 <= j < k implies s_ac[j] == Some(core::cmp::Ordering::Equal) by {}
                    }
                }
            }
        }
        impl<$($T: OrdVerified),+> OrdVerified for ($($T,)+) {
            proof fn lemma_obeys_cmp_spec() {
                $($T::lemma_obeys_cmp_spec(); )+
            }
            proof fn lemma_cmp_consistent(a: &Self, b: &Self) {
                $($T::lemma_cmp_consistent(&a.$idx, &b.$idx); )+
            }
        }
        }
    };
}

tuple_cmp_impl!(0 T, );
tuple_cmp_impl!(0 U, 1 T, );
tuple_cmp_impl!(0 V, 1 U, 2 T, );
tuple_cmp_impl!(0 W, 1 V, 2 U, 3 T, );
tuple_cmp_impl!(0 X, 1 W, 2 V, 3 U, 4 T, );
tuple_cmp_impl!(0 Y, 1 X, 2 W, 3 V, 4 U, 5 T, );
tuple_cmp_impl!(0 Z, 1 Y, 2 X, 3 W, 4 V, 5 U, 6 T, );
tuple_cmp_impl!(0 A, 1 Z, 2 Y, 3 X, 4 W, 5 V, 6 U, 7 T, );
tuple_cmp_impl!(0 B, 1 A, 2 Z, 3 Y, 4 X, 5 W, 6 V, 7 U, 8 T, );
tuple_cmp_impl!(0 C, 1 B, 2 A, 3 Z, 4 Y, 5 X, 6 W, 7 V, 8 U, 9 T, );
tuple_cmp_impl!(0 D, 1 C, 2 B, 3 A, 4 Z, 5 Y, 6 X, 7 W, 8 V, 9 U, 10 T, );
tuple_cmp_impl!(0 E, 1 D, 2 C, 3 B, 4 A, 5 Z, 6 Y, 7 X, 8 W, 9 V, 10 U, 11 T, );
