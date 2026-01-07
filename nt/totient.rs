//! Proofs and specifications for the [Euler's totient function](https://en.wikipedia.org/wiki/Euler%27s_totient_function), 
//! also denoted as `phi(n)`.

use super::{
    set_nat_range, is_factor_of, is_common_factor, is_coprime, is_prime,
};
use vstd::prelude::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::div_mod::*;
use vstd::set_lib::*;
use vstd::math::{min, max};
use vstd::{assert_by_contradiction, calc};

verus! {

/// This function defines the prime numbers in range [lo, hi).
pub open spec fn set_prime_range(lo: nat, hi: nat) -> Set<nat> {
    Set::<nat>::new(|p: nat| is_prime(p) && lo <= p < hi)
}

/// This function defines the totient function `phi(n)`, which computes
/// the number of integers in `1..=n` that is coprime with `n`,
pub open spec fn totient(n: nat) -> nat 
    recommends n > 0,
{
    set_nat_range(1, n + 1).filter(|m: nat| is_coprime(n, m)).len()
}

// TODO: totient_exec

} // verus!