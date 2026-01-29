//! Open version for closed specifications in `vstd::bytes`.

#[allow(unused_imports)]
use vstd::prelude::*;

// TODO: lemmas proving that the open versions are equivalent.

verus! {

pub open spec fn spec_u16_from_le_bytes(s: Seq<u8>) -> u16
    recommends
        s.len() == 2,
{
    (s[0] as u16) | ((s[1] as u16) << 8)
}

pub open spec fn spec_u16_to_le_bytes(x: u16) -> Seq<u8>
{
    seq![
        (x & 0xff) as u8, ((x >> 8) & 0xff) as u8,
    ]
}

pub open spec fn spec_u32_from_le_bytes(s: Seq<u8>) -> u32
    recommends
        s.len() == 4,
{
    (s[0] as u32) | ((s[1] as u32) << 8) | ((s[2] as u32) << 16) | ((s[3] as u32) << 24)
}

pub open spec fn spec_u32_to_le_bytes(x: u32) -> Seq<u8>
{
    seq![
        (x & 0xff) as u8, ((x >> 8) & 0xff) as u8, 
        ((x >> 16) & 0xff) as u8, ((x >> 24) & 0xff) as u8,
    ]
}

pub open spec fn spec_u64_from_le_bytes(s: Seq<u8>) -> u64
    recommends
        s.len() == 8,
{
    (s[0] as u64) | ((s[1] as u64) << 8) | ((s[2] as u64) << 16) | ((s[3] as u64) << 24)
    | ((s[4] as u64) << 32) | ((s[5] as u64) << 40) | ((s[6] as u64) << 48) | ((s[7] as u64) << 56)
}

pub use vstd::bytes::spec_u64_to_le_bytes_open as spec_u64_to_le_bytes;

pub open spec fn spec_u128_from_le_bytes(s: Seq<u8>) -> u128
    recommends
        s.len() == 16,
{
    (s[0] as u128) | ((s[1] as u128) << 8) | ((s[2] as u128) << 16) | ((s[3] as u128) << 24)
    | ((s[4] as u128) << 32) | ((s[5] as u128) << 40) | ((s[6] as u128) << 48) | ((s[7] as u128) << 56)
    | ((s[8] as u128) << 64) | ((s[9] as u128) << 72) | ((s[10] as u128) << 80) | ((s[11] as u128) << 88)
    | ((s[12] as u128) << 96) | ((s[13] as u128) << 104) | ((s[14] as u128) << 112) | ((s[15] as u128) << 120)
}

pub open spec fn spec_u128_to_le_bytes(x: u128) -> Seq<u8>
{
    seq![
        (x & 0xff) as u8, ((x >> 8) & 0xff) as u8, 
        ((x >> 16) & 0xff) as u8, ((x >> 24) & 0xff) as u8,
        ((x >> 32) & 0xff) as u8, ((x >> 40) & 0xff) as u8,
        ((x >> 48) & 0xff) as u8, ((x >> 56) & 0xff) as u8,
        ((x >> 64) & 0xff) as u8, ((x >> 72) & 0xff) as u8,
        ((x >> 80) & 0xff) as u8, ((x >> 88) & 0xff) as u8,
        ((x >> 96) & 0xff) as u8, ((x >> 104) & 0xff) as u8,
        ((x >> 112) & 0xff) as u8, ((x >> 120) & 0xff) as u8,
    ]
}

mod tests {
    use super::*;
    use verus_builtin::assert_by_compute;

    proof fn test_spec_u16_from_le_bytes() {
        assert_by_compute(
            spec_u16_from_le_bytes(seq![128u8, 127u8]) == 0x7f80u16
        );
    }

    proof fn test_spec_u16_to_le_bytes() {
        assert_by_compute(
            spec_u16_to_le_bytes(0x7f80u16) == seq![128u8, 127u8]
        );
    }

    proof fn test_spec_u32_from_le_bytes() {
        assert_by_compute(
            spec_u32_from_le_bytes(seq![128u8, 127u8, 255u8, 0u8]) == 0xff7f80u32
        );
    }

    proof fn test_spec_u32_to_le_bytes() {
        assert_by_compute(
            spec_u32_to_le_bytes(0xff7f80u32) == seq![128u8, 127u8, 255u8, 0u8]
        );
    }

    proof fn test_spec_u64_from_le_bytes() {
        assert_by_compute(
            spec_u64_from_le_bytes(seq![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8]) 
            == 0x0807060504030201u64
        );
    }

    proof fn test_spec_u64_to_le_bytes() {
        assert_by_compute(
            spec_u64_to_le_bytes(0x0807060504030201u64) 
            == seq![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8]
        );
    }

    proof fn test_spec_u128_from_le_bytes() {
        assert_by_compute(
            spec_u128_from_le_bytes(
                seq![
                    1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8,
                    9u8, 10u8, 11u8, 12u8, 13u8, 14u8, 15u8, 16u8
                ]
            ) 
            == 0x100f0e0d0c0b0a090807060504030201u128
        );
    }

    proof fn test_spec_u128_to_le_bytes() {
        assert_by_compute(
            spec_u128_to_le_bytes(0x100f0e0d0c0b0a090807060504030201u128) 
            == seq![
                1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8,
                9u8, 10u8, 11u8, 12u8, 13u8, 14u8, 15u8, 16u8
            ]
        );
    }
}

} // verus!