//! Block (row group) of a row under uniform groups of `bs` rows: `i / bs`, computed as a shift when `bs` is a power
//! of two (`Div`: the divisor with its shift, found once by `div_of`).
use vstd::prelude::*;
use vstd::arithmetic::power2::{pow2, lemma_pow2_pos};

verus! {

/// A positive divisor `bs`, with `sh` such that `bs == 2^sh` when `pw2`.
#[derive(Clone, Copy)]
pub struct Div {
    pub bs: u64,
    pub sh: u64,
    pub pw2: bool,
}

pub open spec fn div_ok(d: Div, bs: int) -> bool {
    &&& d.bs as int == bs
    &&& bs >= 1
    &&& d.pw2 ==> d.sh < 64 && pow2(d.sh as nat) == bs
}

/// The divisor `bs` (at least 1) with its shift when it is a power of two.
pub fn div_of(bs: u64) -> (d: Div)
    requires bs >= 1,
    ensures div_ok(d, bs as int),
{
    let mut sh: u64 = 0;
    let mut p: u64 = 1;
    proof { vstd::arithmetic::power2::lemma2_to64(); }
    while sh < 63 && p < bs
        invariant
            sh <= 63,
            p as nat == pow2(sh as nat),
            bs >= 1,
        decreases 63 - sh,
    {
        proof {
            vstd::arithmetic::power2::lemma_pow2_unfold((sh + 1) as nat);
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(sh as nat, 63);
            vstd::arithmetic::power2::lemma2_to64();
            vstd::arithmetic::power2::lemma2_to64_rest();
        }
        p = p * 2;
        sh = sh + 1;
    }
    Div { bs, sh, pw2: p == bs }
}

/// `i / bs`.
pub fn grp(i: usize, d: Div) -> (g: usize)
    requires d.bs >= 1, d.pw2 ==> d.sh < 64 && pow2(d.sh as nat) == d.bs as int,
    ensures g as int == i as int / d.bs as int,
    no_unwind
{
    if d.pw2 {
        proof {
            vstd::bits::lemma_u64_shr_is_div(i as u64, d.sh);
        }
        ((i as u64) >> d.sh) as usize
    } else {
        ((i as u64) / d.bs) as usize
    }
}

} // verus!
