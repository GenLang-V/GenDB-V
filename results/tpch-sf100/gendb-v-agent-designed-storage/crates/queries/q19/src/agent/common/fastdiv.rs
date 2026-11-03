//! Division by a runtime divisor fixed for many calls (for example rows per group): a right shift when the divisor
//! is a power of two, else the division. `Divisor::new` finds the shift once; `Divisor::div` is exact (`x / d`).
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;
use vstd::bits::{lemma_u64_shr_is_div, lemma_u64_shl_is_mul, lemma_u64_pow2_no_overflow};

verus! {

/// A divisor `d >= 1` with its shift: when `pw`, `d == 2^sh`.
#[derive(Clone, Copy)]
pub struct Divisor {
    pub d: u64,
    pub sh: u64,
    pub pw: bool,
}

/// `v` divides by `d`.
pub open spec fn divisor_ok(v: Divisor, d: int) -> bool {
    &&& v.d == d
    &&& d >= 1
    &&& v.pw ==> v.sh < 64 && pow2(v.sh as nat) == d
}

impl Divisor {
    /// The divisor `d` and, when `d` is a power of two, its shift.
    pub fn new(d: u64) -> (r: Divisor)
        requires d >= 1,
        ensures divisor_ok(r, d as int),
    {
        let mut sh: u64 = 0;
        while sh < 64
            invariant sh <= 64,
            decreases 64 - sh,
        {
            proof {
                lemma_u64_pow2_no_overflow(sh as nat);
                lemma_u64_shl_is_mul(1, sh);
            }
            if (1u64 << sh) == d {
                return Divisor { d, sh, pw: true };
            }
            sh = sh + 1;
        }
        Divisor { d, sh: 0, pw: false }
    }

    /// `x / d`.
    #[inline(always)]
    pub fn div(&self, x: u64) -> (q: u64)
        requires divisor_ok(*self, self.d as int),
        ensures q == x / self.d,
        no_unwind
    {
        if self.pw {
            proof {
                lemma_u64_shr_is_div(x, self.sh);
            }
            x >> self.sh
        } else {
            x / self.d
        }
    }
}

} // verus!
