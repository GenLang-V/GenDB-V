//! An exact signed accumulator wider than `i128`: value `hi * 2^128 + lo` (`lo` unsigned). Additions of `i128`
//! values and of other accumulators are exact while the values stay below `2^253` in absolute value; the
//! conversion back to `i128` fails exactly when the value is outside `i128`.
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
pub struct Wide {
    pub lo: u128,
    pub hi: i128,
}

pub open spec fn two128() -> int {
    0x1_0000_0000_0000_0000int * 0x1_0000_0000_0000_0000int
}

/// The limit of the exact range (`2^253`).
pub open spec fn wide_limit() -> int {
    0x2000_0000_0000_0000_0000_0000_0000_0000int * two128()
}

/// The value of an accumulator.
pub open spec fn wval(w: Wide) -> int {
    w.hi as int * two128() + w.lo as int
}

/// In the exact range, `hi` is far from the `i64` limits.
proof fn lemma_hi_bound(w: Wide)
    requires -wide_limit() <= wval(w) <= wide_limit(),
    ensures -0x2000_0000_0000_0000_0000_0000_0000_0001 <= w.hi <= 0x2000_0000_0000_0000_0000_0000_0000_0000,
{
    let (h, l) = (w.hi as int, w.lo as int);
    assert(0 <= l < two128());
    if h > 0x2000_0000_0000_0000_0000_0000_0000_0000 {
        assert(h * two128() >= 0x2000_0000_0000_0000_0000_0000_0000_0001 * two128()) by (nonlinear_arith)
            requires h >= 0x2000_0000_0000_0000_0000_0000_0000_0001int, two128() > 0;
    }
    if h < -0x2000_0000_0000_0000_0000_0000_0000_0001 {
        assert(h * two128() <= -0x2000_0000_0000_0000_0000_0000_0000_0002 * two128()) by (nonlinear_arith)
            requires h <= -0x2000_0000_0000_0000_0000_0000_0000_0002int, two128() > 0;
    }
}

pub fn wide_zero() -> (w: Wide)
    ensures wval(w) == 0,
{
    Wide { lo: 0, hi: 0 }
}

/// `w + v`, exact.
pub fn wide_add_i128(w: Wide, v: i128) -> (r: Wide)
    requires -wide_limit() <= wval(w) <= wide_limit(),
    ensures wval(r) == wval(w) + v,
{
    proof {
        lemma_hi_bound(w);
    }
    if v >= 0 {
        let u = v as u128;
        if w.lo <= u128::MAX - u {
            Wide { lo: w.lo + u, hi: w.hi }
        } else {
            Wide { lo: w.lo - (u128::MAX - u) - 1, hi: w.hi + 1 }
        }
    } else {
        let u = ((-(v + 1)) as u128) + 1;
        assert(u as int == -(v as int));
        if w.lo >= u {
            Wide { lo: w.lo - u, hi: w.hi }
        } else {
            Wide { lo: w.lo + (u128::MAX - u) + 1, hi: w.hi - 1 }
        }
    }
}

/// `w + x`, exact.
pub fn wide_add(w: Wide, x: Wide) -> (r: Wide)
    requires
        -wide_limit() <= wval(w) <= wide_limit(),
        -wide_limit() <= wval(x) <= wide_limit(),
    ensures wval(r) == wval(w) + wval(x),
{
    proof {
        lemma_hi_bound(w);
        lemma_hi_bound(x);
    }
    let hi = w.hi + x.hi;
    if w.lo <= u128::MAX - x.lo {
        let r = Wide { lo: w.lo + x.lo, hi };
        proof {
            assert(wval(r) == (w.hi as int + x.hi as int) * two128() + w.lo as int + x.lo as int);
            assert((w.hi as int + x.hi as int) * two128() == w.hi as int * two128() + x.hi as int * two128()) by (nonlinear_arith);
        }
        r
    } else {
        let r = Wide { lo: w.lo - (u128::MAX - x.lo) - 1, hi: hi + 1 };
        proof {
            assert(wval(r) == (w.hi as int + x.hi as int + 1) * two128() + w.lo as int + x.lo as int - two128());
            assert((w.hi as int + x.hi as int + 1) * two128() == w.hi as int * two128() + x.hi as int * two128() + two128())
                by (nonlinear_arith);
        }
        r
    }
}

/// The value as an `i128`, or `None` exactly when it is outside `i128`.
pub fn wide_to_i128(w: Wide) -> (r: Option<i128>)
    ensures
        match r {
            Some(x) => x as int == wval(w),
            None => wval(w) < i128::MIN || wval(w) > i128::MAX,
        },
{
    let half: u128 = 0x8000_0000_0000_0000_0000_0000_0000_0000u128;
    if w.hi == 0 && w.lo < half {
        Some(w.lo as i128)
    } else if w.hi == -1 && w.lo >= half {
        let m = w.lo - half;
        let r = (m as i128) - 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffi128 - 1;
        Some(r)
    } else {
        proof {
            let (h, l) = (w.hi as int, w.lo as int);
            if h >= 1 {
                assert(h * two128() >= two128()) by (nonlinear_arith) requires h >= 1, two128() > 0;
            } else if h <= -2 {
                assert(h * two128() <= -2 * two128()) by (nonlinear_arith) requires h <= -2, two128() > 0;
            }
        }
        None
    }
}

} // verus!
