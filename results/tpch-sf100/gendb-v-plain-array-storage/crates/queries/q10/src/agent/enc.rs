//! A non-negative sum with its count in one `i64`: `0` when the count is 0, else `sum + 1` (`enc`). The values are
//! kept at most `CAP` (2^61), so the sum of two of them fits `i64`; `enc_combine` adds two encoded pairs and
//! refuses (`None`) a result beyond `CAP`. Used for the per-order and per-customer revenue accumulators: every value
//! the fast path adds is checked non-negative, and a zero count with a zero sum is "no group".
use vstd::prelude::*;

verus! {

/// Bound of the encoded values.
pub const CAP: i64 = 0x2000_0000_0000_0000;

/// The encoding of a sum `s` with count `c`.
pub open spec fn enc(s: int, c: int) -> int { if c == 0 { 0 } else { s + 1 } }

/// `e` encodes the non-negative sum `s` with count `c` (a zero count has a zero sum), within `CAP`.
pub open spec fn enc_ok(e: i64, s: int, c: int) -> bool {
    &&& 0 <= s && 0 <= c
    &&& c == 0 ==> s == 0
    &&& e as int == enc(s, c)
    &&& e <= CAP
}

/// The sum an encoded value stands for.
pub open spec fn dec(e: i64) -> int { if e == 0 { 0 } else { e - 1 } }

pub proof fn lemma_enc_dec(e: i64, s: int, c: int)
    requires enc_ok(e, s, c),
    ensures dec(e) == s, (e != 0) == (c > 0), e >= 0,
{
}

/// The empty pair.
pub proof fn lemma_enc_zero()
    ensures enc_ok(0, 0, 0),
{
}

/// Adds two encoded pairs; `None` when the sum leaves `CAP`.
pub fn enc_combine(e1: i64, e2: i64, Ghost(s1): Ghost<int>, Ghost(c1): Ghost<int>, Ghost(s2): Ghost<int>, Ghost(c2): Ghost<int>)
    -> (r: Option<i64>)
    requires enc_ok(e1, s1, c1), enc_ok(e2, s2, c2),
    ensures r matches Some(e) ==> enc_ok(e, s1 + s2, c1 + c2),
    no_unwind
{
    if e1 == 0 {
        Some(e2)
    } else if e2 == 0 {
        Some(e1)
    } else {
        let x = e1 + e2 - 1;
        if x <= CAP { Some(x) } else { None }
    }
}

/// Encodes a run's sum `s` (with or without a counted row); `None` when it leaves `CAP`.
pub fn enc_run(s: i64, any: bool, Ghost(c): Ghost<int>) -> (r: Option<i64>)
    requires 0 <= s, 0 <= c, any == (c > 0), c == 0 ==> s == 0,
    ensures r matches Some(e) ==> enc_ok(e, s as int, c),
    no_unwind
{
    if !any {
        Some(0)
    } else if s < CAP {
        Some(s + 1)
    } else {
        None
    }
}

} // verus!
