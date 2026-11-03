//! Customer partitions of the fast path. Partition `pp` holds the customer rows `[plo(pp), plo(pp + 1))`: `PW`
//! rows each (the last one shorter, later ones empty), so one partition's accumulators (`PW` x 9 bytes) stay in a
//! core's L2 cache. A phase-1 task writes its records partitioned into one flat buffer with `cap` slots per
//! partition: the records of partition `pp` are the first `cnt[pp]` entries of segment `seg(.., pp, cap)`, and every
//! one names a customer of the partition (`precs_ok`). A record is packed into one `u64` (`pack`): the customer row
//! in the high 24 bits, the revenue plus `RB` in the low 40 bits; `rcv`/`rrv` are the customer and revenue views of a
//! packed buffer, which the record specifications are stated over.
use vstd::prelude::*;
use crate::spec::numeric::abs;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::kernel::dsum;
use super::recs::*;
use super::phase1::{lemma_labs_lsum, lemma_lcnt_zero};

verus! {

/// Customer rows per partition.
pub const PW: usize = 65536;
/// Most partitions of the fast path (`MAX_NP * PW` customer rows).
pub const MAX_NP: usize = 4096;

/// Customer rows addressable in a packed record (24 bits).
pub const MAX_CUST: u64 = 0x100_0000;
/// Scale of the customer row in a packed record (2^40).
pub const PK: u64 = 0x100_0000_0000;
/// Offset of the revenue in a packed record (2^39): revenues in `[-RB, RB)`.
pub const RB: i64 = 0x80_0000_0000;

/// The customer rows of a packed record buffer.
pub open spec fn rcv(rp: Seq<u64>) -> Seq<u32> {
    Seq::new(rp.len(), |i: int| (rp[i] as int / PK as int) as u32)
}

/// The revenues of a packed record buffer.
pub open spec fn rrv(rp: Seq<u64>) -> Seq<i64> {
    Seq::new(rp.len(), |i: int| (rp[i] as int % PK as int - RB) as i64)
}

/// The record of customer row `c` with revenue `r`.
#[inline(always)]
pub fn pack(c: u64, r: i64) -> (x: u64)
    requires c < MAX_CUST, -RB <= r < RB,
    ensures x as int / PK as int == c, x as int % PK as int - RB == r,
    no_unwind
{
    let lo: u64 = (r + RB) as u64;
    proof {
        assert(c * PK + lo < 0x1_0000_0000_0000_0000) by (nonlinear_arith)
            requires c < MAX_CUST, lo < PK;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse((c * PK + lo) as int, PK as int, c as int, lo as int);
    }
    c * PK + lo
}

/// The customer row and revenue of a record.
#[inline(always)]
pub fn unpack(x: u64) -> (r: (usize, i64))
    ensures r.0 as int == (x as int) / (PK as int), r.0 < MAX_CUST, r.1 as int == (x as int) % (PK as int) - RB,
    no_unwind
{
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, PK as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, PK as int);
        assert((x as int) / (PK as int) < (MAX_CUST as int)) by (nonlinear_arith)
            requires x < 0x1_0000_0000_0000_0000, PK * (x as int / PK as int) + x as int % PK as int == x,
                x as int % PK as int >= 0;
    }
    ((x / PK) as usize, (x % PK) as i64 - RB)
}

/// Writing a packed record updates both views at its slot.
pub proof fn lemma_pack_update(rp: Seq<u64>, at: int, x: u64, c: int, r: int)
    requires
        0 <= at < rp.len(),
        x as int / PK as int == c, x as int % PK as int - RB == r,
        0 <= c < MAX_CUST, -RB <= r < RB,
    ensures
        rcv(rp.update(at, x)) == rcv(rp).update(at, c as u32),
        rrv(rp.update(at, x)) == rrv(rp).update(at, r as i64),
{
    assert(rcv(rp.update(at, x)) =~= rcv(rp).update(at, c as u32));
    assert(rrv(rp.update(at, x)) =~= rrv(rp).update(at, r as i64));
}

/// First customer row of partition `pp` (clamped to the table).
pub open spec fn plo(m: M, pp: int) -> int {
    if pp * PW < m.c_n { pp * PW } else { m.c_n }
}

/// Segment `pp` (`cap` slots) of a flat partitioned buffer.
pub open spec fn seg<T>(s: Seq<T>, pp: int, cap: int) -> Seq<T> {
    s.subrange(pp * cap, pp * cap + cap)
}

/// The records `(rc, rr)[0, n)` of the orders `[lo, hi)` whose customers lie in `[clo, chi)`: every record names a
/// customer of the range, the records of each such customer sum to its revenue over the orders, and the absolute
/// values are bounded by `mass`.
pub open spec fn precs_ok(m: M, p: QP, rc: Seq<u32>, rr: Seq<i64>, n: int, lo: int, hi: int, mass: int, clo: int, chi: int) -> bool {
    &&& 0 <= n <= rc.len() && n <= rr.len()
    &&& forall|i: int| 0 <= i < n ==> clo <= #[trigger] rc[i] < chi
    &&& forall|c: int| clo <= c < chi ==> {
        &&& #[trigger] rsum(rc, rr, n, c) == dsum(csum_f(m, p, c), lo, hi)
        &&& rcnt(rc, n, c) == dsum(chit_f(m, p, c), lo, hi)
        &&& dsum(cabs_f(m, p, c), lo, hi) <= mass
    }
    &&& rabs(rr, n) <= mass
}

/// Partition `pp` of a task's flat buffers.
pub open spec fn part_ok(m: M, p: QP, rc: Seq<u32>, rr: Seq<i64>, cnt: Seq<usize>, cap: int, pp: int, lo: int, hi: int, mass: int) -> bool {
    precs_ok(m, p, seg(rc, pp, cap), seg(rr, pp, cap), cnt[pp] as int, lo, hi, mass, plo(m, pp), plo(m, pp + 1))
}

/// Every partition `[0, np)` of a task's flat buffers.
pub open spec fn parts_ok(m: M, p: QP, rc: Seq<u32>, rr: Seq<i64>, cnt: Seq<usize>, cap: int, np: int, lo: int, hi: int, mass: int) -> bool {
    &&& cap >= 0 && np >= 0
    &&& rc.len() >= np * cap && rr.len() >= np * cap && cnt.len() >= np
    &&& forall|pp: int| 0 <= pp < np ==> #[trigger] part_ok(m, p, rc, rr, cnt, cap, pp, lo, hi, mass)
}

// ------------------------------------------------------------------------------------------------ arithmetic

/// Partition bounds are nondecreasing; with `np * PW >= c_n` the last one is the table end.
pub proof fn lemma_plo_mono(m: M, a: int, b: int)
    requires 0 <= a <= b, m.c_n >= 0,
    ensures 0 <= plo(m, a) <= plo(m, b) <= m.c_n,
{
    assert(a * PW <= b * PW) by (nonlinear_arith) requires a <= b;
    assert(a * PW >= 0) by (nonlinear_arith) requires a >= 0;
}

/// Customer row `c` lies in partition `c / PW`.
pub proof fn lemma_part_of(m: M, c: int, np: int)
    requires 0 <= c < m.c_n, np * PW >= m.c_n,
    ensures
        0 <= c / (PW as int) < np,
        plo(m, c / (PW as int)) <= c < plo(m, c / (PW as int) + 1),
{
    let pp = c / (PW as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c, PW as int);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(c, PW as int);
    assert(pp * PW <= c) by (nonlinear_arith) requires PW * pp + c % (PW as int) == c, c % (PW as int) >= 0;
    assert(c < (pp + 1) * PW) by (nonlinear_arith) requires PW * pp + c % (PW as int) == c, c % (PW as int) < PW;
    assert(pp >= 0) by (nonlinear_arith) requires c >= 0, pp == c / (PW as int);
    assert(pp < np) by (nonlinear_arith) requires pp * PW <= c, np * PW >= m.c_n, c < m.c_n;
}

/// Customers of distinct partitions are distinct.
pub proof fn lemma_part_disjoint(m: M, a: int, b: int, c: int, d: int)
    requires 0 <= a, 0 <= b, a != b, plo(m, a) <= c < plo(m, a + 1), plo(m, b) <= d < plo(m, b + 1), m.c_n >= 0,
    ensures c != d,
{
    if a < b {
        lemma_plo_mono(m, a + 1, b);
    } else {
        lemma_plo_mono(m, b + 1, a);
    }
}

/// Segments of distinct partitions occupy disjoint slots.
pub proof fn lemma_seg_slots(pp: int, qq: int, cap: int, np: int)
    requires 0 <= pp < np, 0 <= qq < np, cap >= 0,
    ensures
        0 <= pp * cap,
        pp * cap + cap <= np * cap,
        pp < qq ==> pp * cap + cap <= qq * cap,
        qq < pp ==> qq * cap + cap <= pp * cap,
{
    assert(0 <= pp * cap) by (nonlinear_arith) requires pp >= 0, cap >= 0;
    assert(pp * cap + cap <= np * cap) by (nonlinear_arith) requires pp + 1 <= np, cap >= 0;
    if pp < qq {
        assert(pp * cap + cap <= qq * cap) by (nonlinear_arith) requires pp + 1 <= qq, cap >= 0;
    }
    if qq < pp {
        assert(qq * cap + cap <= pp * cap) by (nonlinear_arith) requires qq + 1 <= pp, cap >= 0;
    }
}

// ------------------------------------------------------------------------------------------------ records

/// No record and no order counted for the range: the empty records of an empty order range.
pub proof fn lemma_precs_empty(m: M, p: QP, rc: Seq<u32>, rr: Seq<i64>, lo: int, clo: int, chi: int)
    ensures precs_ok(m, p, rc, rr, 0, lo, lo, 0, clo, chi),
{
    assert(rabs(rr, 0) == 0);
    assert forall|c: int| clo <= c < chi implies {
        &&& #[trigger] rsum(rc, rr, 0, c) == dsum(csum_f(m, p, c), lo, lo)
        &&& rcnt(rc, 0, c) == dsum(chit_f(m, p, c), lo, lo)
        &&& dsum(cabs_f(m, p, c), lo, lo) <= 0
    } by {}
}

/// The order at `q` counts for no customer of the range: the records stay, the mass may grow.
pub proof fn lemma_precs_skip(m: M, p: QP, rc: Seq<u32>, rr: Seq<i64>, n: int, lo: int, q: int, mass: int, mass2: int,
    clo: int, chi: int)
    requires
        model_ok(m),
        0 <= lo <= q < m.o_n,
        precs_ok(m, p, rc, rr, n, lo, q, mass, clo, chi),
        mass <= mass2,
        forall|c: int| clo <= c < chi ==> !(#[trigger] ohit(m, p, c, q)) || lcnt(m, q) <= 0,
    ensures precs_ok(m, p, rc, rr, n, lo, q + 1, mass2, clo, chi),
{
    assert forall|c: int| clo <= c < chi implies {
        &&& #[trigger] rsum(rc, rr, n, c) == dsum(csum_f(m, p, c), lo, q + 1)
        &&& rcnt(rc, n, c) == dsum(chit_f(m, p, c), lo, q + 1)
        &&& dsum(cabs_f(m, p, c), lo, q + 1) <= mass2
    } by {
        lemma_dsum_step(csum_f(m, p, c), lo, q);
        lemma_dsum_step(chit_f(m, p, c), lo, q);
        lemma_dsum_step(cabs_f(m, p, c), lo, q);
        assert(rsum(rc, rr, n, c) == dsum(csum_f(m, p, c), lo, q));
        if ohit(m, p, c, q) {
            lemma_lcnt_zero(m, q);
        }
    }
}

/// The order at `q` of customer `cp` (in the range) with a returned lineitem is appended as record `n`.
pub proof fn lemma_precs_add(m: M, p: QP, rc: Seq<u32>, rr: Seq<i64>, rc2: Seq<u32>, rr2: Seq<i64>, n: int, lo: int, q: int,
    mass: int, clo: int, chi: int, cp: int, rev: int, ab: int)
    requires
        model_ok(m),
        0 <= lo <= q < m.o_n,
        precs_ok(m, p, rc, rr, n, lo, q, mass, clo, chi),
        n < rc.len(), n < rr.len(),
        rc2.len() == rc.len(), rr2.len() == rr.len(),
        forall|i: int| 0 <= i < n ==> rc2[i] == rc[i] && rr2[i] == rr[i],
        rc2[n] as int == cp, rr2[n] as int == rev,
        clo <= cp < chi,
        0 <= clo, chi <= m.c_n,
        ohit(m, p, cp, q),
        lcnt(m, q) > 0,
        rev == lsum(m, q), ab == labs(m, q),
    ensures precs_ok(m, p, rc2, rr2, n + 1, lo, q + 1, mass + ab, clo, chi),
{
    lemma_labs_lsum(m, q);
    lemma_rec_ext(rc, rr, rc2, rr2, n, 0);
    lemma_rec_step(rc2, rr2, n, 0);
    assert forall|i: int| 0 <= i < n + 1 implies clo <= #[trigger] rc2[i] < chi by {
        if i < n {
            assert(rc2[i] == rc[i]);
        }
    }
    assert forall|c: int| clo <= c < chi implies {
        &&& #[trigger] rsum(rc2, rr2, n + 1, c) == dsum(csum_f(m, p, c), lo, q + 1)
        &&& rcnt(rc2, n + 1, c) == dsum(chit_f(m, p, c), lo, q + 1)
        &&& dsum(cabs_f(m, p, c), lo, q + 1) <= mass + ab
    } by {
        lemma_rec_ext(rc, rr, rc2, rr2, n, c);
        lemma_rec_step(rc2, rr2, n, c);
        lemma_dsum_step(csum_f(m, p, c), lo, q);
        lemma_dsum_step(chit_f(m, p, c), lo, q);
        lemma_dsum_step(cabs_f(m, p, c), lo, q);
        assert(rsum(rc, rr, n, c) == dsum(csum_f(m, p, c), lo, q));
        if c != cp {
            // under the customer primary key, the order names only customer row cp
            assert(ckey(m, c) != ckey(m, cp));
            assert(!ohit(m, p, c, q));
        }
    }
}

} // verus!
