//! Phase B of the partitioned plan (`round::fast_counts`): per partition of 64 local groups, every group's number of
//! distinct supplier rows that the subquery does not exclude, over every phase-A output (`sel::SelOut`).
//!
//! A task handles the partitions `[q0, q1)`. Per partition `q` it gathers the entries of region `q` of every output
//! into scratch (`ents`; `gath`), sorts them by slot into `loc` (`common::scatter::scatter_hi`: an entry's high bits
//! `v >> 20` are its slot), and counts each slot's segment by supplier row, the low bits `v & (2^20 - 1)`
//! (`common::segcount::count_seg`). The scratch is sized by the caller; a partition that does not fit stops the task
//! (`ok == false`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use super::sel::*;
use super::common::marks::*;
use super::common::scatter::*;
use super::common::segcount::*;

verus! {

/// Mask of an entry's supplier row.
pub const XMASK: u32 = 0xF_FFFF;

/// The gathered entries below `n` hold the entry of slot `h` and supplier row `x`.
pub open spec fn ghas(ents: Seq<u32>, n: int, h: int, x: int) -> bool {
    &&& 0 <= x < 0x10_0000
    &&& exists|k: int| 0 <= k < n && #[trigger] ents[k] as int == enc(h, x)
}

/// High bits are the slot, low bits the supplier row.
proof fn lemma_bits20(v: u32)
    by (bit_vector)
    ensures v >> 20u32 == v / 0x10_0000u32, v & 0xF_FFFFu32 == v % 0x10_0000u32,
{
}

/// Some output's region of local group `g` holds supplier row `x`.
pub open spec fn in_any(outs: Seq<SelOut>, g: int, x: int) -> bool {
    exists|t: int| 0 <= t < outs.len() && #[trigger] reg_has(outs[t], g, x)
}

/// The distinct supplier rows of local group `g` that the subquery does not exclude.
pub open spec fn dset2(outs: Seq<SelOut>, excl: Seq<u64>, sn: int, g: int) -> Set<int> {
    Set::range(0, sn).filter(|x: int| in_any(outs, g, x) && !bit_at(excl, x))
}

/// Every output has valid regions for `np` partitions and supplier rows below `sn`.
pub open spec fn outs_shape(outs: Seq<SelOut>, np: int, sn: int) -> bool {
    forall|t: int| 0 <= t < outs.len() ==> #[trigger] regs_ok(outs[t].start@, outs[t].cur@, outs[t].out@, np, sn)
}

/// Region `q` of output `o` holds the entry of slot `h` and supplier row `x`.
pub open spec fn rq_has(o: SelOut, q: int, h: int, x: int) -> bool {
    &&& 0 <= x < 0x10_0000
    &&& exists|k: int| o.start@[q] <= k < o.cur@[q] && #[trigger] o.out@[k] as int == enc(h, x)
}

/// Gathered: regions `q` of the outputs below `t`, and positions below `k` of output `t`'s region `q`.
pub open spec fn gath(outs: Seq<SelOut>, q: int, t: int, k: int, h: int, x: int) -> bool {
    ||| exists|t2: int| 0 <= t2 < t && #[trigger] rq_has(outs[t2], q, h, x)
    ||| (0 <= t < outs.len() && 0 <= x < 0x10_0000
        && exists|k2: int| outs[t].start@[q] <= k2 < k && #[trigger] outs[t].out@[k2] as int == enc(h, x))
}

pub struct GrpTask {
    pub outs: Arc<Vec<SelOut>>,
    pub excl: Arc<Vec<u64>>,
    pub sn: usize,
    pub np: usize,
    pub q0: usize,
    pub q1: usize,
    /// Scratch of equal lengths: the gathered entries, and the entries sorted by slot.
    pub ents: Vec<u32>,
    pub loc: Vec<u32>,
    /// Scratch: 65 slot offsets.
    pub offs: Vec<usize>,
    /// Scratch: an empty bitmap of supplier rows.
    pub marks: Vec<u64>,
    /// Output: one count per local group of the partitions (`64 * (q1 - q0)` entries).
    pub counts: Vec<u64>,
}

pub struct GrpOut {
    pub counts: Vec<u64>,
    /// False when a partition did not fit the scratch.
    pub ok: bool,
}

/// The decoding of a packed entry is its slot and supplier row.
proof fn lemma_dec(v: int, h: int, x: int)
    requires 0 <= v,
    ensures (v / 0x10_0000 == h && v % 0x10_0000 == x) <==> (0 <= x < 0x10_0000 && v == enc(h, x)),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v, 0x10_0000);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(v, 0x10_0000);
    if 0 <= x < 0x10_0000 && v == enc(h, x) {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(v, 0x10_0000, h, x);
    }
}

/// Group `64 q + h` is slot `h` of partition `q`.
proof fn lemma_rq(o: SelOut, q: int, h: int, x: int)
    requires 0 <= q, 0 <= h < 64,
    ensures reg_has(o, 64 * q + h, x) == rq_has(o, q, h, x),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(64 * q + h, 64, q, h);
}

/// Every entry of slot `h`'s sorted segment is a gathered entry, so its supplier row is below `sn`.
proof fn lemma_sel_bound(ents: Seq<u32>, n: int, h: int, sn: int)
    requires 0 <= n <= ents.len(), forall|k: int| 0 <= k < n ==> mval(#[trigger] ents[k], XMASK) < sn,
    ensures
        forall|w: int| 0 <= w < sel(hi_keys(ents, 20), ents, n, h).len()
            ==> mval(#[trigger] sel(hi_keys(ents, 20), ents, n, h)[w], XMASK) < sn,
{
    let ks = hi_keys(ents, 20);
    let sq = sel(ks, ents, n, h);
    assert forall|w: int| 0 <= w < sq.len() implies mval(#[trigger] sq[w], XMASK) < sn by {
        let e = sq[w];
        assert(sq.contains(e));
        lemma_sel_mem(ks, ents, n, h, e);
        let k = choose|k: int| 0 <= k < n && ks[k].ix() == h && #[trigger] ents[k] == e;
        assert(mval(ents[k], XMASK) < sn);
    }
}

/// After output `t`'s whole region, output `t + 1`'s region starts.
proof fn lemma_gath_next(outs: Seq<SelOut>, q: int, t: int, b: int, h: int, x: int)
    requires 0 <= t < outs.len(), b == outs[t].cur@[q],
    ensures gath(outs, q, t + 1, if t + 1 < outs.len() { outs[t + 1].start@[q] as int } else { 0 }, h, x) == gath(outs, q, t, b, h, x),
{
    let lhs = gath(outs, q, t + 1, if t + 1 < outs.len() { outs[t + 1].start@[q] as int } else { 0 }, h, x);
    let rhs = gath(outs, q, t, b, h, x);
    if lhs {
        if exists|t2: int| 0 <= t2 < t + 1 && #[trigger] rq_has(outs[t2], q, h, x) {
            let t2 = choose|t2: int| 0 <= t2 < t + 1 && #[trigger] rq_has(outs[t2], q, h, x);
            if t2 == t {
                let k = choose|k: int| outs[t].start@[q] <= k < outs[t].cur@[q] && #[trigger] outs[t].out@[k] as int == enc(h, x);
                assert(rhs);
            }
        }
    }
    if rhs {
        if 0 <= x < 0x10_0000 && exists|k2: int| outs[t].start@[q] <= k2 < b && #[trigger] outs[t].out@[k2] as int == enc(h, x) {
            let k2 = choose|k2: int| outs[t].start@[q] <= k2 < b && #[trigger] outs[t].out@[k2] as int == enc(h, x);
            assert(rq_has(outs[t], q, h, x));
        }
    }
}

/// Gathering position `k` of output `t`: the scratch adds its entry.
proof fn lemma_gath_push(outs: Seq<SelOut>, q: int, t: int, k: int, e0: Seq<u32>, es: Seq<u32>, n: int)
    requires
        0 <= t < outs.len(),
        outs[t].start@[q] <= k,
        0 <= n < e0.len(), e0.len() == es.len(),
        es == e0.update(n, outs[t].out@[k]),
        forall|h: int, x: int| #[trigger] ghas(e0, n, h, x) <==> gath(outs, q, t, k, h, x),
    ensures
        forall|h: int, x: int| #[trigger] ghas(es, n + 1, h, x) <==> gath(outs, q, t, k + 1, h, x),
{
    assert forall|h: int, x: int| #[trigger] ghas(es, n + 1, h, x) <==> gath(outs, q, t, k + 1, h, x) by {
        if ghas(es, n + 1, h, x) {
            let k2 = choose|k2: int| 0 <= k2 < n + 1 && #[trigger] es[k2] as int == enc(h, x);
            if k2 < n {
                assert(e0[k2] == es[k2]);
                assert(ghas(e0, n, h, x));
                if !(exists|t2: int| 0 <= t2 < t && #[trigger] rq_has(outs[t2], q, h, x)) {
                    let k3 = choose|k3: int| outs[t].start@[q] <= k3 < k && #[trigger] outs[t].out@[k3] as int == enc(h, x);
                    assert(outs[t].start@[q] <= k3 < k + 1);
                }
            } else {
                assert(outs[t].out@[k] as int == enc(h, x));
            }
        }
        if gath(outs, q, t, k + 1, h, x) {
            if gath(outs, q, t, k, h, x) {
                assert(ghas(e0, n, h, x));
                let k2 = choose|k2: int| 0 <= k2 < n && #[trigger] e0[k2] as int == enc(h, x);
                assert(es[k2] == e0[k2]);
                assert(es[k2] as int == enc(h, x));
            } else {
                let k3 = choose|k3: int| outs[t].start@[q] <= k3 < k + 1 && #[trigger] outs[t].out@[k3] as int == enc(h, x);
                assert(k3 == k);
                assert(es[n] as int == enc(h, x));
            }
        }
    }
}

/// The counted segment of slot `h` is the distinct set of local group `64 q + h`.
proof fn lemma_slot_set(outs: Seq<SelOut>, excl: Seq<u64>, sn: int, q: int, h: int, ents: Seq<u32>, n: int,
    offs: Seq<usize>, loc: Seq<u32>)
    requires
        0 <= q, 0 <= h < 64,
        0 <= n <= ents.len(),
        scattered(hi_keys(ents, 20), ents, n, 64, offs, loc),
        0 <= offs[h] <= offs[h + 1] <= loc.len(),
        forall|h2: int, x: int| #[trigger] ghas(ents, n, h2, x) <==> gath(outs, q, outs.len() as int, 0, h2, x),
    ensures
        kept(loc, offs[h] as int, offs[h + 1] as int, XMASK, excl, sn) == dset2(outs, excl, sn, 64 * q + h),
{
    let a = offs[h] as int;
    let b = offs[h + 1] as int;
    let ks = hi_keys(ents, 20);
    let sq = sel(ks, ents, n, h);
    assert(loc.subrange(a, b) == sq);
    let k1 = kept(loc, a, b, XMASK, excl, sn);
    let k2 = dset2(outs, excl, sn, 64 * q + h);
    assert forall|x: int| #[trigger] k1.contains(x) == k2.contains(x) by {
        // A position of the segment holds x <==> a gathered entry of slot h holds x.
        if has_val(loc, a, b, XMASK, x) {
            let p = choose|p: int| a <= p < b && #[trigger] mval(loc[p], XMASK) == x;
            let e = loc[p];
            assert(sq[p - a] == e);
            assert(sq.contains(e));
            lemma_sel_mem(ks, ents, n, h, e);
            let k = choose|k: int| 0 <= k < n && ks[k].ix() == h && #[trigger] ents[k] == e;
            lemma_bits20(e);
            assert(ks[k] == (ents[k] >> 20u32) as usize);
            lemma_dec(e as int, h, x);
            assert(ghas(ents, n, h, x));
        }
        if ghas(ents, n, h, x) {
            let k = choose|k: int| 0 <= k < n && #[trigger] ents[k] as int == enc(h, x);
            let e = ents[k];
            lemma_dec(e as int, h, x);
            lemma_bits20(e);
            assert(ks[k] == (ents[k] >> 20u32) as usize);
            lemma_sel_mem(ks, ents, n, h, e);
            assert(sq.contains(e));
            let w = choose|w: int| 0 <= w < sq.len() && sq[w] == e;
            assert(loc[a + w] == e);
            assert(a <= a + w < b);
            assert(mval(loc[a + w], XMASK) == x);
            assert(has_val(loc, a, b, XMASK, x));
        }
        if in_any(outs, 64 * q + h, x) {
            let t = choose|t: int| 0 <= t < outs.len() && #[trigger] reg_has(outs[t], 64 * q + h, x);
            lemma_rq(outs[t], q, h, x);
            assert(gath(outs, q, outs.len() as int, 0, h, x));
        }
        if gath(outs, q, outs.len() as int, 0, h, x) {
            let t = choose|t: int| 0 <= t < outs.len() && #[trigger] rq_has(outs[t], q, h, x);
            lemma_rq(outs[t], q, h, x);
            assert(in_any(outs, 64 * q + h, x));
        }
    }
    assert(k1 =~= k2);
}

/// What a task needs: valid outputs, the exclusion bitmap and an empty scratch bitmap over `sn` rows, partitions below
/// `np`, scratch of equal lengths, 65 offsets and one count per local group.
pub open spec fn grp_pre(t: GrpTask) -> bool {
    &&& outs_shape(t.outs@, t.np as int, t.sn as int)
    &&& t.sn <= 64 * t.excl@.len()
    &&& t.sn <= 64 * t.marks@.len()
    &&& holds(t.marks@, Set::empty())
    &&& t.q0 <= t.q1 <= t.np
    &&& t.np < 0x10_0000
    &&& t.loc@.len() == t.ents@.len()
    &&& t.offs@.len() == 65
    &&& t.counts@.len() == 64 * (t.q1 - t.q0)
}

impl WorkerTask for GrpTask {
    type Output = GrpOut;

    open spec fn pre(&self) -> bool {
        grp_pre(*self)
    }

    open spec fn post(&self, out: GrpOut) -> bool {
        out.ok ==> {
            &&& out.counts@.len() == 64 * (self.q1 - self.q0)
            &&& forall|g: int| 64 * self.q0 <= g < 64 * self.q1 ==>
                #[trigger] dset2(self.outs@, self.excl@, self.sn as int, g).len() == out.counts@[g - 64 * self.q0] as int
        }
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.q0 as u64, self.q1 as u64)
    }

    fn run(self) -> (out: GrpOut) {
        let GrpTask { outs, excl, sn, np, q0, q1, ents, loc, offs, marks, counts } = self;
        let mut ents = ents;
        let mut loc = loc;
        let mut offs = offs;
        let mut marks = marks;
        let mut counts = counts;
        let os: &Vec<SelOut> = &*outs;
        let ex: &Vec<u64> = &*excl;
        let nprod = os.len();
        let cap = ents.len();
        let mut q = q0;
        while q < q1
            invariant
                os@ == self.outs@, ex@ == self.excl@, sn == self.sn, np == self.np, q0 == self.q0, q1 == self.q1,
                nprod == os@.len(),
                np < 0x10_0000,
                outs_shape(os@, np as int, sn as int),
                sn <= 64 * ex@.len(),
                sn <= 64 * marks@.len(),
                holds(marks@, Set::empty()),
                q0 <= q <= q1 <= np,
                cap == ents@.len(), cap == loc@.len(),
                offs@.len() == 65,
                counts@.len() == 64 * (q1 - q0),
                forall|g: int| 64 * q0 <= g < 64 * q ==>
                    #[trigger] dset2(os@, ex@, sn as int, g).len() == counts@[g - 64 * q0] as int,
            decreases q1 - q,
        {
            // Gather region `q` of every output.
            let mut n: usize = 0;
            let mut t: usize = 0;
            proof {
                assert forall|h: int, x: int| #[trigger] ghas(ents@, 0, h, x) <==>
                    gath(os@, q as int, 0, if 0 < nprod { os@[0].start@[q as int] as int } else { 0 }, h, x) by {}
            }
            while t < nprod
                invariant
                    os@ == self.outs@, nprod == os@.len(),
                    outs_shape(os@, np as int, sn as int),
                    q < q1 <= np,
                    t <= nprod,
                    n <= cap, cap == ents@.len(),
                    forall|k: int| 0 <= k < n ==> (#[trigger] ents@[k] >> 20u32) < 64 && mval(ents@[k], XMASK) < sn,
                    forall|h: int, x: int| #[trigger] ghas(ents@, n as int, h, x) <==>
                        gath(os@, q as int, t as int, if t < nprod { os@[t as int].start@[q as int] as int } else { 0 }, h, x),
                decreases nprod - t,
            {
                let o = &os[t];
                proof {
                    assert(regs_ok(o.start@, o.cur@, o.out@, np as int, sn as int));
                }
                let a = o.start[q];
                let b = o.cur[q];
                proof {
                    assert(o.start@[q + 1] <= o.start@[np as int]);
                    assert(ent_ok(o.out@, a as int, b as int, sn as int));
                }
                let mut k = a;
                while k < b
                    invariant
                        os@ == self.outs@, nprod == os@.len(),
                        t < nprod, *o == os@[t as int],
                        q < np,
                        a == o.start@[q as int], b == o.cur@[q as int],
                        b <= o.out@.len(),
                        ent_ok(o.out@, a as int, b as int, sn as int),
                        a <= k <= b,
                        n <= cap, cap == ents@.len(),
                        forall|k2: int| 0 <= k2 < n ==> (#[trigger] ents@[k2] >> 20u32) < 64 && mval(ents@[k2], XMASK) < sn,
                        forall|h: int, x: int| #[trigger] ghas(ents@, n as int, h, x) <==>
                            gath(os@, q as int, t as int, k as int, h, x),
                    decreases b - k,
                {
                    if n >= cap {
                        return GrpOut { counts, ok: false };
                    }
                    let ghost e0 = ents@;
                    ents[n] = o.out[k];
                    proof {
                        assert(slot_of_ent(o.out@[k as int] as int) < 64 && x_of_ent(o.out@[k as int] as int) < sn);
                        lemma_bits20(o.out@[k as int]);
                        lemma_gath_push(os@, q as int, t as int, k as int, e0, ents@, n as int);
                        assert forall|k2: int| 0 <= k2 < n + 1 implies (#[trigger] ents@[k2] >> 20u32) < 64 && mval(ents@[k2], XMASK) < sn by {
                            if k2 < n { assert(ents@[k2] == e0[k2]); }
                        }
                    }
                    n = n + 1;
                    k = k + 1;
                }
                proof {
                    assert forall|h: int, x: int| #[trigger] ghas(ents@, n as int, h, x) <==>
                        gath(os@, q as int, t + 1, if t + 1 < nprod { os@[t + 1].start@[q as int] as int } else { 0 }, h, x) by {
                        lemma_gath_next(os@, q as int, t as int, b as int, h, x);
                    }
                }
                t = t + 1;
            }
            // Sort by slot.
            let mut h: usize = 0;
            while h < 65
                invariant offs@.len() == 65, h <= 65, forall|h2: int| 0 <= h2 < h ==> #[trigger] offs@[h2] == 0,
                decreases 65 - h,
            {
                offs[h] = 0;
                h = h + 1;
            }
            scatter_hi(&ents, 20, n, 64, &mut offs, &mut loc);
            proof {
                assert forall|h2: int, w: int| 0 <= h2 < 64 && 0 <= w < sel(hi_keys(ents@, 20), ents@, n as int, h2).len()
                    implies mval(#[trigger] sel(hi_keys(ents@, 20), ents@, n as int, h2)[w], XMASK) < sn by {
                    lemma_sel_bound(ents@, n as int, h2, sn as int);
                }
            }
            // Count every slot's segment.
            let mut h: usize = 0;
            while h < 64
                invariant
                    os@ == self.outs@, ex@ == self.excl@, sn == self.sn, q0 == self.q0, q1 == self.q1,
                    nprod == os@.len(),
                    sn <= 64 * ex@.len(),
                    sn <= 64 * marks@.len(),
                    holds(marks@, Set::empty()),
                    q0 <= q < q1, q1 <= np, np < 0x10_0000,
                    h <= 64,
                    n <= cap, cap == ents@.len(), cap == loc@.len(),
                    scattered(hi_keys(ents@, 20), ents@, n as int, 64, offs@, loc@),
                    forall|h2: int, w: int| 0 <= h2 < 64 && 0 <= w < sel(hi_keys(ents@, 20), ents@, n as int, h2).len()
                        ==> mval(#[trigger] sel(hi_keys(ents@, 20), ents@, n as int, h2)[w], XMASK) < sn,
                    forall|h2: int, x: int| #[trigger] ghas(ents@, n as int, h2, x) <==>
                        gath(os@, q as int, nprod as int, 0, h2, x),
                    counts@.len() == 64 * (q1 - q0),
                    forall|g: int| 64 * q0 <= g < 64 * q + h ==>
                        #[trigger] dset2(os@, ex@, sn as int, g).len() == counts@[g - 64 * q0] as int,
                decreases 64 - h,
            {
                let a = offs[h];
                let b = offs[h + 1];
                proof {
                    lemma_offs_le(hi_keys(ents@, 20), ents@, n as int, 64, offs@, loc@, h + 1);
                    assert(loc@.subrange(a as int, b as int) == sel(hi_keys(ents@, 20), ents@, n as int, h as int));
                    assert forall|k: int| a <= k < b implies mval(#[trigger] loc@[k], XMASK) < sn by {
                        assert(loc@[k] == loc@.subrange(a as int, b as int)[k - a]);
                    }
                }
                let c = count_seg(&loc, a, b, XMASK, ex, &mut marks, sn);
                proof {
                    lemma_slot_set(os@, ex@, sn as int, q as int, h as int, ents@, n as int, offs@, loc@);
                    assert(64 * q + h - 64 * q0 < counts@.len()) by (nonlinear_arith)
                        requires q < q1, h < 64, counts@.len() == 64 * (q1 - q0), q0 <= q;
                }
                let ghost c0 = counts@;
                proof {
                    assert((q - q0) * 64 < 0x400_0000) by (nonlinear_arith) requires q - q0 < 0x10_0000;
                }
                let base = (q - q0) * 64;
                proof {
                    assert(base + h == 64 * q + h - 64 * q0);
                }
                counts[base + h] = c;
                proof {
                    assert forall|g: int| 64 * q0 <= g < 64 * q + h + 1 implies
                        #[trigger] dset2(os@, ex@, sn as int, g).len() == counts@[g - 64 * q0] as int by {
                        if g < 64 * q + h {
                            assert(counts@[g - 64 * q0] == c0[g - 64 * q0]);
                        }
                    }
                }
                h = h + 1;
            }
            q = q + 1;
        }
        GrpOut { counts, ok: true }
    }
}

} // verus!
