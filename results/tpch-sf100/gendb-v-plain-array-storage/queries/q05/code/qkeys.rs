//! Phase A (parallel): the order keys of the *qualifying* orders (dated in the year, customer in the region: a
//! non-`NONE` code), with their codes. Each task lists the qualifying orders of one chunk of order rows, batch by
//! batch (`batch::batch_list`), reading `o_orderkey` only for them, and reports whether its keys ascend strictly.
//! When every list ascends and each list's first key exceeds the previous non-empty list's last key, their
//! concatenation (ghost only, never built) is the strictly ascending list of all qualifying keys (`qkeys_ok`).
//! The calling thread checks this (`build_qkeys`) and hands each chunk's list to one lineitem task (`scan`) with
//! the outer bounds of its keys: the key after the previous non-empty list's last key and the next non-empty
//! list's first key. Every qualifying key between those bounds is in the chunk's list (`chunk_ok`), which is all
//! the merge needs; nothing depends on the order of the stored rows. Otherwise the caller falls back to the slow
//! mode.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::put;
use crate::agent::model::*;
use crate::agent::contrib::*;
use crate::agent::rows::*;
use crate::agent::batch::*;
use crate::agent::codes::{chunk_lo, chunk_hi, cover, lemma_chunk, lemma_cover};

verus! {

/// `k` is the key of an order whose code is `code` (not `NONE`).
pub open spec fn qkey_at(x: Ctx, k: i64, code: u8) -> bool {
    &&& code != NONE
    &&& exists|j: int| 0 <= j < no(x.sv) && #[trigger] o_ok(x.sv)[j] == k && ord_code(x.sv, x.slots, x.pd, x.t, j) == code
}

/// Every listed key is a qualifying order's key with its code.
pub open spec fn qsound(x: Ctx, keys: Seq<i64>, codes: Seq<u8>, n: int) -> bool {
    &&& 0 <= n <= keys.len()
    &&& n <= codes.len()
    &&& forall|p: int| 0 <= p < n ==> #[trigger] qkey_at(x, keys[p], codes[p])
}

/// The key of every qualifying order of the rows `[a, b)` is listed.
pub open spec fn qcomplete(x: Ctx, keys: Seq<i64>, n: int, a: int, b: int) -> bool {
    forall|j: int| a <= j < b && #[trigger] ord_code(x.sv, x.slots, x.pd, x.t, j) != NONE
        ==> exists|p: int| 0 <= p < n && keys[p] == o_ok(x.sv)[j]
}

/// The first `n` keys ascend strictly.
pub open spec fn qsorted(keys: Seq<i64>, n: int) -> bool {
    forall|p: int, p2: int| 0 <= p < p2 < n ==> #[trigger] keys[p] < #[trigger] keys[p2]
}

/// The strictly ascending list of the keys of all qualifying orders, with their codes.
pub open spec fn qkeys_ok(x: Ctx, keys: Seq<i64>, codes: Seq<u8>) -> bool {
    &&& keys.len() == codes.len()
    &&& qsound(x, keys, codes, keys.len() as int)
    &&& qcomplete(x, keys, keys.len() as int, 0, no(x.sv) as int)
    &&& qsorted(keys, keys.len() as int)
}

/// The lower end of the safe interval before list position `p`.
pub open spec fn lo_at(keys: Seq<i64>, p: int) -> int {
    if p > 0 { keys[p - 1] as int + 1 } else { i64::MIN as int }
}

/// The upper end of the safe interval before list position `p`.
pub open spec fn hi_at(keys: Seq<i64>, p: int) -> int {
    if p < keys.len() { keys[p] as int } else { i64::MAX as int }
}

/// One chunk's qualifying keys `keys[0..n)` (with codes) and the bounds `[lo, hi)` around them.
pub struct ChunkKeys {
    pub keys: Vec<i64>,
    pub codes: Vec<u8>,
    pub n: usize,
    pub lo: i64,
    pub hi: i64,
}

/// The listed keys ascend strictly, lie in `[lo, hi)`, and are exactly the qualifying keys in `[lo, hi)`.
pub open spec fn chunk_ok(x: Ctx, keys: Seq<i64>, codes: Seq<u8>, n: int, lo: int, hi: int) -> bool {
    &&& qsound(x, keys, codes, n)
    &&& qsorted(keys, n)
    &&& forall|p: int| 0 <= p < n ==> lo <= #[trigger] keys[p] < hi
    &&& forall|j: int| 0 <= j < no(x.sv) && #[trigger] ord_code(x.sv, x.slots, x.pd, x.t, j) != NONE
        && lo <= o_ok(x.sv)[j] < hi ==> exists|p: int| 0 <= p < n && keys[p] == o_ok(x.sv)[j]
}

/// A chunk's slice of the list of all qualifying keys, with the bounds next to it, is `chunk_ok`.
proof fn lemma_chunk_ok(x: Ctx, g: Seq<i64>, gc: Seq<u8>, s: int, keys: Seq<i64>, codes: Seq<u8>, n: int)
    requires
        qkeys_ok(x, g, gc), forall|q: int| 0 <= q < g.len() ==> #[trigger] g[q] < i64::MAX,
        0 <= s, 0 <= n, s + n <= g.len(), n <= keys.len(), n <= codes.len(),
        forall|p: int| 0 <= p < n ==> #[trigger] keys[p] == g[s + p] && codes[p] == gc[s + p],
    ensures chunk_ok(x, keys, codes, n, lo_at(g, s), hi_at(g, s + n)),
{
    assert forall|p: int| 0 <= p < n implies #[trigger] qkey_at(x, keys[p], codes[p]) by {
        assert(qkey_at(x, g[s + p], gc[s + p]));
    }
    assert forall|p: int, p2: int| 0 <= p < p2 < n implies #[trigger] keys[p] < #[trigger] keys[p2] by {
        assert(g[s + p] < g[s + p2]);
    }
    assert forall|p: int| 0 <= p < n implies lo_at(g, s) <= #[trigger] keys[p] < hi_at(g, s + n) by {
        assert(keys[p] == g[s + p] && g[s + p] < i64::MAX);
        if s > 0 { assert(g[s - 1] < g[s + p]); }
        if s + n < g.len() { assert(g[s + p] < g[s + n]); }
    }
    assert forall|j: int| 0 <= j < no(x.sv) && #[trigger] ord_code(x.sv, x.slots, x.pd, x.t, j) != NONE
        && lo_at(g, s) <= o_ok(x.sv)[j] < hi_at(g, s + n) implies exists|p: int| 0 <= p < n && keys[p] == o_ok(x.sv)[j] by {
        let r = choose|r: int| 0 <= r < g.len() && g[r] == o_ok(x.sv)[j];
        if r < s {
            if r < s - 1 { assert(g[r] < g[s - 1]); }
        } else if r >= s + n {
            if r > s + n { assert(g[s + n] < g[r]); }
        } else {
            assert(keys[r - s] == g[r]);
        }
    }
}

// ------------------------------------------------------------------------------------------ the task

/// Bytes of the smallest per-task output buffer (above the allocator's largest heap threshold, 32 MiB).
pub const MIN_MAP: usize = 0x2100000;

/// One chunk of order rows `[a, b)`; `keys`/`codes` have one slot per row.
pub struct OrderTask {
    pub sh: Arc<Shared>,
    pub a: usize,
    pub b: usize,
    pub idx: Vec<usize>,
    pub ci: Vec<usize>,
    pub qj: Vec<usize>,
    pub qr: Vec<usize>,
    pub keys: Vec<i64>,
    pub codes: Vec<u8>,
    pub x: Ghost<Ctx>,
}

pub struct OrderOut {
    pub keys: Vec<i64>,
    pub codes: Vec<u8>,
    pub n: usize,
    pub asc: bool,
}

/// The task's result: the qualifying keys of `[a, b)`, ascending when `asc`.
pub open spec fn order_post(x: Ctx, a: int, b: int, out: OrderOut) -> bool {
    &&& qsound(x, out.keys@, out.codes@, out.n as int)
    &&& qcomplete(x, out.keys@, out.n as int, a, b)
    &&& out.asc ==> qsorted(out.keys@, out.n as int)
}

impl WorkerTask for OrderTask {
    type Output = OrderOut;

    open spec fn pre(&self) -> bool {
        &&& shared_ok(*self.sh, self.x@)
        &&& self.sh.fast
        &&& self.a <= self.b <= self.sh.c.no
        &&& self.idx@.len() == BATCH && self.ci@.len() == BATCH && self.qj@.len() == BATCH && self.qr@.len() == BATCH
        &&& self.keys@.len() >= self.b - self.a
        &&& self.codes@.len() >= self.b - self.a
    }

    open spec fn post(&self, out: OrderOut) -> bool {
        order_post(self.x@, self.a as int, self.b as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.a as u64, self.b as u64)
    }

    fn run(self) -> (out: OrderOut) {
        let OrderTask { sh, a, b, idx, ci, qj, qr, keys, codes, x } = self;
        let shr: &Shared = &*sh;
        let ghost xv = x@;
        let ghost sv = xv.sv;
        let mut idx = idx;
        let mut ci = ci;
        let mut qj = qj;
        let mut qr = qr;
        let mut keys = keys;
        let mut codes = codes;
        let ook = shr.c.ook;
        assert(ook@ == o_ok(sv) && ook@.len() == shr.c.no);
        let mut n: usize = 0;
        let mut asc = true;
        let mut jb = a;
        while jb < b
            invariant
                shared_ok(*shr, xv), shr.fast, sv == xv.sv, ook@ == o_ok(sv), ook@.len() == shr.c.no,
                a <= jb <= b <= shr.c.no,
                idx@.len() == BATCH, ci@.len() == BATCH, qj@.len() == BATCH, qr@.len() == BATCH,
                keys@.len() >= b - a, codes@.len() >= b - a, n <= jb - a,
                qsound(xv, keys@, codes@, n as int),
                qcomplete(xv, keys@, n as int, a as int, jb as int),
                asc ==> qsorted(keys@, n as int),
            decreases b - jb,
        {
            let je = if b - jb > BATCH { jb + BATCH } else { b };
            let nq = batch_list(shr, jb, je, &mut idx, &mut ci, &mut qj, &mut qr, Ghost(xv));
            let ghost n0 = n;
            let ghost k0 = keys@;
            let mut p: usize = 0;
            while p < nq
                invariant
                    shared_ok(*shr, xv), shr.fast, sv == xv.sv, ook@ == o_ok(sv), ook@.len() == shr.c.no,
                    a <= jb < je <= b <= shr.c.no, je - jb <= BATCH, nq <= je - jb,
                    hlist_ok(*shr, xv, qj@, qr@, nq as int, jb as int, je as int),
                    keys@.len() >= b - a, codes@.len() >= b - a,
                    p <= nq, n == n0 + p, n0 <= jb - a,
                    forall|y: int| 0 <= y < n0 ==> #[trigger] keys@[y] == k0[y],
                    forall|y: int| 0 <= y < p ==> #[trigger] keys@[n0 + y] == o_ok(sv)[qj@[y] as int],
                    qsound(xv, keys@, codes@, n as int),
                    asc ==> qsorted(keys@, n as int),
                decreases nq - p,
            {
                let j = qj[p];
                let k = ook[j];
                let code = shr.ccode[qr[p]];
                proof {
                    assert(jb <= qj@[p as int] < je);
                    assert(qkey_at(xv, k, code));
                }
                if n > 0 && keys[n - 1] >= k {
                    asc = false;
                }
                let ghost kb = keys@;
                let ghost cb = codes@;
                put(&mut keys, n, k);
                put(&mut codes, n, code);
                proof {
                    assert forall|y: int| 0 <= y < n implies #[trigger] keys@[y] == kb[y] && codes@[y] == cb[y] by {}
                    assert forall|y: int| 0 <= y < n0 implies #[trigger] keys@[y] == k0[y] by {}
                    assert forall|y: int| 0 <= y < p + 1 implies #[trigger] keys@[n0 + y] == o_ok(sv)[qj@[y] as int] by {}
                    assert forall|y: int| 0 <= y < n + 1 implies #[trigger] qkey_at(xv, keys@[y], codes@[y]) by {
                        if y < n { assert(qkey_at(xv, kb[y], cb[y])); }
                    }
                    if asc {
                        assert forall|y: int, y2: int| 0 <= y < y2 < n + 1 implies #[trigger] keys@[y] < #[trigger] keys@[y2] by {
                            if y2 < n as int {
                                assert(kb[y] < kb[y2]);
                            } else if y < n - 1 {
                                assert(kb[y] < kb[n - 1]);
                            }
                        }
                    }
                }
                n = n + 1;
                p = p + 1;
            }
            proof {
                assert forall|j: int| a <= j < je && #[trigger] ord_code(sv, xv.slots, xv.pd, xv.t, j) != NONE
                    implies exists|y: int| 0 <= y < n && keys@[y] == o_ok(sv)[j] by {
                    if j < jb {
                        let y = choose|y: int| 0 <= y < n0 && k0[y] == o_ok(sv)[j];
                        assert(keys@[y] == k0[y]);
                    } else {
                        let y = choose|y: int| 0 <= y < nq && qj@[y] == j;
                        assert(keys@[n0 + y] == o_ok(sv)[qj@[y] as int]);
                    }
                }
            }
            jb = je;
        }
        OrderOut { keys, codes, n, asc }
    }
}

// ------------------------------------------------------------------------------------------ the driver

/// Concatenation step: the list of the first chunks, extended by the next chunk's list.
proof fn lemma_append(x: Ctx, g: Seq<i64>, gc: Seq<u8>, k: Seq<i64>, kc: Seq<u8>, n: int, lo: int, mid: int, hi: int,
    gsorted: bool, ok: bool)
    requires
        g.len() == gc.len(), qsound(x, g, gc, g.len() as int), qcomplete(x, g, g.len() as int, lo, mid),
        qsound(x, k, kc, n), qcomplete(x, k, n, mid, hi), n == k.len(), n == kc.len(),
        gsorted ==> qsorted(g, g.len() as int),
        ok ==> qsorted(k, n) && (g.len() > 0 && n > 0 ==> g[g.len() - 1] < k[0]),
    ensures
        qsound(x, g + k, gc + kc, g.len() + n),
        qcomplete(x, g + k, g.len() + n, lo, hi),
        gsorted && ok ==> qsorted(g + k, g.len() + n),
{
    let gk = g + k;
    let gkc = gc + kc;
    let m = g.len() as int;
    assert forall|p: int| 0 <= p < m + n implies #[trigger] qkey_at(x, gk[p], gkc[p]) by {
        if p < m {
            assert(gk[p] == g[p] && gkc[p] == gc[p]);
            assert(qkey_at(x, g[p], gc[p]));
        } else {
            assert(gk[p] == k[p - m] && gkc[p] == kc[p - m]);
            assert(qkey_at(x, k[p - m], kc[p - m]));
        }
    }
    assert forall|j: int| lo <= j < hi && #[trigger] ord_code(x.sv, x.slots, x.pd, x.t, j) != NONE
        implies exists|p: int| 0 <= p < m + n && gk[p] == o_ok(x.sv)[j] by {
        if j < mid {
            let p = choose|p: int| 0 <= p < m && g[p] == o_ok(x.sv)[j];
            assert(gk[p] == g[p]);
        } else {
            let p = choose|p: int| 0 <= p < n && k[p] == o_ok(x.sv)[j];
            assert(gk[m + p] == k[p]);
        }
    }
    if gsorted && ok {
        assert forall|p: int, p2: int| 0 <= p < p2 < m + n implies #[trigger] gk[p] < #[trigger] gk[p2] by {
            if p2 < m {
                assert(g[p] < g[p2]);
            } else if p >= m {
                assert(k[p - m] < k[p2 - m]);
            } else {
                if p < m - 1 { assert(g[p] < g[m - 1]); }
                if p2 > m { assert(k[0] < k[p2 - m]); }
            }
        }
    }
}

/// The task outputs `outs[0..u)`, truncated to their lengths, lie in `g`/`gc` one after the other from `starts`.
pub open spec fn slices_ok(g: Seq<i64>, gc: Seq<u8>, starts: Seq<int>, outs: Seq<OrderOut>, u: int) -> bool {
    &&& g.len() == gc.len()
    &&& starts.len() == u
    &&& forall|w: int| 0 <= w < u ==> 0 <= #[trigger] starts[w] && starts[w] + outs[w].n <= g.len()
        && (w + 1 < u ==> starts[w + 1] == starts[w] + outs[w].n)
        && (w + 1 == u ==> g.len() == starts[w] + outs[w].n)
    &&& forall|w: int, p: int| 0 <= w < u && 0 <= p < outs[w].n ==> #[trigger] g[starts[w] + p] == #[trigger] outs[w].keys@[p]
        && gc[starts[w] + p] == outs[w].codes@[p]
    &&& u == 0 ==> g.len() == 0
}

/// Appending output `u` (its first `n` keys and codes) keeps the slices.
proof fn lemma_slices_push(g: Seq<i64>, gc: Seq<u8>, starts: Seq<int>, outs: Seq<OrderOut>, u: int)
    requires
        slices_ok(g, gc, starts, outs, u), 0 <= u < outs.len(),
        outs[u].n <= outs[u].keys@.len(), outs[u].n <= outs[u].codes@.len(),
    ensures ({
        let n = outs[u].n as int;
        slices_ok(g + outs[u].keys@.subrange(0, n), gc + outs[u].codes@.subrange(0, n), starts.push(g.len() as int), outs, u + 1)
    }),
{
    let n = outs[u].n as int;
    let g2 = g + outs[u].keys@.subrange(0, n);
    let gc2 = gc + outs[u].codes@.subrange(0, n);
    let s2 = starts.push(g.len() as int);
    assert forall|w: int| 0 <= w < u + 1 implies 0 <= #[trigger] s2[w] && s2[w] + outs[w].n <= g2.len()
        && (w + 1 < u + 1 ==> s2[w + 1] == s2[w] + outs[w].n)
        && (w + 1 == u + 1 ==> g2.len() == s2[w] + outs[w].n) by {
        if w < u { assert(s2[w] == starts[w]); }
    }
    assert forall|w: int, p: int| 0 <= w < u + 1 && 0 <= p < outs[w].n implies #[trigger] g2[s2[w] + p] == #[trigger] outs[w].keys@[p]
        && gc2[s2[w] + p] == outs[w].codes@[p] by {
        if w < u {
            assert(s2[w] == starts[w]);
            assert(g2[starts[w] + p] == g[starts[w] + p]);
            assert(gc2[starts[w] + p] == gc[starts[w] + p]);
        } else {
            assert(g2[g.len() + p] == outs[u].keys@[p]);
            assert(gc2[g.len() + p] == outs[u].codes@[p]);
        }
    }
}

/// `los[w]` is the lower bound before slice `w`.
pub open spec fn los_ok(los: Seq<i64>, g: Seq<i64>, starts: Seq<int>, u: int) -> bool {
    &&& los.len() == u
    &&& forall|w: int| 0 <= w < u ==> #[trigger] los[w] as int == lo_at(g, starts[w])
}

/// Appending keys keeps the lower bounds of the earlier slices; the next one is `lo`.
proof fn lemma_los_push(los: Seq<i64>, lo: i64, g: Seq<i64>, k: Seq<i64>, starts: Seq<int>, u: int)
    requires
        los_ok(los, g, starts, u), starts.len() == u, forall|w: int| 0 <= w < u ==> #[trigger] starts[w] <= g.len(),
        lo as int == lo_at(g, g.len() as int),
    ensures los_ok(los.push(lo), g + k, starts.push(g.len() as int), u + 1),
{
    let g2 = g + k;
    let s2 = starts.push(g.len() as int);
    assert forall|w: int| 0 <= w < u + 1 implies #[trigger] los.push(lo)[w] as int == lo_at(g2, s2[w]) by {
        if w < u {
            assert(s2[w] == starts[w]);
            if starts[w] > 0 { assert(g2[starts[w] - 1] == g[starts[w] - 1]); }
        } else {
            if g.len() > 0 { assert(g2[g.len() - 1] == g[g.len() - 1]); }
        }
    }
}

/// The facts of one slice `w` of `slices_ok`.
proof fn lemma_slice_at(g: Seq<i64>, gc: Seq<u8>, starts: Seq<int>, outs: Seq<OrderOut>, u: int, w: int)
    requires slices_ok(g, gc, starts, outs, u), 0 <= w < u,
    ensures
        0 <= starts[w], starts[w] + outs[w].n <= g.len(),
        w + 1 < u ==> starts[w + 1] == starts[w] + outs[w].n,
        w + 1 == u ==> g.len() == starts[w] + outs[w].n,
        forall|p: int| 0 <= p < outs[w].n ==> #[trigger] g[starts[w] + p] == outs[w].keys@[p] && gc[starts[w] + p] == outs[w].codes@[p],
{
    assert forall|p: int| 0 <= p < outs[w].n implies #[trigger] g[starts[w] + p] == outs[w].keys@[p] && gc[starts[w] + p] == outs[w].codes@[p] by {
        assert(g[starts[w] + p] == outs[w].keys@[p]);
    }
}

/// The task output `o` of order chunk `[a, b)` truncated to its length, as `lemma_append` takes it.
proof fn lemma_out_trunc(x: Ctx, o: OrderOut, a: int, b: int)
    requires order_post(x, a, b, o),
    ensures ({
        let ku = o.keys@.subrange(0, o.n as int);
        let cu = o.codes@.subrange(0, o.n as int);
        &&& ku.len() == o.n && cu.len() == o.n
        &&& qsound(x, ku, cu, o.n as int)
        &&& qcomplete(x, ku, o.n as int, a, b)
        &&& o.asc ==> qsorted(ku, o.n as int)
    }),
{
    let ku = o.keys@.subrange(0, o.n as int);
    let cu = o.codes@.subrange(0, o.n as int);
    assert forall|p: int| 0 <= p < o.n implies #[trigger] qkey_at(x, ku[p], cu[p]) by {
        assert(qkey_at(x, o.keys@[p], o.codes@[p]));
    }
    assert forall|j: int| a <= j < b && #[trigger] ord_code(x.sv, x.slots, x.pd, x.t, j) != NONE
        implies exists|p: int| 0 <= p < o.n && ku[p] == o_ok(x.sv)[j] by {
        let p = choose|p: int| 0 <= p < o.n && o.keys@[p] == o_ok(x.sv)[j];
        assert(ku[p] == o.keys@[p]);
    }
    if o.asc {
        assert forall|p: int, p2: int| 0 <= p < p2 < o.n implies #[trigger] ku[p] < #[trigger] ku[p2] by {
            assert(o.keys@[p] < o.keys@[p2]);
        }
    }
}

/// Every key of `g` is below `i64::MAX` after appending `k` whose keys are at most its last key `last < MAX`.
proof fn lemma_below_max(g: Seq<i64>, k: Seq<i64>, n: int)
    requires
        forall|q: int| 0 <= q < g.len() ==> #[trigger] g[q] < i64::MAX,
        n == k.len(), n > 0 ==> k[n - 1] < i64::MAX, qsorted(k, n),
    ensures forall|q: int| 0 <= q < (g + k).len() ==> #[trigger] (g + k)[q] < i64::MAX,
{
    assert forall|q: int| 0 <= q < (g + k).len() implies #[trigger] (g + k)[q] < i64::MAX by {
        if q < g.len() {
            assert((g + k)[q] == g[q]);
        } else {
            assert((g + k)[q] == k[q - g.len()]);
            if q - g.len() < n - 1 { assert(k[q - g.len()] < k[n - 1]); }
        }
    }
}

/// Phase A with `nt` tasks: per order chunk `t` (`chunk_lo/hi(t)`), its qualifying keys with their bounds, or
/// `None` when the keys of all chunks, in chunk order, do not ascend strictly (or reach `i64::MAX`).
pub fn build_qkeys(sh: &Arc<Shared>, nt: usize, dispatch: &mut Dispatch, Ghost(x): Ghost<Ctx>)
    -> (r: Result<Option<Vec<ChunkKeys>>, WorkerFailure>)
    requires shared_ok(**sh, x), sh.fast, 1 <= nt <= MAX_WORKERS, nt <= sh.c.no,
    ensures r matches Ok(Some(v)) ==> v@.len() == nt && forall|t: int| 0 <= t < nt ==>
        chunk_ok(x, (#[trigger] v@[t]).keys@, v@[t].codes@, v@[t].n as int, v@[t].lo as int, v@[t].hi as int)
        && v@[t].n <= v@[t].keys@.len() && v@[t].n <= v@[t].codes@.len(),
{
    hide(slices_ok);
    hide(qkeys_ok);
    let shr: &Shared = &**sh;
    let no = shr.c.no;
    let ch = no / nt;
    let mut tasks: Vec<OrderTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            shared_ok(*shr, x), shr.fast, shr == &**sh, 1 <= nt <= MAX_WORKERS, nt <= no, no == shr.c.no, t <= nt, ch == no / nt,
            tasks@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).pre() && *tasks@[u].sh == *shr && tasks@[u].x@ == x
                && tasks@[u].a == chunk_lo(u, no as int, nt as int) && tasks@[u].b == chunk_hi(u, no as int, nt as int),
        decreases nt - t,
    {
        proof {
            lemma_chunk(t as int, no as int, nt as int);
            assert(t * ch <= no) by (nonlinear_arith) requires ch == no / nt, 1 <= nt <= no, t < nt;
            assert(t + 1 < nt ==> (t + 1) * ch <= no) by (nonlinear_arith) requires ch == no / nt, 1 <= nt, t < nt;
        }
        let a = t * ch;
        let b = if t + 1 == nt { no } else { (t + 1) * ch };
        // Room for every row of the chunk, but never less than `MIN_MAP` bytes: such a request is always a fresh,
        // lazily zeroed mapping (smaller ones may be served by the allocator's heap and cleared on this thread).
        let kcap = if b - a < MIN_MAP / 8 { MIN_MAP / 8 } else { b - a };
        let ccap = if b - a < MIN_MAP { MIN_MAP } else { b - a };
        let task = OrderTask {
            sh: sh.clone(), a, b,
            idx: vec![0usize; BATCH], ci: vec![0usize; BATCH], qj: vec![0usize; BATCH], qr: vec![0usize; BATCH],
            keys: vec![0i64; kcap], codes: vec![0u8; ccap], x: Ghost(x),
        };
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let ghost ov = outs@;
    proof {
        assert forall|w: int| 0 <= w < nt implies order_post(x, chunk_lo(w, no as int, nt as int), chunk_hi(w, no as int, nt as int),
            #[trigger] ov[w]) by {
            assert(tv[w].post(ov[w]));
        }
    }
    // Pass 1: the lower bounds, and whether the concatenation `g` of the lists (ghost) ascends.
    let ghost mut g: Seq<i64> = Seq::empty();
    let ghost mut gc: Seq<u8> = Seq::empty();
    let ghost mut starts: Seq<int> = Seq::empty();
    let mut los: Vec<i64> = Vec::new();
    let mut asc = true;
    let mut seen = false;
    let mut lo: i64 = i64::MIN;
    let mut u: usize = 0;
    assert(slices_ok(g, gc, starts, ov, 0)) by { reveal(slices_ok); }
    while u < nt
        invariant
            no == shr.c.no, u <= nt, outs@ == ov, ov.len() == nt, 1 <= nt,
            g.len() == gc.len(), starts.len() == u,
            forall|w: int| 0 <= w < nt ==> order_post(x, chunk_lo(w, no as int, nt as int), chunk_hi(w, no as int, nt as int), #[trigger] ov[w]),
            slices_ok(g, gc, starts, ov, u as int),
            qsound(x, g, gc, g.len() as int),
            qcomplete(x, g, g.len() as int, 0, cover(u as int, no as int, nt as int)),
            asc ==> qsorted(g, g.len() as int) && lo as int == lo_at(g, g.len() as int)
                && (forall|q: int| 0 <= q < g.len() ==> #[trigger] g[q] < i64::MAX)
                && los_ok(los@, g, starts, u as int),
            los@.len() == u,
            seen == (g.len() > 0),
        decreases nt - u,
    {
        proof { lemma_cover(u as int, no as int, nt as int); }
        let ghost (g0, gc0, s0, los0) = (g, gc, starts, los@);
        let n = outs[u].n;
        let ok = outs[u].asc && (n == 0 || !seen || lo <= outs[u].keys[0]);
        let link = asc && ok;
        proof {
            let o = ov[u as int];
            lemma_out_trunc(x, o, cover(u as int, no as int, nt as int), cover(u as int + 1, no as int, nt as int));
            let ku = o.keys@.subrange(0, n as int);
            let cu = o.codes@.subrange(0, n as int);
            if link && g0.len() > 0 && n > 0 {
                assert(ku[0] == o.keys@[0]);
            }
            lemma_append(x, g0, gc0, ku, cu, n as int, 0, cover(u as int, no as int, nt as int),
                cover(u as int + 1, no as int, nt as int), asc, link);
            lemma_slices_push(g0, gc0, s0, ov, u as int);
            if asc {
                assert forall|w: int| 0 <= w < u implies #[trigger] s0[w] <= g0.len() by {
                    lemma_slice_at(g0, gc0, s0, ov, u as int, w);
                }
                lemma_los_push(los0, lo, g0, ku, s0, u as int);
            }
            g = g0 + ku;
            gc = gc0 + cu;
            starts = s0.push(g0.len() as int);
        }
        los.push(lo);
        let mut last_ok = true;
        if n > 0 {
            seen = true;
            let last = outs[u].keys[n - 1];
            if last == i64::MAX {
                // No key may follow the last one: the merge's bounds need `last + 1`.
                last_ok = false;
            } else {
                lo = last + 1;
            }
            proof {
                assert(g[g.len() - 1] == last);
            }
        }
        proof {
            if link && last_ok {
                let ku = ov[u as int].keys@.subrange(0, n as int);
                if n > 0 { assert(ku[n - 1] == ov[u as int].keys@[n - 1]); }
                lemma_below_max(g0, ku, n as int);
            }
        }
        asc = link && last_ok;
        u = u + 1;
    }
    proof { lemma_cover(nt as int, no as int, nt as int); }
    if !asc {
        return Ok(None);
    }
    assert(qkeys_ok(x, g, gc)) by { reveal(qkeys_ok); }
    // Pass 2 (backward): the upper bounds.
    proof {
        assert forall|v: int| 0 <= v < nt implies (#[trigger] ov[v]).n <= ov[v].keys@.len() by {
            assert(order_post(x, chunk_lo(v, no as int, nt as int), chunk_hi(v, no as int, nt as int), ov[v]));
        }
    }
    let mut his: Vec<i64> = vec![0i64; nt];
    let mut hi: i64 = i64::MAX;
    let mut w: usize = nt;
    while w > 0
        invariant
            w <= nt, outs@ == ov, ov.len() == nt, his@.len() == nt, 1 <= nt, starts.len() == nt,
            slices_ok(g, gc, starts, ov, nt as int),
            forall|v: int| 0 <= v < nt ==> (#[trigger] ov[v]).n <= ov[v].keys@.len(),
            hi as int == hi_at(g, if w < nt { starts[w as int] } else { g.len() as int }),
            forall|v: int| w <= v < nt ==> #[trigger] his@[v] as int == hi_at(g, starts[v] + ov[v].n),
        decreases w,
    {
        let v = w - 1;
        proof { lemma_slice_at(g, gc, starts, ov, nt as int, v as int); }
        let n = outs[v].n;
        put(&mut his, v, hi);
        if n > 0 {
            hi = outs[v].keys[0];
            proof { assert(g[starts[v as int] + 0] == ov[v as int].keys@[0]); }
        }
        w = v;
    }
    // The chunks, moved out of the task outputs.
    let mut chunks: Vec<ChunkKeys> = Vec::new();
    let mut outs = outs;
    u = 0;
    while u < nt
        invariant
            u <= nt, ov.len() == nt, outs@ == ov.subrange(u as int, nt as int),
            los@.len() == nt, his@.len() == nt, chunks@.len() == u, starts.len() == nt,
            qkeys_ok(x, g, gc), forall|q: int| 0 <= q < g.len() ==> #[trigger] g[q] < i64::MAX,
            slices_ok(g, gc, starts, ov, nt as int),
            los_ok(los@, g, starts, nt as int),
            forall|v: int| 0 <= v < nt ==> #[trigger] his@[v] as int == hi_at(g, starts[v] + ov[v].n),
            forall|v: int| 0 <= v < nt ==> order_post(x, chunk_lo(v, no as int, nt as int), chunk_hi(v, no as int, nt as int), #[trigger] ov[v]),
            forall|v: int| 0 <= v < u ==> chunk_ok(x, (#[trigger] chunks@[v]).keys@, chunks@[v].codes@, chunks@[v].n as int,
                chunks@[v].lo as int, chunks@[v].hi as int) && chunks@[v].n <= chunks@[v].keys@.len() && chunks@[v].n <= chunks@[v].codes@.len(),
        decreases nt - u,
    {
        proof { assert(outs@[0] == ov[u as int]); }
        let o = outs.remove(0);
        proof {
            assert(outs@ =~= ov.subrange(u as int + 1, nt as int));
            assert(order_post(x, chunk_lo(u as int, no as int, nt as int), chunk_hi(u as int, no as int, nt as int), ov[u as int]));
            lemma_slice_at(g, gc, starts, ov, nt as int, u as int);
            assert(los@[u as int] as int == lo_at(g, starts[u as int]));
            lemma_chunk_ok(x, g, gc, starts[u as int], o.keys@, o.codes@, o.n as int);
        }
        let OrderOut { keys, codes, n, asc: _ } = o;
        chunks.push(ChunkKeys { keys, codes, n, lo: los[u], hi: his[u] });
        u = u + 1;
    }
    Ok(Some(chunks))
}

} // verus!
