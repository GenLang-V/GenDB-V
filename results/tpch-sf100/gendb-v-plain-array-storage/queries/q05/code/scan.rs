//! Phase B, the lineitem merge: one task per range of lineitem rows `[ca, cb)`.
//!
//! Fast mode: the task merges the order keys of its rows against its order chunk's ascending list of qualifying
//! keys, which holds every qualifying key between the list's outer bounds (`qkeys::chunk_ok`). It keeps a position
//! `p` in that list and the *safe interval* `[lo, hi)` between the key before `p` (or the lower bound) and the key
//! at `p` (or the upper bound), which holds no qualifying key (`lemma_safe_in`). Rows whose keys lie in it are
//! skipped, whole blocks at a time (`common::key_skip`); a row with key `hi` becomes an entry with that order's
//! code; a row past `hi` moves `p` on; any other row (a key below `lo`, or past the upper bound: the rows are out
//! of order or the range was misplaced) becomes a `SLOW` entry, computed from scratch. The start position is a binary search for the first row's key. Nothing here
//! depends on the stored row order: an order that does not ascend only costs time.
//!
//! Slow mode: every row is a `SLOW` entry. In both modes the accumulators end with the group sums of `[ca, cb)`.
use vstd::prelude::*;
use std::sync::Arc;
use crate::agent::model::*;
use crate::agent::contrib::*;
use crate::agent::plan::*;
use crate::agent::cols::*;
use crate::agent::rows::*;
use crate::agent::qkeys::*;
use crate::agent::common::exact_sum::*;
use crate::agent::common::key_skip::*;
use crate::gendb_entry::parallel::WorkerTask;

verus! {

// ------------------------------------------------------------------------------------------ safe intervals

/// No order with a non-`NONE` code has a key in `[lo, hi)`.
pub open spec fn safe(x: Ctx, lo: int, hi: int) -> bool {
    forall|j: int| 0 <= j < no(x.sv) && #[trigger] ord_code(x.sv, x.slots, x.pd, x.t, j) != NONE
        ==> (o_ok(x.sv)[j] as int) < lo || (o_ok(x.sv)[j] as int) >= hi
}

/// The lower end of the safe interval before position `p` of a chunk's list (`lo` before its first key).
pub open spec fn lo_in(keys: Seq<i64>, lo: int, p: int) -> int {
    if p > 0 { keys[p - 1] as int + 1 } else { lo }
}

/// The upper end of the safe interval before position `p` of a chunk's list `keys[0..n)` (`hi` after its last).
pub open spec fn hi_in(keys: Seq<i64>, n: int, hi: int, p: int) -> int {
    if p < n { keys[p] as int } else { hi }
}

/// Between two consecutive keys of a chunk's list (or a key and a bound) there is no qualifying key.
pub proof fn lemma_safe_in(x: Ctx, keys: Seq<i64>, codes: Seq<u8>, n: int, lo: int, hi: int, p: int)
    requires chunk_ok(x, keys, codes, n, lo, hi), 0 <= p <= n,
    ensures safe(x, lo_in(keys, lo, p), hi_in(keys, n, hi, p)),
{
    assert forall|j: int| 0 <= j < no(x.sv) && #[trigger] ord_code(x.sv, x.slots, x.pd, x.t, j) != NONE
        implies (o_ok(x.sv)[j] as int) < lo_in(keys, lo, p) || (o_ok(x.sv)[j] as int) >= hi_in(keys, n, hi, p) by {
        let k = o_ok(x.sv)[j] as int;
        if lo_in(keys, lo, p) <= k && k < hi_in(keys, n, hi, p) {
            if p > 0 { assert(lo <= keys[p - 1]); }
            if p < n { assert(keys[p] < hi); }
            let q = choose|q: int| 0 <= q < n && keys[q] == o_ok(x.sv)[j];
            if q < p - 1 {
                assert(keys[q] < keys[p - 1]);
            } else if q > p {
                assert(keys[p] < keys[q]);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------ group sums

/// The entries' group sums are the group sums of the lineitem rows `[ca, row)`.
pub open spec fn sums_rel(x: Ctx, gids: Seq<usize>, ng: usize, ent: Seq<usize>, ca: int, row: int) -> bool {
    forall|g: int| 0 <= g < ng ==> {
        &&& #[trigger] esum(x, gids, g, ent, ent.len() as int) == gsum_r(x.sv, x.rp, x.pd, x.t, gids, g, ca, row)
        &&& eabs(x, gids, g, ent, ent.len() as int) == gabs_r(x.sv, x.rp, x.pd, x.t, gids, g, ca, row)
        &&& ecnt(x, gids, g, ent, ent.len() as int) == gcnt_r(x.sv, x.rp, x.pd, x.t, gids, g, ca, row)
    }
}

/// A row that is not a candidate adds nothing.
pub proof fn lemma_sums_skip(x: Ctx, gids: Seq<usize>, ng: usize, ent: Seq<usize>, ca: int, row: int)
    requires sums_rel(x, gids, ng, ent, ca, row), ca <= row, !cand(x.sv, x.rp, x.pd, x.t, row),
    ensures sums_rel(x, gids, ng, ent, ca, row + 1),
{
    assert forall|g: int| 0 <= g < ng implies {
        &&& #[trigger] esum(x, gids, g, ent, ent.len() as int) == gsum_r(x.sv, x.rp, x.pd, x.t, gids, g, ca, row + 1)
        &&& eabs(x, gids, g, ent, ent.len() as int) == gabs_r(x.sv, x.rp, x.pd, x.t, gids, g, ca, row + 1)
        &&& ecnt(x, gids, g, ent, ent.len() as int) == gcnt_r(x.sv, x.rp, x.pd, x.t, gids, g, ca, row + 1)
    } by {
        lemma_range_step(x.sv, x.rp, x.pd, x.t, gids, g, ca, row);
        assert(esum(x, gids, g, ent, ent.len() as int) == gsum_r(x.sv, x.rp, x.pd, x.t, gids, g, ca, row));
        assert(gterm(x.sv, x.rp, x.pd, x.t, gids, g, row) == 0);
    }
}

/// A row recorded as an entry adds its terms to both sides.
pub proof fn lemma_sums_push(x: Ctx, gids: Seq<usize>, ng: usize, ent: Seq<usize>, ca: int, row: usize)
    requires sums_rel(x, gids, ng, ent, ca, row as int), ca <= row,
    ensures sums_rel(x, gids, ng, ent.push(row), ca, row as int + 1),
{
    let e2 = ent.push(row);
    assert forall|g: int| 0 <= g < ng implies {
        &&& #[trigger] esum(x, gids, g, e2, e2.len() as int) == gsum_r(x.sv, x.rp, x.pd, x.t, gids, g, ca, row as int + 1)
        &&& eabs(x, gids, g, e2, e2.len() as int) == gabs_r(x.sv, x.rp, x.pd, x.t, gids, g, ca, row as int + 1)
        &&& ecnt(x, gids, g, e2, e2.len() as int) == gcnt_r(x.sv, x.rp, x.pd, x.t, gids, g, ca, row as int + 1)
    } by {
        lemma_range_step(x.sv, x.rp, x.pd, x.t, gids, g, ca, row as int);
        lemma_esum_prefix(x, gids, g, ent, e2, ent.len() as int);
        assert(e2[ent.len() as int] == row);
    }
}

/// Rows `[r0, r1)` whose keys lie in a safe interval add nothing.
pub proof fn lemma_skip_rows(sh: Shared, x: Ctx, ent: Seq<usize>, ca: int, r0: int, r1: int, lo: int, hi: int)
    requires
        shared_ok(sh, x), sh.fast, safe(x, lo, hi),
        0 <= ca <= r0 <= r1 <= nl(x.sv),
        forall|c: int| r0 <= c < r1 ==> lo <= #[trigger] l_ok(x.sv)[c] < hi,
        sums_rel(x, sh.gids@, sh.ng, ent, ca, r0),
    ensures sums_rel(x, sh.gids@, sh.ng, ent, ca, r1),
    decreases r1 - r0,
{
    if r1 > r0 {
        lemma_skip_rows(sh, x, ent, ca, r0, r1 - 1, lo, hi);
        let c = r1 - 1;
        assert(lo <= l_ok(x.sv)[c] < hi);
        assert forall|j: int| 0 <= j < no(x.sv) && #[trigger] o_ok(x.sv)[j] == l_ok(x.sv)[c]
            implies ord_code(x.sv, x.slots, x.pd, x.t, j) == NONE by {
        }
        lemma_no_code_order(x.sv, x.rp, x.pd, x.t, sh.gids@, x.slots, sh.gos@, c);
        lemma_sums_skip(x, sh.gids@, sh.ng, ent, ca, c);
    }
}

// ------------------------------------------------------------------------------------------ executable pieces

/// A start position for the merge at key `k` in `keys[0..n)`: `p > 0` only when the key before it is below `k`
/// (the first position not below `k` when the list ascends).
fn start_pos(keys: &Vec<i64>, n: usize, k: i64) -> (p: usize)
    requires n <= keys@.len(),
    ensures p <= n, p > 0 ==> keys@[p - 1] < k,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while lo < hi
        invariant lo <= hi <= n, n <= keys@.len(), lo > 0 ==> keys@[lo - 1] < k,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if keys[mid] < k { lo = mid + 1; } else { hi = mid; }
    }
    lo
}

/// Merges the lineitem rows `[ca, cb)` against a chunk's list `keys[0..nk)` with bounds `[klo, khi)` (fast mode).
fn merge_rows(sh: &Shared, keys: &Vec<i64>, codes: &Vec<u8>, nk: usize, klo: i64, khi: i64, ca: usize, cb: usize,
    b: &mut Buf, accs: &mut Vec<Acc>, Ghost(x): Ghost<Ctx>, Ghost(ent): Ghost<Seq<usize>>) -> (ent2: Ghost<Seq<usize>>)
    requires
        shared_ok(*sh, x), sh.fast, chunk_ok(x, keys@, codes@, nk as int, klo as int, khi as int),
        nk <= keys@.len(), nk <= codes@.len(),
        ca <= cb <= sh.c.nl,
        buf_ok(*old(b), *sh, x, ent),
        accs_rel(old(accs)@, x, sh.gids@, sh.ng, ent, ent.len() - old(b).nr),
        sums_rel(x, sh.gids@, sh.ng, ent, ca as int, ca as int),
    ensures
        buf_ok(*final(b), *sh, x, ent2@),
        accs_rel(final(accs)@, x, sh.gids@, sh.ng, ent2@, ent2@.len() - final(b).nr),
        sums_rel(x, sh.gids@, sh.ng, ent2@, ca as int, cb as int),
    no_unwind
{
    hide(shared_ok);
    hide(buf_ok);
    hide(accs_rel);
    hide(sums_rel);
    hide(safe);
    hide(chunk_ok);
    let ghost sv = x.sv;
    let ghost e0 = ent;
    if ca == cb {
        return Ghost(e0);
    }
    let lok = sh.c.lok;
    assert(lok@ == l_ok(sv) && lok@.len() == sh.c.nl) by { reveal(shared_ok); }
    let mut p = start_pos(keys, nk, lok[ca]);
    let mut lo: i64 = if p > 0 { keys[p - 1] + 1 } else { klo };
    let mut hi: i64 = if p < nk { keys[p] } else { khi };
    let mut row = ca;
    let ghost mut e = ent;
    while row < cb
        invariant
            shared_ok(*sh, x), sh.fast, sv == x.sv, chunk_ok(x, keys@, codes@, nk as int, klo as int, khi as int),
            lok@ == l_ok(sv), lok@.len() == sh.c.nl, nk <= keys@.len(), nk <= codes@.len(),
            ca <= row <= cb <= sh.c.nl, p <= nk,
            lo as int == lo_in(keys@, klo as int, p as int), hi as int == hi_in(keys@, nk as int, khi as int, p as int),
            sums_rel(x, sh.gids@, sh.ng, e, ca as int, row as int),
            buf_ok(*b, *sh, x, e),
            accs_rel(accs@, x, sh.gids@, sh.ng, e, e.len() - b.nr),
        decreases cb - row, nk - p,
    {
        // The rows whose keys lie in the safe interval: whole blocks with one vector test each, then key by key.
        let r2 = skip_to(lok, row, cb, lo, hi);
        proof {
            lemma_safe_in(x, keys@, codes@, nk as int, klo as int, khi as int, p as int);
            lemma_skip_rows(*sh, x, e, ca as int, row as int, r2 as int, lo as int, hi as int);
        }
        row = r2;
        if row < cb {
            let k = lok[row];
            if k == hi && p < nk {
                // The rows of the qualifying order with key `hi`, each an entry with its code.
                let code = codes[p];
                proof {
                    reveal(chunk_ok);
                    assert(qkey_at(x, keys@[p as int], codes@[p as int]));
                }
                while row < cb && lok[row] == hi
                    invariant
                        shared_ok(*sh, x), sh.fast, sv == x.sv, lok@ == l_ok(sv), lok@.len() == sh.c.nl,
                        r2 <= row <= cb <= sh.c.nl, ca <= r2, lok@[r2 as int] == hi,
                        qkey_at(x, hi, code),
                        sums_rel(x, sh.gids@, sh.ng, e, ca as int, row as int),
                        buf_ok(*b, *sh, x, e),
                        accs_rel(accs@, x, sh.gids@, sh.ng, e, e.len() - b.nr),
                    decreases cb - row,
                {
                    proof {
                        assert(entry_ok(x, row as int, code));
                        lemma_sums_push(x, sh.gids@, sh.ng, e, ca as int, row);
                    }
                    push_entry(sh, b, accs, row, code, Ghost(x), Ghost(e));
                    proof { e = e.push(row); }
                    row = row + 1;
                }
            } else if k > hi && p < nk {
                lo = hi + 1;
                p = p + 1;
                hi = if p < nk { keys[p] } else { khi };
            } else {
                proof { lemma_sums_push(x, sh.gids@, sh.ng, e, ca as int, row); }
                push_entry(sh, b, accs, row, SLOW, Ghost(x), Ghost(e));
                proof { e = e.push(row); }
                row = row + 1;
            }
        }
    }
    Ghost(e)
}

// ------------------------------------------------------------------------------------------ the task

pub struct LineTask {
    pub sh: Arc<Shared>,
    pub keys: Vec<i64>,
    pub codes: Vec<u8>,
    pub nk: usize,
    pub klo: i64,
    pub khi: i64,
    pub ca: usize,
    pub cb: usize,
    pub fast: bool,
    pub buf: Buf,
    pub accs: Vec<Acc>,
    pub x: Ghost<Ctx>,
}

pub struct LineOut {
    pub accs: Vec<Acc>,
}

/// The task's result: every accumulator holds its group's sums over `[ca, cb)`.
pub open spec fn line_post(sh: Shared, x: Ctx, ca: int, cb: int, out: LineOut) -> bool {
    &&& out.accs@.len() == sh.ng
    &&& forall|g: int| 0 <= g < sh.ng ==> acc_ok(#[trigger] out.accs@[g],
        gsum_r(x.sv, x.rp, x.pd, x.t, sh.gids@, g, ca, cb), gabs_r(x.sv, x.rp, x.pd, x.t, sh.gids@, g, ca, cb),
        gcnt_r(x.sv, x.rp, x.pd, x.t, sh.gids@, g, ca, cb))
}

/// The task's input: shared state, its chunk's key list (fast mode), the row range, an empty buffer, zero
/// accumulators.
pub open spec fn line_pre(sh: Shared, x: Ctx, keys: Seq<i64>, codes: Seq<u8>, nk: int, klo: int, khi: int, ca: int, cb: int,
    fast: bool, buf: Buf, accs: Seq<Acc>) -> bool {
    &&& shared_ok(sh, x)
    &&& fast ==> sh.fast && chunk_ok(x, keys, codes, nk, klo, khi) && nk <= keys.len() && nk <= codes.len()
    &&& 0 <= ca <= cb <= sh.c.nl
    &&& buf.rrow@.len() == CAP && buf.rcode@.len() == CAP && buf.rsc@.len() == CAP && buf.rsk@.len() == CAP && buf.nr == 0
    &&& accs.len() == sh.ng
    &&& forall|g: int| 0 <= g < sh.ng ==> acc_ok(#[trigger] accs[g], 0, 0, 0)
}

impl WorkerTask for LineTask {
    type Output = LineOut;

    open spec fn pre(&self) -> bool {
        line_pre(*self.sh, self.x@, self.keys@, self.codes@, self.nk as int, self.klo as int, self.khi as int,
            self.ca as int, self.cb as int, self.fast, self.buf, self.accs@)
    }

    open spec fn post(&self, out: LineOut) -> bool {
        line_post(*self.sh, self.x@, self.ca as int, self.cb as int, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.ca as u64, self.cb as u64)
    }

    fn run(self) -> (out: LineOut) {
        hide(buf_ok);
        hide(sums_rel);
        let LineTask { sh, keys, codes, nk, klo, khi, ca, cb, fast, buf, accs, x } = self;
        let shr: &Shared = &*sh;
        let mut buf = buf;
        let mut accs = accs;
        let ghost xv = x@;
        let ghost sv = xv.sv;
        let ghost mut ent: Seq<usize> = Seq::empty();
        proof {
            assert forall|g: int| 0 <= g < shr.ng implies acc_ok(#[trigger] accs@[g], esum(xv, shr.gids@, g, ent, 0),
                eabs(xv, shr.gids@, g, ent, 0), ecnt(xv, shr.gids@, g, ent, 0)) by {}
            assert(sums_rel(xv, shr.gids@, shr.ng, ent, ca as int, ca as int)) by {
                reveal(sums_rel);
                assert forall|g: int| 0 <= g < shr.ng implies {
                    &&& #[trigger] esum(xv, shr.gids@, g, ent, ent.len() as int) == gsum_r(sv, xv.rp, xv.pd, xv.t, shr.gids@, g, ca as int, ca as int)
                    &&& eabs(xv, shr.gids@, g, ent, ent.len() as int) == gabs_r(sv, xv.rp, xv.pd, xv.t, shr.gids@, g, ca as int, ca as int)
                    &&& ecnt(xv, shr.gids@, g, ent, ent.len() as int) == gcnt_r(sv, xv.rp, xv.pd, xv.t, shr.gids@, g, ca as int, ca as int)
                } by {}
            }
        }
        assert(buf_ok(buf, *shr, xv, ent)) by { reveal(buf_ok); }
        if fast {
            let g2 = merge_rows(shr, &keys, &codes, nk, klo, khi, ca, cb, &mut buf, &mut accs, Ghost(xv), Ghost(ent));
            proof { ent = g2@; }
        } else {
            let mut row = ca;
            while row < cb
                invariant
                    shared_ok(*shr, xv), sv == xv.sv, ca <= row <= cb <= shr.c.nl,
                    buf_ok(buf, *shr, xv, ent),
                    accs_rel(accs@, xv, shr.gids@, shr.ng, ent, ent.len() - buf.nr),
                    sums_rel(xv, shr.gids@, shr.ng, ent, ca as int, row as int),
                decreases cb - row,
            {
                proof { lemma_sums_push(xv, shr.gids@, shr.ng, ent, ca as int, row); }
                push_entry(shr, &mut buf, &mut accs, row, SLOW, Ghost(xv), Ghost(ent));
                proof { ent = ent.push(row); }
                row = row + 1;
            }
        }
        proof { reveal(buf_ok); }
        flush(shr, &mut buf, &mut accs, Ghost(xv), Ghost(ent));
        proof {
            reveal(sums_rel);
            assert forall|g: int| 0 <= g < shr.ng implies acc_ok(#[trigger] accs@[g],
                gsum_r(sv, xv.rp, xv.pd, xv.t, shr.gids@, g, ca as int, cb as int), gabs_r(sv, xv.rp, xv.pd, xv.t, shr.gids@, g, ca as int, cb as int),
                gcnt_r(sv, xv.rp, xv.pd, xv.t, shr.gids@, g, ca as int, cb as int)) by {
                assert(acc_ok(accs@[g], esum(xv, shr.gids@, g, ent, ent.len() as int), eabs(xv, shr.gids@, g, ent, ent.len() as int),
                    ecnt(xv, shr.gids@, g, ent, ent.len() as int)));
            }
        }
        LineOut { accs }
    }
}

} // verus!
