//! Phase 1 of the fast path (co-clustered layout): one task per range of orders positions `[o_lo, o_hi)` with its
//! lineitem rows `[l_lo, l_hi)`. The rows are consumed in chunks of at most `runs::CH` rows of one fast block: the
//! chunk's key runs and running totals are built branch-free (`runs::build_runs`), then each run is added to its
//! order (`take_chunk` / `take_run`); `seek` closes the orders before a run's key (co-clustering: the order position
//! of the rows never decreases). Rows of other blocks take the exact `i128` step (`take_row`). Closing an order
//! (`close_next`) appends, when it is dated in the window, has a returned lineitem and its customer exists, the packed
//! record (customer row, revenue) to the segment of the customer's partition (`part`) in the preallocated flat buffer
//! and adds the order's absolute revenue to the mass. The consumer state is `Cur` with invariant `cur_ok`. The result
//! satisfies `part::parts_ok` over the range, unless (`big`) the mass would leave `i64`, a revenue leaves the packed
//! range or a segment is full (then the general path runs).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::kernel::*;
use super::recs::*;
use super::part::*;
use super::runs::*;

verus! {

/// The orders positions `[o_lo, o_hi)` of one task, whose lineitem rows are `[l_lo, l_hi)` (co-clustered), with
/// preallocated flat record buffers of `np` segments of `cap` slots and zeroed segment counts.
pub struct Chunk {
    pub cols: Cols,
    pub o_lo: usize,
    pub o_hi: usize,
    pub l_lo: usize,
    pub l_hi: usize,
    pub np: usize,
    pub cap: usize,
    pub rp: Vec<u64>,
    pub cnt: Vec<usize>,
    pub gt: Vec<Slot>,
    pub m: Ghost<M>,
    pub p: Ghost<QP>,
}

/// A task's partitioned records (segment `pp`: `(rc, rr)[pp * cap, pp * cap + cnt[pp])`) and their mass, or `big`.
pub struct ChunkOut {
    pub rp: Vec<u64>,
    pub cnt: Vec<usize>,
    pub cap: usize,
    pub mass: u64,
    pub big: bool,
}

pub open spec fn chunk_pre(t: Chunk) -> bool {
    let m = t.m@;
    let p = t.p@;
    &&& cols_ok(t.cols, m, p)
    &&& model_ok(m)
    &&& m.cluster == 1
    &&& m.c_n <= u32::MAX + 1
    &&& m.c_n <= MAX_CUST
    &&& 1 <= t.np <= MAX_NP
    &&& t.np * PW >= m.c_n
    &&& t.cap <= u32::MAX
    &&& t.o_lo <= t.o_hi <= m.o_n
    &&& t.rp@.len() >= t.np * t.cap
    &&& t.cnt@.len() >= t.np
    &&& forall|i: int| 0 <= i < t.cnt@.len() ==> #[trigger] t.cnt@[i] == 0
    &&& t.gt@.len() == CH_SLOTS
    &&& t.l_lo <= t.l_hi <= m.l_n
    &&& lb_ok(m, t.o_lo as int, t.l_lo as int)
    &&& lb_ok(m, t.o_hi as int, t.l_hi as int)
}

pub open spec fn chunk_post(t: Chunk, out: ChunkOut) -> bool {
    let m = t.m@;
    let p = t.p@;
    !out.big ==> {
        &&& out.mass <= i64::MAX
        &&& out.cap == t.cap
        &&& parts_ok(m, p, rcv(out.rp@), rrv(out.rp@), out.cnt@, t.cap as int, t.np as int, t.o_lo as int, t.o_hi as int, out.mass as int)
    }
}

/// An order counted for no customer: every partition stays, the mass may grow.
proof fn lemma_parts_skip(m: M, p: QP, rc: Seq<u32>, rr: Seq<i64>, cnt: Seq<usize>, cap: int, np: int, lo: int, q: int,
    mass: int, mass2: int)
    requires
        model_ok(m),
        0 <= lo <= q < m.o_n,
        np * PW >= m.c_n,
        parts_ok(m, p, rc, rr, cnt, cap, np, lo, q, mass),
        mass <= mass2,
        forall|c: int| 0 <= c < m.c_n ==> !(#[trigger] ohit(m, p, c, q)) || lcnt(m, q) <= 0,
    ensures parts_ok(m, p, rc, rr, cnt, cap, np, lo, q + 1, mass2),
{
    assert forall|pp: int| 0 <= pp < np implies #[trigger] part_ok(m, p, rc, rr, cnt, cap, pp, lo, q + 1, mass2) by {
        assert(part_ok(m, p, rc, rr, cnt, cap, pp, lo, q, mass));
        lemma_plo_mono(m, pp, pp + 1);
        lemma_precs_skip(m, p, seg(rc, pp, cap), seg(rr, pp, cap), cnt[pp] as int, lo, q, mass, mass2,
            plo(m, pp), plo(m, pp + 1));
    }
}

/// The order at `q` of customer `cp` appended as the next record of its partition `pp0`.
proof fn lemma_parts_add(m: M, p: QP, rc: Seq<u32>, rr: Seq<i64>, cnt: Seq<usize>, rc2: Seq<u32>, rr2: Seq<i64>,
    cnt2: Seq<usize>, cap: int, np: int, lo: int, q: int, mass: int, pp0: int, cp: int, rev: int, ab: int)
    requires
        model_ok(m),
        0 <= lo <= q < m.o_n,
        np * PW >= m.c_n,
        m.c_n <= u32::MAX + 1,
        parts_ok(m, p, rc, rr, cnt, cap, np, lo, q, mass),
        0 <= pp0 < np,
        cap <= u32::MAX,
        cnt[pp0] < cap,
        rc2 == rc.update(pp0 * cap + cnt[pp0], cp as u32),
        rr2 == rr.update(pp0 * cap + cnt[pp0], rev as i64),
        cnt2 == cnt.update(pp0, (cnt[pp0] + 1) as usize),
        0 <= cp < m.c_n,
        plo(m, pp0) <= cp < plo(m, pp0 + 1),
        i64::MIN <= rev <= i64::MAX,
        ohit(m, p, cp, q),
        lcnt(m, q) > 0,
        rev == lsum(m, q), ab == labs(m, q),
    ensures parts_ok(m, p, rc2, rr2, cnt2, cap, np, lo, q + 1, mass + ab),
{
    lemma_labs_lsum(m, q);
    let at = pp0 * cap + cnt[pp0];
    lemma_seg_slots(pp0, pp0, cap, np);
    assert(at < rc.len() && at < rr.len() && pp0 < cnt.len());
    assert(rc2.len() == rc.len() && rr2.len() == rr.len() && cnt2.len() == cnt.len());
    assert forall|pp: int| 0 <= pp < np implies #[trigger] part_ok(m, p, rc2, rr2, cnt2, cap, pp, lo, q + 1, mass + ab) by {
        assert(part_ok(m, p, rc, rr, cnt, cap, pp, lo, q, mass));
        lemma_seg_slots(pp, pp0, cap, np);
        lemma_plo_mono(m, pp, pp + 1);
        lemma_plo_mono(m, pp + 1, np);
        lemma_plo_mono(m, pp0, pp0 + 1);
        let (s, s2) = (seg(rc, pp, cap), seg(rc2, pp, cap));
        let (t, t2) = (seg(rr, pp, cap), seg(rr2, pp, cap));
        if pp == pp0 {
            assert(s2 =~= s.update(cnt[pp0] as int, cp as u32));
            assert(t2 =~= t.update(cnt[pp0] as int, rev as i64));
            lemma_precs_add(m, p, s, t, s2, t2, cnt[pp0] as int, lo, q, mass, plo(m, pp), plo(m, pp + 1), cp, rev, ab);
            assert(cnt2[pp] == cnt[pp0] + 1);
        } else {
            assert(s2 =~= s);
            assert(t2 =~= t);
            assert(cnt2[pp] == cnt[pp]);
            assert forall|c: int| plo(m, pp) <= c < plo(m, pp + 1) implies !(#[trigger] ohit(m, p, c, q)) || lcnt(m, q) <= 0 by {
                lemma_part_disjoint(m, pp, pp0, c, cp);
                assert(ckey(m, c) != ckey(m, cp));
            }
            lemma_precs_skip(m, p, s, t, cnt[pp] as int, lo, q, mass, mass + ab, plo(m, pp), plo(m, pp + 1));
        }
    }
}

/// An order's revenue is bounded by its absolute revenue; with no returned lineitem both are zero and the count
/// is not positive only then.
pub proof fn lemma_labs_lsum(m: M, q: int)
    requires m.l_n >= 0,
    ensures
        abs(lsum(m, q)) <= labs(m, q),
        lcnt(m, q) >= 0,
        labs(m, q) >= 0,
{
    assert forall|j: int| 0 <= j < m.l_n implies abs(#[trigger] lsum_f(m, q)(j)) <= labs_f(m, q)(j) by {}
    lemma_dsum_abs(lsum_f(m, q), labs_f(m, q), 0, m.l_n);
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] lcnt_f(m, q)(j) >= 0 by {}
    lemma_isum_nonneg(0, m.l_n, lcnt_f(m, q));
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] labs_f(m, q)(j) >= 0 by {}
    lemma_isum_nonneg(0, m.l_n, labs_f(m, q));
}

/// Without a counted lineitem the order's sums are zero.
pub proof fn lemma_lcnt_zero(m: M, q: int)
    requires lcnt(m, q) <= 0,
    ensures labs(m, q) == 0, lsum(m, q) == 0,
{
    assert forall|j: int| 0 <= j < m.l_n implies !lhit(m, q, j) by {
        if lhit(m, q, j) {
            assert forall|t: int| 0 <= t < m.l_n implies #[trigger] lcnt_f(m, q)(t) >= 0 by {}
            lemma_isum_ge_term(m.l_n, lcnt_f(m, q), j);
        }
    }
    lemma_isum_zero(m.l_n, labs_f(m, q));
    lemma_isum_zero(m.l_n, lsum_f(m, q));
}

/// The fixed parameters of one task (a copy of the task's fields without its buffers).
#[derive(Clone, Copy)]
pub struct Span {
    pub cols: Cols,
    pub o_lo: usize,
    pub o_hi: usize,
    pub l_lo: usize,
    pub l_hi: usize,
    pub np: usize,
    pub cap: usize,
    pub m: Ghost<M>,
    pub p: Ghost<QP>,
}

/// The consumer state of one task: the current order `q` (its block cursor `og`/`oge` and, when `q < o_hi`, its
/// key, customer key and date), the sums of its rows consumed so far, the records of the orders before it and their
/// mass.
pub struct Cur {
    pub q: usize,
    pub og: usize,
    pub oge: u64,
    pub okv: i64,
    pub ocv: i64,
    pub odv: i64,
    pub cnt: u64,
    pub sum: i128,
    pub ab: u128,
    pub ovf: bool,
    pub mass: u64,
    pub rp: Vec<u64>,
    pub cv: Vec<usize>,
}

/// `q` is the current order: rows before `jq` belong to earlier orders, rows `[jq, j)` to `q` (their sums are the
/// pending ones), rows from `j` to `q` or later orders; the orders before `q` are recorded.
pub open spec fn cur_ok(m: M, p: QP, t: Span, cur: Cur, jq: int, j: int) -> bool {
    &&& t.o_lo <= cur.q <= t.o_hi
    &&& m.o_bs >= 1
    &&& cur.q < t.o_hi ==> {
        &&& cur.og * m.o_bs <= cur.q < cur.oge
        &&& cur.oge == (cur.og + 1) * m.o_bs
        &&& cur.okv as int == okey(m, cur.q as int)
        &&& cur.ocv as int == ocust(m, cur.q as int)
        &&& cur.odv as int == odate(m, cur.q as int)
    }
    &&& cur.oge <= m.o_n + m.o_bs
    &&& t.l_lo <= jq <= j <= t.l_hi
    &&& forall|r: int| 0 <= r < jq ==> #[trigger] lpos(m, r) < cur.q
    &&& forall|r: int| jq <= r < j ==> #[trigger] lpos(m, r) == cur.q
    &&& forall|r: int| j <= r < m.l_n ==> #[trigger] lpos(m, r) >= cur.q
    &&& acc_ok(m, cur.q as int, jq, j, cur.cnt, cur.sum, cur.ab, cur.ovf)
    &&& cur.mass <= i64::MAX
    &&& parts_ok(m, p, rcv(cur.rp@), rrv(cur.rp@), cur.cv@, t.cap as int, t.np as int, t.o_lo as int, cur.q as int, cur.mass as int)
}

/// The fixed facts of a task (`chunk_pre` without the buffers).
pub open spec fn task_ok(t: Span) -> bool {
    let m = t.m@;
    let p = t.p@;
    &&& cols_ok(t.cols, m, p)
    &&& model_ok(m)
    &&& m.cluster == 1
    &&& m.c_n <= u32::MAX + 1
    &&& m.c_n <= MAX_CUST
    &&& 1 <= t.np <= MAX_NP
    &&& t.np * PW >= m.c_n
    &&& t.cap <= u32::MAX
    &&& t.o_lo <= t.o_hi <= m.o_n
    &&& t.l_lo <= t.l_hi <= m.l_n
    &&& lb_ok(m, t.o_lo as int, t.l_lo as int)
    &&& lb_ok(m, t.o_hi as int, t.l_hi as int)
}

/// The order values at `q < o_hi` with its block cursor (moved to the next block when `q` starts it).
#[inline(always)]
fn load_order(c: &Cols, q: usize, og: usize, oge: u64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: (usize, u64, i64, i64, i64))
    requires
        cols_ok(*c, m, p), model_ok(m), q < m.o_n,
        m.o_bs >= 1, og * m.o_bs <= q <= oge, oge == (og + 1) * m.o_bs,
    ensures
        r.0 * m.o_bs <= q < r.1, r.1 == (r.0 + 1) * m.o_bs, r.1 <= m.o_n + m.o_bs,
        r.2 as int == okey(m, q as int), r.3 as int == ocust(m, q as int), r.4 as int == odate(m, q as int),
    no_unwind
{
    let mut og = og;
    let mut oge = oge;
    if q as u64 == oge {
        proof {
            assert((og + 2) * m.o_bs == (og + 1) * m.o_bs + m.o_bs) by (nonlinear_arith);
            assert(og < q) by (nonlinear_arith) requires og * m.o_bs <= q, m.o_bs >= 1, og >= 0, q == (og + 1) * m.o_bs;
        }
        og = og + 1;
        oge = oge + c.o_bs;
    }
    proof {
        lemma_div_in(q as int, m.o_bs, og as int);
        lemma_block_bound(q as int, m.o_bs, m.o_n, m.o_nb);
        assert(og * m.o_bs <= q);
        assert(oge == og * m.o_bs + m.o_bs) by (nonlinear_arith) requires oge == (og + 1) * m.o_bs;
    }
    let (okv, ocv, odv) = order_at(c, q, og, Ghost(m), Ghost(p));
    (og, oge, okv, ocv, odv)
}

/// Close the current order `q` (every later row belongs to a later order): record it when it is dated in the window,
/// has a returned lineitem and its customer exists, then make `q + 1` current with no rows. `true`: `big` (a full
/// segment or a mass outside `i64`).
#[inline(always)]
fn close_next(t: &Span, cur: &mut Cur, Ghost(jq): Ghost<int>, Ghost(j): Ghost<int>) -> (big: bool)
    requires
        task_ok(*t),
        cur_ok(t.m@, t.p@, *t, *old(cur), jq, j),
        old(cur).q < t.o_hi,
        forall|r: int| j <= r < t.m@.l_n ==> #[trigger] lpos(t.m@, r) > old(cur).q,
    ensures
        !big ==> cur_ok(t.m@, t.p@, *t, *final(cur), j, j) && final(cur).q == old(cur).q + 1,
    no_unwind
{
    let ghost m = t.m@;
    let ghost p = t.p@;
    let c = &t.cols;
    let q = cur.q;
    let np = t.np;
    let cap = t.cap;
    proof {
        // the order's rows are exactly [jq, j)
        assert forall|r: int| 0 <= r < m.l_n && (r < jq || r >= j) implies lkey(m, r) != okey(m, q as int) by {
            lemma_lpos_key(m, q as int, r);
        }
        lemma_run_totals(m, q as int, jq, j);
    }
    let n = cur.cnt;
    let sum = cur.sum;
    let ab = cur.ab;
    let ovf = cur.ovf;
    let mut recorded = false;
    if n > 0 && cur.odv >= c.lo && cur.odv <= c.hi {
        match cust_find(c, cur.ocv, Ghost(m), Ghost(p)) {
            Some(cp) => {
                let mass = cur.mass;
                if ovf || ab > (0x7fff_ffff_ffff_ffffu64 - mass) as u128 {
                    return true;
                }
                let pp = cp / PW;
                proof {
                    lemma_part_of(m, cp as int, np as int);
                    lemma_seg_slots(pp as int, pp as int, cap as int, np as int);
                    assert(part_ok(m, p, rcv(cur.rp@), rrv(cur.rp@), cur.cv@, cap as int, pp as int, t.o_lo as int, q as int, mass as int));
                }
                let k = cur.cv[pp];
                let rlen = cur.rp.len();
                proof {
                    assert(pp * cap + cap <= np * cap);
                    assert(np * cap <= rlen);
                }
                if k >= cap || sum < -(RB as i128) || sum >= RB as i128 {
                    return true;
                }
                let at = pp * cap + k;
                let ghost (rp0, cnt0) = (cur.rp@, cur.cv@);
                proof {
                    lemma_labs_lsum(m, q as int);
                }
                let x = pack(cp as u64, sum as i64);
                put(&mut cur.rp, at, x);
                put(&mut cur.cv, pp, k + 1);
                proof {
                    lemma_pack_update(rp0, at as int, x, cp as int, sum as int);
                    lemma_parts_add(m, p, rcv(rp0), rrv(rp0), cnt0, rcv(cur.rp@), rrv(cur.rp@), cur.cv@, cap as int, np as int, t.o_lo as int,
                        q as int, mass as int, pp as int, cp as int, sum as int, ab as int);
                }
                cur.mass = mass + ab as u64;
                recorded = true;
            },
            None => {},
        }
    }
    if !recorded {
        proof {
            assert forall|c2: int| 0 <= c2 < m.c_n implies !(#[trigger] ohit(m, p, c2, q as int)) || lcnt(m, q as int) <= 0 by {}
            lemma_parts_skip(m, p, rcv(cur.rp@), rrv(cur.rp@), cur.cv@, cap as int, np as int, t.o_lo as int, q as int,
                cur.mass as int, cur.mass as int);
        }
    }
    let q1 = q + 1;
    if q1 < t.o_hi {
        let r = load_order(c, q1, cur.og, cur.oge, Ghost(m), Ghost(p));
        cur.og = r.0;
        cur.oge = r.1;
        cur.okv = r.2;
        cur.ocv = r.3;
        cur.odv = r.4;
    }
    cur.q = q1;
    cur.cnt = 0;
    cur.sum = 0;
    cur.ab = 0;
    cur.ovf = false;
    proof {
        assert forall|r: int| 0 <= r < j implies #[trigger] lpos(m, r) < q1 by {
            if r >= jq {
                assert(lpos(m, r) == q);
            }
        }
        assert forall|r: int| j <= r < m.l_n implies #[trigger] lpos(m, r) >= q1 by {
            assert(lpos(m, r) > q);
        }
    }
    false
}

/// A row `r < l_hi` at or after the cursor belongs to an order in `[q, o_hi)`; with another key than `q`'s, every row
/// from it on belongs to a later order.
proof fn lemma_row_later(t: Span, cur: Cur, jq: int, j: int, r: int)
    requires
        task_ok(t),
        cur_ok(t.m@, t.p@, t, cur, jq, j),
        j <= r < t.l_hi,
    ensures
        cur.q <= lpos(t.m@, r) < t.o_hi,
        cur.q < t.o_hi,
        lkey(t.m@, r) != okey(t.m@, cur.q as int) ==> forall|r2: int| r <= r2 < t.m@.l_n ==> #[trigger] lpos(t.m@, r2) > cur.q,
        lkey(t.m@, r) == okey(t.m@, cur.q as int) ==> lpos(t.m@, r) == cur.q,
{
    let m = t.m@;
    assert(lpos(m, r) < t.o_hi);
    assert(lpos(m, r) >= cur.q);
    lemma_lpos_key(m, cur.q as int, r);
    if lkey(m, r) != okey(m, cur.q as int) {
        assert forall|r2: int| r <= r2 < m.l_n implies #[trigger] lpos(m, r2) > cur.q by {
            lemma_lpos_mono(m, r, r2);
        }
    }
}

/// Make the order of row `r0` (key `k`) current: close every order before it.
#[inline(always)]
fn seek(t: &Span, cur: &mut Cur, k: i64, Ghost(jq): Ghost<int>, Ghost(r0): Ghost<int>) -> (r: (bool, Ghost<int>))
    requires
        task_ok(*t),
        cur_ok(t.m@, t.p@, *t, *old(cur), jq, r0),
        r0 < t.l_hi,
        lkey(t.m@, r0) == k as int,
    ensures
        !r.0 ==> cur_ok(t.m@, t.p@, *t, *final(cur), r.1@, r0) && lpos(t.m@, r0) == final(cur).q
            && final(cur).q < t.o_hi,
    no_unwind
{
    let ghost m = t.m@;
    let ghost mut jq2 = jq;
    proof { lemma_row_later(*t, *cur, jq2, r0, r0); }
    while cur.okv != k
        invariant
            task_ok(*t), t.m@ == m,
            r0 < t.l_hi,
            lkey(m, r0) == k as int,
            cur_ok(m, t.p@, *t, *cur, jq2, r0),
            cur.q <= lpos(m, r0) < t.o_hi,
        decreases lpos(m, r0) - cur.q,
    {
        proof { lemma_row_later(*t, *cur, jq2, r0, r0); }
        if close_next(t, cur, Ghost(jq2), Ghost(r0)) {
            return (true, Ghost(jq2));
        }
        proof {
            jq2 = r0;
            lemma_row_later(*t, *cur, jq2, r0, r0);
        }
    }
    proof { lemma_row_later(*t, *cur, jq2, r0, r0); }
    (false, Ghost(jq2))
}

/// Run `i` of a chunk `[j, e)` (rows `[st[i], st[i + 1])`) added to its order.
#[inline(always)]
fn take_run(t: &Span, cur: &mut Cur, gt: &Vec<Slot>, i: usize, j: usize,
    e: usize, Ghost(st): Ghost<Seq<int>>, Ghost(ng): Ghost<int>, Ghost(jq): Ghost<int>) -> (r: (bool, Ghost<int>))
    requires
        task_ok(*t),
        run_ok(t.m@, gt@, st, ng, j as int, e as int),
        gt@.len() == CH_SLOTS,
        j < e <= t.l_hi,
        e - j <= CH,
        i < ng,
        cur_ok(t.m@, t.p@, *t, *old(cur), jq, st[i as int]),
    ensures
        !r.0 ==> cur_ok(t.m@, t.p@, *t, *final(cur), r.1@, st[i + 1]),
    no_unwind
{
    let ghost m = t.m@;
    let ghost p = t.p@;
    let ghost mut jq2 = jq;
    let k = gt[i + 1].0;
    let ghost r0 = st[i as int];
    let ghost r1 = st[i as int + 1];
    proof {
        assert(lt_next(st, i as int));
        assert(j <= st[i as int] <= e && j <= st[i + 1] <= e);
        assert(keys_in(m, gt@[i + 1].0 as int, r0, r1));
        lemma_keys_at(m, gt@[i + 1].0 as int, r0, r1, r0);
    }
    let sk = seek(t, cur, k, Ghost(jq2), Ghost(r0));
    if sk.0 {
        return (true, Ghost(jq2));
    }
    proof {
        jq2 = sk.1@;
        lemma_row_later(*t, *cur, jq2, r0, r0);
        assert(tot_ok(m, j as int, r0, gt@[i as int].3, gt@[i as int].1, gt@[i as int].2));
        assert(tot_ok(m, j as int, r1, gt@[i + 1].3, gt@[i + 1].1, gt@[i + 1].2));
        lemma_lpos_key(m, cur.q as int, r0);
        assert forall|r: int| r0 <= r < r1 implies #[trigger] lkey(m, r) == okey(m, cur.q as int) by {
            lemma_keys_at(m, gt@[i + 1].0 as int, r0, r1, r);
        }
        assert forall|r: int| r0 <= r < r1 implies #[trigger] lpos(m, r) == cur.q by {
            assert(lkey(m, r) == okey(m, cur.q as int));
            lemma_lpos_key(m, cur.q as int, r);
        }
        assert forall|r: int| r1 <= r < m.l_n implies #[trigger] lpos(m, r) >= cur.q by {
            assert(lpos(m, r) >= cur.q);
        }
    }
    let a = acc_run(cur.cnt, cur.sum, cur.ab, cur.ovf, gt, i, Ghost(m), Ghost(cur.q as int),
        Ghost(jq2), Ghost(j as int), Ghost(r0), Ghost(r1));
    cur.cnt = a.0;
    cur.sum = a.1;
    cur.ab = a.2;
    cur.ovf = a.3;
    (false, Ghost(jq2))
}

/// The chunk `[j, e)` of fast block `lg`: its key runs (`runs::build_runs`), each added to its order.
fn take_chunk(t: &Span, cur: &mut Cur, gt: &mut Vec<Slot>,
    j: usize, e: usize, lg: usize, tgt: u16, pb: i64, db: i64, Ghost(jq): Ghost<int>) -> (r: (bool, Ghost<int>))
    requires
        task_ok(*t),
        cur_ok(t.m@, t.p@, *t, *old(cur), jq, j as int),
        j < e <= t.l_hi,
        lg < t.m@.l_nb,
        lg * t.m@.l_bs <= j && e <= (lg + 1) * t.m@.l_bs,
        e - j <= CH,
        fast_block(t.m@, lg as int), pb == t.m@.l_price_b[lg as int], db == t.m@.l_disc_b[lg as int],
        forall|r: int| 0 <= r < t.m@.l_n && r / t.m@.l_bs == lg ==>
            (#[trigger] lflag(t.m@, r) == r_text()) == (t.m@.l_rf_c[r] as int == tgt as int),
        old(gt)@.len() == CH_SLOTS,
    ensures
        final(gt)@.len() == CH_SLOTS,
        !r.0 ==> cur_ok(t.m@, t.p@, *t, *final(cur), r.1@, e as int),
    no_unwind
{
    let ghost m = t.m@;
    let ghost p = t.p@;
    let c = &t.cols;
    let kb = c.l_key_b[lg];
    let (ng, Ghost(st)) = build_runs(c, j, e, kb, tgt, pb, db, gt, Ghost(m), Ghost(p), Ghost(lg as int));
    let ghost mut jq2 = jq;
    let mut i: usize = 0;
    while i < ng
        invariant
            task_ok(*t), t.m@ == m, t.p@ == p, t.cols == *c,
            run_ok(m, gt@, st, ng as int, j as int, e as int),
            gt@.len() == CH_SLOTS,
            j < e <= t.l_hi,
            e - j <= CH,
            i <= ng,
            cur_ok(m, p, *t, *cur, jq2, st[i as int]),
        decreases ng - i,
    {
        let r = take_run(t, cur, gt, i, j, e, Ghost(st), Ghost(ng as int), Ghost(jq2));
        if r.0 {
            return (true, Ghost(jq2));
        }
        proof { jq2 = r.1@; }
        i = i + 1;
    }
    (false, Ghost(jq2))
}

/// Row `j` of block `lg` outside the `i64` arithmetic: the exact `i128` step for its order.
fn take_row(t: &Span, cur: &mut Cur, j: usize, lg: usize, tgt: u16, Ghost(jq): Ghost<int>) -> (r: (bool, Ghost<int>))
    requires
        task_ok(*t),
        cur_ok(t.m@, t.p@, *t, *old(cur), jq, j as int),
        j < t.l_hi,
        lg < t.m@.l_nb,
        j as int / t.m@.l_bs == lg,
        forall|r: int| 0 <= r < t.m@.l_n && r / t.m@.l_bs == lg ==>
            (#[trigger] lflag(t.m@, r) == r_text()) == (t.m@.l_rf_c[r] as int == tgt as int),
    ensures
        !r.0 ==> cur_ok(t.m@, t.p@, *t, *final(cur), r.1@, j + 1),
    no_unwind
{
    let ghost m = t.m@;
    let ghost p = t.p@;
    let c = &t.cols;
    proof { assert(in_i64(lkey(m, j as int))); }
    let k = c.l_key_b[lg] + c.l_key_c[j] as i64;
    let sk = seek(t, cur, k, Ghost(jq), Ghost(j as int));
    if sk.0 {
        return (true, Ghost(jq));
    }
    let ghost jq2 = sk.1@;
    proof {
        lemma_row_later(*t, *cur, jq2, j as int, j as int);
        assert forall|r: int| j + 1 <= r < m.l_n implies #[trigger] lpos(m, r) >= cur.q by {
            assert(lpos(m, r) >= cur.q);
        }
    }
    let hitj = c.l_rf_c[j] as u16 == tgt;
    let a: i128 = if hitj { row_arg(c, j, lg, Ghost(m), Ghost(p)) } else { 0 };
    let r = acc_row(cur.cnt, cur.sum, cur.ab, cur.ovf, hitj, a, Ghost(m), Ghost(cur.q as int), Ghost(jq2),
        Ghost(j as int));
    cur.cnt = r.0;
    cur.sum = r.1;
    cur.ab = r.2;
    cur.ovf = r.3;
    (false, Ghost(jq2))
}

impl WorkerTask for Chunk {
    type Output = ChunkOut;

    open spec fn pre(&self) -> bool {
        chunk_pre(*self)
    }

    open spec fn post(&self, out: ChunkOut) -> bool {
        chunk_post(*self, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.o_lo as u64, self.o_hi as u64)
    }

    fn run(self) -> (out: ChunkOut) {
        let ghost m = self.m@;
        let ghost p = self.p@;
        let c = self.cols;
        let o_lo = self.o_lo;
        let o_hi = self.o_hi;
        let l_lo = self.l_lo;
        let l_hi = self.l_hi;
        let np = self.np;
        let cap = self.cap;
        let t = Span { cols: self.cols, o_lo, o_hi, l_lo, l_hi, np, cap, m: self.m, p: self.p };
        let Chunk { rp, cnt, gt, .. } = self;
        let mut gt = gt;
        // the orders block cursor
        let og64 = (o_lo as u64) / c.o_bs;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(o_lo as int, m.o_bs);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(o_lo as int, m.o_bs);
            assert(m.o_bs * og64 == og64 * m.o_bs) by (nonlinear_arith);
            assert((og64 + 1) * m.o_bs == og64 * m.o_bs + m.o_bs) by (nonlinear_arith);
            assert(og64 <= o_lo) by (nonlinear_arith) requires og64 * m.o_bs <= o_lo, m.o_bs >= 1, og64 >= 0;
            if o_lo < m.o_n {
                lemma_block_bound(o_lo as int, m.o_bs, m.o_n, m.o_nb);
                lemma_div_in(o_lo as int, m.o_bs, og64 as int);
            }
        }
        let mut cur = Cur {
            q: o_lo, og: og64 as usize, oge: (og64 + 1) * c.o_bs, okv: 0, ocv: 0, odv: 0,
            cnt: 0, sum: 0, ab: 0, ovf: false, mass: 0, rp, cv: cnt,
        };
        if o_lo < o_hi {
            let r = load_order(&c, o_lo, cur.og, cur.oge, Ghost(m), Ghost(p));
            cur.og = r.0;
            cur.oge = r.1;
            cur.okv = r.2;
            cur.ocv = r.3;
            cur.odv = r.4;
        }
        // the lineitem block cursor
        let mut j = l_lo;
        let lg64 = (j as u64) / c.l_bs;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j as int, m.l_bs);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(j as int, m.l_bs);
            assert(m.l_bs * lg64 == lg64 * m.l_bs) by (nonlinear_arith);
            assert((lg64 + 1) * m.l_bs == lg64 * m.l_bs + m.l_bs) by (nonlinear_arith);
            assert(lg64 <= j) by (nonlinear_arith) requires lg64 * m.l_bs <= j, m.l_bs >= 1, lg64 >= 0;
        }
        let mut lg: usize = lg64 as usize;
        let mut lge: u64 = (lg64 + 1) * c.l_bs;
        let ghost mut jq: int = l_lo as int;
        proof {
            assert forall|pp: int| 0 <= pp < np implies #[trigger] part_ok(m, p, rcv(cur.rp@), rrv(cur.rp@), cur.cv@, cap as int, pp, o_lo as int, o_lo as int, 0) by {
                lemma_seg_slots(pp, pp, cap as int, np as int);
                lemma_precs_empty(m, p, seg(rcv(cur.rp@), pp, cap as int), seg(rrv(cur.rp@), pp, cap as int), o_lo as int, plo(m, pp), plo(m, pp + 1));
            }
            assert(np * cap >= 0) by (nonlinear_arith) requires np >= 0, cap >= 0;
            assert(task_ok(t));
            assert(cur_ok(m, p, t, cur, jq, j as int));
        }
        while j < l_hi
            invariant
                task_ok(t), t.m@ == m, t.p@ == p, t.cols == c, t.o_lo == o_lo, t.o_hi == o_hi, t.l_lo == l_lo,
                t.l_hi == l_hi, t.np == np, t.cap == cap,
                cur_ok(m, p, t, cur, jq, j as int),
                lcur_ok(m, j as int, lg as int, lge as int),
                gt@.len() == CH_SLOTS,
            decreases l_hi - j,
        {
            if j as u64 == lge {
                proof {
                    assert((lg + 2) * m.l_bs == (lg + 1) * m.l_bs + m.l_bs) by (nonlinear_arith);
                    assert(lg < j) by (nonlinear_arith) requires lg * m.l_bs <= j, m.l_bs >= 1, lg >= 0, j == (lg + 1) * m.l_bs;
                }
                lg = lg + 1;
                lge = lge + c.l_bs;
            }
            proof {
                lemma_div_in(j as int, m.l_bs, lg as int);
                lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
            }
            let bi = block_info(&c, lg, Ghost(m), Ghost(p));
            if bi.1 {
                let e0: usize = if lge < l_hi as u64 { lge as usize } else { l_hi };
                let e: usize = if e0 - j > CH { j + CH } else { e0 };
                let r = take_chunk(&t, &mut cur, &mut gt, j, e, lg, bi.0, bi.2, bi.3, Ghost(jq));
                if r.0 {
                    return ChunkOut { rp: cur.rp, cnt: cur.cv, cap, mass: cur.mass, big: true };
                }
                proof { jq = r.1@; }
                j = e;
            } else {
                let r = take_row(&t, &mut cur, j, lg, bi.0, Ghost(jq));
                if r.0 {
                    return ChunkOut { rp: cur.rp, cnt: cur.cv, cap, mass: cur.mass, big: true };
                }
                proof { jq = r.1@; }
                j = j + 1;
            }
        }
        // the remaining orders have no rows after the cursor
        while cur.q < o_hi
            invariant
                task_ok(t), t.m@ == m, t.p@ == p, t.o_hi == o_hi, t.l_hi == l_hi, t.cap == cap,
                cur_ok(m, p, t, cur, jq, l_hi as int),
            decreases o_hi - cur.q,
        {
            proof {
                assert forall|r: int| l_hi <= r < m.l_n implies #[trigger] lpos(m, r) > cur.q by {
                    assert(lpos(m, r) >= o_hi);
                }
            }
            if close_next(&t, &mut cur, Ghost(jq), Ghost(l_hi as int)) {
                return ChunkOut { rp: cur.rp, cnt: cur.cv, cap, mass: cur.mass, big: true };
            }
            proof { jq = l_hi as int; }
        }
        ChunkOut { rp: cur.rp, cnt: cur.cv, cap, mass: cur.mass, big: false }
    }
}

} // verus!
