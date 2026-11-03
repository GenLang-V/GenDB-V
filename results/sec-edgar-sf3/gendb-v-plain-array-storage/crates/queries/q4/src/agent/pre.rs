//! P1: the candidate pre rows (`nf::pre_cand`: `stmt = $2` and an adsh with a selected sub row), in row order,
//! each with its selected sub row and the hash of its `(tag, version)`.
//!
//! A task scans rows `lo..hi` into a preallocated buffer of `(row, sub row, hash)` triples; when the buffer is
//! full it stops at the first row it cannot record (`stopped`) and the calling thread finishes the range
//! (`scan_serial`). Consecutive rows of one filing share their adsh, so the last sub lookup is cached
//! (`cache_ok`): a row with the same adsh bytes reuses it.
use vstd::prelude::*;
use std::sync::Arc;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::buf::Buf;
use crate::agent::common::hash::*;
use crate::agent::common::chains::NONE;
use crate::agent::common::text::*;
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::sub::*;

verus! {

/// The candidate pre rows among `lo..hi`, in row order.
pub open spec fn cands_in(c: Ctx, lo: int, hi: int) -> Seq<int>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else {
        cands_in(c, lo, hi - 1) + if pre_cand(c, hi - 1) { seq![hi - 1] } else { Seq::<int>::empty() }
    }
}

/// The hash of the `(tag, version)` of pre row `l`.
pub open spec fn pre_tv_hash(c: Ctx, l: int) -> u64 {
    pair_hash_spec(1, p_tag(c, l), p_ver(c, l))
}

/// `out` lists the candidates among `lo..hi` with their sub rows and `(tag, version)` hashes.
pub open spec fn cands_ok(c: Ctx, out: Seq<(usize, usize, u64)>, lo: int, hi: int) -> bool {
    let cs = cands_in(c, lo, hi);
    &&& out.len() == cs.len()
    &&& forall|q: int| 0 <= q < cs.len() ==> {
        let (l, j, h) = #[trigger] out[q];
        &&& l as int == cs[q]
        &&& sub_of(c, j as int, p_adsh(c, l as int))
        &&& h == pre_tv_hash(c, l as int)
    }
}

/// The candidates among `lo..hi` are candidate rows of that range, in increasing order.
pub proof fn lemma_cands_mem(c: Ctx, lo: int, hi: int, q: int)
    requires 0 <= q < cands_in(c, lo, hi).len(),
    ensures
        lo <= cands_in(c, lo, hi)[q] < hi, pre_cand(c, cands_in(c, lo, hi)[q]),
        forall|q2: int| 0 <= q2 < q ==> cands_in(c, lo, hi)[q2] < cands_in(c, lo, hi)[q],
    decreases hi - lo,
{
    let pre = cands_in(c, lo, hi - 1);
    if q < pre.len() {
        assert(cands_in(c, lo, hi)[q] == pre[q]);
        lemma_cands_mem(c, lo, hi - 1, q);
        assert forall|q2: int| 0 <= q2 < q implies cands_in(c, lo, hi)[q2] < cands_in(c, lo, hi)[q] by {
            assert(cands_in(c, lo, hi)[q2] == pre[q2]);
        }
    } else {
        assert(cands_in(c, lo, hi)[q] == hi - 1);
        assert forall|q2: int| 0 <= q2 < q implies cands_in(c, lo, hi)[q2] < cands_in(c, lo, hi)[q] by {
            assert(cands_in(c, lo, hi)[q2] == pre[q2]);
            lemma_cands_mem(c, lo, hi - 1, q2);
        }
    }
}

/// Candidates of consecutive ranges concatenate.
pub proof fn lemma_cands_split(c: Ctx, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures cands_in(c, lo, hi) == cands_in(c, lo, mid) + cands_in(c, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_cands_split(c, lo, mid, hi - 1);
        assert(cands_in(c, lo, hi) =~= cands_in(c, lo, mid) + cands_in(c, mid, hi));
    } else {
        assert(cands_in(c, mid, hi) =~= Seq::<int>::empty());
        assert(cands_in(c, lo, hi) =~= cands_in(c, lo, mid) + cands_in(c, mid, hi));
    }
}

/// Candidate lists of consecutive ranges concatenate.
pub proof fn lemma_cands_ok_append(c: Ctx, a: Seq<(usize, usize, u64)>, b: Seq<(usize, usize, u64)>, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi, cands_ok(c, a, lo, mid), cands_ok(c, b, mid, hi),
    ensures cands_ok(c, a + b, lo, hi),
{
    lemma_cands_split(c, lo, mid, hi);
    let cs = cands_in(c, lo, hi);
    assert forall|q: int| 0 <= q < cs.len() implies {
        let (l, j, h) = #[trigger] (a + b)[q];
        &&& l as int == cs[q]
        &&& sub_of(c, j as int, p_adsh(c, l as int))
        &&& h == pre_tv_hash(c, l as int)
    } by {
        if q < a.len() {
            assert((a + b)[q] == a[q]);
        } else {
            assert((a + b)[q] == b[q - a.len()]);
        }
    }
}

/// The columns and index a pre scan reads.
pub struct PreScan {
    pub p_adsh: TextCol,
    pub p_stmt: TextCol,
    pub p_stmtv: &'static [u8],
    pub p_tag: TextCol,
    pub p_ver: TextCol,
    pub stmt: &'static [u8],
    pub stmt_len: usize,
    pub sx: Arc<SubIndex>,
}

#[verifier::opaque]
pub open spec fn pre_scan_ok(p: &PreScan, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& p.p_adsh@ == p_adsh_v(c) && p.p_stmt@ == p_stmt_v(c) && p.p_stmtv@ == p_stmtv_s(c)
    &&& p.p_tag@ == p_tag_v(c) && p.p_ver@ == p_ver_v(c)
    &&& p.stmt@ == c.stmt && p.stmt_len == c.stmt.len()
    &&& sub_index_ok(&*p.sx, c)
    &&& text_wf(p.p_adsh@, c.npre) && text_wf(p.p_stmt@, c.npre) && p.p_stmtv@.len() == c.npre
    &&& text_wf(p.p_tag@, c.npre) && text_wf(p.p_ver@, c.npre)
}

/// The last sub lookup: row `cache.0` (`NONE` before the first) gave `cache.1`.
pub open spec fn cache_ok(c: Ctx, cache: (usize, usize)) -> bool {
    cache.0 == NONE || ((cache.0 as int) < c.npre && sub_answer(c, cache.1, p_adsh(c, cache.0 as int)))
}

/// `j` is the selected sub row of adsh `a`, or `NONE` when there is none.
pub open spec fn sub_answer(c: Ctx, j: usize, a: Seq<u8>) -> bool {
    &&& j == NONE <==> !has_sub(c, a)
    &&& j != NONE ==> sub_of(c, j as int, a)
}

/// One row: its sub row when it is a candidate (`NONE` otherwise), and the updated cache.
fn pre_row(p: &PreScan, l: usize, cache: (usize, usize), Ghost(c): Ghost<Ctx>) -> (r: (usize, (usize, usize)))
    requires pre_scan_ok(p, c), (l as int) < c.npre, cache_ok(c, cache),
    ensures
        cache_ok(c, r.1),
        (r.0 != NONE) == pre_cand(c, l as int),
        r.0 != NONE ==> sub_of(c, r.0 as int, p_adsh(c, l as int)),
    no_unwind
{
    proof { reveal(pre_scan_ok); }
    if p.p_stmtv[l] == 0 {
        return (NONE, cache);
    }
    let (st, stl) = text_val(&p.p_stmt, l, Ghost(c.npre));
    if !bytes_eq(st, stl, p.stmt, p.stmt_len) {
        return (NONE, cache);
    }
    let (a, al) = text_val(&p.p_adsh, l, Ghost(c.npre));
    let mut hit = false;
    if cache.0 != NONE {
        let (ca, cal) = text_val(&p.p_adsh, cache.0, Ghost(c.npre));
        hit = bytes_eq(ca, cal, a, al);
    }
    let j = if hit {
        cache.1
    } else {
        let h = text_hash(0, a, al);
        sub_find(&*p.sx, a, al, h, Ghost(c))
    };
    (j, (l, j))
}

/// One pre scan task: rows `lo..hi` into `out`.
pub struct PreTask {
    pub lo: usize,
    pub hi: usize,
    pub scan: PreScan,
    pub out: Buf<(usize, usize, u64)>,
    pub ctx: Ghost<Ctx>,
}

pub struct PreOut {
    pub out: Buf<(usize, usize, u64)>,
    pub stopped: usize,
}

impl WorkerTask for PreTask {
    type Output = PreOut;

    open spec fn pre(&self) -> bool {
        &&& pre_scan_ok(&self.scan, self.ctx@)
        &&& self.lo <= self.hi && (self.hi as int) <= self.ctx@.npre
        &&& self.out.wf() && self.out.view().len() == 0
    }

    open spec fn post(&self, r: PreOut) -> bool {
        &&& r.out.wf()
        &&& self.lo <= r.stopped <= self.hi
        &&& cands_ok(self.ctx@, r.out.view(), self.lo as int, r.stopped as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (r: PreOut) {
        let PreTask { lo, hi, scan, out, ctx } = self;
        let ghost c = ctx@;
        let mut out = out;
        let cap = out.cap();
        let mut cache: (usize, usize) = (NONE, NONE);
        let mut l = lo;
        let mut full = false;
        proof {
            assert(cands_in(c, lo as int, lo as int) =~= Seq::<int>::empty());
        }
        while l < hi && !full
            invariant
                pre_scan_ok(&scan, c), lo <= l <= hi, (hi as int) <= c.npre, cache_ok(c, cache),
                out.wf(), cap == out.capacity(), cands_ok(c, out.view(), lo as int, l as int),
            decreases hi - l, if full { 0int } else { 1int },
        {
            proof { reveal(pre_scan_ok); }
            let (j, nc) = pre_row(&scan, l, cache, Ghost(c));
            cache = nc;
            if j != NONE {
                if out.len() >= cap {
                    full = true;
                } else {
                    let (t, tl) = text_val(&scan.p_tag, l, Ghost(c.npre));
                    let (v, vl) = text_val(&scan.p_ver, l, Ghost(c.npre));
                    let h = pair_hash(1, t, tl, v, vl);
                    let ghost o0 = out.view();
                    out.push((l, j, h));
                    proof {
                        lemma_cands_step(c, lo as int, l as int, o0, (l, j, h));
                    }
                    l = l + 1;
                }
            } else {
                proof {
                    assert(cands_in(c, lo as int, l + 1) =~= cands_in(c, lo as int, l as int));
                }
                l = l + 1;
            }
        }
        PreOut { out, stopped: l }
    }
}

/// One candidate row more.
proof fn lemma_cands_step(c: Ctx, lo: int, l: int, o: Seq<(usize, usize, u64)>, x: (usize, usize, u64))
    requires
        lo <= l, cands_ok(c, o, lo, l), pre_cand(c, l), x.0 as int == l,
        sub_of(c, x.1 as int, p_adsh(c, l)), x.2 == pre_tv_hash(c, l),
    ensures cands_ok(c, o.push(x), lo, l + 1),
{
    let cs = cands_in(c, lo, l + 1);
    assert(cs == cands_in(c, lo, l).push(l));
    assert forall|q: int| 0 <= q < cs.len() implies {
        let (a, j, h) = #[trigger] o.push(x)[q];
        &&& a as int == cs[q]
        &&& sub_of(c, j as int, p_adsh(c, a as int))
        &&& h == pre_tv_hash(c, a as int)
    } by {
        if q < o.len() {
            assert(o.push(x)[q] == o[q]);
        }
    }
}

/// The candidates among `lo..hi` on the calling thread (finishes a task that stopped early).
pub fn scan_serial(p: &PreScan, lo: usize, hi: usize, Ghost(c): Ghost<Ctx>) -> (out: Vec<(usize, usize, u64)>)
    requires pre_scan_ok(p, c), lo <= hi, (hi as int) <= c.npre,
    ensures cands_ok(c, out@, lo as int, hi as int),
{
    proof { reveal(pre_scan_ok); }
    let mut out: Vec<(usize, usize, u64)> = Vec::new();
    let mut cache: (usize, usize) = (NONE, NONE);
    let mut l = lo;
    proof {
        assert(cands_in(c, lo as int, lo as int) =~= Seq::<int>::empty());
    }
    while l < hi
        invariant
            pre_scan_ok(p, c), lo <= l <= hi, (hi as int) <= c.npre, cache_ok(c, cache),
            cands_ok(c, out@, lo as int, l as int),
        decreases hi - l,
    {
        proof { reveal(pre_scan_ok); }
        let (j, nc) = pre_row(p, l, cache, Ghost(c));
        cache = nc;
        if j != NONE {
            let (t, tl) = text_val(&p.p_tag, l, Ghost(c.npre));
            let (v, vl) = text_val(&p.p_ver, l, Ghost(c.npre));
            let h = pair_hash(1, t, tl, v, vl);
            let ghost o0 = out@;
            out.push((l, j, h));
            proof {
                lemma_cands_step(c, lo as int, l as int, o0, (l, j, h));
            }
        } else {
            proof {
                assert(cands_in(c, lo as int, l + 1) =~= cands_in(c, lo as int, l as int));
            }
        }
        l = l + 1;
    }
    out
}

/// A copy of the scan's handles is a scan of the same context.
pub proof fn lemma_pre_scan_copy(p: &PreScan, r: &PreScan, c: Ctx)
    requires
        pre_scan_ok(p, c),
        r.p_adsh@ == p.p_adsh@ && r.p_stmt@ == p.p_stmt@ && r.p_stmtv@ == p.p_stmtv@ && r.p_tag@ == p.p_tag@
            && r.p_ver@ == p.p_ver@ && r.stmt@ == p.stmt@ && r.stmt_len == p.stmt_len && *r.sx == *p.sx,
    ensures pre_scan_ok(r, c),
{
    reveal(pre_scan_ok);
}

} // verus!
