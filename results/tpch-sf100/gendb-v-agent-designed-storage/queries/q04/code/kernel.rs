//! Q4 scan kernel over storage `facts` (model: `super::model`). A scan task walks stored orders rows `[q0, q1)` and,
//! in step, the co-clustered lineitem rows: the lines of each order are one contiguous run, so one cursor finds
//! every order's lines (`merge_inv`). Per order it decides the EXISTS (some line with `l_commitdate <
//! l_receiptdate`) and the date window `[lo, hi]`, and counts qualifying orders per o_orderpriority dictionary index.
//! The task finds its lineitem start by binary search over the cursor condition (`lineitem_start`), so tasks are
//! independent. Groups are tracked incrementally (no division per row).
use vstd::prelude::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::stores::facts::interface::common::keyidx::{fkey, key_find};
use super::model::*;
use super::fast::{fast_ok, run_fast, FLAGS_LEN, OB};

verus! {

/// `n` zero counters.
pub open spec fn zeros(n: nat) -> Seq<usize> {
    Seq::new(n, |_i: int| 0usize)
}

/// The stored orders row of stored lineitem row `j`'s order (`rpos`), by the orders key index.
pub fn order_pos_at(c: &Cols, k: Ghost<int>, j: usize) -> (p: usize)
    requires
        cols_ok(*c, k@),
        keys_distinct(*c),
        j < c.n_l,
    ensures
        p as int == rpos(*c, lkey(*c, j as int)),
    no_unwind
{
    proof {
        lemma_div_below(j as int, c.bs_l as int, c.lk_bases@.len() as int);
        assert(in_i64(lkey(*c, j as int)));
    }
    let g = j / c.bs_l;
    let kk = c.lk_bases[g] as i128 + c.lk_codes[j] as i128;
    match key_find(c.ok_codes, c.ok_bases, c.oi_codes, c.oi_bases, c.bs_o, c.oi_kind, c.n_o, kk) {
        Some(p) => {
            proof {
                assert(okey(*c, p as int) == kk);
                lemma_rpos_of(*c, p as int);
            }
            p
        },
        None => {
            proof {
                assert forall|q: int| 0 <= q < c.n_o implies #[trigger] okey(*c, q) != kk by {
                    assert(fkey(c.ok_codes@, c.ok_bases@, c.bs_o as int, q) != kk);
                }
                lemma_rpos_none(*c, kk as int);
            }
            c.n_o
        },
    }
}

/// The first stored lineitem row whose order is at or after stored orders row `q` (binary search; the rows' orders
/// are nondecreasing).
pub fn lineitem_start(c: &Cols, k: Ghost<int>, q: usize) -> (r: usize)
    requires
        cols_ok(*c, k@),
        keys_distinct(*c),
        lines_clustered(*c),
    ensures
        merge_inv(*c, q as int, r as int),
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = c.n_l;
    while lo < hi
        invariant
            cols_ok(*c, k@),
            keys_distinct(*c),
            lines_clustered(*c),
            lo <= hi <= c.n_l,
            lo > 0 ==> rpos(*c, lkey(*c, lo - 1)) < q,
            hi < c.n_l ==> rpos(*c, lkey(*c, hi as int)) >= q,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if order_pos_at(c, k, mid) < q {
            lo = mid + 1;
        } else {
            proof {
                if hi < c.n_l {
                    lemma_lines_le(*c, mid as int, hi as int);
                }
            }
            hi = mid;
        }
    }
    lo
}

/// One scan task: stored orders rows `[q0, q1)`, date window `[lo, hi]`, `k` priority counters (zero on entry).
/// `fast`: scan over the run lengths (`super::fast`, with the o_orderdate zone maxima `zmax` and scratch `flags`,
/// `tbuf`, `key`), else the merge walk.
pub struct ScanTask {
    pub cols: Cols,
    pub q0: usize,
    pub q1: usize,
    pub lo: i64,
    pub hi: i64,
    pub k: usize,
    pub counts: Vec<usize>,
    pub fast: bool,
    pub zmax: &'static [i64],
    pub flags: Vec<u8>,
    pub tbuf: Vec<u16>,
    pub key: Vec<u16>,
}

impl WorkerTask for ScanTask {
    type Output = Vec<usize>;

    open spec fn pre(&self) -> bool {
        &&& cols_ok(self.cols, self.k as int)
        &&& keys_distinct(self.cols)
        &&& lines_clustered(self.cols)
        &&& self.q0 <= self.q1 <= self.cols.n_o
        &&& self.counts@ == zeros(self.k as nat)
        &&& self.fast ==> {
            &&& fast_ok(self.cols, self.k as int)
            &&& self.zmax@.len() == self.cols.od_bases@.len()
            &&& forall|q: int| 0 <= q < self.cols.n_o ==> #[trigger] odate(self.cols, q) <= self.zmax@[q / self.cols.bs_o as int]
            &&& self.flags@.len() == FLAGS_LEN
            &&& self.tbuf@.len() == OB
            &&& self.key@.len() == OB
        }
    }

    open spec fn post(&self, out: Vec<usize>) -> bool {
        &&& out@.len() == self.k
        &&& forall|d: int| 0 <= d < self.k ==> #[trigger] out@[d] as int
                == count_raw(self.cols, self.lo as int, self.hi as int, d, self.q0 as int, self.q1 as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.q0 as u64, self.q1 as u64)
    }

    fn run(self) -> (out: Vec<usize>) {
        let ScanTask { cols, q0, q1, lo, hi, k, counts, fast, zmax, flags, tbuf, key } = self;
        if fast {
            proof {
                assert forall|d: int| 0 <= d < k implies #[trigger] counts@[d] == 0 by {}
            }
            run_fast(cols, k, zmax, q0, q1, lo, hi, counts, flags, tbuf, key)
        } else {
            run_merge(cols, k, q0, q1, lo, hi, counts)
        }
    }
}

/// The merge walk over stored orders rows `[q0, q1)` and their lineitem runs (lineitem rows found by key).
fn run_merge(c: Cols, k: usize, q0: usize, q1: usize, lo: i64, hi: i64, counts: Vec<usize>) -> (out: Vec<usize>)
    requires
        cols_ok(c, k as int),
        keys_distinct(c),
        lines_clustered(c),
        q0 <= q1 <= c.n_o,
        counts@ == zeros(k as nat),
    ensures
        out@.len() == k,
        forall|d: int| 0 <= d < k ==> #[trigger] out@[d] as int == count_raw(c, lo as int, hi as int, d, q0 as int, q1 as int),
    no_unwind
{
        let ghost kk = k as int;
        let mut counts = counts;
        let n_l = c.n_l;
        let bs_o = c.bs_o;
        let bs_l = c.bs_l;
        let mut cur = lineitem_start(&c, Ghost(kk), q0);
        // Lineitem group of the cursor: gl, with rem_l rows of it left from cur on.
        proof { lemma_group_of_row(cur as int, bs_l as int); }
        let mut gl = cur / bs_l;
        let mut rem_l = bs_l - cur % bs_l;
        let mut p = q0;
        // Orders group of p: gp, with rem_o rows of it left from p on.
        proof { lemma_group_of_row(p as int, bs_o as int); }
        let mut gp = p / bs_o;
        let mut rem_o = bs_o - p % bs_o;
        proof {
            assert forall|d: int| 0 <= d < k implies #[trigger] counts@[d] as int == count_raw(c, lo as int, hi as int, d, q0 as int, p as int) by {}
        }
        while p < q1
            invariant
                cols_ok(c, kk),
                keys_distinct(c),
                lines_clustered(c),
                kk == k,
                q0 <= p <= q1 <= c.n_o,
                n_l == c.n_l,
                bs_o == c.bs_o,
                bs_l == c.bs_l,
                counts@.len() == k,
                forall|d: int| 0 <= d < k ==> #[trigger] counts@[d] as int == count_raw(c, lo as int, hi as int, d, q0 as int, p as int),
                merge_inv(c, p as int, cur as int),
                gp * bs_o <= p,
                p + rem_o == gp * bs_o + bs_o,
                1 <= rem_o <= bs_o,
                gl * bs_l <= cur,
                cur + rem_l == gl * bs_l + bs_l,
                1 <= rem_l <= bs_l,
            decreases q1 - p,
        {
            proof {
                lemma_div_group(p as int, bs_o as int, gp as int);
                lemma_div_below(p as int, bs_o as int, c.ok_bases@.len() as int);
                assert(in_i64(okey(c, p as int)));
                assert(in_i64(odate(c, p as int)));
                assert(0 <= oprio(c, p as int) < kk);
            }
            let okey_p = c.ok_bases[gp] + c.ok_codes[p] as i64;
            let date_p = c.od_bases[gp] + c.od_codes[p] as i64;
            let ghost c0 = cur as int;
            let mut found = false;
            let mut more = true;
            while more && cur < n_l
                invariant
                    cols_ok(c, kk),
                    n_l == c.n_l,
                    bs_l == c.bs_l,
                    okey_p == okey(c, p as int),
                    c0 <= cur <= n_l,
                    forall|j: int| c0 <= j < cur ==> #[trigger] lkey(c, j) == okey_p,
                    found == exists|j: int| c0 <= j < cur && #[trigger] lmatch(c, j, okey_p as int),
                    !more ==> cur < n_l && lkey(c, cur as int) != okey_p,
                    gl * bs_l <= cur,
                    cur + rem_l == gl * bs_l + bs_l,
                    1 <= rem_l <= bs_l,
                decreases n_l - cur + if more { 1int } else { 0 },
            {
                proof {
                    lemma_div_group(cur as int, bs_l as int, gl as int);
                    lemma_div_below(cur as int, bs_l as int, c.lk_bases@.len() as int);
                    assert(in_i64(lkey(c, cur as int)));
                    assert(in_i64(lcmt(c, cur as int)));
                    assert(in_i64(lrcp(c, cur as int)));
                }
                let key_j = c.lk_bases[gl] + c.lk_codes[cur] as i64;
                if key_j == okey_p {
                    let late = c.lc_bases[gl] + (c.lc_codes[cur] as i64) < c.lr_bases[gl] + (c.lr_codes[cur] as i64);
                    proof {
                        assert(late == lmatch(c, cur as int, okey_p as int));
                        if late {
                            assert(lmatch(c, cur as int, okey_p as int));
                        }
                        if found {
                            let w = choose|j: int| c0 <= j < cur && #[trigger] lmatch(c, j, okey_p as int);
                            assert(c0 <= w < cur + 1 && lmatch(c, w, okey_p as int));
                        }
                        assert forall|j: int| c0 <= j < cur + 1 && #[trigger] lmatch(c, j, okey_p as int)
                            implies found || late by {
                            if j < cur {
                            }
                        }
                    }
                    if late {
                        found = true;
                    }
                    cur = cur + 1;
                    rem_l = rem_l - 1;
                    if rem_l == 0 {
                        proof {
                            lemma_next_group(gl as int, bs_l as int);
                            lemma_group_le(gl as int, bs_l as int);
                        }
                        gl = gl + 1;
                        rem_l = bs_l;
                    }
                } else {
                    more = false;
                }
            }
            proof {
                if cur < n_l && more {
                    assert(false);
                }
                lemma_merge_step(c, p as int, c0, cur as int);
                assert(found == has_line_raw(c, okey_p as int)) by {
                    if has_line_raw(c, okey_p as int) {
                        let w = choose|j: int| 0 <= j < c.n_l && #[trigger] lmatch(c, j, okey_p as int);
                        assert(lkey(c, w) == okey(c, p as int));
                        assert(c0 <= w < cur);
                    }
                }
                lemma_count_bound(c, lo as int, hi as int, 0, q0 as int, p as int);
                assert forall|d: int| 0 <= d < k implies #[trigger] counts@[d] <= p - q0 by {
                    lemma_count_bound(c, lo as int, hi as int, d, q0 as int, p as int);
                }
            }
            let ghost old_counts = counts@;
            if found && lo <= date_p && date_p <= hi {
                let pi = (c.op_bases[gp] + c.op_codes[p] as u64) as usize;
                counts[pi] = counts[pi] + 1;
            }
            proof {
                assert forall|d: int| 0 <= d < k implies #[trigger] counts@[d] as int
                    == count_raw(c, lo as int, hi as int, d, q0 as int, p + 1) by {
                    lemma_count_step(c, lo as int, hi as int, d, q0 as int, p as int);
                    assert(old_counts[d] as int == count_raw(c, lo as int, hi as int, d, q0 as int, p as int));
                }
            }
            p = p + 1;
            rem_o = rem_o - 1;
            if rem_o == 0 {
                proof {
                    lemma_next_group(gp as int, bs_o as int);
                    lemma_group_le(gp as int, bs_o as int);
                }
                gp = gp + 1;
                rem_o = bs_o;
            }
        }
        counts
}

/// Fallback EXISTS for an order key when the co-clustering is not known: scan every stored lineitem row.
pub fn has_line_scan(c: &Cols, k: Ghost<int>, key: i64) -> (r: bool)
    requires cols_ok(*c, k@),
    ensures r == has_line_raw(*c, key as int),
{
    let n_l = c.n_l;
    let mut j: usize = 0;
    while j < n_l
        invariant
            cols_ok(*c, k@),
            n_l == c.n_l,
            j <= n_l,
            forall|i: int| 0 <= i < j ==> !#[trigger] lmatch(*c, i, key as int),
        decreases n_l - j,
    {
        proof {
            lemma_div_below(j as int, c.bs_l as int, c.lk_bases@.len() as int);
            assert(in_i64(lkey(*c, j as int)));
            assert(in_i64(lcmt(*c, j as int)));
            assert(in_i64(lrcp(*c, j as int)));
        }
        let g = j / c.bs_l;
        if c.lk_bases[g] + c.lk_codes[j] as i64 == key
            && c.lc_bases[g] + (c.lc_codes[j] as i64) < c.lr_bases[g] + (c.lr_codes[j] as i64) {
            assert(lmatch(*c, j as int, key as int));
            return true;
        }
        j = j + 1;
    }
    false
}

/// Fallback count (serial, any lineitem order): per stored orders row in `[q0, q1)`, the date window, then a full
/// lineitem scan.
pub fn count_fallback(c: &Cols, k: usize, q0: usize, q1: usize, lo: i64, hi: i64) -> (out: Vec<usize>)
    requires
        cols_ok(*c, k as int),
        q0 <= q1 <= c.n_o,
    ensures
        out@.len() == k,
        forall|d: int| 0 <= d < k ==> #[trigger] out@[d] as int == count_raw(*c, lo as int, hi as int, d, q0 as int, q1 as int),
{
    let mut counts = crate::gendb_entry::work::filled(k, 0usize);
    let mut p = q0;
    proof {
        assert forall|d: int| 0 <= d < k implies #[trigger] counts@[d] as int == count_raw(*c, lo as int, hi as int, d, q0 as int, p as int) by {}
    }
    while p < q1
        invariant
            cols_ok(*c, k as int),
            q0 <= p <= q1 <= c.n_o,
            counts@.len() == k,
            forall|d: int| 0 <= d < k ==> #[trigger] counts@[d] as int == count_raw(*c, lo as int, hi as int, d, q0 as int, p as int),
        decreases q1 - p,
    {
        proof {
            lemma_div_below(p as int, c.bs_o as int, c.ok_bases@.len() as int);
            assert(in_i64(okey(*c, p as int)));
            assert(in_i64(odate(*c, p as int)));
            assert(0 <= oprio(*c, p as int) < k);
            assert forall|d: int| 0 <= d < k implies #[trigger] counts@[d] <= p - q0 by {
                lemma_count_bound(*c, lo as int, hi as int, d, q0 as int, p as int);
            }
        }
        let g = p / c.bs_o;
        let date_p = c.od_bases[g] + c.od_codes[p] as i64;
        let ghost old_counts = counts@;
        if lo <= date_p && date_p <= hi {
            let key = c.ok_bases[g] + c.ok_codes[p] as i64;
            if has_line_scan(c, Ghost(k as int), key) {
                let pi = (c.op_bases[g] + c.op_codes[p] as u64) as usize;
                counts[pi] = counts[pi] + 1;
            }
        }
        proof {
            assert forall|d: int| 0 <= d < k implies #[trigger] counts@[d] as int
                == count_raw(*c, lo as int, hi as int, d, q0 as int, p + 1) by {
                lemma_count_step(*c, lo as int, hi as int, d, q0 as int, p as int);
                assert(old_counts[d] as int == count_raw(*c, lo as int, hi as int, d, q0 as int, p as int));
            }
        }
        p = p + 1;
    }
    counts
}

} // verus!
