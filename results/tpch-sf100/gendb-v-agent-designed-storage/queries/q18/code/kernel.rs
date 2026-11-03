//! Exec kernels of Q18 over the model's parts (`Cols`: the column slices, block sizes and the bound parameter):
//! the customer lookup (`cust_find`), a key's exact count and quantity sum (`acc_ok`, `scan_sums`), the candidate
//! row of an order (`cand_of`), and the chunk task (`Chunk`, a `WorkerTask`) over the orders `[o_lo, o_hi)`. On the
//! co-clustered layout a chunk is one pass over its lineitem rows (`scan::scan_chunk`); otherwise (the general
//! path) each order's sums come from a scan of every lineitem row. Either way the result is the top 100 of the
//! groups of the chunk's orders (`topk_ok` of `qspec::gseq(o_lo, o_hi)`) by o_totalprice DESC, o_orderdate.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::pow10;
use crate::gendb_entry::parallel::WorkerTask;
use crate::stores::custpart::interface::common::keyidx as ck;
use super::common::isum::*;
use super::common::topk::*;
use super::model::*;
use super::qspec::*;
use super::cand::*;
use super::answer::lemma_gseq_wf;

verus! {

// ------------------------------------------------------------------------------------------------ columns

/// The column slices of the model and the bound parameter (`thr`: `$1` as a coefficient at scale 2). Slice lengths
/// are fields because slice `len` may unwind in worker bodies.
#[derive(Clone, Copy)]
pub struct Cols {
    pub l_key_c: &'static [u32],
    pub l_key_b: &'static [i64],
    pub l_qty_c: &'static [u16],
    pub l_qty_b: &'static [i64],
    pub l_bs: u64,
    pub l_n: usize,
    pub l_nb: usize,
    pub o_key_c: &'static [u32],
    pub o_key_b: &'static [i64],
    pub o_cust_c: &'static [u32],
    pub o_cust_b: &'static [i64],
    pub o_tp_c: &'static [u32],
    pub o_tp_b: &'static [i64],
    pub o_date_c: &'static [u16],
    pub o_date_b: &'static [i64],
    pub o_ic: &'static [u32],
    pub o_ib: &'static [u64],
    pub o_kind: u64,
    pub o_bs: u64,
    pub o_bsz: usize,
    pub idx_ok: bool,
    pub o_n: usize,
    pub o_nb: usize,
    pub c_key_c: &'static [u32],
    pub c_key_b: &'static [i64],
    pub c_name_o: &'static [u64],
    pub c_name_y: &'static [u8],
    pub c_bs: u64,
    pub c_bsz: usize,
    pub cidx_ok: bool,
    pub c_n: usize,
    pub c_nb: usize,
    pub c_kind: u64,
    pub e32: &'static [u32],
    pub e64: &'static [u64],
    pub thr: i128,
    pub cluster: u64,
    pub r_lens: &'static [u8],
    pub r_starts: &'static [u64],
    pub qz: &'static [i64],
    pub r_mode: u64,
    pub r_stride: u64,
    pub r_n: usize,
    pub r_sn: usize,
    pub qz_n: usize,
    pub lg_mode: u64,
    pub lg_max: u64,
    pub lg_n: u64,
    pub lg_runs: &'static [u32],
    pub lg_starts: &'static [u32],
    pub lg_rn: usize,
}

/// The slices are the model's parts; `thr` is `100 * $1`.
pub open spec fn cols_ok(c: Cols, m: M, p: QP) -> bool {
    &&& c.l_key_c@ == m.l_key_c && c.l_key_b@ == m.l_key_b
    &&& c.l_qty_c@ == m.l_qty_c && c.l_qty_b@ == m.l_qty_b
    &&& c.l_bs as int == m.l_bs && c.l_n == m.l_n && c.l_nb == m.l_nb
    &&& c.o_key_c@ == m.o_key_c && c.o_key_b@ == m.o_key_b
    &&& c.o_cust_c@ == m.o_cust_c && c.o_cust_b@ == m.o_cust_b
    &&& c.o_tp_c@ == m.o_tp_c && c.o_tp_b@ == m.o_tp_b
    &&& c.o_date_c@ == m.o_date_c && c.o_date_b@ == m.o_date_b
    &&& c.o_ic@ == m.o_ic && c.o_ib@ == m.o_ib && c.o_kind == m.o_kind
    &&& c.o_bs as int == m.o_bs && c.o_n == m.o_n && c.o_nb == m.o_nb
    &&& c.idx_ok ==> c.o_bsz as int == m.o_bs
    &&& c.c_key_c@ == m.c_key_c && c.c_key_b@ == m.c_key_b
    &&& c.c_name_o@ == m.c_name_o && c.c_name_y@ == m.c_name_y
    &&& c.c_bs as int == m.c_bs && c.c_n == m.c_n && c.c_kind == m.c_kind && c.c_nb == m.c_nb
    &&& c.cidx_ok ==> c.c_bsz as int == m.c_bs
    &&& c.e32@ == Seq::<u32>::empty() && c.e64@ == Seq::<u64>::empty()
    &&& c.thr as int == thr(p)
    &&& c.cluster == m.cluster
}

/// The run directory slices are the model's parts; `thr` is an int4 at scale 2.
pub open spec fn rcols_ok(c: Cols, m: M) -> bool {
    &&& -214748364800 <= c.thr <= 214748364700
    &&& c.r_lens@ == m.r_lens && c.r_starts@ == m.r_starts && c.qz@ == m.qz
    &&& c.r_mode == m.r_mode && c.r_stride as int == m.r_stride
    &&& c.r_n == m.r_lens.len() && c.r_sn == m.r_starts.len() && c.qz_n == m.qz.len()
}

/// The run permutation slices are the model's parts.
pub open spec fn lcols_ok(c: Cols, m: M) -> bool {
    &&& c.lg_mode == m.lg_mode && c.lg_max as int == m.lg_max && c.lg_n as int == m.lg_n
    &&& c.lg_runs@ == m.lg_runs && c.lg_starts@ == m.lg_starts && c.lg_rn == m.lg_runs.len()
}

/// `j / bs` is `g` for a row of block `g`.
pub proof fn lemma_div_in(j: int, bs: int, g: int)
    requires bs >= 1, g * bs <= j < (g + 1) * bs,
    ensures j / bs == g,
{
    assert((g + 1) * bs == g * bs + bs) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(j, bs, g, j - g * bs);
}

/// A row index below `n` has its block below the group count.
pub proof fn lemma_block_bound(j: int, bs: int, n: int, nb: int)
    requires bs >= 1, 0 <= j < n, nb * bs >= n,
    ensures 0 <= j / bs < nb,
{
    crate::stores::liruns::interface::common::read::lemma_div_lt(j, bs, nb);
}

// ------------------------------------------------------------------------------------------------ customers

/// The customer row with key `ckv` (one probe at row `ckv - 1` for dense keys, else the key index; a scan when the
/// block size does not fit `usize`), or `None` when no customer has the key.
pub fn cust_find(c: &Cols, ckv: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: Option<usize>)
    requires cols_ok(*c, m, p), model_ok(m),
    ensures
        r matches Some(i) ==> i < m.c_n && ckey(m, i as int) == ckv as int && i as int == cpos(m, ckv as int)
            && ccnt(m, ckv as int) > 0,
        r is None ==> ccnt(m, ckv as int) == 0,
    no_unwind
{
    proof {
        lemma_ccnt(m, ckv as int);
    }
    if c.cidx_ok {
        let guess: usize = if ckv >= 1 && (ckv as u64) <= (c.c_n as u64) { (ckv - 1) as usize } else { c.c_n };
        let r = ck::key_find_guess(c.c_key_c, c.c_key_b, c.e32, c.e64, c.c_bsz, c.c_kind, c.c_n, ckv as i128, guess);
        proof {
            match r {
                Some(i) => {
                    assert(ck::fkey(m.c_key_c, m.c_key_b, m.c_bs, i as int) == ckey(m, i as int));
                },
                None => {
                    assert forall|i: int| 0 <= i < m.c_n implies #[trigger] ckey(m, i) != ckv as int by {
                        assert(ck::fkey(m.c_key_c, m.c_key_b, m.c_bs, i) == ckey(m, i));
                    }
                },
            }
        }
        r
    } else {
        let mut i: usize = 0;
        while i < c.c_n
            invariant
                cols_ok(*c, m, p), model_ok(m),
                i <= m.c_n,
                forall|t: int| 0 <= t < i ==> #[trigger] ckey(m, t) != ckv as int,
            decreases m.c_n - i,
        {
            proof {
                lemma_block_bound(i as int, m.c_bs, m.c_n, m.c_nb);
                assert(in_i64(ckey(m, i as int)));
            }
            let g = ((i as u64) / c.c_bs) as usize;
            if c.c_key_b[g] + c.c_key_c[i] as i64 == ckv {
                proof {
                    assert(g as int == i as int / m.c_bs);
                    assert(ckey(m, i as int) == ckv as int);
                    assert(0 <= i < m.c_n && ckey(m, i as int) == ckv as int);
                    lemma_ccnt(m, ckv as int);
                }
                return Some(i);
            }
            i = i + 1;
        }
        proof {
            lemma_ccnt(m, ckv as int);
        }
        None
    }
}

// ------------------------------------------------------------------------------------------------ lineitem runs

/// `l` is the first lineitem row whose order position is at least `o` (the order positions never decrease).
pub open spec fn lb_ok(m: M, o: int, l: int) -> bool {
    &&& 0 <= l <= m.l_n
    &&& forall|t: int| 0 <= t < l ==> #[trigger] lpos(m, t) < o
    &&& forall|t: int| l <= t < m.l_n ==> #[trigger] lpos(m, t) >= o
}

/// With the cluster flag, the order position is nondecreasing.
pub proof fn lemma_lpos_mono(m: M, a: int, b: int)
    requires model_ok(m), m.cluster == 1, 0 <= a <= b < m.l_n,
    ensures lpos(m, a) <= lpos(m, b),
    decreases b - a,
{
    if a < b {
        lemma_lpos_mono(m, a, b - 1);
        assert(lpos(m, b - 1) <= lpos(m, (b - 1) + 1));
    }
}

/// The order at `q` is the one position with its key, so a lineitem row of that key has position `q`.
pub proof fn lemma_lpos_key(m: M, q: int, t: int)
    requires model_ok(m), 0 <= q < m.o_n,
    ensures (lkey(m, t) == okey(m, q)) == (lpos(m, t) == q),
{
    crate::agent::facts::lemma_opos(m, okey(m, q));
    crate::agent::facts::lemma_opos(m, lkey(m, t));
    if lkey(m, t) == okey(m, q) {
        assert(opos(m, okey(m, q)) == q) by {
            if opos(m, okey(m, q)) != q {
                assert(okey(m, q) != okey(m, q));
            }
        }
    }
}

/// An orders block cursor: `og` is the block of the position `q` (or `q` starts block `og + 1`).
pub open spec fn ocur_ok(m: M, q: int, og: int, oge: int) -> bool {
    &&& m.o_bs >= 1
    &&& og * m.o_bs <= q <= oge
    &&& oge == (og + 1) * m.o_bs
    &&& q <= m.o_n
    &&& oge <= m.o_n + m.o_bs
}

/// Partial sums over lineitem rows `[j0, j)`.
pub open spec fn dsum(f: spec_fn(int) -> int, j0: int, j: int) -> int {
    isum(j, f) - isum(j0, f)
}

/// The quantity bound of one row, in exact integers.
pub open spec fn qmax() -> int { 1000000000000000 }

/// One accumulation state of a key's run: the count and the quantity sum of `[j0, j)`, the sum bounded by the rows.
pub open spec fn acc_ok(m: M, k: int, j0: int, j: int, cnt: u64, sum: i128) -> bool {
    &&& cnt as int == dsum(kcnt_f(m, k), j0, j)
    &&& sum as int == dsum(ksum_f(m, k), j0, j)
    &&& cnt as int <= j - j0
    &&& -(j - j0) * qmax() <= sum as int <= (j - j0) * qmax()
}

/// One row of key `k` with quantity `qv` extends a key's sums (no machine overflow: at most `u64::MAX` rows).
pub proof fn lemma_acc_step(m: M, k: int, j0: int, j: int, cnt: u64, sum: i128, qv: i64)
    requires
        acc_ok(m, k, j0, j, cnt, sum),
        0 <= j0 <= j,
        j < u64::MAX,
        lkey(m, j) == k,
        qv as int == lqty(m, j),
        -qmax() < qv < qmax(),
    ensures
        cnt + 1 <= u64::MAX,
        i128::MIN <= sum + qv <= i128::MAX,
        acc_ok(m, k, j0, j + 1, (cnt + 1) as u64, (sum + qv) as i128),
{
    lemma_isum_step(j, kcnt_f(m, k));
    lemma_isum_step(j, ksum_f(m, k));
    assert(-(j + 1 - j0) * qmax() == -(j - j0) * qmax() - qmax());
    assert((j + 1 - j0) * qmax() == (j - j0) * qmax() + qmax());
    assert((j - j0) * qmax() <= 18446744073709551615 * 1000000000000000) by (nonlinear_arith)
        requires 0 <= j - j0 <= 18446744073709551615;
}

/// Accumulate row `j` (a row of key `k` with quantity `qv`, or not of key `k`) into a key's sums.
fn acc_row(cnt: u64, sum: i128, hitj: bool, qv: i64, Ghost(m): Ghost<M>, Ghost(k): Ghost<int>, Ghost(j0): Ghost<int>,
    Ghost(j): Ghost<int>) -> (r: (u64, i128))
    requires
        acc_ok(m, k, j0, j, cnt, sum),
        0 <= j0 <= j,
        j < u64::MAX,
        hitj == (lkey(m, j) == k),
        hitj ==> qv as int == lqty(m, j) && -qmax() < qv < qmax(),
    ensures
        acc_ok(m, k, j0, j + 1, r.0, r.1),
    no_unwind
{
    proof {
        lemma_isum_step(j, kcnt_f(m, k));
        lemma_isum_step(j, ksum_f(m, k));
        assert(-(j + 1 - j0) * qmax() == -(j - j0) * qmax() - qmax());
        assert((j + 1 - j0) * qmax() == (j - j0) * qmax() + qmax());
        assert((j - j0) * qmax() <= 18446744073709551615 * 1000000000000000) by (nonlinear_arith)
            requires 0 <= j - j0 <= 18446744073709551615;
    }
    if !hitj {
        return (cnt, sum);
    }
    (cnt + 1, sum + qv as i128)
}

/// When a key's rows are exactly `[j0, j)`, its partial sums there are its totals.
pub proof fn lemma_run_totals(m: M, k: int, j0: int, j: int)
    requires
        0 <= j0 <= j <= m.l_n,
        forall|t: int| 0 <= t < m.l_n && (t < j0 || t >= j) ==> lkey(m, t) != k,
    ensures
        dsum(kcnt_f(m, k), j0, j) == kcnt(m, k),
        dsum(ksum_f(m, k), j0, j) == ksum(m, k),
{
    assert forall|t: int| 0 <= t < j0 implies #[trigger] kcnt_f(m, k)(t) == 0 && ksum_f(m, k)(t) == 0 by {}
    assert forall|t: int| j <= t < m.l_n implies #[trigger] kcnt_f(m, k)(t) == 0 && ksum_f(m, k)(t) == 0 by {}
    lemma_isum_prefix_zero(j0, kcnt_f(m, k));
    lemma_isum_prefix_zero(j0, ksum_f(m, k));
    lemma_isum_suffix_zero(j, m.l_n, kcnt_f(m, k));
    lemma_isum_suffix_zero(j, m.l_n, ksum_f(m, k));
}

/// The general path: a key's sums by a scan of every lineitem row.
fn scan_sums(c: &Cols, okv: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: (u64, i128))
    requires cols_ok(*c, m, p), model_ok(m),
    ensures r.0 as int == kcnt(m, okv as int), r.1 as int == ksum(m, okv as int),
    no_unwind
{
    let ghost k = okv as int;
    let mut j: usize = 0;
    let mut cnt: u64 = 0;
    let mut sum: i128 = 0;
    while j < c.l_n
        invariant
            cols_ok(*c, m, p), model_ok(m), k == okv as int,
            j <= m.l_n,
            acc_ok(m, k, 0, j as int, cnt, sum),
        decreases m.l_n - j,
    {
        let g = ((j as u64) / c.l_bs) as usize;
        proof {
            lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
            assert(in_i64(lkey(m, j as int)));
            assert(qmax() == pow10(15)) by {
                assert(pow10(15) == 1000000000000000) by (compute);
            }
        }
        let lk = c.l_key_b[g] + c.l_key_c[j] as i64;
        let hitj = lk == okv;
        let qv: i64 = if hitj { c.l_qty_b[g] + c.l_qty_c[j] as i64 } else { 0 };
        let r = acc_row(cnt, sum, hitj, qv, Ghost(m), Ghost(k), Ghost(0), Ghost(j as int));
        cnt = r.0;
        sum = r.1;
        j = j + 1;
    }
    proof {
        assert(dsum(kcnt_f(m, k), 0, m.l_n) == kcnt(m, k));
        assert(dsum(ksum_f(m, k), 0, m.l_n) == ksum(m, k));
    }
    (cnt, sum)
}

// ------------------------------------------------------------------------------------------------ one order

/// The candidate of the order at `q` (key `okv`, quantity sum `sum` above `$1`, with a lineitem): `Some` exactly
/// when its customer exists, with its row.
pub fn cand_of(c: &Cols, q: usize, og: usize, okv: i64, sum: i128, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: Option<Cand>)
    requires
        cols_ok(*c, m, p), model_ok(m),
        q < m.o_n, og as int == q as int / m.o_bs, okv == okey(m, q as int),
        kcnt(m, okv as int) > 0,
        sum as int == ksum(m, okv as int),
        sum > c.thr,
    ensures
        r is Some == good(m, p, q as int),
        r matches Some(cd) ==> cand_row(m, cd) == grow(m, p, q as int) && cd.cpos < m.c_n,
    no_unwind
{
    proof {
        lemma_block_bound(q as int, m.o_bs, m.o_n, m.o_nb);
        assert(in_i64(okey(m, q as int)));
        assert(pow10(15) == 1000000000000000) by (compute);
    }
    let ckv = c.o_cust_b[og] + c.o_cust_c[q] as i64;
    match cust_find(c, ckv, Ghost(m), Ghost(p)) {
        Some(cp) => {
            let date = c.o_date_b[og] + c.o_date_c[q] as i64;
            let tp = c.o_tp_b[og] + c.o_tp_c[q] as i64;
            let cd = Cand { q, okey: okv, ck: ckv, cpos: cp, date, tp, sum };
            proof {
                assert(cand_row(m, cd) =~= grow(m, p, q as int));
            }
            Some(cd)
        },
        None => None,
    }
}

// ------------------------------------------------------------------------------------------------ chunk task

/// The orders positions `[o_lo, o_hi)` of one task (`fast`: the lineitem rows of these orders are `[l_lo, l_hi)`,
/// co-clustered), with the preallocated top-100 buffer.
pub struct Chunk {
    pub cols: Cols,
    pub o_lo: usize,
    pub o_hi: usize,
    pub l_lo: usize,
    pub l_hi: usize,
    pub fast: bool,
    pub runs: bool,
    pub r_lo: usize,
    pub r_hi: usize,
    pub qm: i128,
    pub kmin: u16,
    pub long: bool,
    pub buf: Vec<Cand>,
    pub m: Ghost<M>,
    pub p: Ghost<QP>,
}

/// A task's result: its top-100 buffer.
pub struct ChunkOut {
    pub buf: Vec<Cand>,
    pub len: usize,
}

pub open spec fn chunk_pre(t: Chunk) -> bool {
    let m = t.m@;
    let p = t.p@;
    &&& cols_ok(t.cols, m, p)
    &&& model_ok(m)
    &&& t.buf@.len() == K
    &&& t.o_lo <= t.o_hi <= m.o_n
    &&& t.fast ==> {
        &&& m.cluster == 1
        &&& t.cols.idx_ok
        &&& t.l_lo <= t.l_hi <= m.l_n
        &&& lb_ok(m, t.o_lo as int, t.l_lo as int)
        &&& lb_ok(m, t.o_hi as int, t.l_hi as int)
    }
    &&& t.runs ==> t.fast && rcols_ok(t.cols, m) && super::scan::rchunk_ok(m, t.r_lo as int, t.r_hi as int, t.l_lo as int, t.l_hi as int, t.qm as int)
        && super::scan::kmin_ok(t.qm as int, t.cols.thr as int, t.kmin as int)
    &&& t.long ==> t.runs && lcols_ok(t.cols, m) && super::scan::long_use_ok(m, t.kmin as int)
}

pub open spec fn chunk_post(t: Chunk, out: ChunkOut) -> bool {
    let m = t.m@;
    let p = t.p@;
    &&& out.buf@.len() == K
    &&& out.len <= K
    &&& topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, out.buf@, out.len as int), gseq(m, p, t.o_lo as int, t.o_hi as int))
    &&& forall|i: int| 0 <= i < out.len ==> (#[trigger] out.buf@[i]).cpos < m.c_n
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
        let ghost task = self;
        let Chunk { cols, o_lo, o_hi, l_lo, l_hi, fast, runs, r_lo, r_hi, qm, kmin, long, buf, m: gm, p: gp } = self;
        let ghost m = gm@;
        let ghost p = gp@;
        let c = cols;
        let mut buf = buf;
        if long {
            let len = super::scan::scan_long(&c, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, kmin, &mut buf, Ghost(m), Ghost(p));
            return ChunkOut { buf, len };
        }
        if runs {
            let len = super::scan::scan_runs(&c, o_lo, o_hi, l_lo, l_hi, r_lo, r_hi, qm, kmin, &mut buf, Ghost(m), Ghost(p));
            return ChunkOut { buf, len };
        }
        if fast {
            let len = super::scan::scan_chunk(&c, o_lo, o_hi, l_lo, l_hi, &mut buf, Ghost(m), Ghost(p));
            return ChunkOut { buf, len };
        }
        // the general path: per order, its sums by a scan of every lineitem row
        let mut len: usize = 0;
        let mut q = o_lo;
        // the orders block cursor (one division per task)
        let og64 = (q as u64) / c.o_bs;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(q as int, m.o_bs);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(q as int, m.o_bs);
            assert(m.o_bs * og64 == og64 * m.o_bs) by (nonlinear_arith);
            assert((og64 + 1) * m.o_bs == og64 * m.o_bs + m.o_bs) by (nonlinear_arith);
            assert(og64 <= q) by (nonlinear_arith) requires og64 * m.o_bs <= q, m.o_bs >= 1, og64 >= 0;
        }
        let mut og: usize = og64 as usize;
        let mut oge: u64 = (og64 + 1) * c.o_bs;
        proof {
            lemma_topk_empty(q18_keys(), q18_fams(), K as nat);
            lemma_gseq_empty(m, p, o_lo as int);
            assert(cands_view(m, buf@, 0) =~= Seq::<Row>::empty());
        }
        while q < o_hi
            invariant
                m == gm@, p == gp@, c == cols,
                cols_ok(c, m, p),
                model_ok(m),
                o_lo <= q <= o_hi <= m.o_n,
                ocur_ok(m, q as int, og as int, oge as int),
                buf@.len() == K,
                len <= K,
                topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, buf@, len as int), gseq(m, p, o_lo as int, q as int)),
                forall|i: int| 0 <= i < len ==> (#[trigger] buf@[i]).cpos < m.c_n,
            decreases o_hi - q,
        {
            if q as u64 == oge {
                proof {
                    assert((og + 2) * m.o_bs == (og + 1) * m.o_bs + m.o_bs) by (nonlinear_arith);
                    lemma_div_in(q as int, m.o_bs, og as int + 1);
                    lemma_block_bound(q as int, m.o_bs, m.o_n, m.o_nb);
                }
                og = og + 1;
                oge = oge + c.o_bs;
            }
            proof {
                lemma_div_in(q as int, m.o_bs, og as int);
                lemma_block_bound(q as int, m.o_bs, m.o_n, m.o_nb);
                assert(in_i64(okey(m, q as int)));
            }
            let okv = c.o_key_b[og] + c.o_key_c[q] as i64;
            let (cnt, sum) = scan_sums(&c, okv, Ghost(m), Ghost(p));
            let ghost g0 = gseq(m, p, o_lo as int, q as int);
            proof {
                lemma_gseq_step(m, p, o_lo as int, q as int);
            }
            if cnt > 0 && sum > c.thr {
                match cand_of(&c, q, og, okv, sum, Ghost(m), Ghost(p)) {
                    Some(cd) => {
                        let ghost lb = buf@;
                        let ghost ln = len;
                        proof {
                            lemma_gseq_wf(m, p, o_lo as int, q as int + 1);
                        }
                        len = topk_insert(&mut buf, len, cd, Ghost(m), Ghost(g0));
                        proof {
                            // every buffered candidate is the inserted one or an earlier one
                            assert forall|i: int| 0 <= i < len implies (#[trigger] buf@[i]).cpos < m.c_n by {
                                if buf@[i] != cd {
                                    let u = choose|u: int| 0 <= u < ln && buf@[i] == lb[u];
                                }
                            }
                        }
                    },
                    None => {},
                }
            } else {
                proof {
                    assert(!good(m, p, q as int));
                }
            }
            q = q + 1;
        }
        ChunkOut { buf, len }
    }
}

} // verus!
