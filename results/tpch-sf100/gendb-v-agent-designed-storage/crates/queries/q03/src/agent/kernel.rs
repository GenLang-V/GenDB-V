//! Exec kernels of Q3 over the model's parts (`Cols`: the column slices, block sizes and the bound parameters).
//! A chunk task (`Chunk`, a `WorkerTask`) walks the orders positions `[o_lo, o_hi)`; for each order it sums the
//! lineitems shipped after the date (`fast_sums`: the contiguous run of the order at the lineitem cursor, using the
//! co-clustering; `scan_sums`: a scan of every lineitem row, the general path), keeps the order when it is a group
//! (`good`: dated before the date, customer of the segment, `cust_ok`), and keeps the top 10 groups by revenue DESC,
//! o_orderdate (`topk_insert`). The result is `topk_ok` of the groups of its range (`qspec::gseq`), or an order
//! whose absolute revenue mass leaves `i128` (the Capacity case).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::{abs, pow10, align, max_nat};
use crate::spec::order::{keys_cmp, key_cmp};
use crate::spec::ast::OrderKey;
use crate::spec::numeric::sign;
use crate::link::expr::{i128_max, lemma_compare_num, lemma_compare_date, lemma_align_same};
use crate::bridge::order::{keys_ok, key_ok, lemma_keys_cmp_antisym, lemma_keys_cmp_trans};
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use crate::stores::facts::interface::common::keyidx as fk;
use crate::stores::custpart::interface::common::keyidx as ck;
use crate::stores::custpart::interface::common::colfmt as cf;
use super::common::isum::*;
use super::common::topk::*;
use super::model::*;
use super::qspec::*;
use super::select::*;
use std::sync::Arc;

verus! {

// ------------------------------------------------------------------------------------------------ candidates

/// A group row: l_orderkey, revenue (coefficient at scale 4), o_orderdate (days), o_shippriority.
#[derive(Clone, Copy)]
pub struct Cand {
    pub okey: i64,
    pub rev: i128,
    pub date: i64,
    pub sp: i64,
}

pub open spec fn cand_row(c: Cand) -> Row {
    seq![Val::Int(c.okey as int), Val::Num { coeff: c.rev as int, scale: 4 }, Val::Date(c.date as int), Val::Int(c.sp as int)]
}

/// The first `len` candidates of a buffer, as rows.
pub open spec fn cands_view(buf: Seq<Cand>, len: int) -> Seq<Row> {
    Seq::new(len as nat, |i: int| cand_row(buf[i]))
}

/// The ORDER BY comparison of two candidate rows: revenue DESC, then o_orderdate.
pub proof fn lemma_cand_cmp(a: Cand, b: Cand)
    ensures
        keys_cmp(q3_keys(), cand_row(a), cand_row(b)) == (if a.rev != b.rev {
            if a.rev > b.rev { -1int } else { 1int }
        } else if a.date < b.date { -1int } else if a.date > b.date { 1int } else { 0int }),
        keys_ok(q3_keys(), q3_fams(), cand_row(a)),
{
    let (ra, rb) = (cand_row(a), cand_row(b));
    let keys = q3_keys();
    let k0 = keys[0];
    let k1 = keys.drop_first();
    assert(k0 == OrderKey { col: 1, desc: true, nulls_first: true });
    assert(k1[0] == OrderKey { col: 2, desc: false, nulls_first: false });
    assert(k1.len() == 1);
    lemma_compare_num(a.rev as int, 4, b.rev as int, 4);
    lemma_align_same(a.rev as int, 4);
    lemma_align_same(b.rev as int, 4);
    assert(max_nat(4, 4) == 4);
    lemma_compare_date(a.date as int, b.date as int);
    assert(ra[1] == (Val::Num { coeff: a.rev as int, scale: 4 }) && rb[1] == (Val::Num { coeff: b.rev as int, scale: 4 }));
    assert(ra[2] == Val::Date(a.date as int) && rb[2] == Val::Date(b.date as int));
    let c0 = key_cmp(k0, ra, rb);
    let c1 = key_cmp(k1[0], ra, rb);
    assert(c0 == -sign(a.rev as int - b.rev as int));
    assert(c1 == sign(a.date as int - b.date as int));
    assert(k1.drop_first().len() == 0);
    assert(keys_cmp(k1.drop_first(), ra, rb) == 0);
    assert(keys_cmp(k1, ra, rb) == c1);
    assert(keys_cmp(keys, ra, rb) == if c0 != 0 { c0 } else { c1 });
    assert forall|t: int| 0 <= t < keys.len() implies #[trigger] key_ok(keys[t], q3_fams()[t], ra) by {}
}

/// `a` comes strictly before `b`: larger revenue, or equal revenue and earlier date.
pub fn better(a: &Cand, b: &Cand) -> (r: bool)
    ensures r == (keys_cmp(q3_keys(), cand_row(*a), cand_row(*b)) < 0),
    no_unwind
{
    proof { lemma_cand_cmp(*a, *b); }
    a.rev > b.rev || (a.rev == b.rev && a.date < b.date)
}

pub proof fn lemma_view_last(buf: Seq<Cand>, len: int)
    requires 0 < len <= buf.len(),
    ensures cands_view(buf, len).last() == cand_row(buf[len - 1]), cands_view(buf, len).len() == len,
{
}

/// The sorted position of a candidate in a sorted buffer: after every row not above it.
fn find_pos(buf: &Vec<Cand>, len: usize, c: Cand, Ghost(all): Ghost<Seq<Row>>) -> (pos: usize)
    requires
        buf@.len() == 10,
        len <= 10,
        topk_ok(q3_keys(), q3_fams(), 10, cands_view(buf@, len as int), all),
        len == 10 ==> keys_cmp(q3_keys(), cand_row(c), cand_row(buf@[9])) < 0,
    ensures
        ins_pos(q3_keys(), cands_view(buf@, len as int), pos as int, cand_row(c)),
        len < 10 || pos < len,
    no_unwind
{
    let ghost keys = q3_keys();
    let ghost fams = q3_fams();
    let ghost view = cands_view(buf@, len as int);
    let ghost rc = cand_row(c);
    proof { lemma_cand_cmp(c, c); }
    let mut pos: usize = 0;
    let mut found = false;
    while pos < len && !found
        invariant
            pos <= len <= 10,
            buf@.len() == 10,
            view == cands_view(buf@, len as int),
            rc == cand_row(c),
            keys == q3_keys(),
            fams == q3_fams(),
            keys_ok(keys, fams, rc),
            topk_ok(keys, fams, 10, view, all),
            forall|i: int| 0 <= i < pos ==> keys_cmp(keys, #[trigger] view[i], rc) <= 0,
            found ==> pos < len && keys_cmp(keys, rc, view[pos as int]) < 0,
        decreases len - pos + if found { 0int } else { 1int },
    {
        let bp = buf[pos];
        let b = better(&c, &bp);
        proof {
            assert(bp == buf@[pos as int]);
            assert(b == (keys_cmp(q3_keys(), cand_row(c), cand_row(bp)) < 0));
            assert(view[pos as int] == cand_row(buf@[pos as int]));
            assert(b == (keys_cmp(keys, rc, view[pos as int]) < 0));
        }
        if b {
            found = true;
        } else {
            proof {
                assert(keys_ok(keys, fams, view[pos as int]));
                lemma_keys_cmp_antisym(keys, fams, rc, view[pos as int]);
                assert(keys_cmp(keys, view[pos as int], rc) <= 0);
                assert forall|i: int| 0 <= i < pos + 1 implies keys_cmp(keys, #[trigger] view[i], rc) <= 0 by {
                    if i < pos {
                    }
                }
            }
            pos = pos + 1;
        }
    }
    proof {
        if pos < len {
            assert(view[pos as int] == cand_row(buf@[pos as int]));
            assert(keys_cmp(keys, rc, view[pos as int]) < 0);
            assert(keys_ok(keys, fams, view[pos as int]));
            lemma_keys_cmp_antisym(keys, fams, rc, view[pos as int]);
            assert forall|i: int| pos <= i < len implies keys_cmp(keys, #[trigger] view[i], rc) > 0 by {
                if i > pos {
                    assert(keys_cmp(keys, view[pos as int], view[i]) <= 0);
                    assert(keys_ok(keys, fams, view[i]));
                    if keys_cmp(keys, view[i], rc) <= 0 {
                        lemma_keys_cmp_trans(keys, fams, view[pos as int], view[i], rc);
                    }
                }
            }
        }
        if len == 10 && pos == 10 {
            assert(view[9] == cand_row(buf@[9]));
            assert(keys_cmp(keys, view[9], rc) <= 0);
            assert(keys_ok(keys, fams, view[9]));
            lemma_keys_cmp_antisym(keys, fams, rc, view[9]);
        }
    }
    pos
}

/// Shift the buffer right from `pos` (dropping the 10th row) and place the candidate at `pos`.
fn shift_insert(buf: &mut Vec<Cand>, len: usize, pos: usize, c: Cand) -> (r: usize)
    requires
        old(buf)@.len() == 10,
        pos <= len <= 10,
        len < 10 || pos < len,
    ensures
        final(buf)@.len() == 10,
        r <= 10,
        cands_view(final(buf)@, r as int) == ins_at(cands_view(old(buf)@, len as int), pos as int, cand_row(c), 10),
    no_unwind
{
    let ghost old_buf = buf@;
    let top: usize = if len < 10 { len } else { 9 };
    let mut i: usize = top;
    while i > pos
        invariant
            pos <= i <= top <= 9,
            buf@.len() == 10,
            forall|t: int| 0 <= t <= i ==> #[trigger] buf@[t] == old_buf[t],
            forall|t: int| i < t <= top ==> #[trigger] buf@[t] == old_buf[t - 1],
        decreases i,
    {
        let prev = buf[i - 1];
        put(buf, i, prev);
        i = i - 1;
    }
    put(buf, pos, c);
    let r: usize = if len < 10 { len + 1 } else { len };
    proof {
        let view = cands_view(old_buf, len as int);
        let nb = cands_view(buf@, r as int);
        let ia = ins_at(view, pos as int, cand_row(c), 10);
        lemma_topk_ins_len(view, pos as int, cand_row(c));
        assert forall|t: int| 0 <= t < nb.len() implies #[trigger] nb[t] == ia[t] by {
            lemma_topk_ins_index(view, pos as int, cand_row(c), t);
        }
        assert(nb =~= ia);
    }
    r
}

/// Insert a candidate into a top-10 buffer of the rows `all` (the candidate's row is new): the buffer becomes the
/// top 10 of `all` with the candidate.
pub fn topk_insert(buf: &mut Vec<Cand>, len: usize, c: Cand, Ghost(all): Ghost<Seq<Row>>) -> (r: usize)
    requires
        old(buf)@.len() == 10,
        len <= 10,
        topk_ok(q3_keys(), q3_fams(), 10, cands_view(old(buf)@, len as int), all),
        rel_wf(q3_keys(), q3_fams(), all.push(cand_row(c))),
    ensures
        final(buf)@.len() == 10,
        r <= 10,
        topk_ok(q3_keys(), q3_fams(), 10, cands_view(final(buf)@, r as int), all.push(cand_row(c))),
    no_unwind
{
    let ghost keys = q3_keys();
    let ghost fams = q3_fams();
    let ghost view = cands_view(buf@, len as int);
    let ghost rc = cand_row(c);
    if len == 10 {
        if !better(&c, &buf[9]) {
            proof {
                lemma_view_last(buf@, 10);
                lemma_cand_cmp(c, c);
                lemma_cand_cmp(buf@[9], buf@[9]);
                lemma_keys_cmp_antisym(keys, fams, rc, cand_row(buf@[9]));
                lemma_topk_skip(keys, fams, 10, view, all, rc);
            }
            return len;
        }
    }
    let pos = find_pos(buf, len, c, Ghost(all));
    let r = shift_insert(buf, len, pos, c);
    proof {
        lemma_topk_insert(keys, fams, 10, view, all, rc, pos as int);
    }
    r
}

proof fn lemma_topk_ins_len(view: Seq<Row>, pos: int, r: Row)
    requires 0 <= pos <= view.len(),
    ensures ins_at(view, pos, r, 10).len() == min_nat(10, view.len() + 1),
{
}

proof fn lemma_topk_ins_index(view: Seq<Row>, pos: int, r: Row, t: int)
    requires 0 <= pos <= view.len(), 0 <= t < ins_at(view, pos, r, 10).len(),
    ensures ins_at(view, pos, r, 10)[t] == if t < pos { view[t] } else if t == pos { r } else { view[t - 1] },
{
}

// ------------------------------------------------------------------------------------------------ columns

/// The column slices of the model and the bound parameters (`$1` as its dictionary entry `seg`, `$2` as `day`).
/// Slice lengths are fields because slice `len` may unwind in worker bodies.
#[derive(Clone, Copy)]
pub struct Cols {
    pub l_key_c: &'static [u32],
    pub l_key_b: &'static [i64],
    pub l_price_c: &'static [u32],
    pub l_price_b: &'static [i64],
    pub l_disc_c: &'static [u8],
    pub l_disc_b: &'static [i64],
    pub l_ship_c: &'static [u16],
    pub l_ship_b: &'static [i64],
    pub l_ship_z: &'static [i64],
    pub l_st: &'static [u32],
    pub l_nst: usize,
    pub l_bs: u64,
    pub l_n: usize,
    pub l_nb: usize,
    pub o_key_c: &'static [u32],
    pub o_key_b: &'static [i64],
    pub o_cust_c: &'static [u32],
    pub o_cust_b: &'static [i64],
    pub o_date_c: &'static [u16],
    pub o_date_b: &'static [i64],
    pub o_sp_c: &'static [u8],
    pub o_sp_b: &'static [i64],
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
    pub c_seg_c: &'static [u8],
    pub c_seg_b: &'static [u64],
    pub c_bs: u64,
    pub c_n: usize,
    pub c_kind: u64,
    pub c_dense: bool,
    pub segc: u8,
    pub seg_fast: bool,
    pub e32: &'static [u32],
    pub e64: &'static [u64],
    pub seg: u64,
    pub day: i64,
    pub cluster: u64,
}

/// The slices are the model's parts; `seg` is the dictionary entry of `$1`; `c_dense`: customer row `c` has key
/// `c + 1`.
pub open spec fn cols_ok(c: Cols, m: M, p: QP) -> bool {
    &&& c.l_key_c@ == m.l_key_c && c.l_key_b@ == m.l_key_b
    &&& c.l_price_c@ == m.l_price_c && c.l_price_b@ == m.l_price_b
    &&& c.l_disc_c@ == m.l_disc_c && c.l_disc_b@ == m.l_disc_b
    &&& c.l_ship_c@ == m.l_ship_c && c.l_ship_b@ == m.l_ship_b && c.l_ship_z@ == m.l_ship_z
    &&& c.l_bs as int == m.l_bs && c.l_n == m.l_n && c.l_nb == m.l_nb
    &&& c.l_st@ == m.l_st && c.l_nst == m.l_st.len()
    &&& c.o_key_c@ == m.o_key_c && c.o_key_b@ == m.o_key_b
    &&& c.o_cust_c@ == m.o_cust_c && c.o_cust_b@ == m.o_cust_b
    &&& c.o_date_c@ == m.o_date_c && c.o_date_b@ == m.o_date_b
    &&& c.o_sp_c@ == m.o_sp_c && c.o_sp_b@ == m.o_sp_b
    &&& c.o_ic@ == m.o_ic && c.o_ib@ == m.o_ib && c.o_kind == m.o_kind
    &&& c.o_bs as int == m.o_bs && c.o_n == m.o_n && c.o_nb == m.o_nb
    &&& c.idx_ok ==> c.o_bsz as int == m.o_bs
    &&& c.c_key_c@ == m.c_key_c && c.c_key_b@ == m.c_key_b
    &&& c.c_seg_c@ == m.c_seg_c && c.c_seg_b@ == m.c_seg_b
    &&& c.c_bs as int == m.c_bs && c.c_n == m.c_n && c.c_kind == m.c_kind
    &&& c.e32@ == Seq::<u32>::empty() && c.e64@ == Seq::<u64>::empty()
    &&& c.seg < dict_n(m) && cf::text_of(m.d_off, m.d_bytes, c.seg as int) == p.seg
    &&& c.day == p.day
    &&& c.cluster == m.cluster
    &&& c.c_dense ==> forall|i: int| 0 <= i < m.c_n ==> #[trigger] ckey(m, i) == i + 1
    &&& c.seg_fast ==> c.c_dense && forall|i: int| 0 <= i < m.c_n ==> (#[trigger] m.c_seg_c[i] == c.segc) == (cseg(m, i) == c.seg as int)
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
    crate::stores::facts::interface::common::read::lemma_div_lt(j, bs, nb);
}

// ------------------------------------------------------------------------------------------------ customers

/// The customer of key `ck` has the segment (`ccnt(ck) > 0`; under the primary key at most one row has the key).
pub fn cust_ok(c: &Cols, ckv: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: bool)
    requires cols_ok(*c, m, p), model_ok(m),
    ensures r == (ccnt(m, p, ckv as int) > 0),
    no_unwind
{
    let ghost f = cmatch_f(m, p, ckv as int);
    if c.c_dense {
        if ckv >= 1 && (ckv as u64) <= (c.c_n as u64) {
            let row = (ckv - 1) as usize;
            proof { lemma_block_bound(row as int, m.c_bs, m.c_n, m.c_nb); }
            let code = c.c_seg_c[row] as u64;
            let hit = code <= c.seg && c.c_seg_b[((row as u64) / c.c_bs) as usize] == c.seg - code;
            proof {
                assert(hit == (cseg(m, row as int) == c.seg as int));
                lemma_seg_match(*c, m, p, row as int);
                assert forall|i: int| 0 <= i < m.c_n && i != row as int implies #[trigger] f(i) == 0 by {
                    assert(ckey(m, i) == i + 1);
                }
                lemma_isum_single(m.c_n, f, row as int);
            }
            hit
        } else {
            proof {
                assert forall|i: int| 0 <= i < m.c_n implies #[trigger] f(i) == 0 by {
                    assert(ckey(m, i) == i + 1);
                }
                lemma_isum_zero(m.c_n, f);
            }
            false
        }
    } else {
        // general path: scan every customer row
        let mut i: usize = 0;
        let mut found = false;
        while i < c.c_n && !found
            invariant
                cols_ok(*c, m, p), model_ok(m),
                i <= m.c_n,
                f == cmatch_f(m, p, ckv as int),
                found ==> i < m.c_n && f(i as int) == 1,
                !found ==> forall|t: int| 0 <= t < i ==> #[trigger] f(t) == 0,
            decreases m.c_n - i + if found { 0int } else { 1int },
        {
            proof {
                lemma_block_bound(i as int, m.c_bs, m.c_n, m.c_nb);
                assert(in_i64(ckey(m, i as int)));
            }
            let g = ((i as u64) / c.c_bs) as usize;
            let key = c.c_key_b[g] + c.c_key_c[i] as i64;
            let code = c.c_seg_c[i] as u64;
            let hit = key == ckv && code <= c.seg && c.c_seg_b[g] == c.seg - code;
            proof {
                lemma_seg_match(*c, m, p, i as int);
                assert(hit == (f(i as int) == 1));
            }
            if hit {
                found = true;
            } else {
                i = i + 1;
            }
        }
        proof {
            assert forall|t: int| 0 <= t < m.c_n implies #[trigger] f(t) >= 0 by {}
            if found {
                lemma_isum_ge_term(m.c_n, f, i as int);
            } else {
                lemma_isum_zero(m.c_n, f);
            }
        }
        found
    }
}

/// A customer row has the segment exactly when its dictionary entry is `seg` (the dictionary entries are distinct).
pub proof fn lemma_seg_match(c: Cols, m: M, p: QP, row: int)
    requires cols_ok(c, m, p), model_ok(m), 0 <= row < m.c_n,
    ensures (segtext(m, row) == p.seg) == (cseg(m, row) == c.seg as int),
{
    assert(in_i64(ckey(m, row)));
    if cseg(m, row) != c.seg as int {
        cf::lemma_dict_distinct(m.d_off, m.d_bytes, dict_n(m), cseg(m, row), c.seg as int);
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

/// A lineitem block cursor: `lg` is the block of the row `j` (or `j` starts block `lg + 1`).
pub open spec fn lcur_ok(m: M, j: int, lg: int, lge: int) -> bool {
    &&& m.l_bs >= 1
    &&& lg * m.l_bs <= j <= lge
    &&& lge == (lg + 1) * m.l_bs
    &&& j <= m.l_n
    &&& lge <= m.l_n + m.l_bs
}

/// An orders block cursor.
pub open spec fn ocur_ok(m: M, q: int, og: int, oge: int) -> bool {
    &&& m.o_bs >= 1
    &&& og * m.o_bs <= q <= oge
    &&& oge == (og + 1) * m.o_bs
    &&& q <= m.o_n
    &&& oge <= m.o_n + m.o_bs
}

/// Bounds of the SUM argument: at most 31 digits.
proof fn lemma_arg_bound(pr: int, ds: int)
    requires -pow10(15) < pr < pow10(15), -pow10(15) < ds < pow10(15),
    ensures abs(pr * (100 - ds)) < pow10(31), pow10(31) == 10000000000000000000000000000000,
        pow10(15) == 1000000000000000,
{
    assert(pow10(15) == 1000000000000000) by (compute);
    assert(pow10(31) == 10000000000000000000000000000000) by (compute);
    let x = abs(pr);
    let y = abs(100 - ds);
    assert(abs(pr * (100 - ds)) == x * y) by (nonlinear_arith) requires x == abs(pr), y == abs(100 - ds);
    assert(x * y < 10000000000000000000000000000000) by (nonlinear_arith)
        requires 0 <= x < 1000000000000000, 0 <= y < 1000000000000100;
}

/// The SUM argument coefficient of lineitem row `j` (block `g`).
pub fn row_arg(c: &Cols, j: usize, g: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (a: i128)
    requires cols_ok(*c, m, p), model_ok(m), j < m.l_n, g as int == j as int / m.l_bs,
    ensures a as int == larg(m, j as int), abs(a as int) < 10000000000000000000000000000000,
    no_unwind
{
    proof {
        lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
        assert(in_i64(lkey(m, j as int)));
        lemma_arg_bound(lprice(m, j as int), ldisc(m, j as int));
    }
    let price = c.l_price_b[g] + c.l_price_c[j] as i64;
    let disc = c.l_disc_b[g] + c.l_disc_c[j] as i64;
    (price as i128) * (100 - disc as i128)
}

/// Partial sums of one order over lineitem rows `[j0, j)`.
pub open spec fn dsum(f: spec_fn(int) -> int, j0: int, j: int) -> int {
    isum(j, f) - isum(j0, f)
}

/// One accumulation step of an order's revenue: the count always; the sum and the absolute sum while the absolute
/// sum stays inside `i128` (beyond it the order's mass is outside the capacity condition).
pub open spec fn acc_ok(m: M, p: QP, q: int, j0: int, j: int, cnt: u64, sum: i128, ab: u128, ovf: bool) -> bool {
    &&& cnt as int == dsum(lcnt_f(m, p, q), j0, j)
    &&& cnt as int <= j - j0
    &&& !ovf ==> sum as int == dsum(lsum_f(m, p, q), j0, j) && ab as int == dsum(labs_f(m, p, q), j0, j)
        && ab as int <= i128_max() && -(ab as int) <= sum as int <= ab as int
    &&& ovf ==> dsum(labs_f(m, p, q), j0, j) > i128_max()
}

/// The terms of an order's sums at one row.
pub proof fn lemma_terms_at(m: M, p: QP, q: int, j: int)
    ensures
        lcnt_f(m, p, q)(j) == if lhit(m, p, q, j) { 1int } else { 0int },
        lsum_f(m, p, q)(j) == if lhit(m, p, q, j) { larg(m, j) } else { 0int },
        labs_f(m, p, q)(j) == if lhit(m, p, q, j) { abs(larg(m, j)) } else { 0int },
        labs_f(m, p, q)(j) >= 0,
{
}

/// Accumulate row `j` (a hit with argument `a`, or not a hit) into an order's sums.
fn acc_row(cnt: u64, sum: i128, ab: u128, ovf: bool, hitj: bool, a: i128, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>,
    Ghost(q): Ghost<int>, Ghost(j0): Ghost<int>, Ghost(j): Ghost<int>) -> (r: (u64, i128, u128, bool))
    requires
        acc_ok(m, p, q, j0, j, cnt, sum, ab, ovf),
        0 <= j0 <= j,
        j < u64::MAX,
        hitj == lhit(m, p, q, j),
        hitj ==> a as int == larg(m, j) && abs(a as int) < 10000000000000000000000000000000,
    ensures
        acc_ok(m, p, q, j0, j + 1, r.0, r.1, r.2, r.3),
    no_unwind
{
    proof {
        lemma_terms_at(m, p, q, j);
        lemma_isum_step(j, lcnt_f(m, p, q));
        lemma_isum_step(j, lsum_f(m, p, q));
        lemma_isum_step(j, labs_f(m, p, q));
    }
    if !hitj {
        return (cnt, sum, ab, ovf);
    }
    let cnt1 = cnt + 1;
    if ovf {
        return (cnt1, sum, ab, ovf);
    }
    let aa: u128 = if a < 0 { (0 - a) as u128 } else { a as u128 };
    assert(aa as int == abs(larg(m, j)));
    let na = ab + aa;
    if na > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 {
        (cnt1, sum, ab, true)
    } else {
        (cnt1, sum + a, na, false)
    }
}

/// The lineitem run of the order at `q` (key `okv`) from the cursor `j0`: count, revenue and absolute revenue of its
/// rows shipped after the date, and the cursor after the run (the first row of the next order).
pub fn fast_sums(c: &Cols, okv: i64, j0: usize, l_hi: usize, lg0: usize, lge0: u64,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(q): Ghost<int>) -> (r: (u64, i128, u128, bool, usize, usize, u64))
    requires
        cols_ok(*c, m, p), model_ok(m), m.cluster == 1,
        0 <= q < m.o_n, okv == okey(m, q),
        lb_ok(m, q, j0 as int),
        j0 <= l_hi <= m.l_n,
        forall|t: int| l_hi <= t < m.l_n ==> #[trigger] lpos(m, t) > q,
        lcur_ok(m, j0 as int, lg0 as int, lge0 as int),
    ensures ({
        let (cnt, sum, ab, ovf, j1, lg1, lge1) = r;
        &&& j0 <= j1 <= l_hi
        &&& lb_ok(m, q + 1, j1 as int)
        &&& lcur_ok(m, j1 as int, lg1 as int, lge1 as int)
        &&& cnt as int == lcnt(m, p, q)
        &&& !ovf ==> sum as int == lsum(m, p, q) && ab as int == labs(m, p, q) && ab as int <= i128_max()
        &&& ovf ==> labs(m, p, q) > i128_max()
    }),
    no_unwind
{
    let mut j = j0;
    let mut lg = lg0;
    let mut lge = lge0;
    let mut cnt: u64 = 0;
    let mut sum: i128 = 0;
    let mut ab: u128 = 0;
    let mut ovf = false;
    let mut stop = false;
    while j < l_hi && !stop
        invariant
            cols_ok(*c, m, p), model_ok(m), m.cluster == 1,
            0 <= q < m.o_n, okv == okey(m, q),
            lb_ok(m, q, j0 as int),
            j0 <= j <= l_hi <= m.l_n,
            lcur_ok(m, j as int, lg as int, lge as int),
            forall|t: int| j0 <= t < j ==> #[trigger] lkey(m, t) == okey(m, q),
            stop ==> j < l_hi && lkey(m, j as int) != okey(m, q),
            acc_ok(m, p, q, j0 as int, j as int, cnt, sum, ab, ovf),
        decreases l_hi - j + if stop { 0int } else { 1int },
    {
        if j as u64 == lge {
            proof {
                assert((lg + 2) * m.l_bs == (lg + 1) * m.l_bs + m.l_bs) by (nonlinear_arith);
                // the next block holds row j < l_n, so it is a block of the table
                lemma_div_in(j as int, m.l_bs, lg as int + 1);
                lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
            }
            lg = lg + 1;
            lge = lge + c.l_bs;
        }
        assert(lg * m.l_bs <= j < lge && lge == (lg + 1) * m.l_bs);
        proof {
            lemma_div_in(j as int, m.l_bs, lg as int);
            lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
            assert(in_i64(lkey(m, j as int)));
        }
        let lk = c.l_key_b[lg] + c.l_key_c[j] as i64;
        if lk != okv {
            stop = true;
        } else {
            let sh = c.l_ship_b[lg] + c.l_ship_c[j] as i64;
            let hitj = sh > c.day;
            let a: i128 = if hitj { row_arg(c, j, lg, Ghost(m), Ghost(p)) } else { 0 };
            let r = acc_row(cnt, sum, ab, ovf, hitj, a, Ghost(m), Ghost(p), Ghost(q), Ghost(j0 as int), Ghost(j as int));
            cnt = r.0;
            sum = r.1;
            ab = r.2;
            ovf = r.3;
            j = j + 1;
        }
    }
    proof {
        // the order's rows are exactly [j0, j)
        assert forall|t: int| 0 <= t < m.l_n && (t < j0 || t >= j) implies lkey(m, t) != okey(m, q) by {
            lemma_lpos_key(m, q, t);
            if t >= j {
                if j < l_hi {
                    lemma_lpos_key(m, q, j as int);
                    lemma_lpos_mono(m, j as int, t);
                }
            }
        }
        lemma_run_totals(m, p, q, j0 as int, j as int);
        assert forall|t: int| 0 <= t < j implies #[trigger] lpos(m, t) < q + 1 by {
            if t >= j0 {
                lemma_lpos_key(m, q, t);
            }
        }
        assert forall|t: int| j <= t < m.l_n implies #[trigger] lpos(m, t) >= q + 1 by {
            if j < l_hi {
                lemma_lpos_key(m, q, j as int);
                lemma_lpos_mono(m, j as int, t);
            }
        }
    }
    (cnt, sum, ab, ovf, j, lg, lge)
}

/// When an order's rows are exactly `[j0, j)`, its partial sums there are its totals.
pub proof fn lemma_run_totals(m: M, p: QP, q: int, j0: int, j: int)
    requires
        0 <= j0 <= j <= m.l_n,
        forall|t: int| 0 <= t < m.l_n && (t < j0 || t >= j) ==> lkey(m, t) != okey(m, q),
    ensures
        dsum(lcnt_f(m, p, q), j0, j) == lcnt(m, p, q),
        dsum(lsum_f(m, p, q), j0, j) == lsum(m, p, q),
        dsum(labs_f(m, p, q), j0, j) == labs(m, p, q),
{
    assert forall|t: int| 0 <= t < j0 implies #[trigger] lcnt_f(m, p, q)(t) == 0 && lsum_f(m, p, q)(t) == 0 && labs_f(m, p, q)(t) == 0 by {}
    assert forall|t: int| j <= t < m.l_n implies #[trigger] lcnt_f(m, p, q)(t) == 0 && lsum_f(m, p, q)(t) == 0 && labs_f(m, p, q)(t) == 0 by {}
    lemma_isum_prefix_zero(j0, lcnt_f(m, p, q));
    lemma_isum_prefix_zero(j0, lsum_f(m, p, q));
    lemma_isum_prefix_zero(j0, labs_f(m, p, q));
    lemma_isum_suffix_zero(j, m.l_n, lcnt_f(m, p, q));
    lemma_isum_suffix_zero(j, m.l_n, lsum_f(m, p, q));
    lemma_isum_suffix_zero(j, m.l_n, labs_f(m, p, q));
}

/// The general path: an order's sums by a scan of every lineitem row.
fn scan_sums(c: &Cols, okv: i64, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(q): Ghost<int>) -> (r: (u64, i128, u128, bool))
    requires
        cols_ok(*c, m, p), model_ok(m),
        0 <= q < m.o_n, okv == okey(m, q),
    ensures ({
        let (cnt, sum, ab, ovf) = r;
        &&& cnt as int == lcnt(m, p, q)
        &&& !ovf ==> sum as int == lsum(m, p, q) && ab as int == labs(m, p, q) && ab as int <= i128_max()
        &&& ovf ==> labs(m, p, q) > i128_max()
    }),
    no_unwind
{
    let mut j: usize = 0;
    let mut cnt: u64 = 0;
    let mut sum: i128 = 0;
    let mut ab: u128 = 0;
    let mut ovf = false;
    while j < c.l_n
        invariant
            cols_ok(*c, m, p), model_ok(m),
            0 <= q < m.o_n, okv == okey(m, q),
            j <= m.l_n,
            acc_ok(m, p, q, 0, j as int, cnt, sum, ab, ovf),
        decreases m.l_n - j,
    {
        let g = ((j as u64) / c.l_bs) as usize;
        proof {
            lemma_block_bound(j as int, m.l_bs, m.l_n, m.l_nb);
            assert(in_i64(lkey(m, j as int)));
        }
        let lk = c.l_key_b[g] + c.l_key_c[j] as i64;
        let sh = c.l_ship_b[g] + c.l_ship_c[j] as i64;
        let hitj = lk == okv && sh > c.day;
        let a: i128 = if hitj { row_arg(c, j, g, Ghost(m), Ghost(p)) } else { 0 };
        let r = acc_row(cnt, sum, ab, ovf, hitj, a, Ghost(m), Ghost(p), Ghost(q), Ghost(0), Ghost(j as int));
        cnt = r.0;
        sum = r.1;
        ab = r.2;
        ovf = r.3;
        j = j + 1;
    }
    proof {
        assert(dsum(lcnt_f(m, p, q), 0, m.l_n) == lcnt(m, p, q));
        assert(dsum(lsum_f(m, p, q), 0, m.l_n) == lsum(m, p, q));
        assert(dsum(labs_f(m, p, q), 0, m.l_n) == labs(m, p, q));
    }
    (cnt, sum, ab, ovf)
}

// ------------------------------------------------------------------------------------------------ chunk task

/// The group rows of a range of orders are distinct and their ORDER BY keys are in their families.
pub proof fn lemma_gseq_wf_range(m: M, p: QP, lo: int, hi: int)
    requires model_ok(m), 0 <= lo, hi <= m.o_n,
    ensures rel_wf(q3_keys(), q3_fams(), gseq(m, p, lo, hi)),
{
    lemma_gseq_nodup(m, p, lo, hi);
    lemma_gseq_contains(m, p, lo, hi);
    let s = gseq(m, p, lo, hi);
    assert forall|i: int| 0 <= i < s.len() implies keys_ok(q3_keys(), q3_fams(), #[trigger] s[i]) by {
        assert(s.contains(s[i]));
        let q = choose|q: int| lo <= q < hi && good(m, p, q) && s[i] == grow(m, p, q);
        assert forall|t: int| 0 <= t < q3_keys().len() implies #[trigger] key_ok(q3_keys()[t], q3_fams()[t], s[i]) by {}
    }
}

/// The orders positions `[o_lo, o_hi)` of one task (`fast`: the lineitem rows of these orders are `[l_lo, l_hi)`,
/// co-clustered), with the preallocated top-10 buffer.
pub struct Chunk {
    pub cols: Cols,
    pub o_lo: usize,
    pub o_hi: usize,
    pub l_lo: usize,
    pub l_hi: usize,
    pub fast: bool,
    pub buf: Vec<Cand>,
    pub sel: Vec<usize>,
    pub bm: Arc<Vec<u64>>,
    pub use_bm: bool,
    pub m: Ghost<M>,
    pub p: Ghost<QP>,
}

/// A task's result: its top-10 buffer, or (`ovf`) an order of the range whose revenue mass leaves `i128`.
pub struct ChunkOut {
    pub buf: Vec<Cand>,
    pub len: usize,
    pub ovf: bool,
    pub ovf_q: usize,
}

pub open spec fn chunk_pre(t: Chunk) -> bool {
    let m = t.m@;
    let p = t.p@;
    &&& cols_ok(t.cols, m, p)
    &&& model_ok(m)
    &&& t.buf@.len() == 10
    &&& t.o_lo <= t.o_hi <= m.o_n
    &&& t.fast && t.cols.seg_fast ==> t.sel@.len() == BATCH
    &&& t.use_bm ==> bm_ok(t.bm@, m, t.cols)
    &&& t.fast ==> {
        &&& m.cluster == 1
        &&& t.l_lo <= t.l_hi <= m.l_n
        &&& lb_ok(m, t.o_lo as int, t.l_lo as int)
        &&& lb_ok(m, t.o_hi as int, t.l_hi as int)
    }
}

pub open spec fn chunk_post(t: Chunk, out: ChunkOut) -> bool {
    let m = t.m@;
    let p = t.p@;
    &&& out.buf@.len() == 10
    &&& out.len <= 10
    &&& out.ovf ==> t.o_lo <= out.ovf_q < t.o_hi && good(m, p, out.ovf_q as int) && labs(m, p, out.ovf_q as int) > i128_max()
    &&& !out.ovf ==> {
        &&& topk_ok(q3_keys(), q3_fams(), 10, cands_view(out.buf@, out.len as int), gseq(m, p, t.o_lo as int, t.o_hi as int))
        &&& forall|q: int| t.o_lo <= q < t.o_hi && #[trigger] good(m, p, q) ==> labs(m, p, q) <= i128_max()
    }
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
        let Chunk { cols, o_lo, o_hi, l_lo, l_hi, fast, buf, sel, bm, use_bm, m: gm, p: gp } = self;
        let ghost m = gm@;
        let ghost p = gp@;
        if fast && cols.seg_fast {
            let mut buf = buf;
            let mut sel = sel;
            let bmv: &Vec<u64> = &*bm;
            if o_hi < cols.l_nst {
                let (aligned, len, ovf, ovf_q) = super::dirsel::run_dir(&cols, bmv, use_bm, o_lo, o_hi, &mut buf, &mut sel,
                    Ghost(m), Ghost(p));
                if aligned {
                    return ChunkOut { buf, len, ovf, ovf_q };
                }
            }
            let (len, ovf, ovf_q) = run_sel(&cols, bmv, use_bm, o_lo, o_hi, l_lo, l_hi, &mut buf, &mut sel, Ghost(m), Ghost(p));
            return ChunkOut { buf, len, ovf, ovf_q };
        }
        let c = cols;
        let mut buf = buf;
        let mut len: usize = 0;
        let mut q = o_lo;
        let mut j = l_lo;
        let mut lg: usize = 0;
        let mut lge: u64 = 0;
        if fast {
            let lg64 = (j as u64) / c.l_bs;
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j as int, m.l_bs);
                vstd::arithmetic::div_mod::lemma_mod_pos_bound(j as int, m.l_bs);
                assert(m.l_bs * lg64 == lg64 * m.l_bs) by (nonlinear_arith);
                assert((lg64 + 1) * m.l_bs == lg64 * m.l_bs + m.l_bs) by (nonlinear_arith);
                assert(lg64 <= j) by (nonlinear_arith) requires lg64 * m.l_bs <= j, m.l_bs >= 1, lg64 >= 0;
            }
            lg = lg64 as usize;
            lge = (lg64 + 1) * c.l_bs;
        }
        proof {
            lemma_topk_empty(q3_keys(), q3_fams(), 10);
            lemma_gseq_empty(m, p, o_lo as int);
            assert(cands_view(buf@, 0) =~= Seq::<Row>::empty());
        }
        let mut found = false;
        let mut found_q: usize = 0;
        while q < o_hi && !found
            invariant
                task == (Chunk { cols, o_lo, o_hi, l_lo, l_hi, fast, buf: task.buf, sel: task.sel, bm: task.bm, use_bm, m: gm, p: gp }),
                found ==> o_lo <= found_q < o_hi && good(m, p, found_q as int) && labs(m, p, found_q as int) > i128_max(),
                m == gm@, p == gp@, c == cols,
                cols_ok(c, m, p),
                model_ok(m),
                o_lo <= q <= o_hi <= m.o_n,
                buf@.len() == 10,
                len <= 10,
                fast && !found ==> {
                    &&& m.cluster == 1
                    &&& j <= l_hi <= m.l_n
                    &&& lb_ok(m, q as int, j as int)
                    &&& lb_ok(m, o_hi as int, l_hi as int)
                    &&& lcur_ok(m, j as int, lg as int, lge as int)
                },
                topk_ok(q3_keys(), q3_fams(), 10, cands_view(buf@, len as int), gseq(m, p, o_lo as int, q as int)),
                forall|q2: int| o_lo <= q2 < q && #[trigger] good(m, p, q2) ==> labs(m, p, q2) <= i128_max(),
            decreases o_hi - q + if found { 0int } else { 1int },
        {
            let og = ((q as u64) / c.o_bs) as usize;
            proof {
                lemma_block_bound(q as int, m.o_bs, m.o_n, m.o_nb);
                assert(in_i64(okey(m, q as int)));
            }
            let okv = c.o_key_b[og] + c.o_key_c[q] as i64;
            let mut cnt: u64 = 0;
            let mut sum: i128 = 0;
            let mut ab: u128 = 0;
            let mut ovf = false;
            if fast {
                proof {
                    assert forall|t: int| l_hi <= t < m.l_n implies #[trigger] lpos(m, t) > q by {}
                }
                let r = fast_sums(&c, okv, j, l_hi, lg, lge, Ghost(m), Ghost(p), Ghost(q as int));
                cnt = r.0;
                sum = r.1;
                ab = r.2;
                ovf = r.3;
                j = r.4;
                lg = r.5;
                lge = r.6;
            } else {
                let r = scan_sums(&c, okv, Ghost(m), Ghost(p), Ghost(q as int));
                cnt = r.0;
                sum = r.1;
                ab = r.2;
                ovf = r.3;
            }
            let ghost gq = good(m, p, q as int);
            let ghost g0 = gseq(m, p, o_lo as int, q as int);
            proof {
                lemma_gseq_step(m, p, o_lo as int, q as int);
            }
            if cnt > 0 {
                let date = c.o_date_b[og] + c.o_date_c[q] as i64;
                if date < c.day {
                    let ckv = c.o_cust_b[og] + c.o_cust_c[q] as i64;
                    if cust_ok(&c, ckv, Ghost(m), Ghost(p)) {
                        assert(gq);
                        if ovf {
                            found = true;
                            found_q = q;
                        } else {
                        let sp = c.o_sp_b[og] + c.o_sp_c[q] as i64;
                        let cand = Cand { okey: okv, rev: sum, date, sp };
                        proof {
                            assert(cand_row(cand) =~= grow(m, p, q as int));
                            lemma_gseq_wf_range(m, p, o_lo as int, q as int + 1);
                        }
                        len = topk_insert(&mut buf, len, cand, Ghost(g0));
                        }
                    } else {
                        assert(!gq);
                    }
                } else {
                    assert(!gq);
                }
            } else {
                assert(!gq);
            }
            if !found {
                q = q + 1;
            }
        }
        if found {
            return ChunkOut { buf, len, ovf: true, ovf_q: found_q };
        }
        ChunkOut { buf, len, ovf: false, ovf_q: 0 }
    }
}

} // verus!
