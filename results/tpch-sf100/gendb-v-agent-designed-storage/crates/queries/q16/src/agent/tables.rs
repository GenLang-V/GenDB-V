//! Column handles of the three Q16 tables, read from the storages `custpart` (part) and `suppliers` (partsupp,
//! supplier), and partsupp's key runs from `psrun` (its part `RUNS`; psrun extends suppliers)
//! (partsupp, supplier) as zero-copy extents, and the values they decode to.
//!
//! Every stored table is in canonical row order with uniform groups of `bs` rows (`ng` groups); a frame-of-reference
//! (FOR) column stores row `j` as `base[j / bs] + code[j]` (`fv32`, `fv8`, `fu8`); a dictionary column stores the
//! FOR-coded index of an entry of offsets + bytes; plain text is offsets + bytes (`txt`). `*_row_ok(c, r, j)` states
//! what row `j` of a table is in terms of its handles `c`; `*cols_ok(c, rel)` states it for every row, plus the shape
//! facts (lengths, frame) the readers need. Adapted from the admitted Q2 package (same storages).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::{Column, SqlType};
use crate::spec::typing::value_in_column;
use crate::link::source::rows_in_columns;
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::stored::{StoredParts, part_len};
use crate::gendb_entry::layout::PartView;
use crate::stores::custpart::interface as cpi;
use crate::stores::suppliers::interface as spi;
use crate::stores::psrun::interface as pri;
use crate::stores::custpart::declaration as cpd;
use crate::stores::suppliers::declaration as spd;

verus! {

// ------------------------------------------------------------------------------------------------ decoding

/// FOR value of row `j` (U32 codes, I64 bases, blocks of `bs` rows).
pub open spec fn fv32(c: Seq<u32>, b: Seq<i64>, bs: int, j: int) -> int {
    b[j / bs] + c[j]
}

/// FOR value of row `j` (U8 codes, I64 bases).
pub open spec fn fv8(c: Seq<u8>, b: Seq<i64>, bs: int, j: int) -> int {
    b[j / bs] + c[j]
}

/// FOR dictionary index of row `j` (U8 codes, U64 bases).
pub open spec fn fu8(c: Seq<u8>, b: Seq<u64>, bs: int, j: int) -> int {
    b[j / bs] + c[j]
}

pub open spec fn i64r(x: int) -> bool {
    i64::MIN <= x <= i64::MAX
}

/// Text value `j` of offsets `o` and bytes `y`.
pub open spec fn txt(o: Seq<u64>, y: Seq<u8>, j: int) -> Seq<u8> {
    y.subrange(o[j] as int, o[j + 1] as int)
}

/// `n` text values: `n + 1` offsets, each value a byte range inside `y`.
pub open spec fn txt_ok(o: Seq<u64>, y: Seq<u8>, n: int) -> bool {
    &&& o.len() == n + 1
    &&& forall|j: int| 0 <= j < n ==> #[trigger] o[j] <= o[j + 1] && o[j + 1] <= y.len()
}

/// Uniform groups: `ng` groups of `bs` rows cover the `n` rows (the last possibly partial).
pub open spec fn frame_ok(n: int, bs: int, ng: int) -> bool {
    &&& bs >= 1
    &&& n >= 0
    &&& ng >= 0
    &&& ng * bs >= n
    &&& ng > 0 ==> (ng - 1) * bs < n
}

// ------------------------------------------------------------------------------------------------ handles

/// part: p_partkey (FOR u32), p_brand and p_type (dictionaries), p_size (FOR u8), the key index kind.
#[derive(Clone, Copy)]
pub struct PCols {
    pub n: usize,
    pub bs: usize,
    pub ng: usize,
    pub kind: u64,
    pub key_c: &'static [u32],
    pub key_b: &'static [i64],
    pub brand_c: &'static [u8],
    pub brand_b: &'static [u64],
    pub brand_o: &'static [u64],
    pub brand_y: &'static [u8],
    pub type_c: &'static [u8],
    pub type_b: &'static [u64],
    pub type_o: &'static [u64],
    pub type_y: &'static [u8],
    pub size_c: &'static [u8],
    pub size_b: &'static [i64],
}

/// partsupp: ps_partkey and ps_suppkey (FOR u32), the key index kind of ps_partkey.
#[derive(Clone, Copy)]
pub struct PSCols {
    pub n: usize,
    pub bs: usize,
    pub ng: usize,
    pub kind: u64,
    pub key_c: &'static [u32],
    pub key_b: &'static [i64],
    pub supp_c: &'static [u32],
    pub supp_b: &'static [i64],
    /// psrun's key runs: the ratio, then one entry per block of `RUN_ROWS` rows (`runs_hold`).
    pub runs: &'static [i64],
}

/// supplier: s_suppkey (FOR u32), s_comment (text), key index kind.
#[derive(Clone, Copy)]
pub struct SCols {
    pub n: usize,
    pub bs: usize,
    pub ng: usize,
    pub kind: u64,
    pub key_c: &'static [u32],
    pub key_b: &'static [i64],
    pub comm_o: &'static [u64],
    pub comm_y: &'static [u8],
    /// The number of comment bytes (`comm_y`'s length).
    pub comm_len: usize,
}

/// Every handle the statement reads, and two empty key-index parts (these tables' key indexes have none).
#[derive(Clone, Copy)]
pub struct Cols {
    pub p: PCols,
    pub ps: PSCols,
    pub s: SCols,
    pub e32: &'static [u32],
    pub e64: &'static [u64],
}

// ------------------------------------------------------------------------------------------------ row facts

/// A dictionary of `o.len() - 1` entries.
pub open spec fn dict_ok(o: Seq<u64>, y: Seq<u8>) -> bool {
    o.len() >= 1 && o.len() <= usize::MAX && txt_ok(o, y, o.len() - 1)
}

pub open spec fn part_row_ok(c: PCols, r: Row, i: int) -> bool {
    let bs = c.bs as int;
    &&& r.len() == 9
    &&& r[0] == Val::Int(fv32(c.key_c@, c.key_b@, bs, i)) && i64r(fv32(c.key_c@, c.key_b@, bs, i))
    &&& 0 <= fu8(c.brand_c@, c.brand_b@, bs, i) < c.brand_o@.len() - 1
    &&& r[3] == Val::Text(txt(c.brand_o@, c.brand_y@, fu8(c.brand_c@, c.brand_b@, bs, i)))
    &&& 0 <= fu8(c.type_c@, c.type_b@, bs, i) < c.type_o@.len() - 1
    &&& r[4] == Val::Text(txt(c.type_o@, c.type_y@, fu8(c.type_c@, c.type_b@, bs, i)))
    &&& r[5] == Val::Int(fv8(c.size_c@, c.size_b@, bs, i)) && i64r(fv8(c.size_c@, c.size_b@, bs, i))
}

pub open spec fn pcols_ok(c: PCols, p: Seq<Row>, e32: Seq<u32>, e64: Seq<u64>) -> bool {
    &&& frame_ok(c.n as int, c.bs as int, c.ng as int)
    &&& p.len() == c.n
    &&& c.key_c@.len() == c.n && c.key_b@.len() == c.ng
    &&& c.brand_c@.len() == c.n && c.brand_b@.len() == c.ng && dict_ok(c.brand_o@, c.brand_y@)
    &&& c.type_c@.len() == c.n && c.type_b@.len() == c.ng && dict_ok(c.type_o@, c.type_y@)
    &&& c.size_c@.len() == c.n && c.size_b@.len() == c.ng
    &&& cpi::common::colfmt::dict_sorted(c.brand_o@, c.brand_y@, c.brand_o@.len() - 1)
    &&& cpi::common::colfmt::dict_sorted(c.type_o@, c.type_y@, c.type_o@.len() - 1)
    &&& forall|i: int| 0 <= i < c.n ==> #[trigger] part_row_ok(c, p[i], i)
    &&& cpi::common::keyidx::keyidx_ok(c.key_c@, c.key_b@, e32, e64, c.bs as int, c.kind, c.n as int)
}

pub open spec fn ps_row_ok(c: PSCols, r: Row, k: int) -> bool {
    let bs = c.bs as int;
    &&& r.len() == 5
    &&& r[0] == Val::Int(fv32(c.key_c@, c.key_b@, bs, k)) && i64r(fv32(c.key_c@, c.key_b@, bs, k))
    &&& r[1] == Val::Int(fv32(c.supp_c@, c.supp_b@, bs, k)) && i64r(fv32(c.supp_c@, c.supp_b@, bs, k))
}

pub open spec fn pscols_ok(c: PSCols, ps: Seq<Row>, e32: Seq<u32>, e64: Seq<u64>) -> bool {
    &&& frame_ok(c.n as int, c.bs as int, c.ng as int)
    &&& ps.len() == c.n
    &&& c.key_c@.len() == c.n && c.key_b@.len() == c.ng
    &&& c.supp_c@.len() == c.n && c.supp_b@.len() == c.ng
    &&& forall|k: int| 0 <= k < c.n ==> #[trigger] ps_row_ok(c, ps[k], k)
    &&& spi::common::keyidx::keyidx_ok(c.key_c@, c.key_b@, e32, e64, c.bs as int, c.kind, c.n as int)
}

/// The key runs: `runs[0] >= 1` rows per key; a block entry other than `NO_RUN` is the key of the block's first row,
/// and row `i` of block `b` has key `runs[b + 1] + (i - b * RUN_ROWS) / runs[0]`.
pub open spec fn runs_hold(c: PSCols) -> bool {
    &&& c.runs@.len() == pri::run_blocks(c.n as int) + 1
    &&& c.runs@[0] >= 1
    &&& forall|b: int| 0 <= b < pri::run_blocks(c.n as int) && #[trigger] c.runs@[b + 1] != pri::NO_RUN ==>
        forall|i: int| b * pri::RUN_ROWS <= i < c.n && i < b * pri::RUN_ROWS + pri::RUN_ROWS ==>
            #[trigger] fv32(c.key_c@, c.key_b@, c.bs as int, i) == c.runs@[b + 1] + (i - b * pri::RUN_ROWS) / (c.runs@[0] as int)
}

pub open spec fn supp_row_ok(c: SCols, r: Row, j: int) -> bool {
    let bs = c.bs as int;
    &&& r.len() == 7
    &&& r[0] == Val::Int(fv32(c.key_c@, c.key_b@, bs, j)) && i64r(fv32(c.key_c@, c.key_b@, bs, j))
    &&& r[6] == Val::Text(txt(c.comm_o@, c.comm_y@, j))
}

pub open spec fn scols_ok(c: SCols, s: Seq<Row>, e32: Seq<u32>, e64: Seq<u64>) -> bool {
    &&& frame_ok(c.n as int, c.bs as int, c.ng as int)
    &&& s.len() == c.n
    &&& c.key_c@.len() == c.n && c.key_b@.len() == c.ng
    &&& txt_ok(c.comm_o@, c.comm_y@, c.n as int)
    &&& c.comm_len == c.comm_y@.len()
    &&& forall|j: int| 0 <= j < c.n ==> #[trigger] supp_row_ok(c, s[j], j)
    &&& spi::common::keyidx::keyidx_ok(c.key_c@, c.key_b@, e32, e64, c.bs as int, c.kind, c.n as int)
}

/// The three tables of the statement (full rows, canonical order): part, partsupp, supplier.
pub struct Tabs {
    pub p: Seq<Row>,
    pub ps: Seq<Row>,
    pub s: Seq<Row>,
}

pub open spec fn cols_ok(c: Cols, t: Tabs) -> bool {
    &&& c.e32@ == Seq::<u32>::empty()
    &&& c.e64@ == Seq::<u64>::empty()
    &&& pcols_ok(c.p, t.p, c.e32@, c.e64@)
    &&& pscols_ok(c.ps, t.ps, c.e32@, c.e64@)
    &&& runs_hold(c.ps)
    &&& scols_ok(c.s, t.s, c.e32@, c.e64@)
}

// ------------------------------------------------------------------------------------------------ lemmas

/// Row `j` of `n` lies in a group below `ng`.
pub proof fn lemma_grp_bound(n: int, bs: int, ng: int, j: int)
    requires frame_ok(n, bs, ng), 0 <= j < n,
    ensures 0 <= j / bs < ng,
{
    cpi::common::read::lemma_div_lt(j, bs, ng);
}

/// Rows `g * bs .. (g + 1) * bs` are group `g`.
pub proof fn lemma_in_group(bs: int, g: int, j: int)
    requires bs >= 1, g >= 0, g * bs <= j < g * bs + bs,
    ensures j / bs == g,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bs);
    let q = j / bs;
    assert(bs * q == q * bs) by (nonlinear_arith);
    if q < g {
        assert(q * bs + bs <= g * bs) by (nonlinear_arith) requires q < g, bs >= 1;
    }
    if q > g {
        assert(q * bs >= g * bs + bs) by (nonlinear_arith) requires q > g, bs >= 1;
    }
}

/// The block size the handles use: the stored one when it is at most the row count, else the row count (or 1 for an
/// empty table). Same groups for every row: one group when the stored blocks exceed the table.
pub open spec fn eff_bs(n: int, bt: int) -> int {
    if bt <= n { bt } else if n > 0 { n } else { 1 }
}

/// The effective block size gives the frame of the stored uniform groups and the same group of every row.
proof fn lemma_eff_bs(n: int, bt: int, ng: int)
    requires 0 <= n, 1 <= bt, n + bt <= u64::MAX, ng == cpi::common::colfmt::nblocks_of(n, bt),
    ensures
        frame_ok(n, eff_bs(n, bt), ng),
        forall|j: int| 0 <= j < n ==> #[trigger] (j / eff_bs(n, bt)) == j / bt,
{
    cpi::common::colfmt::lemma_nblocks(n, bt);
    if bt > n && n > 0 {
        assert(ng == 1) by {
            assert((n + bt - 1) / bt == 1) by {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n + bt - 1, bt);
                vstd::arithmetic::div_mod::lemma_mod_pos_bound(n + bt - 1, bt);
                let q = (n + bt - 1) / bt;
                assert(bt * q == q * bt) by (nonlinear_arith);
                if q >= 2 {
                    assert(q * bt >= 2 * bt) by (nonlinear_arith) requires q >= 2, bt >= 1;
                }
                if q <= 0 {
                    assert(q * bt <= 0) by (nonlinear_arith) requires q <= 0, bt >= 1;
                }
            }
        }
        assert forall|j: int| 0 <= j < n implies #[trigger] (j / eff_bs(n, bt)) == j / bt by {
            vstd::arithmetic::div_mod::lemma_basic_div(j, bt);
            vstd::arithmetic::div_mod::lemma_basic_div(j, n);
        }
    }
}

/// The stored block size as `usize` (`eff_bs`), from the layout part and the row count.
fn eff_bs_exec(bt: u64, n: usize) -> (b: usize)
    requires bt >= 1,
    ensures b as int == eff_bs(n as int, bt as int),
{
    if bt <= n as u64 { bt as usize } else if n > 0 { n } else { 1 }
}

// ------------------------------------------------------------------------------------------------ openers

/// The shape of a table's frame parts: layout `[rows, block]` and uniform groups.
pub open spec fn frame_parts_ok(tp: Seq<PartView>, n: int) -> bool {
    &&& tp.len() >= 2
    &&& tp[0] is U64
    &&& cpi::common::colfmt::u64s(tp[0]).len() == 2
    &&& cpi::common::colfmt::groups_part_ok(tp[1], n, cpi::common::colfmt::u64s(tp[0])[1] as int)
}

proof fn lemma_frame_parts(tp: Seq<PartView>, n: int)
    requires frame_parts_ok(tp, n),
    ensures ({
        let bt = cpi::common::colfmt::u64s(tp[0])[1] as int;
        let ng = part_len(tp[1]) - 1;
        &&& 1 <= bt && n + bt <= u64::MAX && n >= 0
        &&& part_len(tp[1]) >= 1
        &&& ng == cpi::common::colfmt::nblocks_of(n, bt)
        &&& frame_ok(n, eff_bs(n, bt), ng)
        &&& forall|j: int| 0 <= j < n ==> #[trigger] (j / eff_bs(n, bt)) == j / bt
    }),
{
    let bt = cpi::common::colfmt::u64s(tp[0])[1] as int;
    cpi::common::colfmt::lemma_uniform_groups(tp[1], n, bt);
    lemma_eff_bs(n, bt, part_len(tp[1]) - 1);
}

/// A key index stays valid under the effective block size (every row keeps its group); custpart's key index.
proof fn lemma_keyidx_eff_cp(kc: Seq<u32>, kb: Seq<i64>, bt: int, b: int, kind: u64, n: int)
    requires
        cpi::common::keyidx::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bt, kind, n),
        b >= 1, kb.len() * b >= n,
        forall|j: int| 0 <= j < n ==> #[trigger] (j / b) == j / bt,
    ensures cpi::common::keyidx::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), b, kind, n),
{
    if kind >= 1 {
        assert forall|r: int| 0 <= r < n - 1 implies #[trigger] cpi::common::keyidx::sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), b, kind, r) by {
            assert(cpi::common::keyidx::sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bt, kind, r));
            assert(r / b == r / bt);
            assert((r + 1) / b == (r + 1) / bt);
        }
    }
    if kind == 2 {
        assert(cpi::common::keyidx::idx_map(Seq::<u32>::empty(), Seq::<u64>::empty(), b, n)
            =~= cpi::common::keyidx::idx_map(Seq::<u32>::empty(), Seq::<u64>::empty(), bt, n));
    }
}

/// A key index stays valid under the effective block size (every row keeps its group); suppliers' key index.
proof fn lemma_keyidx_eff_sp(kc: Seq<u32>, kb: Seq<i64>, bt: int, b: int, kind: u64, n: int)
    requires
        spi::common::keyidx::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bt, kind, n),
        b >= 1, kb.len() * b >= n,
        forall|j: int| 0 <= j < n ==> #[trigger] (j / b) == j / bt,
    ensures spi::common::keyidx::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), b, kind, n),
{
    if kind >= 1 {
        assert forall|r: int| 0 <= r < n - 1 implies #[trigger] spi::common::keyidx::sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), b, kind, r) by {
            assert(spi::common::keyidx::sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bt, kind, r));
            assert(r / b == r / bt);
            assert((r + 1) / b == (r + 1) / bt);
        }
    }
    if kind == 2 {
        assert(spi::common::keyidx::idx_map(Seq::<u32>::empty(), Seq::<u64>::empty(), b, n)
            =~= spi::common::keyidx::idx_map(Seq::<u32>::empty(), Seq::<u64>::empty(), bt, n));
    }
}

/// The text parts of `n` values in the interface's form give `txt_ok`.
proof fn lemma_txt_ok(o: Seq<u64>, y: Seq<u8>, n: int)
    requires cpi::common::colfmt::text_parts_wf(o, y, n),
    ensures txt_ok(o, y, n),
{
    assert forall|j: int| 0 <= j < n implies #[trigger] o[j] <= o[j + 1] && o[j + 1] <= y.len() by {
        assert(cpi::common::colfmt::text_range_ok(o, y, j));
    }
}

/// The text parts of `n` values in the interface's form give `txt_ok` (suppliers' format).
proof fn lemma_txt_ok_sp(o: Seq<u64>, y: Seq<u8>, n: int)
    requires spi::common::colfmt::text_parts_wf(o, y, n),
    ensures txt_ok(o, y, n),
{
    assert forall|j: int| 0 <= j < n implies #[trigger] o[j] <= o[j + 1] && o[j + 1] <= y.len() by {
        assert(spi::common::colfmt::text_range_ok(o, y, j));
    }
}

/// part: the decoded columns of every row.
proof fn lemma_part_rows(tp: Seq<PartView>, rel: Seq<Row>, c: PCols)
    requires
        tp.len() == cpi::PA_PARTS,
        frame_parts_ok(tp, rel.len() as int),
        cpi::common::colfmt::rows_width(rel, 9),
        tp[2] is U32, tp[10] is U8, tp[14] is U8, tp[18] is U8,
        cpi::common::colfmt::int_col_at(tp, 1, 2, 3, rel, 0),
        cpi::common::colfmt::dict_col_at(tp, 1, 10, 11, 12, 13, rel, 3),
        cpi::common::colfmt::dict_col_at(tp, 1, 14, 15, 16, 17, rel, 4),
        cpi::common::colfmt::int_col_at(tp, 1, 18, 19, rel, 5),
        rows_in_columns(rel, cpd::stored_columns_t1()),
        c.n == rel.len(),
        c.bs as int == eff_bs(rel.len() as int, cpi::common::colfmt::u64s(tp[0])[1] as int),
        c.key_c@ == cpi::common::colfmt::u32s(tp[2]), c.key_b@ == cpi::common::colfmt::i64s(tp[3]),
        c.brand_c@ == cpi::common::colfmt::u8s(tp[10]), c.brand_b@ == cpi::common::colfmt::u64s(tp[11]),
        c.brand_o@ == cpi::common::colfmt::u64s(tp[12]), c.brand_y@ == cpi::common::colfmt::u8s(tp[13]),
        c.type_c@ == cpi::common::colfmt::u8s(tp[14]), c.type_b@ == cpi::common::colfmt::u64s(tp[15]),
        c.type_o@ == cpi::common::colfmt::u64s(tp[16]), c.type_y@ == cpi::common::colfmt::u8s(tp[17]),
        c.size_c@ == cpi::common::colfmt::u8s(tp[18]), c.size_b@ == cpi::common::colfmt::i64s(tp[19]),
    ensures forall|i: int| 0 <= i < c.n ==> #[trigger] part_row_ok(c, rel[i], i),
{
    let n = rel.len() as int;
    let bt = cpi::common::colfmt::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    lemma_frame_parts(tp, n);
    assert forall|i: int| 0 <= i < n implies #[trigger] part_row_ok(c, rel[i], i) by {
        cpi::common::read::lemma_for_row(tp[1], n, bt, tp[3], tp[2], i);
        cpi::common::read::lemma_for_row(tp[1], n, bt, tp[11], tp[10], i);
        cpi::common::read::lemma_for_row(tp[1], n, bt, tp[15], tp[14], i);
        cpi::common::read::lemma_for_row(tp[1], n, bt, tp[19], tp[18], i);
        assert(i / b == i / bt);
        assert(rel[i].len() == cpd::stored_columns_t1().len());
        assert(value_in_column(rel[i][0], cpd::stored_columns_t1()[0]));
        assert(value_in_column(rel[i][5], cpd::stored_columns_t1()[5]));
    }
}

/// part: the rows of `rel` in terms of the handles `c` taken from the part parts `tp`.
proof fn lemma_part_cols(tp: Seq<PartView>, rel: Seq<Row>, c: PCols, e32: Seq<u32>, e64: Seq<u64>)
    requires
        cpi::part_ok(tp, rel),
        rows_in_columns(rel, cpd::stored_columns_t1()),
        e32 == Seq::<u32>::empty(), e64 == Seq::<u64>::empty(),
        c.n == rel.len(),
        c.ng == part_len(tp[1]) - 1,
        c.bs as int == eff_bs(rel.len() as int, cpi::common::colfmt::u64s(tp[0])[1] as int),
        c.key_c@ == cpi::common::colfmt::u32s(tp[2]), c.key_b@ == cpi::common::colfmt::i64s(tp[3]),
        c.brand_c@ == cpi::common::colfmt::u8s(tp[10]), c.brand_b@ == cpi::common::colfmt::u64s(tp[11]),
        c.brand_o@ == cpi::common::colfmt::u64s(tp[12]), c.brand_y@ == cpi::common::colfmt::u8s(tp[13]),
        c.type_c@ == cpi::common::colfmt::u8s(tp[14]), c.type_b@ == cpi::common::colfmt::u64s(tp[15]),
        c.type_o@ == cpi::common::colfmt::u64s(tp[16]), c.type_y@ == cpi::common::colfmt::u8s(tp[17]),
        c.size_c@ == cpi::common::colfmt::u8s(tp[18]), c.size_b@ == cpi::common::colfmt::i64s(tp[19]),
        c.kind == cpi::common::colfmt::u64s(tp[28])[0],
        c.brand_o@.len() <= usize::MAX, c.type_o@.len() <= usize::MAX,
    ensures pcols_ok(c, rel, e32, e64),
{
    let n = rel.len() as int;
    let bt = cpi::common::colfmt::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    assert(frame_parts_ok(tp, n));
    lemma_frame_parts(tp, n);
    lemma_part_rows(tp, rel, c);
    lemma_txt_ok(c.brand_o@, c.brand_y@, c.brand_o@.len() - 1);
    lemma_txt_ok(c.type_o@, c.type_y@, c.type_o@.len() - 1);
    lemma_keyidx_eff_cp(c.key_c@, c.key_b@, bt, b, c.kind, n);
}

/// The kinds and lengths of the part parts the opener reads.
proof fn lemma_part_shape(tp: Seq<PartView>, rel: Seq<Row>)
    requires cpi::part_ok(tp, rel),
    ensures
        frame_parts_ok(tp, rel.len() as int),
        tp[2] is U32 && part_len(tp[2]) == rel.len(),
        tp[3] is I64 && part_len(tp[3]) == part_len(tp[1]) - 1,
        tp[10] is U8 && part_len(tp[10]) == rel.len(),
        tp[11] is U64 && part_len(tp[11]) == part_len(tp[1]) - 1,
        tp[12] is U64,
        tp[13] is U8,
        tp[14] is U8 && part_len(tp[14]) == rel.len(),
        tp[15] is U64 && part_len(tp[15]) == part_len(tp[1]) - 1,
        tp[16] is U64,
        tp[17] is U8,
        tp[18] is U8 && part_len(tp[18]) == rel.len(),
        tp[19] is I64 && part_len(tp[19]) == part_len(tp[1]) - 1,
        tp[28] is U64 && part_len(tp[28]) == 1,
{
}

fn open_part(cp: &mut StoredParts, Ghost(rel): Ghost<Seq<Row>>, e32: &'static [u32], e64: &'static [u64]) -> (c: PCols)
    requires
        old(cp)@.len() == cpi::CUSTPART_PARTS,
        cpi::part_ok(old(cp)@.subrange(cpi::PART_FIRST as int, (cpi::PART_FIRST + cpi::PA_PARTS) as int), rel),
        rows_in_columns(rel, cpd::stored_columns_t1()),
        e32@ == Seq::<u32>::empty(),
        e64@ == Seq::<u64>::empty(),
    ensures
        final(cp)@ == old(cp)@,
        pcols_ok(c, rel, e32@, e64@),
{
    hide(cpi::part_ok);
    let ghost tp = cp@.subrange(cpi::PART_FIRST as int, (cpi::PART_FIRST + cpi::PA_PARTS) as int);
    proof {
        lemma_part_shape(tp, rel);
        lemma_frame_parts(tp, rel.len() as int);
    }
    let f = cpi::PART_FIRST;
    let n = cp.part_len(f + 2);
    let lay = cp.extent_u64(f, 0, 2);
    let bs = eff_bs_exec(lay[1], n);
    let ng = cp.part_len(f + 1) - 1;
    let key_c = cp.extent_u32(f + 2, 0, n);
    let key_b = cp.extent_i64(f + 3, 0, ng);
    let brand_c = cp.extent_u8(f + 10, 0, n);
    let brand_b = cp.extent_u64(f + 11, 0, ng);
    let l = cp.part_len(f + 12);
    let brand_o = cp.extent_u64(f + 12, 0, l);
    let l = cp.part_len(f + 13);
    let brand_y = cp.extent_u8(f + 13, 0, l);
    let type_c = cp.extent_u8(f + 14, 0, n);
    let type_b = cp.extent_u64(f + 15, 0, ng);
    let l = cp.part_len(f + 16);
    let type_o = cp.extent_u64(f + 16, 0, l);
    let l = cp.part_len(f + 17);
    let type_y = cp.extent_u8(f + 17, 0, l);
    let size_c = cp.extent_u8(f + 18, 0, n);
    let size_b = cp.extent_i64(f + 19, 0, ng);
    let kk = cp.extent_u64(f + 28, 0, 1);
    let kind = kk[0];
    let c = PCols { n, bs, ng, kind, key_c, key_b, brand_c, brand_b, brand_o, brand_y, type_c, type_b, type_o, type_y,
        size_c, size_b };
    proof {
        assert(lay@ =~= cpi::common::colfmt::u64s(tp[0]));
        assert(key_c@ =~= cpi::common::colfmt::u32s(tp[2]));
        assert(key_b@ =~= cpi::common::colfmt::i64s(tp[3]));
        assert(brand_c@ =~= cpi::common::colfmt::u8s(tp[10]));
        assert(brand_b@ =~= cpi::common::colfmt::u64s(tp[11]));
        assert(brand_o@ =~= cpi::common::colfmt::u64s(tp[12]));
        assert(brand_y@ =~= cpi::common::colfmt::u8s(tp[13]));
        assert(type_c@ =~= cpi::common::colfmt::u8s(tp[14]));
        assert(type_b@ =~= cpi::common::colfmt::u64s(tp[15]));
        assert(type_o@ =~= cpi::common::colfmt::u64s(tp[16]));
        assert(type_y@ =~= cpi::common::colfmt::u8s(tp[17]));
        assert(size_c@ =~= cpi::common::colfmt::u8s(tp[18]));
        assert(size_b@ =~= cpi::common::colfmt::i64s(tp[19]));
        assert(kk@ =~= cpi::common::colfmt::u64s(tp[28]));
        lemma_part_cols(tp, rel, c, e32@, e64@);
    }
    c
}

/// partsupp: the rows of `rel` in terms of the handles `c` taken from the partsupp parts `tp`.
proof fn lemma_partsupp_cols(tp: Seq<PartView>, rel: Seq<Row>, c: PSCols, e32: Seq<u32>, e64: Seq<u64>)
    requires
        spi::partsupp_ok(tp, rel),
        rows_in_columns(rel, spd::stored_columns_t0()),
        e32 == Seq::<u32>::empty(), e64 == Seq::<u64>::empty(),
        c.n == rel.len(),
        c.ng == part_len(tp[1]) - 1,
        c.bs as int == eff_bs(rel.len() as int, spi::common::colfmt::u64s(tp[0])[1] as int),
        c.key_c@ == spi::common::colfmt::u32s(tp[2]), c.key_b@ == spi::common::colfmt::i64s(tp[3]),
        c.supp_c@ == spi::common::colfmt::u32s(tp[4]), c.supp_b@ == spi::common::colfmt::i64s(tp[5]),
        c.kind == spi::common::colfmt::u64s(tp[12])[0],
    ensures pscols_ok(c, rel, e32, e64),
{
    let n = rel.len() as int;
    let bt = spi::common::colfmt::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    assert(frame_parts_ok(tp, n));
    lemma_frame_parts(tp, n);
    assert forall|k: int| 0 <= k < n implies #[trigger] ps_row_ok(c, rel[k], k) by {
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[3], tp[2], k);
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[5], tp[4], k);
        assert(k / b == k / bt);
        assert(rel[k].len() == spd::stored_columns_t0().len());
        assert(value_in_column(rel[k][0], spd::stored_columns_t0()[0]));
        assert(value_in_column(rel[k][1], spd::stored_columns_t0()[1]));
    }
    lemma_keyidx_eff_sp(c.key_c@, c.key_b@, bt, b, c.kind, n);
}

/// The kinds and lengths of the partsupp parts the opener reads.
proof fn lemma_partsupp_shape(tp: Seq<PartView>, rel: Seq<Row>)
    requires spi::partsupp_ok(tp, rel),
    ensures
        frame_parts_ok(tp, rel.len() as int),
        tp[2] is U32 && part_len(tp[2]) == rel.len(),
        tp[3] is I64 && part_len(tp[3]) == part_len(tp[1]) - 1,
        tp[4] is U32 && part_len(tp[4]) == rel.len(),
        tp[5] is I64 && part_len(tp[5]) == part_len(tp[1]) - 1,
        tp[12] is U64 && part_len(tp[12]) == 1,
{
}

fn open_partsupp(sp: &mut StoredParts, rs: &mut StoredParts, Ghost(rel): Ghost<Seq<Row>>, e32: &'static [u32], e64: &'static [u64]) -> (c: PSCols)
    requires
        old(sp)@.len() == spi::SUPPLIERS_PARTS,
        old(rs)@.len() == pri::PSRUN_PARTS,
        spi::partsupp_ok(old(sp)@.subrange(spi::PARTSUPP_FIRST as int, (spi::PARTSUPP_FIRST + spi::PS_PARTS) as int), rel),
        pri::runs_ok(old(rs)@[pri::RUNS as int], rel),
        rows_in_columns(rel, spd::stored_columns_t0()),
        e32@ == Seq::<u32>::empty(),
        e64@ == Seq::<u64>::empty(),
    ensures
        final(sp)@ == old(sp)@,
        final(rs)@ == old(rs)@,
        pscols_ok(c, rel, e32@, e64@),
        runs_hold(c),
{
    hide(spi::partsupp_ok);
    let ghost tp = sp@.subrange(spi::PARTSUPP_FIRST as int, (spi::PARTSUPP_FIRST + spi::PS_PARTS) as int);
    proof {
        lemma_partsupp_shape(tp, rel);
        lemma_frame_parts(tp, rel.len() as int);
    }
    let f = spi::PARTSUPP_FIRST;
    let n = sp.part_len(f + 2);
    let lay = sp.extent_u64(f, 0, 2);
    let bs = eff_bs_exec(lay[1], n);
    let ng = sp.part_len(f + 1) - 1;
    let key_c = sp.extent_u32(f + 2, 0, n);
    let key_b = sp.extent_i64(f + 3, 0, ng);
    let supp_c = sp.extent_u32(f + 4, 0, n);
    let supp_b = sp.extent_i64(f + 5, 0, ng);
    let kk = sp.extent_u64(f + 12, 0, 1);
    let kind = kk[0];
    let ghost rp = rs@[pri::RUNS as int];
    proof {
        assert(rp is I64);
    }
    let runs = rs.extent_i64(pri::RUNS, 0, rs.part_len(pri::RUNS));
    let c = PSCols { n, bs, ng, kind, key_c, key_b, supp_c, supp_b, runs };
    proof {
        assert(lay@ =~= spi::common::colfmt::u64s(tp[0]));
        assert(key_c@ =~= spi::common::colfmt::u32s(tp[2]));
        assert(key_b@ =~= spi::common::colfmt::i64s(tp[3]));
        assert(supp_c@ =~= spi::common::colfmt::u32s(tp[4]));
        assert(supp_b@ =~= spi::common::colfmt::i64s(tp[5]));
        assert(kk@ =~= spi::common::colfmt::u64s(tp[12]));
        lemma_partsupp_cols(tp, rel, c, e32@, e64@);
        assert(runs@ =~= spi::common::colfmt::i64s(rp));
        assert forall|b: int| 0 <= b < pri::run_blocks(c.n as int) && #[trigger] c.runs@[b + 1] != pri::NO_RUN implies
            forall|i: int| b * pri::RUN_ROWS <= i < c.n && i < b * pri::RUN_ROWS + pri::RUN_ROWS ==>
                #[trigger] fv32(c.key_c@, c.key_b@, c.bs as int, i) == c.runs@[b + 1] + (i - b * pri::RUN_ROWS) / (c.runs@[0] as int) by {
            assert(pri::block_run(rel, b, c.runs@[b + 1] as int, c.runs@[0] as int));
            assert forall|i: int| b * pri::RUN_ROWS <= i < c.n && i < b * pri::RUN_ROWS + pri::RUN_ROWS implies
                #[trigger] fv32(c.key_c@, c.key_b@, c.bs as int, i) == c.runs@[b + 1] + (i - b * pri::RUN_ROWS) / (c.runs@[0] as int) by {
                assert(ps_row_ok(c, rel[i], i));
            }
        }
    }
    c
}

/// supplier: the rows of `rel` in terms of the handles `c` taken from the supplier parts `tp`.
proof fn lemma_supplier_cols(tp: Seq<PartView>, rel: Seq<Row>, c: SCols, e32: Seq<u32>, e64: Seq<u64>)
    requires
        spi::supplier_ok(tp, rel),
        rows_in_columns(rel, spd::stored_columns_t1()),
        e32 == Seq::<u32>::empty(), e64 == Seq::<u64>::empty(),
        c.n == rel.len(),
        c.ng == part_len(tp[1]) - 1,
        c.bs as int == eff_bs(rel.len() as int, spi::common::colfmt::u64s(tp[0])[1] as int),
        c.key_c@ == spi::common::colfmt::u32s(tp[2]), c.key_b@ == spi::common::colfmt::i64s(tp[3]),
        c.comm_o@ == spi::common::colfmt::u64s(tp[14]), c.comm_y@ == spi::common::colfmt::u8s(tp[15]),
        c.comm_len == c.comm_y@.len(),
        c.kind == spi::common::colfmt::u64s(tp[16])[0],
    ensures scols_ok(c, rel, e32, e64),
{
    let n = rel.len() as int;
    let bt = spi::common::colfmt::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    assert(frame_parts_ok(tp, n));
    lemma_frame_parts(tp, n);
    assert forall|j: int| 0 <= j < n implies #[trigger] supp_row_ok(c, rel[j], j) by {
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[3], tp[2], j);
        assert(j / b == j / bt);
        assert(rel[j].len() == spd::stored_columns_t1().len());
        assert(value_in_column(rel[j][0], spd::stored_columns_t1()[0]));
    }
    lemma_txt_ok_sp(c.comm_o@, c.comm_y@, n);
    lemma_keyidx_eff_sp(c.key_c@, c.key_b@, bt, b, c.kind, n);
}

/// The kinds and lengths of the supplier parts the opener reads.
proof fn lemma_supplier_shape(tp: Seq<PartView>, rel: Seq<Row>)
    requires spi::supplier_ok(tp, rel),
    ensures
        frame_parts_ok(tp, rel.len() as int),
        tp[2] is U32 && part_len(tp[2]) == rel.len(),
        tp[3] is I64 && part_len(tp[3]) == part_len(tp[1]) - 1,
        tp[14] is U64 && part_len(tp[14]) == rel.len() + 1,
        tp[15] is U8,
        tp[16] is U64 && part_len(tp[16]) == 1,
{
}

fn open_supplier(sp: &mut StoredParts, Ghost(rel): Ghost<Seq<Row>>, e32: &'static [u32], e64: &'static [u64]) -> (c: SCols)
    requires
        old(sp)@.len() == spi::SUPPLIERS_PARTS,
        spi::supplier_ok(old(sp)@.subrange(spi::SUPPLIER_FIRST as int, (spi::SUPPLIER_FIRST + spi::SU_PARTS) as int), rel),
        rows_in_columns(rel, spd::stored_columns_t1()),
        e32@ == Seq::<u32>::empty(),
        e64@ == Seq::<u64>::empty(),
    ensures
        final(sp)@ == old(sp)@,
        scols_ok(c, rel, e32@, e64@),
{
    hide(spi::supplier_ok);
    let ghost tp = sp@.subrange(spi::SUPPLIER_FIRST as int, (spi::SUPPLIER_FIRST + spi::SU_PARTS) as int);
    proof {
        lemma_supplier_shape(tp, rel);
        lemma_frame_parts(tp, rel.len() as int);
    }
    let f = spi::SUPPLIER_FIRST;
    let n = sp.part_len(f + 2);
    let lay = sp.extent_u64(f, 0, 2);
    let bs = eff_bs_exec(lay[1], n);
    let ng = sp.part_len(f + 1) - 1;
    let key_c = sp.extent_u32(f + 2, 0, n);
    let key_b = sp.extent_i64(f + 3, 0, ng);
    let l = sp.part_len(f + 14);
    let comm_o = sp.extent_u64(f + 14, 0, l);
    let l = sp.part_len(f + 15);
    let comm_y = sp.extent_u8(f + 15, 0, l);
    let kk = sp.extent_u64(f + 16, 0, 1);
    let kind = kk[0];
    let c = SCols { n, bs, ng, kind, key_c, key_b, comm_o, comm_y, comm_len: l };
    proof {
        assert(lay@ =~= spi::common::colfmt::u64s(tp[0]));
        assert(key_c@ =~= spi::common::colfmt::u32s(tp[2]));
        assert(key_b@ =~= spi::common::colfmt::i64s(tp[3]));
        assert(comm_o@ =~= spi::common::colfmt::u64s(tp[14]));
        assert(comm_y@ =~= spi::common::colfmt::u8s(tp[15]));
        assert(kk@ =~= spi::common::colfmt::u64s(tp[16]));
        lemma_supplier_cols(tp, rel, c, e32@, e64@);
    }
    c
}

/// Opens every column handle (one extent per part, on the calling thread) over the stored relations `cr`
/// (custpart) and `sr` (suppliers).
pub fn open_cols(stores: &mut Stores, Ghost(cr): Ghost<Seq<Seq<Row>>>, Ghost(sr): Ghost<Seq<Seq<Row>>>) -> (c: Cols)
    requires
        cpi::represents(old(stores).custpart@, cr),
        spi::represents(old(stores).suppliers@, sr),
        pri::represents(old(stores).psrun@, sr),
        rows_in_columns(cr[1], cpd::stored_columns_t1()),
        rows_in_columns(sr[0], spd::stored_columns_t0()),
        rows_in_columns(sr[1], spd::stored_columns_t1()),
    ensures
        final(stores)@ == old(stores)@,
        cols_ok(c, Tabs { p: cr[1], ps: sr[0], s: sr[1] }),
{
    proof {
        let tp = stores.suppliers@.subrange(spi::PARTSUPP_FIRST as int, (spi::PARTSUPP_FIRST + spi::PS_PARTS) as int);
        assert(stores.suppliers@[(spi::PARTSUPP_FIRST + spi::PS_PARTKEY_CODES) as int] == tp[spi::PS_PARTKEY_CODES as int]);
        assert(stores.suppliers@[(spi::PARTSUPP_FIRST + spi::PS_LAYOUT) as int] == tp[spi::PS_LAYOUT as int]);
    }
    let e32 = stores.suppliers.extent_u32(spi::PARTSUPP_FIRST + spi::PS_PARTKEY_CODES, 0, 0);
    let e64 = stores.suppliers.extent_u64(spi::PARTSUPP_FIRST + spi::PS_LAYOUT, 0, 0);
    proof {
        assert(e32@ =~= Seq::<u32>::empty());
        assert(e64@ =~= Seq::<u64>::empty());
    }
    let p = open_part(&mut stores.custpart, Ghost(cr[1]), e32, e64);
    let ps = open_partsupp(&mut stores.suppliers, &mut stores.psrun, Ghost(sr[0]), e32, e64);
    let s = open_supplier(&mut stores.suppliers, Ghost(sr[1]), e32, e64);
    Cols { p, ps, s, e32, e64 }
}

} // verus!
