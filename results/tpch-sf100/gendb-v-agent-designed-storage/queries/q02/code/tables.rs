//! Column handles of the five Q2 tables, read from the admitted storages `custpart` (part) and `suppliers`
//! (partsupp, supplier, nation, region) as zero-copy extents, and the values they decode to.
//!
//! Every stored table is in canonical row order with uniform groups of `bs` rows (`ng` groups); a frame-of-reference
//! (FOR) column stores row `j` as `base[j / bs] + code[j]` (`fv32`, `fv8`, `fu8`); a dictionary column stores the
//! FOR-coded index of an entry of offsets + bytes; plain text is offsets + bytes (`txt`). `*_row_ok(c, r, j)` states
//! what row `j` of a table is in terms of its handles `c`; `*cols_ok(c, rel)` states it for every row, plus the shape
//! facts (lengths, frame) the readers need.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::{Column, SqlType};
use crate::spec::typing::value_in_column;
use crate::spec::numeric::{abs, pow10};
use crate::spec::int::int_in_range;
use crate::link::source::rows_in_columns;
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::stored::{StoredParts, part_len};
use crate::gendb_entry::layout::PartView;
use crate::stores::custpart::interface as cpi;
use crate::stores::suppliers::interface as spi;
use crate::stores::custpart::declaration as cpd;
use crate::stores::suppliers::declaration as spd;
use crate::stores::suppliers::interface::common::colfmt::rows_width;

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

/// part: p_partkey (FOR u32), p_mfgr and p_type (dictionaries), p_size (FOR u8).
#[derive(Clone, Copy)]
pub struct PCols {
    pub n: usize,
    pub bs: usize,
    pub ng: usize,
    pub kind: u64,
    pub key_c: &'static [u32],
    pub key_b: &'static [i64],
    pub mfgr_c: &'static [u8],
    pub mfgr_b: &'static [u64],
    pub mfgr_o: &'static [u64],
    pub mfgr_y: &'static [u8],
    pub type_c: &'static [u8],
    pub type_b: &'static [u64],
    pub type_o: &'static [u64],
    pub type_y: &'static [u8],
    pub size_c: &'static [u8],
    pub size_b: &'static [i64],
}

/// partsupp: ps_partkey, ps_suppkey, ps_supplycost (FOR u32), the key index kind of ps_partkey.
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
    pub cost_c: &'static [u32],
    pub cost_b: &'static [i64],
}

/// supplier: s_suppkey (FOR u32), s_nationkey (FOR u8), s_acctbal (FOR u32), text columns, key index kind.
#[derive(Clone, Copy)]
pub struct SCols {
    pub n: usize,
    pub bs: usize,
    pub ng: usize,
    pub kind: u64,
    pub key_c: &'static [u32],
    pub key_b: &'static [i64],
    pub nat_c: &'static [u8],
    pub nat_b: &'static [i64],
    pub acct_c: &'static [u32],
    pub acct_b: &'static [i64],
    pub name_o: &'static [u64],
    pub name_y: &'static [u8],
    pub addr_o: &'static [u64],
    pub addr_y: &'static [u8],
    pub phone_o: &'static [u64],
    pub phone_y: &'static [u8],
    pub comm_o: &'static [u64],
    pub comm_y: &'static [u8],
}

/// nation: n_nationkey, n_regionkey (FOR u8), n_name.
#[derive(Clone, Copy)]
pub struct NCols {
    pub n: usize,
    pub bs: usize,
    pub ng: usize,
    pub key_c: &'static [u8],
    pub key_b: &'static [i64],
    pub reg_c: &'static [u8],
    pub reg_b: &'static [i64],
    pub name_o: &'static [u64],
    pub name_y: &'static [u8],
}

/// region: r_regionkey (FOR u8), r_name.
#[derive(Clone, Copy)]
pub struct RCols {
    pub n: usize,
    pub bs: usize,
    pub ng: usize,
    pub key_c: &'static [u8],
    pub key_b: &'static [i64],
    pub name_o: &'static [u64],
    pub name_y: &'static [u8],
}

/// Every handle the statement reads, and two empty key-index parts (these tables' key indexes have none).
#[derive(Clone, Copy)]
pub struct Cols {
    pub p: PCols,
    pub ps: PSCols,
    pub s: SCols,
    pub n: NCols,
    pub r: RCols,
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
    &&& 0 <= fu8(c.mfgr_c@, c.mfgr_b@, bs, i) < c.mfgr_o@.len() - 1
    &&& r[2] == Val::Text(txt(c.mfgr_o@, c.mfgr_y@, fu8(c.mfgr_c@, c.mfgr_b@, bs, i)))
    &&& 0 <= fu8(c.type_c@, c.type_b@, bs, i) < c.type_o@.len() - 1
    &&& r[4] == Val::Text(txt(c.type_o@, c.type_y@, fu8(c.type_c@, c.type_b@, bs, i)))
    &&& r[5] == Val::Int(fv8(c.size_c@, c.size_b@, bs, i)) && i64r(fv8(c.size_c@, c.size_b@, bs, i))
}

pub open spec fn pcols_ok(c: PCols, p: Seq<Row>) -> bool {
    &&& frame_ok(c.n as int, c.bs as int, c.ng as int)
    &&& p.len() == c.n
    &&& c.key_c@.len() == c.n && c.key_b@.len() == c.ng
    &&& c.mfgr_c@.len() == c.n && c.mfgr_b@.len() == c.ng && dict_ok(c.mfgr_o@, c.mfgr_y@)
    &&& c.type_c@.len() == c.n && c.type_b@.len() == c.ng && dict_ok(c.type_o@, c.type_y@)
    &&& c.size_c@.len() == c.n && c.size_b@.len() == c.ng
    &&& forall|i: int| 0 <= i < c.n ==> #[trigger] part_row_ok(c, p[i], i)
    &&& c.kind == 1 ==> forall|i: int| 0 <= i < c.n - 1
        ==> #[trigger] fv32(c.key_c@, c.key_b@, c.bs as int, i) <= fv32(c.key_c@, c.key_b@, c.bs as int, i + 1)
}

pub open spec fn ps_row_ok(c: PSCols, r: Row, k: int) -> bool {
    let bs = c.bs as int;
    &&& r.len() == 5
    &&& r[0] == Val::Int(fv32(c.key_c@, c.key_b@, bs, k)) && i64r(fv32(c.key_c@, c.key_b@, bs, k))
    &&& r[1] == Val::Int(fv32(c.supp_c@, c.supp_b@, bs, k)) && i64r(fv32(c.supp_c@, c.supp_b@, bs, k))
    &&& r[3] == (Val::Num { coeff: fv32(c.cost_c@, c.cost_b@, bs, k), scale: 2 }) && i64r(fv32(c.cost_c@, c.cost_b@, bs, k))
}

pub open spec fn pscols_ok(c: PSCols, ps: Seq<Row>, e32: Seq<u32>, e64: Seq<u64>) -> bool {
    &&& frame_ok(c.n as int, c.bs as int, c.ng as int)
    &&& ps.len() == c.n
    &&& c.key_c@.len() == c.n && c.key_b@.len() == c.ng
    &&& c.supp_c@.len() == c.n && c.supp_b@.len() == c.ng
    &&& c.cost_c@.len() == c.n && c.cost_b@.len() == c.ng
    &&& forall|k: int| 0 <= k < c.n ==> #[trigger] ps_row_ok(c, ps[k], k)
    &&& spi::common::keyidx::keyidx_ok(c.key_c@, c.key_b@, e32, e64, c.bs as int, c.kind, c.n as int)
}

pub open spec fn supp_row_ok(c: SCols, r: Row, j: int) -> bool {
    let bs = c.bs as int;
    &&& r.len() == 7
    &&& r[0] == Val::Int(fv32(c.key_c@, c.key_b@, bs, j)) && i64r(fv32(c.key_c@, c.key_b@, bs, j))
    &&& r[1] == Val::Text(txt(c.name_o@, c.name_y@, j))
    &&& r[2] == Val::Text(txt(c.addr_o@, c.addr_y@, j))
    &&& r[3] == Val::Int(fv8(c.nat_c@, c.nat_b@, bs, j)) && i64r(fv8(c.nat_c@, c.nat_b@, bs, j))
    &&& r[4] == Val::Text(txt(c.phone_o@, c.phone_y@, j))
    &&& r[5] == (Val::Num { coeff: fv32(c.acct_c@, c.acct_b@, bs, j), scale: 2 }) && i64r(fv32(c.acct_c@, c.acct_b@, bs, j))
    &&& r[6] == Val::Text(txt(c.comm_o@, c.comm_y@, j))
}

pub open spec fn scols_ok(c: SCols, s: Seq<Row>, e32: Seq<u32>, e64: Seq<u64>) -> bool {
    &&& frame_ok(c.n as int, c.bs as int, c.ng as int)
    &&& s.len() == c.n
    &&& c.key_c@.len() == c.n && c.key_b@.len() == c.ng
    &&& c.nat_c@.len() == c.n && c.nat_b@.len() == c.ng
    &&& c.acct_c@.len() == c.n && c.acct_b@.len() == c.ng
    &&& txt_ok(c.name_o@, c.name_y@, c.n as int) && txt_ok(c.addr_o@, c.addr_y@, c.n as int)
    &&& txt_ok(c.phone_o@, c.phone_y@, c.n as int) && txt_ok(c.comm_o@, c.comm_y@, c.n as int)
    &&& forall|j: int| 0 <= j < c.n ==> #[trigger] supp_row_ok(c, s[j], j)
    &&& spi::common::keyidx::keyidx_ok(c.key_c@, c.key_b@, e32, e64, c.bs as int, c.kind, c.n as int)
}

pub open spec fn nat_row_ok(c: NCols, r: Row, q: int) -> bool {
    let bs = c.bs as int;
    &&& r.len() == 4
    &&& r[0] == Val::Int(fv8(c.key_c@, c.key_b@, bs, q)) && i64r(fv8(c.key_c@, c.key_b@, bs, q))
    &&& r[1] == Val::Text(txt(c.name_o@, c.name_y@, q))
    &&& r[2] == Val::Int(fv8(c.reg_c@, c.reg_b@, bs, q)) && i64r(fv8(c.reg_c@, c.reg_b@, bs, q))
}

pub open spec fn ncols_ok(c: NCols, n: Seq<Row>) -> bool {
    &&& frame_ok(c.n as int, c.bs as int, c.ng as int)
    &&& n.len() == c.n
    &&& c.key_c@.len() == c.n && c.key_b@.len() == c.ng
    &&& c.reg_c@.len() == c.n && c.reg_b@.len() == c.ng
    &&& txt_ok(c.name_o@, c.name_y@, c.n as int)
    &&& forall|q: int| 0 <= q < c.n ==> #[trigger] nat_row_ok(c, n[q], q)
}

pub open spec fn reg_row_ok(c: RCols, r: Row, q: int) -> bool {
    let bs = c.bs as int;
    &&& r.len() == 3
    &&& r[0] == Val::Int(fv8(c.key_c@, c.key_b@, bs, q)) && i64r(fv8(c.key_c@, c.key_b@, bs, q))
    &&& r[1] == Val::Text(txt(c.name_o@, c.name_y@, q))
}

pub open spec fn rcols_ok(c: RCols, r: Seq<Row>) -> bool {
    &&& frame_ok(c.n as int, c.bs as int, c.ng as int)
    &&& r.len() == c.n
    &&& c.key_c@.len() == c.n && c.key_b@.len() == c.ng
    &&& txt_ok(c.name_o@, c.name_y@, c.n as int)
    &&& forall|q: int| 0 <= q < c.n ==> #[trigger] reg_row_ok(c, r[q], q)
}

/// The five tables of the statement (full rows, canonical order): part, supplier, partsupp, nation, region.
pub struct Tabs {
    pub p: Seq<Row>,
    pub s: Seq<Row>,
    pub ps: Seq<Row>,
    pub n: Seq<Row>,
    pub r: Seq<Row>,
}

pub open spec fn cols_ok(c: Cols, t: Tabs) -> bool {
    &&& c.e32@ == Seq::<u32>::empty()
    &&& c.e64@ == Seq::<u64>::empty()
    &&& pcols_ok(c.p, t.p)
    &&& pscols_ok(c.ps, t.ps, c.e32@, c.e64@)
    &&& scols_ok(c.s, t.s, c.e32@, c.e64@)
    &&& ncols_ok(c.n, t.n)
    &&& rcols_ok(c.r, t.r)
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

/// A numeric(15,2) value's coefficient fits `i64`.
proof fn lemma_num15(v: Val, coeff: int)
    requires value_in_column(v, Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        v == (Val::Num { coeff, scale: 2 }),
    ensures i64r(coeff),
{
    assert(pow10(15) == 1000000000000000) by (compute);
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

/// part: the rows of `rel` in terms of the handles `c` taken from the part parts `tp`.
proof fn lemma_part_cols(tp: Seq<PartView>, rel: Seq<Row>, c: PCols)
    requires
        cpi::part_ok(tp, rel),
        rows_in_columns(rel, cpd::stored_columns_t1()),
        c.n == rel.len(),
        c.ng == part_len(tp[1]) - 1,
        c.bs as int == eff_bs(rel.len() as int, cpi::common::colfmt::u64s(tp[0])[1] as int),
        c.key_c@ == cpi::common::colfmt::u32s(tp[2]), c.key_b@ == cpi::common::colfmt::i64s(tp[3]),
        c.mfgr_c@ == cpi::common::colfmt::u8s(tp[6]), c.mfgr_b@ == cpi::common::colfmt::u64s(tp[7]),
        c.mfgr_o@ == cpi::common::colfmt::u64s(tp[8]), c.mfgr_y@ == cpi::common::colfmt::u8s(tp[9]),
        c.type_c@ == cpi::common::colfmt::u8s(tp[14]), c.type_b@ == cpi::common::colfmt::u64s(tp[15]),
        c.type_o@ == cpi::common::colfmt::u64s(tp[16]), c.type_y@ == cpi::common::colfmt::u8s(tp[17]),
        c.size_c@ == cpi::common::colfmt::u8s(tp[18]), c.size_b@ == cpi::common::colfmt::i64s(tp[19]),
        c.kind == cpi::common::colfmt::u64s(tp[28])[0],
        c.mfgr_o@.len() <= usize::MAX, c.type_o@.len() <= usize::MAX,
    ensures pcols_ok(c, rel),
{
    let n = rel.len() as int;
    let bt = cpi::common::colfmt::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    let gs = cpi::common::colfmt::u64s(tp[1]);
    lemma_frame_parts(tp, n);
    assert forall|i: int| 0 <= i < n implies #[trigger] part_row_ok(c, rel[i], i) by {
        cpi::common::read::lemma_for_row(tp[1], n, bt, tp[3], tp[2], i);
        cpi::common::read::lemma_for_row(tp[1], n, bt, tp[7], tp[6], i);
        cpi::common::read::lemma_for_row(tp[1], n, bt, tp[15], tp[14], i);
        cpi::common::read::lemma_for_row(tp[1], n, bt, tp[19], tp[18], i);
        assert(i / b == i / bt);
        assert(rel[i].len() == cpd::stored_columns_t1().len());
        assert(value_in_column(rel[i][0], cpd::stored_columns_t1()[0]));
        assert(rel[i].len() == cpd::stored_columns_t1().len());
        assert(value_in_column(rel[i][5], cpd::stored_columns_t1()[5]));
    }
    assert forall|j: int| 0 <= j < c.mfgr_o@.len() - 1 implies #[trigger] c.mfgr_o@[j] <= c.mfgr_o@[j + 1] && c.mfgr_o@[j + 1] <= c.mfgr_y@.len() by {
        assert(cpi::common::colfmt::text_range_ok(c.mfgr_o@, c.mfgr_y@, j));
    }
    assert forall|j: int| 0 <= j < c.type_o@.len() - 1 implies #[trigger] c.type_o@[j] <= c.type_o@[j + 1] && c.type_o@[j + 1] <= c.type_y@.len() by {
        assert(cpi::common::colfmt::text_range_ok(c.type_o@, c.type_y@, j));
    }
    if c.kind == 1 {
        assert forall|i: int| 0 <= i < n - 1 implies #[trigger] fv32(c.key_c@, c.key_b@, b, i) <= fv32(c.key_c@, c.key_b@, b, i + 1) by {
            assert(cpi::common::keyidx::sorted_at(c.key_c@, c.key_b@, Seq::<u32>::empty(), Seq::<u64>::empty(), bt, c.kind, i));
            assert(i / b == i / bt);
            assert((i + 1) / b == (i + 1) / bt);
        }
    }
}

/// The kinds and lengths of the part parts the opener reads.
proof fn lemma_part_shape(tp: Seq<PartView>, rel: Seq<Row>)
    requires cpi::part_ok(tp, rel),
    ensures
        frame_parts_ok(tp, rel.len() as int),
        tp[2] is U32 && part_len(tp[2]) == rel.len(),
        tp[3] is I64 && part_len(tp[3]) == part_len(tp[1]) - 1,
        tp[6] is U8 && part_len(tp[6]) == rel.len(),
        tp[7] is U64 && part_len(tp[7]) == part_len(tp[1]) - 1,
        tp[8] is U64,
        tp[9] is U8,
        tp[14] is U8 && part_len(tp[14]) == rel.len(),
        tp[15] is U64 && part_len(tp[15]) == part_len(tp[1]) - 1,
        tp[16] is U64,
        tp[17] is U8,
        tp[18] is U8 && part_len(tp[18]) == rel.len(),
        tp[19] is I64 && part_len(tp[19]) == part_len(tp[1]) - 1,
        tp[28] is U64 && part_len(tp[28]) == 1,
{
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
        tp[8] is U32 && part_len(tp[8]) == rel.len(),
        tp[9] is I64 && part_len(tp[9]) == part_len(tp[1]) - 1,
        tp[12] is U64 && part_len(tp[12]) == 1,
{
}

/// The kinds and lengths of the supplier parts the opener reads.
proof fn lemma_supplier_shape(tp: Seq<PartView>, rel: Seq<Row>)
    requires spi::supplier_ok(tp, rel),
    ensures
        frame_parts_ok(tp, rel.len() as int),
        tp[2] is U32 && part_len(tp[2]) == rel.len(),
        tp[3] is I64 && part_len(tp[3]) == part_len(tp[1]) - 1,
        tp[4] is U64 && part_len(tp[4]) == rel.len() + 1,
        tp[5] is U8,
        tp[6] is U64 && part_len(tp[6]) == rel.len() + 1,
        tp[7] is U8,
        tp[8] is U8 && part_len(tp[8]) == rel.len(),
        tp[9] is I64 && part_len(tp[9]) == part_len(tp[1]) - 1,
        tp[10] is U64 && part_len(tp[10]) == rel.len() + 1,
        tp[11] is U8,
        tp[12] is U32 && part_len(tp[12]) == rel.len(),
        tp[13] is I64 && part_len(tp[13]) == part_len(tp[1]) - 1,
        tp[14] is U64 && part_len(tp[14]) == rel.len() + 1,
        tp[15] is U8,
        tp[16] is U64 && part_len(tp[16]) == 1,
{
}

/// The kinds and lengths of the nation parts the opener reads.
proof fn lemma_nation_shape(tp: Seq<PartView>, rel: Seq<Row>)
    requires spi::nation_ok(tp, rel),
    ensures
        frame_parts_ok(tp, rel.len() as int),
        tp[2] is U8 && part_len(tp[2]) == rel.len(),
        tp[3] is I64 && part_len(tp[3]) == part_len(tp[1]) - 1,
        tp[4] is U64 && part_len(tp[4]) == rel.len() + 1,
        tp[5] is U8,
        tp[6] is U8 && part_len(tp[6]) == rel.len(),
        tp[7] is I64 && part_len(tp[7]) == part_len(tp[1]) - 1,
{
}

/// The kinds and lengths of the region parts the opener reads.
proof fn lemma_region_shape(tp: Seq<PartView>, rel: Seq<Row>)
    requires spi::region_ok(tp, rel),
    ensures
        frame_parts_ok(tp, rel.len() as int),
        tp[2] is U8 && part_len(tp[2]) == rel.len(),
        tp[3] is I64 && part_len(tp[3]) == part_len(tp[1]) - 1,
        tp[4] is U64 && part_len(tp[4]) == rel.len() + 1,
        tp[5] is U8,
{
}

fn open_part(cp: &mut StoredParts, Ghost(rel): Ghost<Seq<Row>>) -> (c: PCols)
    requires
        old(cp)@.len() == cpi::CUSTPART_PARTS,
        cpi::part_ok(old(cp)@.subrange(cpi::PART_FIRST as int, (cpi::PART_FIRST + cpi::PA_PARTS) as int), rel),
        rows_in_columns(rel, cpd::stored_columns_t1()),
    ensures
        final(cp)@ == old(cp)@,
        pcols_ok(c, rel),
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
    let mfgr_c = cp.extent_u8(f + 6, 0, n);
    let mfgr_b = cp.extent_u64(f + 7, 0, ng);
    let l = cp.part_len(f + 8);
    let mfgr_o = cp.extent_u64(f + 8, 0, l);
    let l = cp.part_len(f + 9);
    let mfgr_y = cp.extent_u8(f + 9, 0, l);
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
    let c = PCols { n, bs, ng, kind, key_c, key_b, mfgr_c, mfgr_b, mfgr_o, mfgr_y, type_c, type_b, type_o, type_y, size_c, size_b };
    proof {
        assert(lay@ =~= cpi::common::colfmt::u64s(tp[0]));
        assert(key_c@ =~= cpi::common::colfmt::u32s(tp[2]));
        assert(key_b@ =~= cpi::common::colfmt::i64s(tp[3]));
        assert(mfgr_c@ =~= cpi::common::colfmt::u8s(tp[6]));
        assert(mfgr_b@ =~= cpi::common::colfmt::u64s(tp[7]));
        assert(mfgr_o@ =~= cpi::common::colfmt::u64s(tp[8]));
        assert(mfgr_y@ =~= cpi::common::colfmt::u8s(tp[9]));
        assert(type_c@ =~= cpi::common::colfmt::u8s(tp[14]));
        assert(type_b@ =~= cpi::common::colfmt::u64s(tp[15]));
        assert(type_o@ =~= cpi::common::colfmt::u64s(tp[16]));
        assert(type_y@ =~= cpi::common::colfmt::u8s(tp[17]));
        assert(size_c@ =~= cpi::common::colfmt::u8s(tp[18]));
        assert(size_b@ =~= cpi::common::colfmt::i64s(tp[19]));
        assert(kk@ =~= cpi::common::colfmt::u64s(tp[28]));
        lemma_part_cols(tp, rel, c);
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
        c.cost_c@ == spi::common::colfmt::u32s(tp[8]), c.cost_b@ == spi::common::colfmt::i64s(tp[9]),
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
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[9], tp[8], k);
        assert(k / b == k / bt);
        assert(rel[k].len() == spd::stored_columns_t0().len());
        assert(value_in_column(rel[k][0], spd::stored_columns_t0()[0]));
        assert(rel[k].len() == spd::stored_columns_t0().len());
        assert(value_in_column(rel[k][1], spd::stored_columns_t0()[1]));
        assert(rel[k].len() == spd::stored_columns_t0().len());
        assert(value_in_column(rel[k][3], spd::stored_columns_t0()[3]));
        lemma_num15(rel[k][3], fv32(c.cost_c@, c.cost_b@, b, k));
    }
    lemma_keyidx_eff(c.key_c@, c.key_b@, bt, b, c.kind, n);
}

/// A key index stays valid under the effective block size (every row keeps its group).
proof fn lemma_keyidx_eff(kc: Seq<u32>, kb: Seq<i64>, bt: int, b: int, kind: u64, n: int)
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

fn open_partsupp(sp: &mut StoredParts, Ghost(rel): Ghost<Seq<Row>>, e32: &'static [u32], e64: &'static [u64]) -> (c: PSCols)
    requires
        old(sp)@.len() == spi::SUPPLIERS_PARTS,
        spi::partsupp_ok(old(sp)@.subrange(spi::PARTSUPP_FIRST as int, (spi::PARTSUPP_FIRST + spi::PS_PARTS) as int), rel),
        rows_in_columns(rel, spd::stored_columns_t0()),
        e32@ == Seq::<u32>::empty(),
        e64@ == Seq::<u64>::empty(),
    ensures
        final(sp)@ == old(sp)@,
        pscols_ok(c, rel, e32@, e64@),
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
    let cost_c = sp.extent_u32(f + 8, 0, n);
    let cost_b = sp.extent_i64(f + 9, 0, ng);
    let kk = sp.extent_u64(f + 12, 0, 1);
    let kind = kk[0];
    let c = PSCols { n, bs, ng, kind, key_c, key_b, supp_c, supp_b, cost_c, cost_b };
    proof {
        assert(lay@ =~= spi::common::colfmt::u64s(tp[0]));
        assert(key_c@ =~= spi::common::colfmt::u32s(tp[2]));
        assert(key_b@ =~= spi::common::colfmt::i64s(tp[3]));
        assert(supp_c@ =~= spi::common::colfmt::u32s(tp[4]));
        assert(supp_b@ =~= spi::common::colfmt::i64s(tp[5]));
        assert(cost_c@ =~= spi::common::colfmt::u32s(tp[8]));
        assert(cost_b@ =~= spi::common::colfmt::i64s(tp[9]));
        assert(kk@ =~= spi::common::colfmt::u64s(tp[12]));
        lemma_partsupp_cols(tp, rel, c, e32@, e64@);
    }
    c
}

/// supplier: the decoded columns of every row.
proof fn lemma_supplier_rows(tp: Seq<PartView>, rel: Seq<Row>, c: SCols)
    requires
        tp.len() == spi::SU_PARTS,
        frame_parts_ok(tp, rel.len() as int),
        rows_width(rel, 7),
        tp[2] is U32, tp[8] is U8, tp[12] is U32,
        spi::common::colfmt::int_col_at(tp, 1, 2, 3, rel, 0),
        spi::common::colfmt::text_col_at(tp, 4, 5, rel, 1),
        spi::common::colfmt::text_col_at(tp, 6, 7, rel, 2),
        spi::common::colfmt::int_col_at(tp, 1, 8, 9, rel, 3),
        spi::common::colfmt::text_col_at(tp, 10, 11, rel, 4),
        spi::common::colfmt::num_col_at(tp, 1, 12, 13, rel, 5, 2),
        spi::common::colfmt::text_col_at(tp, 14, 15, rel, 6),
        rows_in_columns(rel, spd::stored_columns_t1()),
        c.n == rel.len(),
        c.bs as int == eff_bs(rel.len() as int, spi::common::colfmt::u64s(tp[0])[1] as int),
        c.key_c@ == spi::common::colfmt::u32s(tp[2]), c.key_b@ == spi::common::colfmt::i64s(tp[3]),
        c.name_o@ == spi::common::colfmt::u64s(tp[4]), c.name_y@ == spi::common::colfmt::u8s(tp[5]),
        c.addr_o@ == spi::common::colfmt::u64s(tp[6]), c.addr_y@ == spi::common::colfmt::u8s(tp[7]),
        c.nat_c@ == spi::common::colfmt::u8s(tp[8]), c.nat_b@ == spi::common::colfmt::i64s(tp[9]),
        c.phone_o@ == spi::common::colfmt::u64s(tp[10]), c.phone_y@ == spi::common::colfmt::u8s(tp[11]),
        c.acct_c@ == spi::common::colfmt::u32s(tp[12]), c.acct_b@ == spi::common::colfmt::i64s(tp[13]),
        c.comm_o@ == spi::common::colfmt::u64s(tp[14]), c.comm_y@ == spi::common::colfmt::u8s(tp[15]),
    ensures forall|j: int| 0 <= j < c.n ==> #[trigger] supp_row_ok(c, rel[j], j),
{
    let n = rel.len() as int;
    let bt = spi::common::colfmt::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    lemma_frame_parts(tp, n);
    assert forall|j: int| 0 <= j < n implies #[trigger] supp_row_ok(c, rel[j], j) by {
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[3], tp[2], j);
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[9], tp[8], j);
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[13], tp[12], j);
        assert(j / b == j / bt);
        assert(rel[j].len() == spd::stored_columns_t1().len());
        assert(value_in_column(rel[j][0], spd::stored_columns_t1()[0]));
        assert(value_in_column(rel[j][3], spd::stored_columns_t1()[3]));
        assert(value_in_column(rel[j][5], spd::stored_columns_t1()[5]));
        lemma_num15(rel[j][5], fv32(c.acct_c@, c.acct_b@, b, j));
    }
}

/// The text parts of `n` values in the interface's form give `txt_ok`.
proof fn lemma_txt_ok(o: Seq<u64>, y: Seq<u8>, n: int)
    requires spi::common::colfmt::text_parts_wf(o, y, n),
    ensures txt_ok(o, y, n),
{
    assert forall|j: int| 0 <= j < n implies #[trigger] o[j] <= o[j + 1] && o[j + 1] <= y.len() by {
        assert(spi::common::colfmt::text_range_ok(o, y, j));
    }
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
        c.name_o@ == spi::common::colfmt::u64s(tp[4]), c.name_y@ == spi::common::colfmt::u8s(tp[5]),
        c.addr_o@ == spi::common::colfmt::u64s(tp[6]), c.addr_y@ == spi::common::colfmt::u8s(tp[7]),
        c.nat_c@ == spi::common::colfmt::u8s(tp[8]), c.nat_b@ == spi::common::colfmt::i64s(tp[9]),
        c.phone_o@ == spi::common::colfmt::u64s(tp[10]), c.phone_y@ == spi::common::colfmt::u8s(tp[11]),
        c.acct_c@ == spi::common::colfmt::u32s(tp[12]), c.acct_b@ == spi::common::colfmt::i64s(tp[13]),
        c.comm_o@ == spi::common::colfmt::u64s(tp[14]), c.comm_y@ == spi::common::colfmt::u8s(tp[15]),
        c.kind == spi::common::colfmt::u64s(tp[16])[0],
    ensures scols_ok(c, rel, e32, e64),
{
    let n = rel.len() as int;
    let bt = spi::common::colfmt::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    assert(frame_parts_ok(tp, n));
    lemma_frame_parts(tp, n);
    lemma_supplier_rows(tp, rel, c);
    lemma_txt_ok(c.name_o@, c.name_y@, n);
    lemma_txt_ok(c.addr_o@, c.addr_y@, n);
    lemma_txt_ok(c.phone_o@, c.phone_y@, n);
    lemma_txt_ok(c.comm_o@, c.comm_y@, n);
    lemma_keyidx_eff(c.key_c@, c.key_b@, bt, b, c.kind, n);
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
    let l = sp.part_len(f + 4);
    let name_o = sp.extent_u64(f + 4, 0, l);
    let l = sp.part_len(f + 5);
    let name_y = sp.extent_u8(f + 5, 0, l);
    let l = sp.part_len(f + 6);
    let addr_o = sp.extent_u64(f + 6, 0, l);
    let l = sp.part_len(f + 7);
    let addr_y = sp.extent_u8(f + 7, 0, l);
    let nat_c = sp.extent_u8(f + 8, 0, n);
    let nat_b = sp.extent_i64(f + 9, 0, ng);
    let l = sp.part_len(f + 10);
    let phone_o = sp.extent_u64(f + 10, 0, l);
    let l = sp.part_len(f + 11);
    let phone_y = sp.extent_u8(f + 11, 0, l);
    let acct_c = sp.extent_u32(f + 12, 0, n);
    let acct_b = sp.extent_i64(f + 13, 0, ng);
    let l = sp.part_len(f + 14);
    let comm_o = sp.extent_u64(f + 14, 0, l);
    let l = sp.part_len(f + 15);
    let comm_y = sp.extent_u8(f + 15, 0, l);
    let kk = sp.extent_u64(f + 16, 0, 1);
    let kind = kk[0];
    let c = SCols { n, bs, ng, kind, key_c, key_b, nat_c, nat_b, acct_c, acct_b, name_o, name_y, addr_o, addr_y,
        phone_o, phone_y, comm_o, comm_y };
    proof {
        assert(lay@ =~= spi::common::colfmt::u64s(tp[0]));
        assert(key_c@ =~= spi::common::colfmt::u32s(tp[2]));
        assert(key_b@ =~= spi::common::colfmt::i64s(tp[3]));
        assert(name_o@ =~= spi::common::colfmt::u64s(tp[4]));
        assert(name_y@ =~= spi::common::colfmt::u8s(tp[5]));
        assert(addr_o@ =~= spi::common::colfmt::u64s(tp[6]));
        assert(addr_y@ =~= spi::common::colfmt::u8s(tp[7]));
        assert(nat_c@ =~= spi::common::colfmt::u8s(tp[8]));
        assert(nat_b@ =~= spi::common::colfmt::i64s(tp[9]));
        assert(phone_o@ =~= spi::common::colfmt::u64s(tp[10]));
        assert(phone_y@ =~= spi::common::colfmt::u8s(tp[11]));
        assert(acct_c@ =~= spi::common::colfmt::u32s(tp[12]));
        assert(acct_b@ =~= spi::common::colfmt::i64s(tp[13]));
        assert(comm_o@ =~= spi::common::colfmt::u64s(tp[14]));
        assert(comm_y@ =~= spi::common::colfmt::u8s(tp[15]));
        assert(kk@ =~= spi::common::colfmt::u64s(tp[16]));
        lemma_supplier_cols(tp, rel, c, e32@, e64@);
    }
    c
}

/// nation: the rows of `rel` in terms of the handles `c` taken from the nation parts `tp`.
proof fn lemma_nation_cols(tp: Seq<PartView>, rel: Seq<Row>, c: NCols)
    requires
        spi::nation_ok(tp, rel),
        rows_in_columns(rel, spd::stored_columns_t2()),
        c.n == rel.len(),
        c.ng == part_len(tp[1]) - 1,
        c.bs as int == eff_bs(rel.len() as int, spi::common::colfmt::u64s(tp[0])[1] as int),
        c.key_c@ == spi::common::colfmt::u8s(tp[2]), c.key_b@ == spi::common::colfmt::i64s(tp[3]),
        c.name_o@ == spi::common::colfmt::u64s(tp[4]), c.name_y@ == spi::common::colfmt::u8s(tp[5]),
        c.reg_c@ == spi::common::colfmt::u8s(tp[6]), c.reg_b@ == spi::common::colfmt::i64s(tp[7]),
    ensures ncols_ok(c, rel),
{
    let n = rel.len() as int;
    let bt = spi::common::colfmt::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    assert(frame_parts_ok(tp, n));
    lemma_frame_parts(tp, n);
    assert forall|q: int| 0 <= q < n implies #[trigger] nat_row_ok(c, rel[q], q) by {
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[3], tp[2], q);
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[7], tp[6], q);
        assert(q / b == q / bt);
        assert(rel[q].len() == spd::stored_columns_t2().len());
        assert(value_in_column(rel[q][0], spd::stored_columns_t2()[0]));
        assert(rel[q].len() == spd::stored_columns_t2().len());
        assert(value_in_column(rel[q][2], spd::stored_columns_t2()[2]));
    }
    assert forall|j: int| 0 <= j < n implies #[trigger] c.name_o@[j] <= c.name_o@[j + 1] && c.name_o@[j + 1] <= c.name_y@.len() by {
        assert(spi::common::colfmt::text_range_ok(c.name_o@, c.name_y@, j));
    }
}

fn open_nation(sp: &mut StoredParts, Ghost(rel): Ghost<Seq<Row>>) -> (c: NCols)
    requires
        old(sp)@.len() == spi::SUPPLIERS_PARTS,
        spi::nation_ok(old(sp)@.subrange(spi::NATION_FIRST as int, (spi::NATION_FIRST + spi::NA_PARTS) as int), rel),
        rows_in_columns(rel, spd::stored_columns_t2()),
    ensures
        final(sp)@ == old(sp)@,
        ncols_ok(c, rel),
{
    hide(spi::nation_ok);
    let ghost tp = sp@.subrange(spi::NATION_FIRST as int, (spi::NATION_FIRST + spi::NA_PARTS) as int);
    proof {
        lemma_nation_shape(tp, rel);
        lemma_frame_parts(tp, rel.len() as int);
    }
    let f = spi::NATION_FIRST;
    let n = sp.part_len(f + 2);
    let lay = sp.extent_u64(f, 0, 2);
    let bs = eff_bs_exec(lay[1], n);
    let ng = sp.part_len(f + 1) - 1;
    let key_c = sp.extent_u8(f + 2, 0, n);
    let key_b = sp.extent_i64(f + 3, 0, ng);
    let l = sp.part_len(f + 4);
    let name_o = sp.extent_u64(f + 4, 0, l);
    let l = sp.part_len(f + 5);
    let name_y = sp.extent_u8(f + 5, 0, l);
    let reg_c = sp.extent_u8(f + 6, 0, n);
    let reg_b = sp.extent_i64(f + 7, 0, ng);
    let c = NCols { n, bs, ng, key_c, key_b, reg_c, reg_b, name_o, name_y };
    proof {
        assert(lay@ =~= spi::common::colfmt::u64s(tp[0]));
        assert(key_c@ =~= spi::common::colfmt::u8s(tp[2]));
        assert(key_b@ =~= spi::common::colfmt::i64s(tp[3]));
        assert(name_o@ =~= spi::common::colfmt::u64s(tp[4]));
        assert(name_y@ =~= spi::common::colfmt::u8s(tp[5]));
        assert(reg_c@ =~= spi::common::colfmt::u8s(tp[6]));
        assert(reg_b@ =~= spi::common::colfmt::i64s(tp[7]));
        lemma_nation_cols(tp, rel, c);
    }
    c
}

/// region: the rows of `rel` in terms of the handles `c` taken from the region parts `tp`.
proof fn lemma_region_cols(tp: Seq<PartView>, rel: Seq<Row>, c: RCols)
    requires
        spi::region_ok(tp, rel),
        rows_in_columns(rel, spd::stored_columns_t3()),
        c.n == rel.len(),
        c.ng == part_len(tp[1]) - 1,
        c.bs as int == eff_bs(rel.len() as int, spi::common::colfmt::u64s(tp[0])[1] as int),
        c.key_c@ == spi::common::colfmt::u8s(tp[2]), c.key_b@ == spi::common::colfmt::i64s(tp[3]),
        c.name_o@ == spi::common::colfmt::u64s(tp[4]), c.name_y@ == spi::common::colfmt::u8s(tp[5]),
    ensures rcols_ok(c, rel),
{
    let n = rel.len() as int;
    let bt = spi::common::colfmt::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    assert(frame_parts_ok(tp, n));
    lemma_frame_parts(tp, n);
    assert forall|q: int| 0 <= q < n implies #[trigger] reg_row_ok(c, rel[q], q) by {
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[3], tp[2], q);
        assert(q / b == q / bt);
        assert(rel[q].len() == spd::stored_columns_t3().len());
        assert(value_in_column(rel[q][0], spd::stored_columns_t3()[0]));
    }
    assert forall|j: int| 0 <= j < n implies #[trigger] c.name_o@[j] <= c.name_o@[j + 1] && c.name_o@[j + 1] <= c.name_y@.len() by {
        assert(spi::common::colfmt::text_range_ok(c.name_o@, c.name_y@, j));
    }
}

fn open_region(sp: &mut StoredParts, Ghost(rel): Ghost<Seq<Row>>) -> (c: RCols)
    requires
        old(sp)@.len() == spi::SUPPLIERS_PARTS,
        spi::region_ok(old(sp)@.subrange(spi::REGION_FIRST as int, (spi::REGION_FIRST + spi::RE_PARTS) as int), rel),
        rows_in_columns(rel, spd::stored_columns_t3()),
    ensures
        final(sp)@ == old(sp)@,
        rcols_ok(c, rel),
{
    hide(spi::region_ok);
    let ghost tp = sp@.subrange(spi::REGION_FIRST as int, (spi::REGION_FIRST + spi::RE_PARTS) as int);
    proof {
        lemma_region_shape(tp, rel);
        lemma_frame_parts(tp, rel.len() as int);
    }
    let f = spi::REGION_FIRST;
    let n = sp.part_len(f + 2);
    let lay = sp.extent_u64(f, 0, 2);
    let bs = eff_bs_exec(lay[1], n);
    let ng = sp.part_len(f + 1) - 1;
    let key_c = sp.extent_u8(f + 2, 0, n);
    let key_b = sp.extent_i64(f + 3, 0, ng);
    let l = sp.part_len(f + 4);
    let name_o = sp.extent_u64(f + 4, 0, l);
    let l = sp.part_len(f + 5);
    let name_y = sp.extent_u8(f + 5, 0, l);
    let c = RCols { n, bs, ng, key_c, key_b, name_o, name_y };
    proof {
        assert(lay@ =~= spi::common::colfmt::u64s(tp[0]));
        assert(key_c@ =~= spi::common::colfmt::u8s(tp[2]));
        assert(key_b@ =~= spi::common::colfmt::i64s(tp[3]));
        assert(name_o@ =~= spi::common::colfmt::u64s(tp[4]));
        assert(name_y@ =~= spi::common::colfmt::u8s(tp[5]));
        lemma_region_cols(tp, rel, c);
    }
    c
}

/// Opens every column handle (one extent per part, on the calling thread) over the stored relations `cr`
/// (custpart) and `sr` (suppliers).
pub fn open_cols(stores: &mut Stores, Ghost(cr): Ghost<Seq<Seq<Row>>>, Ghost(sr): Ghost<Seq<Seq<Row>>>) -> (c: Cols)
    requires
        cpi::represents(old(stores).custpart@, cr),
        spi::represents(old(stores).suppliers@, sr),
        rows_in_columns(cr[1], cpd::stored_columns_t1()),
        rows_in_columns(sr[0], spd::stored_columns_t0()),
        rows_in_columns(sr[1], spd::stored_columns_t1()),
        rows_in_columns(sr[2], spd::stored_columns_t2()),
        rows_in_columns(sr[3], spd::stored_columns_t3()),
    ensures
        final(stores)@ == old(stores)@,
        cols_ok(c, Tabs { p: cr[1], s: sr[1], ps: sr[0], n: sr[2], r: sr[3] }),
{
    let p = open_part(&mut stores.custpart, Ghost(cr[1]));
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
    let ps = open_partsupp(&mut stores.suppliers, Ghost(sr[0]), e32, e64);
    let s = open_supplier(&mut stores.suppliers, Ghost(sr[1]), e32, e64);
    let n = open_nation(&mut stores.suppliers, Ghost(sr[2]));
    let r = open_region(&mut stores.suppliers, Ghost(sr[3]));
    Cols { p, ps, s, n, r, e32, e64 }
}

} // verus!
