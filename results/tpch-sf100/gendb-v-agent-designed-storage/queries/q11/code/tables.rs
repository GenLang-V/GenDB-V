//! Column handles of the three Q11 tables, read from the admitted storage `suppliers` (partsupp, supplier,
//! nation) as zero-copy extents, and the values they decode to.
//!
//! Every stored table is in canonical row order with uniform groups of `bs` rows (`ng` groups); a frame-of-reference
//! (FOR) column stores row `j` as `base[j / bs] + code[j]` (`fv32`, `fv16`, `fv8`); plain text is offsets + bytes
//! (`txt`). `*_row_ok(c, r, j)` states what row `j` of a table is in terms of its handles `c`; `*cols_ok(c, rel)`
//! states it for every row, plus the shape facts (lengths, frame) the readers need. partsupp also carries its key
//! index kind: kind 1 means the stored rows are sorted by ps_partkey (`pscols_ok`, `ps_sorted`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::{Column, SqlType};
use crate::spec::typing::value_in_column;
use crate::spec::numeric::{abs, pow10};
use crate::link::source::rows_in_columns;
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::stored::{StoredParts, part_len};
use crate::gendb_entry::layout::PartView;
use crate::stores::suppliers::interface as spi;
use crate::stores::suppliers::declaration as spd;
use crate::stores::suppliers::interface::common::colfmt as cf;

verus! {

// ------------------------------------------------------------------------------------------------ decoding

/// FOR value of row `j` (U32 codes, I64 bases, blocks of `bs` rows).
pub open spec fn fv32(c: Seq<u32>, b: Seq<i64>, bs: int, j: int) -> int {
    b[j / bs] + c[j]
}

/// FOR value of row `j` (U16 codes, I64 bases).
pub open spec fn fv16(c: Seq<u16>, b: Seq<i64>, bs: int, j: int) -> int {
    b[j / bs] + c[j]
}

/// FOR value of row `j` (U8 codes, I64 bases).
pub open spec fn fv8(c: Seq<u8>, b: Seq<i64>, bs: int, j: int) -> int {
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

/// partsupp: ps_partkey, ps_suppkey (FOR u32), ps_availqty (FOR u16), ps_supplycost (FOR u32), the key index
/// kind of ps_partkey (1: rows sorted by ps_partkey), and the run layout of ps_partkey when known (`krun`: row `k`
/// has ps_partkey `kfirst + k / 4`, `krun_ok`), so the scan derives keys without reading the key column.
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
    pub qty_c: &'static [u16],
    pub qty_b: &'static [i64],
    pub cost_c: &'static [u32],
    pub cost_b: &'static [i64],
    pub krun: bool,
    pub kfirst: i64,
}

/// supplier: s_suppkey (FOR u32), s_nationkey (FOR u8).
#[derive(Clone, Copy)]
pub struct SCols {
    pub n: usize,
    pub bs: usize,
    pub ng: usize,
    pub key_c: &'static [u32],
    pub key_b: &'static [i64],
    pub nat_c: &'static [u8],
    pub nat_b: &'static [i64],
}

/// nation: n_nationkey (FOR u8), n_name.
#[derive(Clone, Copy)]
pub struct NCols {
    pub n: usize,
    pub bs: usize,
    pub ng: usize,
    pub key_c: &'static [u8],
    pub key_b: &'static [i64],
    pub name_o: &'static [u64],
    pub name_y: &'static [u8],
}

/// Every handle the statement reads.
#[derive(Clone, Copy)]
pub struct Cols {
    pub ps: PSCols,
    pub s: SCols,
    pub n: NCols,
}

// ------------------------------------------------------------------------------------------------ row facts

pub open spec fn ps_row_ok(c: PSCols, r: Row, k: int) -> bool {
    let bs = c.bs as int;
    &&& r.len() == 5
    &&& r[0] == Val::Int(fv32(c.key_c@, c.key_b@, bs, k)) && i64r(fv32(c.key_c@, c.key_b@, bs, k))
    &&& r[1] == Val::Int(fv32(c.supp_c@, c.supp_b@, bs, k)) && i64r(fv32(c.supp_c@, c.supp_b@, bs, k))
    &&& r[2] == Val::Int(fv16(c.qty_c@, c.qty_b@, bs, k)) && i64r(fv16(c.qty_c@, c.qty_b@, bs, k))
    &&& r[3] == (Val::Num { coeff: fv32(c.cost_c@, c.cost_b@, bs, k), scale: 2 })
    &&& abs(fv32(c.cost_c@, c.cost_b@, bs, k)) < pow10(15)
}

/// The rows are sorted by ps_partkey (consecutive keys nondecreasing).
pub open spec fn ps_sorted(c: PSCols) -> bool {
    forall|i: int| 0 <= i < c.n - 1
        ==> #[trigger] fv32(c.key_c@, c.key_b@, c.bs as int, i) <= fv32(c.key_c@, c.key_b@, c.bs as int, i + 1)
}

pub open spec fn pscols_ok(c: PSCols, ps: Seq<Row>) -> bool {
    &&& frame_ok(c.n as int, c.bs as int, c.ng as int)
    &&& ps.len() == c.n
    &&& c.key_c@.len() == c.n && c.key_b@.len() == c.ng
    &&& c.supp_c@.len() == c.n && c.supp_b@.len() == c.ng
    &&& c.qty_c@.len() == c.n && c.qty_b@.len() == c.ng
    &&& c.cost_c@.len() == c.n && c.cost_b@.len() == c.ng
    &&& forall|k: int| 0 <= k < c.n ==> #[trigger] ps_row_ok(c, ps[k], k)
    &&& c.kind == 1 ==> ps_sorted(c)
    &&& krun_ok(c)
}

/// With `krun`, ps_partkey runs of 4 rows with consecutive keys from `kfirst`: row `k`'s key is `kfirst + k / 4`.
#[verifier::opaque]
pub open spec fn krun_ok(c: PSCols) -> bool {
    c.krun ==> forall|k: int| 0 <= k < c.n ==> #[trigger] fv32(c.key_c@, c.key_b@, c.bs as int, k) == c.kfirst + k / 4
}

pub open spec fn supp_row_ok(c: SCols, r: Row, j: int) -> bool {
    let bs = c.bs as int;
    &&& r.len() == 7
    &&& r[0] == Val::Int(fv32(c.key_c@, c.key_b@, bs, j)) && i64r(fv32(c.key_c@, c.key_b@, bs, j))
    &&& r[3] == Val::Int(fv8(c.nat_c@, c.nat_b@, bs, j)) && i64r(fv8(c.nat_c@, c.nat_b@, bs, j))
}

pub open spec fn scols_ok(c: SCols, s: Seq<Row>) -> bool {
    &&& frame_ok(c.n as int, c.bs as int, c.ng as int)
    &&& s.len() == c.n
    &&& c.key_c@.len() == c.n && c.key_b@.len() == c.ng
    &&& c.nat_c@.len() == c.n && c.nat_b@.len() == c.ng
    &&& forall|j: int| 0 <= j < c.n ==> #[trigger] supp_row_ok(c, s[j], j)
}

pub open spec fn nat_row_ok(c: NCols, r: Row, q: int) -> bool {
    let bs = c.bs as int;
    &&& r.len() == 4
    &&& r[0] == Val::Int(fv8(c.key_c@, c.key_b@, bs, q)) && i64r(fv8(c.key_c@, c.key_b@, bs, q))
    &&& r[1] == Val::Text(txt(c.name_o@, c.name_y@, q))
}

pub open spec fn ncols_ok(c: NCols, n: Seq<Row>) -> bool {
    &&& frame_ok(c.n as int, c.bs as int, c.ng as int)
    &&& n.len() == c.n
    &&& c.key_c@.len() == c.n && c.key_b@.len() == c.ng
    &&& txt_ok(c.name_o@, c.name_y@, c.n as int)
    &&& forall|q: int| 0 <= q < c.n ==> #[trigger] nat_row_ok(c, n[q], q)
}

/// The three tables of the statement (full rows, canonical order): partsupp, supplier, nation.
pub struct Tabs {
    pub ps: Seq<Row>,
    pub s: Seq<Row>,
    pub n: Seq<Row>,
}

pub open spec fn cols_ok(c: Cols, t: Tabs) -> bool {
    &&& pscols_ok(c.ps, t.ps)
    &&& scols_ok(c.s, t.s)
    &&& ncols_ok(c.n, t.n)
}

// ------------------------------------------------------------------------------------------------ lemmas

/// Row `j` of `n` lies in a group below `ng`.
pub proof fn lemma_grp_bound(n: int, bs: int, ng: int, j: int)
    requires frame_ok(n, bs, ng), 0 <= j < n,
    ensures 0 <= j / bs < ng,
{
    spi::common::read::lemma_div_lt(j, bs, ng);
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
    requires 0 <= n, 1 <= bt, n + bt <= u64::MAX, ng == cf::nblocks_of(n, bt),
    ensures
        frame_ok(n, eff_bs(n, bt), ng),
        forall|j: int| 0 <= j < n ==> #[trigger] (j / eff_bs(n, bt)) == j / bt,
{
    cf::lemma_nblocks(n, bt);
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

/// A numeric(15,2) value's coefficient is below `10^15` in absolute value.
proof fn lemma_num15(v: Val, coeff: int)
    requires value_in_column(v, Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        v == (Val::Num { coeff, scale: 2 }),
    ensures abs(coeff) < pow10(15),
{
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
    &&& cf::u64s(tp[0]).len() == 2
    &&& cf::groups_part_ok(tp[1], n, cf::u64s(tp[0])[1] as int)
}

proof fn lemma_frame_parts(tp: Seq<PartView>, n: int)
    requires frame_parts_ok(tp, n),
    ensures ({
        let bt = cf::u64s(tp[0])[1] as int;
        let ng = part_len(tp[1]) - 1;
        &&& 1 <= bt && n + bt <= u64::MAX && n >= 0
        &&& part_len(tp[1]) >= 1
        &&& ng == cf::nblocks_of(n, bt)
        &&& frame_ok(n, eff_bs(n, bt), ng)
        &&& forall|j: int| 0 <= j < n ==> #[trigger] (j / eff_bs(n, bt)) == j / bt
    }),
{
    let bt = cf::u64s(tp[0])[1] as int;
    cf::lemma_uniform_groups(tp[1], n, bt);
    lemma_eff_bs(n, bt, part_len(tp[1]) - 1);
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
        tp[6] is U16 && part_len(tp[6]) == rel.len(),
        tp[7] is I64 && part_len(tp[7]) == part_len(tp[1]) - 1,
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
        tp[8] is U8 && part_len(tp[8]) == rel.len(),
        tp[9] is I64 && part_len(tp[9]) == part_len(tp[1]) - 1,
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
{
}

/// A key index of kind 1 (rows sorted by key) under the effective block size: consecutive keys nondecreasing.
proof fn lemma_sorted_eff(kc: Seq<u32>, kb: Seq<i64>, bt: int, b: int, kind: u64, n: int)
    requires
        spi::common::keyidx::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bt, kind, n),
        kind == 1,
        b >= 1,
        forall|j: int| 0 <= j < n ==> #[trigger] (j / b) == j / bt,
    ensures forall|i: int| 0 <= i < n - 1 ==> #[trigger] fv32(kc, kb, b, i) <= fv32(kc, kb, b, i + 1),
{
    assert forall|i: int| 0 <= i < n - 1 implies #[trigger] fv32(kc, kb, b, i) <= fv32(kc, kb, b, i + 1) by {
        assert(spi::common::keyidx::sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), bt, kind, i));
        assert(i / b == i / bt);
        assert((i + 1) / b == (i + 1) / bt);
    }
}

/// partsupp: the rows of `rel` in terms of the handles `c` taken from the partsupp parts `tp`.
proof fn lemma_partsupp_cols(tp: Seq<PartView>, rel: Seq<Row>, c: PSCols)
    requires
        spi::partsupp_ok(tp, rel),
        rows_in_columns(rel, spd::stored_columns_t0()),
        c.n == rel.len(),
        c.ng == part_len(tp[1]) - 1,
        c.bs as int == eff_bs(rel.len() as int, cf::u64s(tp[0])[1] as int),
        c.key_c@ == cf::u32s(tp[2]), c.key_b@ == cf::i64s(tp[3]),
        c.supp_c@ == cf::u32s(tp[4]), c.supp_b@ == cf::i64s(tp[5]),
        c.qty_c@ == u16s(tp[6]), c.qty_b@ == cf::i64s(tp[7]),
        c.cost_c@ == cf::u32s(tp[8]), c.cost_b@ == cf::i64s(tp[9]),
        c.kind == cf::u64s(tp[12])[0],
        !c.krun,
    ensures pscols_ok(c, rel),
{
    let n = rel.len() as int;
    let bt = cf::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    assert(frame_parts_ok(tp, n));
    lemma_frame_parts(tp, n);
    assert forall|k: int| 0 <= k < n implies #[trigger] ps_row_ok(c, rel[k], k) by {
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[3], tp[2], k);
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[5], tp[4], k);
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[7], tp[6], k);
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[9], tp[8], k);
        assert(k / b == k / bt);
        assert(rel[k].len() == spd::stored_columns_t0().len());
        assert(value_in_column(rel[k][0], spd::stored_columns_t0()[0]));
        assert(value_in_column(rel[k][1], spd::stored_columns_t0()[1]));
        assert(value_in_column(rel[k][2], spd::stored_columns_t0()[2]));
        assert(value_in_column(rel[k][3], spd::stored_columns_t0()[3]));
        lemma_num15(rel[k][3], fv32(c.cost_c@, c.cost_b@, b, k));
    }
    if c.kind == 1 {
        lemma_sorted_eff(c.key_c@, c.key_b@, bt, b, c.kind, n);
    }
    reveal(krun_ok);
}

/// The run layout `[ratio, first]` of storage suppliers_psrun with `ratio == 4` gives `krun_ok` for `kfirst = first`.
pub proof fn lemma_krun(c: PSCols, ps: Seq<Row>, run: Seq<i64>)
    requires
        pscols_ok(c, ps), run.len() == 2, run[0] == 4,
        forall|k: int| 0 <= k < ps.len() ==> #[trigger] ps[k][0] == Val::Int(run[1] + k / (run[0] as int)),
    ensures pscols_ok(PSCols { krun: true, kfirst: run[1], ..c }, ps),
{
    let c2 = PSCols { krun: true, kfirst: run[1], ..c };
    assert forall|k: int| 0 <= k < c2.n implies #[trigger] ps_row_ok(c2, ps[k], k) by {
        assert(ps_row_ok(c, ps[k], k));
    }
    reveal(krun_ok);
    assert forall|k: int| 0 <= k < c2.n implies #[trigger] fv32(c2.key_c@, c2.key_b@, c2.bs as int, k) == c2.kfirst + k / 4 by {
        assert(ps_row_ok(c, ps[k], k));
        assert(ps[k][0] == Val::Int(run[1] + k / (run[0] as int)));
    }
    if c.kind == 1 {
        assert(ps_sorted(c2));
    }
}

/// The values of a U16 part (empty for another kind).
pub open spec fn u16s(p: PartView) -> Seq<u16> {
    match p {
        PartView::U16(s) => s,
        _ => Seq::empty(),
    }
}

fn open_partsupp(sp: &mut StoredParts, Ghost(rel): Ghost<Seq<Row>>) -> (c: PSCols)
    requires
        old(sp)@.len() == spi::SUPPLIERS_PARTS,
        spi::partsupp_ok(old(sp)@.subrange(spi::PARTSUPP_FIRST as int, (spi::PARTSUPP_FIRST + spi::PS_PARTS) as int), rel),
        rows_in_columns(rel, spd::stored_columns_t0()),
    ensures
        final(sp)@ == old(sp)@,
        pscols_ok(c, rel),
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
    let qty_c = sp.extent_u16(f + 6, 0, n);
    let qty_b = sp.extent_i64(f + 7, 0, ng);
    let cost_c = sp.extent_u32(f + 8, 0, n);
    let cost_b = sp.extent_i64(f + 9, 0, ng);
    let kk = sp.extent_u64(f + 12, 0, 1);
    let kind = kk[0];
    let c = PSCols { n, bs, ng, kind, key_c, key_b, supp_c, supp_b, qty_c, qty_b, cost_c, cost_b, krun: false, kfirst: 0 };
    proof {
        reveal(krun_ok);
        assert(lay@ =~= cf::u64s(tp[0]));
        assert(key_c@ =~= cf::u32s(tp[2]));
        assert(key_b@ =~= cf::i64s(tp[3]));
        assert(supp_c@ =~= cf::u32s(tp[4]));
        assert(supp_b@ =~= cf::i64s(tp[5]));
        assert(qty_c@ =~= u16s(tp[6]));
        assert(qty_b@ =~= cf::i64s(tp[7]));
        assert(cost_c@ =~= cf::u32s(tp[8]));
        assert(cost_b@ =~= cf::i64s(tp[9]));
        assert(kk@ =~= cf::u64s(tp[12]));
        lemma_partsupp_cols(tp, rel, c);
    }
    c
}

/// supplier: the rows of `rel` in terms of the handles `c` taken from the supplier parts `tp`.
proof fn lemma_supplier_cols(tp: Seq<PartView>, rel: Seq<Row>, c: SCols)
    requires
        spi::supplier_ok(tp, rel),
        rows_in_columns(rel, spd::stored_columns_t1()),
        c.n == rel.len(),
        c.ng == part_len(tp[1]) - 1,
        c.bs as int == eff_bs(rel.len() as int, cf::u64s(tp[0])[1] as int),
        c.key_c@ == cf::u32s(tp[2]), c.key_b@ == cf::i64s(tp[3]),
        c.nat_c@ == cf::u8s(tp[8]), c.nat_b@ == cf::i64s(tp[9]),
    ensures scols_ok(c, rel),
{
    let n = rel.len() as int;
    let bt = cf::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    assert(frame_parts_ok(tp, n));
    lemma_frame_parts(tp, n);
    assert forall|j: int| 0 <= j < n implies #[trigger] supp_row_ok(c, rel[j], j) by {
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[3], tp[2], j);
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[9], tp[8], j);
        assert(j / b == j / bt);
        assert(rel[j].len() == spd::stored_columns_t1().len());
        assert(value_in_column(rel[j][0], spd::stored_columns_t1()[0]));
        assert(value_in_column(rel[j][3], spd::stored_columns_t1()[3]));
    }
}

fn open_supplier(sp: &mut StoredParts, Ghost(rel): Ghost<Seq<Row>>) -> (c: SCols)
    requires
        old(sp)@.len() == spi::SUPPLIERS_PARTS,
        spi::supplier_ok(old(sp)@.subrange(spi::SUPPLIER_FIRST as int, (spi::SUPPLIER_FIRST + spi::SU_PARTS) as int), rel),
        rows_in_columns(rel, spd::stored_columns_t1()),
    ensures
        final(sp)@ == old(sp)@,
        scols_ok(c, rel),
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
    let nat_c = sp.extent_u8(f + 8, 0, n);
    let nat_b = sp.extent_i64(f + 9, 0, ng);
    let c = SCols { n, bs, ng, key_c, key_b, nat_c, nat_b };
    proof {
        assert(lay@ =~= cf::u64s(tp[0]));
        assert(key_c@ =~= cf::u32s(tp[2]));
        assert(key_b@ =~= cf::i64s(tp[3]));
        assert(nat_c@ =~= cf::u8s(tp[8]));
        assert(nat_b@ =~= cf::i64s(tp[9]));
        lemma_supplier_cols(tp, rel, c);
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
        c.bs as int == eff_bs(rel.len() as int, cf::u64s(tp[0])[1] as int),
        c.key_c@ == cf::u8s(tp[2]), c.key_b@ == cf::i64s(tp[3]),
        c.name_o@ == cf::u64s(tp[4]), c.name_y@ == cf::u8s(tp[5]),
    ensures ncols_ok(c, rel),
{
    let n = rel.len() as int;
    let bt = cf::u64s(tp[0])[1] as int;
    let b = c.bs as int;
    assert(frame_parts_ok(tp, n));
    lemma_frame_parts(tp, n);
    assert forall|q: int| 0 <= q < n implies #[trigger] nat_row_ok(c, rel[q], q) by {
        spi::common::read::lemma_for_row(tp[1], n, bt, tp[3], tp[2], q);
        assert(q / b == q / bt);
        assert(rel[q].len() == spd::stored_columns_t2().len());
        assert(value_in_column(rel[q][0], spd::stored_columns_t2()[0]));
    }
    assert forall|j: int| 0 <= j < n implies #[trigger] c.name_o@[j] <= c.name_o@[j + 1] && c.name_o@[j + 1] <= c.name_y@.len() by {
        assert(cf::text_range_ok(c.name_o@, c.name_y@, j));
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
    let c = NCols { n, bs, ng, key_c, key_b, name_o, name_y };
    proof {
        assert(lay@ =~= cf::u64s(tp[0]));
        assert(key_c@ =~= cf::u8s(tp[2]));
        assert(key_b@ =~= cf::i64s(tp[3]));
        assert(name_o@ =~= cf::u64s(tp[4]));
        assert(name_y@ =~= cf::u8s(tp[5]));
        lemma_nation_cols(tp, rel, c);
    }
    c
}

/// Opens every column handle (one extent per part, on the calling thread) over the stored relations `sr`
/// (suppliers: partsupp, supplier, nation, region).
pub fn open_cols(stores: &mut Stores, Ghost(sr): Ghost<Seq<Seq<Row>>>) -> (c: Cols)
    requires
        spi::represents(old(stores).suppliers@, sr),
        rows_in_columns(sr[0], spd::stored_columns_t0()),
        rows_in_columns(sr[1], spd::stored_columns_t1()),
        rows_in_columns(sr[2], spd::stored_columns_t2()),
    ensures
        final(stores)@ == old(stores)@,
        cols_ok(c, Tabs { ps: sr[0], s: sr[1], n: sr[2] }),
{
    let ps = open_partsupp(&mut stores.suppliers, Ghost(sr[0]));
    let s = open_supplier(&mut stores.suppliers, Ghost(sr[1]));
    let n = open_nation(&mut stores.suppliers, Ghost(sr[2]));
    Cols { ps, s, n }
}

} // verus!
