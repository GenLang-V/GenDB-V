//! Reading the stored parts on the calling thread: whole-part extents, and per table the column slices the kernel
//! reads with their decoded views (`common::forview`), established from each storage's `represents` and the
//! relations' shapes (`world::rels_shapes`). Lineitem and orders are read from storage `li_okruns` (facts' 75 parts,
//! then the l_orderkey run starts `st`, stated over the stored lineitem rows by `runs_wf`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::gendb_entry::stored::{StoredParts, part_len};
use crate::gendb_entry::layout::PartView;
use crate::stores::facts::interface as fi;
use crate::stores::facts::interface::common::colfmt as fcf;
use crate::stores::facts::interface::common::keyidx as okx;
use crate::stores::li_okruns::interface as lr;
use crate::stores::custpart::interface as ci;
use crate::stores::custpart::interface::common::colfmt as ccf;
use crate::stores::custpart::interface::common::keyidx as ckx;
use crate::stores::suppliers::interface as si;
use crate::stores::suppliers::interface::common::colfmt as scf;
use crate::stores::suppliers::interface::common::keyidx as skx;
use crate::agent::q5spec::*;
use crate::agent::sqlrow::{is_int8, is_num15};
use crate::agent::lookup::keys_unique;
use crate::agent::world::*;
use crate::agent::common::forview::*;
use crate::agent::views_facts as vf;
use crate::agent::views_custpart as vc;
use crate::agent::views_suppliers as vs;

verus! {

// ------------------------------------------------------------------------------------------- whole parts

pub fn whole_u8(sp: &mut StoredParts, p: usize) -> (r: &'static [u8])
    requires p < old(sp)@.len(), old(sp)@[p as int] is U8,
    ensures final(sp)@ == old(sp)@, r@ == old(sp)@[p as int]->U8_0,
{
    let n = sp.part_len(p);
    let r = sp.extent_u8(p, 0, n);
    proof {
        assert(r@ =~= old(sp)@[p as int]->U8_0);
    }
    r
}

pub fn whole_u16(sp: &mut StoredParts, p: usize) -> (r: &'static [u16])
    requires p < old(sp)@.len(), old(sp)@[p as int] is U16,
    ensures final(sp)@ == old(sp)@, r@ == old(sp)@[p as int]->U16_0,
{
    let n = sp.part_len(p);
    let r = sp.extent_u16(p, 0, n);
    proof {
        assert(r@ =~= old(sp)@[p as int]->U16_0);
    }
    r
}

pub fn whole_u32(sp: &mut StoredParts, p: usize) -> (r: &'static [u32])
    requires p < old(sp)@.len(), old(sp)@[p as int] is U32,
    ensures final(sp)@ == old(sp)@, r@ == old(sp)@[p as int]->U32_0,
{
    let n = sp.part_len(p);
    let r = sp.extent_u32(p, 0, n);
    proof {
        assert(r@ =~= old(sp)@[p as int]->U32_0);
    }
    r
}

pub fn whole_u64(sp: &mut StoredParts, p: usize) -> (r: &'static [u64])
    requires p < old(sp)@.len(), old(sp)@[p as int] is U64,
    ensures final(sp)@ == old(sp)@, r@ == old(sp)@[p as int]->U64_0,
{
    let n = sp.part_len(p);
    let r = sp.extent_u64(p, 0, n);
    proof {
        assert(r@ =~= old(sp)@[p as int]->U64_0);
    }
    r
}

pub fn whole_i64(sp: &mut StoredParts, p: usize) -> (r: &'static [i64])
    requires p < old(sp)@.len(), old(sp)@[p as int] is I64,
    ensures final(sp)@ == old(sp)@, r@ == old(sp)@[p as int]->I64_0,
{
    let n = sp.part_len(p);
    let r = sp.extent_i64(p, 0, n);
    proof {
        assert(r@ =~= old(sp)@[p as int]->I64_0);
    }
    r
}

// ------------------------------------------------------------------------------------------- lineitem

/// The lineitem columns the kernel reads.
pub struct LineCols {
    pub lk_c: &'static [u32],
    pub lk_b: &'static [i64],
    pub ls_c: &'static [u32],
    pub ls_b: &'static [i64],
    pub le_c: &'static [u32],
    pub le_b: &'static [i64],
    pub ld_c: &'static [u8],
    pub ld_b: &'static [i64],
    /// li_okruns: the start row of every run of equal l_orderkey, then the row count
    pub st: &'static [u32],
    pub n_l: usize,
    pub div: Div,
    pub lrows: Ghost<Seq<Row>>,
}

/// Run `k` of the run starts: rows `[st[k], st[k + 1])` are nonempty, inside the table, share the l_orderkey of their
/// first row, and the row after the run (if any) has another l_orderkey.
pub open spec fn run_l(lrows: Seq<Row>, st: Seq<u32>, k: int) -> bool {
    let a = st[k] as int;
    let b = st[k + 1] as int;
    &&& a < b <= lrows.len()
    &&& forall|s: int| a <= s < b ==> (#[trigger] lrows[s])[0] == lrows[a][0]
    &&& b < lrows.len() ==> lrows[b][0] != lrows[b - 1][0]
}

/// The run starts over the stored lineitem rows: at least one entry, the first is row 0, every run is correct.
pub open spec fn runs_wf(lrows: Seq<Row>, st: Seq<u32>) -> bool {
    &&& st.len() >= 1
    &&& st[0] == 0
    &&& forall|k: int| 0 <= k < st.len() - 1 ==> #[trigger] run_l(lrows, st, k)
}

/// Stored lineitem row `j` decodes to its columns (the kernel's `lrow_ok`).
pub open spec fn line_row_ok(c: LineCols, j: int) -> bool {
    let l = c.lrows@[j];
    let bs = c.div.bs as int;
    &&& l.len() == 15
    &&& l[0] == Val::Int(fv32(c.lk_c@, c.lk_b@, bs, j))
    &&& l[2] == Val::Int(fv32(c.ls_c@, c.ls_b@, bs, j))
    &&& l[5] == (Val::Num { coeff: fv32(c.le_c@, c.le_b@, bs, j), scale: 2 })
    &&& l[6] == (Val::Num { coeff: fv8(c.ld_c@, c.ld_b@, bs, j), scale: 2 })
    &&& abs(fv32(c.le_c@, c.le_b@, bs, j)) < pow10(15)
    &&& abs(fv8(c.ld_c@, c.ld_b@, bs, j)) < pow10(15)
}

pub open spec fn line_cols_ok(c: LineCols, rs: Rels) -> bool {
    let bs = c.div.bs as int;
    &&& c.div.ok()
    &&& c.lrows@.len() == c.n_l
    &&& col32_ok(c.lk_c@, c.lk_b@, bs, c.n_l as int)
    &&& col32_ok(c.ls_c@, c.ls_b@, bs, c.n_l as int)
    &&& col32_ok(c.le_c@, c.le_b@, bs, c.n_l as int)
    &&& col8_ok(c.ld_c@, c.ld_b@, bs, c.n_l as int)
    &&& forall|j: int| 0 <= j < c.n_l ==> #[trigger] line_row_ok(c, j)
    &&& c.lrows@.to_multiset() == rs.l.to_multiset()
    &&& runs_wf(c.lrows@, c.st@)
}

/// The stored lineitem rows of the facts parts.
pub open spec fn lrows_of(parts: Seq<PartView>, rs: Rels) -> Seq<Row> {
    fi::lineitem_rows(parts.subrange(fi::LINEITEM_FIRST as int, (fi::LINEITEM_FIRST + fi::LI_PARTS) as int), rs.l)
}

pub fn read_lineitem(fp: &mut StoredParts, rs: Ghost<Rels>) -> (c: LineCols)
    requires
        lr::represents(old(fp)@, seq![rs@.l, rs@.o]),
        rels_shapes(rs@),
    ensures
        final(fp)@ == old(fp)@,
        line_cols_ok(c, rs@),
        c.lrows@ == lrows_of(old(fp)@.subrange(0, 75), rs@),
{
    let ghost all = fp@;
    let ghost parts = all.subrange(0, 75);
    let ghost tp = parts.subrange(0, 48);
    let ghost lrel = rs@.l;
    let ghost n = lrel.len() as int;
    proof {
        assert(fi::represents(parts, seq![rs@.l, rs@.o]));
        assert(fi::lineitem_ok(tp, lrel));
        assert(forall|i: int| 0 <= i < 48 ==> #[trigger] tp[i] == all[i]);
    }
    let lay = whole_u64(fp, fi::LI_LAYOUT);
    let n_l = fp.part_len(fi::LI_ORDERKEY_CODES);
    let bs = lay[1];
    let (div, _) = div_for(bs, n_l);
    let lk_c = whole_u32(fp, fi::LI_ORDERKEY_CODES);
    let lk_b = whole_i64(fp, fi::LI_ORDERKEY_BASE);
    let ls_c = whole_u32(fp, fi::LI_SUPPKEY_CODES);
    let ls_b = whole_i64(fp, fi::LI_SUPPKEY_BASE);
    let le_c = whole_u32(fp, fi::LI_EXTENDEDPRICE_CODES);
    let le_b = whole_i64(fp, fi::LI_EXTENDEDPRICE_BASE);
    let ld_c = whole_u8(fp, fi::LI_DISCOUNT_CODES);
    let ld_b = whole_i64(fp, fi::LI_DISCOUNT_BASE);
    let st = whole_u32(fp, lr::RUN_STARTS);
    let ghost lrows = lrows_of(parts, rs@);
    proof {
        let lmap = fi::lineitem_map(tp, n);
        assert(lrows == fcf::stored_rows(lrel, lmap));
        assert(fcf::is_perm(lmap, n));
        assert forall|j: int| 0 <= j < n implies {
            let l = #[trigger] lrows[j];
            &&& l == lrel[lmap[j]] && 0 <= lmap[j] < n
        } by {}
        assert forall|j: int| 0 <= j < lrows.len() implies
            (#[trigger] lrows[j][0]) is Int && i64::MIN <= lrows[j][0]->Int_0 <= i64::MAX by {
            assert(lrows[j] == lrel[lmap[j]]);
        }
        assert forall|j: int| 0 <= j < lrows.len() implies
            (#[trigger] lrows[j][2]) is Int && i64::MIN <= lrows[j][2]->Int_0 <= i64::MAX by {
            assert(lrows[j] == lrel[lmap[j]]);
        }
        assert forall|j: int| 0 <= j < lrows.len() implies abs((#[trigger] lrows[j][5])->Num_coeff) < pow10(15) by {
            assert(lrows[j] == lrel[lmap[j]]);
        }
        assert forall|j: int| 0 <= j < lrows.len() implies abs((#[trigger] lrows[j][6])->Num_coeff) < pow10(15) by {
            assert(lrows[j] == lrel[lmap[j]]);
        }
        let b = bs as int;
        let b2 = div.bs as int;
        vf::lemma_int32(tp, 1, 4, 5, lrows, 0, b);
        vf::lemma_int32(tp, 1, 8, 9, lrows, 2, b);
        vf::lemma_num32(tp, 1, 14, 15, lrows, 5, b);
        vf::lemma_num8(tp, 1, 16, 17, lrows, 6, b);
        lemma_col32_rebase(lk_c@, lk_b@, b, b2, n);
        lemma_col32_rebase(ls_c@, ls_b@, b, b2, n);
        lemma_col32_rebase(le_c@, le_b@, b, b2, n);
        lemma_col8_rebase(ld_c@, ld_b@, b, b2, n);
        let c = LineCols { lk_c, lk_b, ls_c, ls_b, le_c, le_b, ld_c, ld_b, st, n_l, div, lrows: Ghost(lrows) };
        // the run starts over the stored rows: li_okruns states them over the l_orderkey column of its parts
        assert(lr::runs_ok(all));
        assert(fcf::u64s(tp[0])[0] == n);
        assert(lr::li_rows(all) == n);
        assert(lr::li_bsize(all) == b);
        assert forall|s: int| 0 <= s < n implies #[trigger] lr::okey_at(all, s) == fv32(lk_c@, lk_b@, b, s) by {}
        assert forall|k: int| 0 <= k < st@.len() - 1 implies #[trigger] run_l(lrows, st@, k) by {
            assert(lr::run_ok(all, k));
            let a = st@[k] as int;
            let e = st@[k + 1] as int;
            assert(lrows[a][0] == Val::Int(lr::okey_at(all, a)));
            assert forall|s: int| a <= s < e implies (#[trigger] lrows[s])[0] == lrows[a][0] by {
                assert(lr::okey_at(all, s) == lr::okey_at(all, a));
                assert(lrows[s][0] == Val::Int(lr::okey_at(all, s)));
            }
            if e < n {
                assert(lrows[e][0] == Val::Int(lr::okey_at(all, e)));
                assert(lrows[e - 1][0] == Val::Int(lr::okey_at(all, e - 1)));
            }
        }
        assert forall|j: int| 0 <= j < n_l implies #[trigger] line_row_ok(c, j) by {
            assert(lrows[j] == lrel[lmap[j]]);
            assert(lrows[j][0] == Val::Int(fv32(lk_c@, lk_b@, b, j)));
            assert(lrows[j][2] == Val::Int(fv32(ls_c@, ls_b@, b, j)));
            assert(lrows[j][5] == (Val::Num { coeff: fv32(le_c@, le_b@, b, j), scale: 2 }));
            assert(lrows[j][6] == (Val::Num { coeff: fv8(ld_c@, ld_b@, b, j), scale: 2 }));
            assert(abs(fv32(le_c@, le_b@, b, j)) < pow10(15));
            assert(abs(fv8(ld_c@, ld_b@, b, j)) < pow10(15));
        }
        fcf::lemma_stored_rows_multiset(lrel, lmap);
    }
    LineCols { lk_c, lk_b, ls_c, ls_b, le_c, le_b, ld_c, ld_b, st, n_l, div, lrows: Ghost(lrows) }
}


// ------------------------------------------------------------------------------------------- orders

/// The orders columns the kernel reads, with the date zone map and the o_orderkey key index.
pub struct OrdCols {
    pub ok_c: &'static [u32],
    pub ok_b: &'static [i64],
    pub oc_c: &'static [u32],
    pub oc_b: &'static [i64],
    pub od_c: &'static [u16],
    pub od_b: &'static [i64],
    pub od_z: &'static [i64],
    pub oi_c: &'static [u32],
    pub oi_b: &'static [u64],
    pub okind: u64,
    pub n_o: usize,
    pub div: Div,
    pub exact: bool,
    pub orows: Ghost<Seq<Row>>,
    pub omap: Ghost<Seq<int>>,
}

/// Stored orders row `p` is its canonical row and decodes to its columns (the kernel's `orow_ok`).
pub open spec fn ord_row_ok(c: OrdCols, rs: Rels, p: int) -> bool {
    let o = c.orows@[p];
    let bs = c.div.bs as int;
    &&& 0 <= c.omap@[p] < rs.o.len()
    &&& o == rs.o[c.omap@[p]]
    &&& o[0] == Val::Int(fv32(c.ok_c@, c.ok_b@, bs, p))
    &&& o[1] == Val::Int(fv32(c.oc_c@, c.oc_b@, bs, p))
    &&& o[4] == Val::Date(fv16(c.od_c@, c.od_b@, bs, p))
}

/// Canonical orders row `i` is some stored orders row.
pub open spec fn ord_cov(c: OrdCols, i: int) -> bool {
    exists|p: int| 0 <= p < c.n_o && #[trigger] c.omap@[p] == i
}

/// Every stored row's date lies between its block's base and zone maximum.
pub open spec fn ord_zone_ok(c: OrdCols, p: int) -> bool {
    let bs = c.div.bs as int;
    c.od_b@[p / bs] <= fv16(c.od_c@, c.od_b@, bs, p) <= c.od_z@[p / bs]
}

pub open spec fn ord_cols_ok(c: OrdCols, rs: Rels) -> bool {
    let bs = c.div.bs as int;
    &&& c.div.ok()
    &&& c.orows@.len() == c.n_o && c.omap@.len() == c.n_o && rs.o.len() == c.n_o
    &&& col32_ok(c.ok_c@, c.ok_b@, bs, c.n_o as int)
    &&& col32_ok(c.oc_c@, c.oc_b@, bs, c.n_o as int)
    &&& col16_ok(c.od_c@, c.od_b@, bs, c.n_o as int)
    &&& c.od_z@.len() == c.od_b@.len()
    &&& forall|p: int| 0 <= p < c.n_o ==> #[trigger] ord_row_ok(c, rs, p)
    &&& forall|p: int| 0 <= p < c.n_o ==> #[trigger] ord_zone_ok(c, p)
    &&& forall|i: int| 0 <= i < rs.o.len() ==> #[trigger] ord_cov(c, i)
    &&& c.exact ==> okx::keyidx_ok(c.ok_c@, c.ok_b@, c.oi_c@, c.oi_b@, bs, c.okind, c.n_o as int)
    &&& keys_unique(c.orows@)
}

/// The stored orders rows of the facts parts.
pub open spec fn orows_of(parts: Seq<PartView>, rs: Rels) -> Seq<Row> {
    fi::orders_rows(parts.subrange(fi::ORDERS_FIRST as int, (fi::ORDERS_FIRST + fi::OR_PARTS) as int), rs.o)
}

pub fn read_orders(fp: &mut StoredParts, rs: Ghost<Rels>) -> (c: OrdCols)
    requires
        lr::represents(old(fp)@, seq![rs@.l, rs@.o]),
        rels_shapes(rs@),
        keys_unique(rs@.o),
    ensures
        final(fp)@ == old(fp)@,
        ord_cols_ok(c, rs@),
        c.orows@ == orows_of(old(fp)@.subrange(0, 75), rs@),
{
    let ghost all = fp@;
    let ghost parts = all.subrange(0, 75);
    let ghost tp = parts.subrange(48, 74);
    let ghost orel = rs@.o;
    let ghost n = orel.len() as int;
    proof {
        assert(fi::represents(parts, seq![rs@.l, rs@.o]));
        assert(fi::orders_ok(tp, orel));
        assert(forall|i: int| 0 <= i < 26 ==> #[trigger] tp[i] == all[48 + i]);
    }
    let lay = whole_u64(fp, 48 + fi::OR_LAYOUT);
    let n_o = fp.part_len(48 + fi::OR_ORDERKEY_CODES);
    let bs = lay[1];
    let (div, exact) = div_for(bs, n_o);
    let ok_c = whole_u32(fp, 48 + fi::OR_ORDERKEY_CODES);
    let ok_b = whole_i64(fp, 48 + fi::OR_ORDERKEY_BASE);
    let oc_c = whole_u32(fp, 48 + fi::OR_CUSTKEY_CODES);
    let oc_b = whole_i64(fp, 48 + fi::OR_CUSTKEY_BASE);
    let od_c = whole_u16(fp, 48 + fi::OR_ORDERDATE_CODES);
    let od_b = whole_i64(fp, 48 + fi::OR_ORDERDATE_BASE);
    let od_z = whole_i64(fp, 48 + fi::OR_ORDERDATE_ZMAX);
    let oi_c = whole_u32(fp, 48 + fi::OR_KEYIDX_CODES);
    let oi_b = whole_u64(fp, 48 + fi::OR_KEYIDX_BASE);
    let kp = whole_u64(fp, 48 + fi::OR_KEYIDX_KIND);
    let okind = kp[0];
    let ghost orows = orows_of(parts, rs@);
    let ghost omap = fi::orders_map(tp, n);
    proof {
        assert(orows == fcf::stored_rows(orel, omap));
        assert(fcf::is_perm(omap, n));
        assert forall|j: int| 0 <= j < n implies {
            let o = #[trigger] orows[j];
            &&& o == orel[omap[j]] && 0 <= omap[j] < n
        } by {}
        assert forall|j: int| 0 <= j < orows.len() implies
            (#[trigger] orows[j][0]) is Int && i64::MIN <= orows[j][0]->Int_0 <= i64::MAX by {
            assert(orows[j] == orel[omap[j]]);
        }
        assert forall|j: int| 0 <= j < orows.len() implies
            (#[trigger] orows[j][1]) is Int && i64::MIN <= orows[j][1]->Int_0 <= i64::MAX by {
            assert(orows[j] == orel[omap[j]]);
        }
        assert forall|j: int| 0 <= j < orows.len() implies i64::MIN <= (#[trigger] orows[j][4])->Date_0 <= i64::MAX by {
            assert(orows[j] == orel[omap[j]]);
        }
        let b = bs as int;
        let b2 = div.bs as int;
        vf::lemma_int32(tp, 1, 4, 5, orows, 0, b);
        vf::lemma_int32(tp, 1, 6, 7, orows, 1, b);
        vf::lemma_date16(tp, 1, 14, 15, orows, 4, b);
        vf::lemma_zone16(tp, 1, 14, 15, 16, n, b);
        lemma_col32_rebase(ok_c@, ok_b@, b, b2, n);
        lemma_col32_rebase(oc_c@, oc_b@, b, b2, n);
        lemma_col16_rebase(od_c@, od_b@, b, b2, n);
        let c = OrdCols { ok_c, ok_b, oc_c, oc_b, od_c, od_b, od_z, oi_c, oi_b, okind, n_o, div, exact,
            orows: Ghost(orows), omap: Ghost(omap) };
        assert forall|p: int| 0 <= p < n_o implies #[trigger] ord_row_ok(c, rs@, p) by {
            assert(orows[p] == orel[omap[p]]);
            assert(orows[p][0] == Val::Int(fv32(ok_c@, ok_b@, b, p)));
            assert(orows[p][1] == Val::Int(fv32(oc_c@, oc_b@, b, p)));
            assert(orows[p][4] == Val::Date(fv16(od_c@, od_b@, b, p)));
        }
        assert forall|p: int| 0 <= p < n_o implies #[trigger] ord_zone_ok(c, p) by {
            assert(p / b2 == p / b);
            assert(fv16(od_c@, od_b@, b2, p) == fv16(od_c@, od_b@, b, p));
        }
        assert forall|i: int| 0 <= i < orel.len() implies #[trigger] ord_cov(c, i) by {
            assert(fcf::covered(omap, i));
            let w = choose|j: int| 0 <= j < omap.len() && omap[j] == i;
            assert(0 <= w < n_o && c.omap@[w] == i);
        }
        assert forall|i: int, j: int| 0 <= i < orows.len() && 0 <= j < orows.len() && #[trigger] orows[i][0] == #[trigger] orows[j][0]
            implies i == j by {
            assert(orows[i] == orel[omap[i]]);
            assert(orows[j] == orel[omap[j]]);
            assert(orel[omap[i]][0] == orel[omap[j]][0]);
            assert(omap[i] == omap[j]);
        }
    }
    OrdCols { ok_c, ok_b, oc_c, oc_b, od_c, od_b, od_z, oi_c, oi_b, okind, n_o, div, exact,
        orows: Ghost(orows), omap: Ghost(omap) }
}

/// The co-clustering flag: when set, the stored lineitem rows follow their stored orders.
pub fn read_cluster(fp: &mut StoredParts, rs: Ghost<Rels>) -> (b: bool)
    requires lr::represents(old(fp)@, seq![rs@.l, rs@.o]),
    ensures
        final(fp)@ == old(fp)@,
        b ==> crate::stores::facts::interface::cluster::clustered(
            lrows_of(old(fp)@.subrange(0, 75), rs@), orows_of(old(fp)@.subrange(0, 75), rs@)),
{
    let ghost parts = fp@.subrange(0, 75);
    proof {
        assert(fi::represents(parts, seq![rs@.l, rs@.o]));
        assert(parts[fi::FACTS_CLUSTER as int] == fp@[fi::FACTS_CLUSTER as int]);
    }
    let f = whole_u64(fp, fi::FACTS_CLUSTER);
    f[0] == 1
}

// ------------------------------------------------------------------------------------------- customer

/// The customer columns the kernel reads.
pub struct CustCols {
    pub ck_c: &'static [u32],
    pub ck_b: &'static [i64],
    pub ckind: u64,
    pub cn_c: &'static [u8],
    pub cn_b: &'static [i64],
    pub n_c: usize,
    pub div: Div,
    pub exact: bool,
    pub e32: &'static [u32],
    pub e64: &'static [u64],
}

/// Customer row `c` decodes to its key and nation key.
pub open spec fn cust_row_ok(c: CustCols, rs: Rels, i: int) -> bool {
    let bs = c.div.bs as int;
    &&& rs.c[i][0] == Val::Int(fv32(c.ck_c@, c.ck_b@, bs, i))
    &&& rs.c[i][3] == Val::Int(fv8(c.cn_c@, c.cn_b@, bs, i))
}

pub open spec fn cust_cols_ok(c: CustCols, rs: Rels) -> bool {
    let bs = c.div.bs as int;
    &&& c.div.ok()
    &&& rs.c.len() == c.n_c
    &&& col32_ok(c.ck_c@, c.ck_b@, bs, c.n_c as int)
    &&& col8_ok(c.cn_c@, c.cn_b@, bs, c.n_c as int)
    &&& forall|i: int| 0 <= i < c.n_c ==> #[trigger] cust_row_ok(c, rs, i)
    &&& c.exact ==> ckx::keyidx_ok(c.ck_c@, c.ck_b@, c.e32@, c.e64@, bs, c.ckind, c.n_c as int)
    &&& c.e32@ == Seq::<u32>::empty() && c.e64@ == Seq::<u64>::empty()
}

pub fn read_customers(cp: &mut StoredParts, rs: Ghost<Rels>, part: Ghost<Seq<Row>>) -> (c: CustCols)
    requires
        ci::represents(old(cp)@, seq![rs@.c, part@]),
        rels_shapes(rs@),
    ensures
        final(cp)@ == old(cp)@,
        cust_cols_ok(c, rs@),
{
    let ghost parts = cp@;
    let ghost tp = parts.subrange(0, 21);
    let ghost crel = rs@.c;
    let ghost n = crel.len() as int;
    proof {
        assert(ci::customer_ok(tp, crel));
        assert(forall|i: int| 0 <= i < 21 ==> #[trigger] tp[i] == parts[i]);
    }
    let lay = whole_u64(cp, ci::CU_LAYOUT);
    let n_c = cp.part_len(ci::CU_CUSTKEY_CODES);
    let bs = lay[1];
    let (div, exact) = div_for(bs, n_c);
    let ck_c = whole_u32(cp, ci::CU_CUSTKEY_CODES);
    let ck_b = whole_i64(cp, ci::CU_CUSTKEY_BASE);
    let cn_c = whole_u8(cp, ci::CU_NATIONKEY_CODES);
    let cn_b = whole_i64(cp, ci::CU_NATIONKEY_BASE);
    let kp = whole_u64(cp, ci::CU_KEYIDX_KIND);
    let ckind = kp[0];
    let e32 = cp.extent_u32(ci::CU_CUSTKEY_CODES, 0, 0);
    let e64 = cp.extent_u64(ci::CU_LAYOUT, 0, 0);
    proof {
        assert(e32@ =~= Seq::<u32>::empty());
        assert(e64@ =~= Seq::<u64>::empty());
        assert forall|j: int| 0 <= j < crel.len() implies
            (#[trigger] crel[j][0]) is Int && i64::MIN <= crel[j][0]->Int_0 <= i64::MAX by {}
        assert forall|j: int| 0 <= j < crel.len() implies
            (#[trigger] crel[j][3]) is Int && i64::MIN <= crel[j][3]->Int_0 <= i64::MAX by {}
        let b = bs as int;
        let b2 = div.bs as int;
        vc::lemma_int32(tp, 1, 2, 3, crel, 0, b);
        vc::lemma_int8(tp, 1, 8, 9, crel, 3, b);
        lemma_col32_rebase(ck_c@, ck_b@, b, b2, n);
        lemma_col8_rebase(cn_c@, cn_b@, b, b2, n);
        let c = CustCols { ck_c, ck_b, ckind, cn_c, cn_b, n_c, div, exact, e32, e64 };
        assert forall|i: int| 0 <= i < n_c implies #[trigger] cust_row_ok(c, rs@, i) by {
            assert(crel[i][0] == Val::Int(fv32(ck_c@, ck_b@, b, i)));
            assert(crel[i][3] == Val::Int(fv8(cn_c@, cn_b@, b, i)));
        }
    }
    CustCols { ck_c, ck_b, ckind, cn_c, cn_b, n_c, div, exact, e32, e64 }
}

// ------------------------------------------------------------------------------------------- supplier

/// The supplier columns the kernel reads.
pub struct SuppCols {
    pub sk_c: &'static [u32],
    pub sk_b: &'static [i64],
    pub skind: u64,
    pub sn_c: &'static [u8],
    pub sn_b: &'static [i64],
    pub n_s: usize,
    pub div: Div,
    pub exact: bool,
}

/// Supplier row `s` decodes to its key and nation key.
pub open spec fn supp_row_ok(c: SuppCols, rs: Rels, i: int) -> bool {
    let bs = c.div.bs as int;
    &&& rs.s[i][0] == Val::Int(fv32(c.sk_c@, c.sk_b@, bs, i))
    &&& rs.s[i][3] == Val::Int(fv8(c.sn_c@, c.sn_b@, bs, i))
}

pub open spec fn supp_cols_ok(c: SuppCols, rs: Rels, e32: Seq<u32>, e64: Seq<u64>) -> bool {
    let bs = c.div.bs as int;
    &&& c.div.ok()
    &&& rs.s.len() == c.n_s
    &&& col32_ok(c.sk_c@, c.sk_b@, bs, c.n_s as int)
    &&& col8_ok(c.sn_c@, c.sn_b@, bs, c.n_s as int)
    &&& forall|i: int| 0 <= i < c.n_s ==> #[trigger] supp_row_ok(c, rs, i)
    &&& c.exact ==> skx::keyidx_ok(c.sk_c@, c.sk_b@, e32, e64, bs, c.skind, c.n_s as int)
}

pub fn read_suppliers(sp: &mut StoredParts, rs: Ghost<Rels>, psupp: Ghost<Seq<Row>>) -> (c: SuppCols)
    requires
        si::represents(old(sp)@, seq![psupp@, rs@.s, rs@.n, rs@.r]),
        rels_shapes(rs@),
    ensures
        final(sp)@ == old(sp)@,
        supp_cols_ok(c, rs@, Seq::<u32>::empty(), Seq::<u64>::empty()),
{
    let ghost parts = sp@;
    let ghost tp = parts.subrange(13, 30);
    let ghost srel = rs@.s;
    let ghost n = srel.len() as int;
    proof {
        assert(si::supplier_ok(tp, srel));
        assert(forall|i: int| 0 <= i < 17 ==> #[trigger] tp[i] == parts[13 + i]);
    }
    let lay = whole_u64(sp, 13 + si::SU_LAYOUT);
    let n_s = sp.part_len(13 + si::SU_SUPPKEY_CODES);
    let bs = lay[1];
    let (div, exact) = div_for(bs, n_s);
    let sk_c = whole_u32(sp, 13 + si::SU_SUPPKEY_CODES);
    let sk_b = whole_i64(sp, 13 + si::SU_SUPPKEY_BASE);
    let sn_c = whole_u8(sp, 13 + si::SU_NATIONKEY_CODES);
    let sn_b = whole_i64(sp, 13 + si::SU_NATIONKEY_BASE);
    let kp = whole_u64(sp, 13 + si::SU_KEYIDX_KIND);
    let skind = kp[0];
    proof {
        assert forall|j: int| 0 <= j < srel.len() implies
            (#[trigger] srel[j][0]) is Int && i64::MIN <= srel[j][0]->Int_0 <= i64::MAX by {}
        assert forall|j: int| 0 <= j < srel.len() implies
            (#[trigger] srel[j][3]) is Int && i64::MIN <= srel[j][3]->Int_0 <= i64::MAX by {}
        let b = bs as int;
        let b2 = div.bs as int;
        vs::lemma_int32(tp, 1, 2, 3, srel, 0, b);
        vs::lemma_int8(tp, 1, 8, 9, srel, 3, b);
        lemma_col32_rebase(sk_c@, sk_b@, b, b2, n);
        lemma_col8_rebase(sn_c@, sn_b@, b, b2, n);
        let c = SuppCols { sk_c, sk_b, skind, sn_c, sn_b, n_s, div, exact };
        assert forall|i: int| 0 <= i < n_s implies #[trigger] supp_row_ok(c, rs@, i) by {
            assert(srel[i][0] == Val::Int(fv32(sk_c@, sk_b@, b, i)));
            assert(srel[i][3] == Val::Int(fv8(sn_c@, sn_b@, b, i)));
        }
    }
    SuppCols { sk_c, sk_b, skind, sn_c, sn_b, n_s, div, exact }
}

} // verus!
