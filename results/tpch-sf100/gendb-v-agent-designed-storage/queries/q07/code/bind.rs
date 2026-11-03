//! Binding of the scan model (`super::model::Cols`) to the three storages: when the model's slices are whole parts
//! (`cols_from_parts`) and the parts represent a database's stored relations, the model's decoded columns are the
//! values of the database's table rows (lineitem and orders through their row maps, supplier and customer in
//! canonical order: `li_link`, `ord_link`, `sup_link`, `cus_link`), and the model's facts hold (`cols_ok`,
//! `keys_ok` from the primary keys, `groups_ok`).
//!
//! The model may use a smaller group size than the stored one when the stored block exceeds the table
//! (`bs_ok`): every row then lies in group 0 under both.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::stored::part_len;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::spec::constraints::*;
use crate::gendb_constraints::declared_db;
use crate::link::query::{proj, proj_all};
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::interface::common::keyidx::{keyidx_ok, fkey, sorted_at, irow, fidx, idx_map, lemma_irow_bound};
use crate::stores::facts::interface::common::read::lemma_for_row;
use crate::stores::suppliers::interface::{SUPPLIER_FIRST, SU_PARTS, SU_LAYOUT, SU_GROUPS, SU_SUPPKEY_CODES, SU_SUPPKEY_BASE,
    SU_NATIONKEY_CODES, SU_NATIONKEY_BASE, SU_KEYIDX_KIND, supplier_ok};
use crate::stores::custpart::interface::{CUSTOMER_FIRST, CU_PARTS, CU_LAYOUT, CU_GROUPS, CU_CUSTKEY_CODES, CU_CUSTKEY_BASE,
    CU_NATIONKEY_CODES, CU_NATIONKEY_BASE, CU_KEYIDX_KIND, customer_ok};
use crate::stores::suppliers::interface::common::colfmt as scf;
use crate::stores::suppliers::interface::common::keyidx as skx;
use crate::stores::custpart::interface::common::colfmt as ccf;
use crate::stores::custpart::interface::common::keyidx as ckx;
use super::common::keysum::*;
use super::model::*;
use super::reduce::*;
use super::body::*;
use super::kernel::groups_ok;

verus! {

pub open spec fn u16s(p: PartView) -> Seq<u16> {
    match p {
        PartView::U16(s) => s,
        _ => Seq::empty(),
    }
}

/// The model's group size `b` decodes like the stored group size `sb` on rows below `n`: equal, or both at least
/// `n` (every row then lies in group 0).
pub open spec fn bs_ok(b: int, sb: int, n: int) -> bool {
    b >= 1 && (b == sb || (b >= n && sb >= n))
}

/// Within uniform groups, a model group size `b` (`bs_ok`) finds the same group as the stored one.
pub proof fn lemma_bs_group(b: int, sb: int, n: int, j: int)
    requires bs_ok(b, sb, n), sb >= 1, 0 <= j < n,
    ensures j / b == j / sb,
{
    if b != sb {
        vstd::arithmetic::div_mod::lemma_basic_div(j, b);
        vstd::arithmetic::div_mod::lemma_basic_div(j, sb);
    }
}

// ------------------------------------------------------------------------------------------------ part positions

/// Facts' parts as storage `li_okruns` keeps them (its first 75 parts).
pub open spec fn fpv(sv: StoresView) -> Seq<PartView> {
    sv.li_okruns.subrange(0, FACTS_PARTS as int)
}

pub open spec fn ltp(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int)
}

pub open spec fn otp(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(ORDERS_FIRST as int, (ORDERS_FIRST + OR_PARTS) as int)
}

pub open spec fn stp(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(SUPPLIER_FIRST as int, (SUPPLIER_FIRST + SU_PARTS) as int)
}

pub open spec fn ctp(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(CUSTOMER_FIRST as int, (CUSTOMER_FIRST + CU_PARTS) as int)
}

/// The stored lineitem and orders relations of `db` (storage `facts`).
pub open spec fn lrel(db: Database) -> Seq<Row> { crate::stores::facts::declaration::stored_relations(db)[0] }
pub open spec fn orel(db: Database) -> Seq<Row> { crate::stores::facts::declaration::stored_relations(db)[1] }
/// The stored supplier relation (storage `suppliers`) and customer relation (storage `custpart`).
pub open spec fn srel(db: Database) -> Seq<Row> { crate::stores::suppliers::declaration::stored_relations(db)[1] }
pub open spec fn crel(db: Database) -> Seq<Row> { crate::stores::custpart::declaration::stored_relations(db)[0] }

/// The row maps of lineitem and orders (stored row -> canonical row).
pub open spec fn lmap(parts: Seq<PartView>, n: int) -> Seq<int> { lineitem_map(ltp(parts), n) }
pub open spec fn omap(parts: Seq<PartView>, n: int) -> Seq<int> { orders_map(otp(parts), n) }

/// The lineitem slices are whole parts of storage `facts`.
pub open spec fn li_from_parts(c: Cols, p: Seq<PartView>) -> bool {
    let t = ltp(p);
    &&& p.len() == FACTS_PARTS
    &&& t[LI_LAYOUT as int] is U64 && u64s(t[LI_LAYOUT as int]).len() == 2
    &&& c.n_l as int == u64s(t[LI_LAYOUT as int])[0]
    &&& bs_ok(c.bs_l as int, u64s(t[LI_LAYOUT as int])[1] as int, c.n_l as int)
    &&& t[LI_SHIPDATE_CODES as int] == PartView::U16(c.ls_codes@)
    &&& t[LI_SHIPDATE_BASE as int] == PartView::I64(c.ls_bases@)
    &&& t[LI_SHIPDATE_ZMAX as int] == PartView::I64(c.ls_zmax@)
    &&& t[LI_SUPPKEY_CODES as int] == PartView::U32(c.lsk_codes@)
    &&& t[LI_SUPPKEY_BASE as int] == PartView::I64(c.lsk_bases@)
    &&& t[LI_LINENUMBER_CODES as int] == PartView::U8(c.lln_codes@)
    &&& t[LI_LINENUMBER_BASE as int] == PartView::I64(c.lln_bases@)
    &&& t[LI_ORDERKEY_CODES as int] == PartView::U32(c.lok_codes@)
    &&& t[LI_ORDERKEY_BASE as int] == PartView::I64(c.lok_bases@)
    &&& t[LI_EXTENDEDPRICE_CODES as int] == PartView::U32(c.lp_codes@)
    &&& t[LI_EXTENDEDPRICE_BASE as int] == PartView::I64(c.lp_bases@)
    &&& t[LI_DISCOUNT_CODES as int] == PartView::U8(c.ld_codes@)
    &&& t[LI_DISCOUNT_BASE as int] == PartView::I64(c.ld_bases@)
}

/// The orders slices are whole parts of storage `facts`.
pub open spec fn ord_from_parts(c: Cols, p: Seq<PartView>) -> bool {
    let t = otp(p);
    &&& p.len() == FACTS_PARTS
    &&& t[OR_LAYOUT as int] is U64 && u64s(t[OR_LAYOUT as int]).len() == 2
    &&& c.n_o as int == u64s(t[OR_LAYOUT as int])[0]
    &&& bs_ok(c.bs_o as int, u64s(t[OR_LAYOUT as int])[1] as int, c.n_o as int)
    &&& t[OR_ORDERKEY_CODES as int] == PartView::U32(c.ok_codes@)
    &&& t[OR_ORDERKEY_BASE as int] == PartView::I64(c.ok_bases@)
    &&& t[OR_KEYIDX_CODES as int] == PartView::U32(c.oi_codes@)
    &&& t[OR_KEYIDX_BASE as int] == PartView::U64(c.oi_bases@)
    &&& t[OR_KEYIDX_KIND as int] is U64 && u64s(t[OR_KEYIDX_KIND as int]).len() == 1
    &&& u64s(t[OR_KEYIDX_KIND as int])[0] == c.oi_kind
    &&& t[OR_CUSTKEY_CODES as int] == PartView::U32(c.oc_codes@)
    &&& t[OR_CUSTKEY_BASE as int] == PartView::I64(c.oc_bases@)
}

/// The supplier slices are whole parts of storage `suppliers`.
pub open spec fn sup_from_parts(c: Cols, p: Seq<PartView>) -> bool {
    let t = stp(p);
    &&& p.len() == crate::stores::suppliers::interface::SUPPLIERS_PARTS
    &&& t[SU_LAYOUT as int] is U64 && u64s(t[SU_LAYOUT as int]).len() == 2
    &&& c.n_s as int == u64s(t[SU_LAYOUT as int])[0]
    &&& bs_ok(c.bs_s as int, u64s(t[SU_LAYOUT as int])[1] as int, c.n_s as int)
    &&& t[SU_SUPPKEY_CODES as int] == PartView::U32(c.sk_codes@)
    &&& t[SU_SUPPKEY_BASE as int] == PartView::I64(c.sk_bases@)
    &&& t[SU_NATIONKEY_CODES as int] == PartView::U8(c.sn_codes@)
    &&& t[SU_NATIONKEY_BASE as int] == PartView::I64(c.sn_bases@)
    &&& t[SU_KEYIDX_KIND as int] is U64 && u64s(t[SU_KEYIDX_KIND as int]).len() == 1
    &&& u64s(t[SU_KEYIDX_KIND as int])[0] == c.s_kind
}

/// The customer slices are whole parts of storage `custpart`.
pub open spec fn cus_from_parts(c: Cols, p: Seq<PartView>) -> bool {
    let t = ctp(p);
    &&& p.len() == crate::stores::custpart::interface::CUSTPART_PARTS
    &&& t[CU_LAYOUT as int] is U64 && u64s(t[CU_LAYOUT as int]).len() == 2
    &&& c.n_c as int == u64s(t[CU_LAYOUT as int])[0]
    &&& bs_ok(c.bs_c as int, u64s(t[CU_LAYOUT as int])[1] as int, c.n_c as int)
    &&& t[CU_CUSTKEY_CODES as int] == PartView::U32(c.ck_codes@)
    &&& t[CU_CUSTKEY_BASE as int] == PartView::I64(c.ck_bases@)
    &&& t[CU_NATIONKEY_CODES as int] == PartView::U8(c.cn_codes@)
    &&& t[CU_NATIONKEY_BASE as int] == PartView::I64(c.cn_bases@)
    &&& t[CU_KEYIDX_KIND as int] is U64 && u64s(t[CU_KEYIDX_KIND as int]).len() == 1
    &&& u64s(t[CU_KEYIDX_KIND as int])[0] == c.c_kind
}

/// The model's slices are whole parts of the three storages.
pub open spec fn cols_from_parts(c: Cols, sv: StoresView) -> bool {
    &&& li_from_parts(c, fpv(sv))
    &&& ord_from_parts(c, fpv(sv))
    &&& sup_from_parts(c, sv.suppliers)
    &&& cus_from_parts(c, sv.custpart)
    &&& c.no_codes@ == Seq::<u32>::empty()
    &&& c.no_bases@ == Seq::<u64>::empty()
}

// ------------------------------------------------------------------------------------------------ links to the tables

/// The decoded lineitem columns are the values of lineitem table rows, stored row `j` being canonical row
/// `lmap[j]` (a bijection).
pub open spec fn li_link(c: Cols, db: Database, m: Seq<int>) -> bool {
    &&& c.n_l == db.tables[0].len()
    &&& is_perm(m, c.n_l as int)
    &&& forall|j: int| 0 <= j < c.n_l ==> {
        &&& (#[trigger] db.tables[0][m[j]])[0] == Val::Int(lkey(c, j))
        &&& db.tables[0][m[j]][2] == Val::Int(lsupp(c, j))
        &&& db.tables[0][m[j]][5] == (Val::Num { coeff: lprice(c, j), scale: 2 })
        &&& db.tables[0][m[j]][6] == (Val::Num { coeff: ldisc(c, j), scale: 2 })
        &&& db.tables[0][m[j]][10] == Val::Date(lship(c, j))
    }
}

/// The decoded orders columns are the values of orders table rows, stored row `p` being canonical row `omap[p]`.
pub open spec fn ord_link(c: Cols, db: Database, m: Seq<int>) -> bool {
    &&& c.n_o == db.tables[1].len()
    &&& is_perm(m, c.n_o as int)
    &&& forall|p: int| 0 <= p < c.n_o ==> {
        &&& (#[trigger] db.tables[1][m[p]])[0] == Val::Int(okey(c, p))
        &&& db.tables[1][m[p]][1] == Val::Int(ocust(c, p))
    }
}

/// The decoded supplier columns are the values of supplier table rows (canonical order).
pub open spec fn sup_link(c: Cols, db: Database) -> bool {
    &&& c.n_s == db.tables[5].len()
    &&& forall|r: int| 0 <= r < c.n_s ==> {
        &&& (#[trigger] db.tables[5][r])[0] == Val::Int(skey(c, r))
        &&& db.tables[5][r][3] == Val::Int(snat(c, r))
    }
}

/// The decoded customer columns are the values of customer table rows (canonical order).
pub open spec fn cus_link(c: Cols, db: Database) -> bool {
    &&& c.n_c == db.tables[2].len()
    &&& forall|r: int| 0 <= r < c.n_c ==> {
        &&& (#[trigger] db.tables[2][r])[0] == Val::Int(ckey(c, r))
        &&& db.tables[2][r][3] == Val::Int(cnat(c, r))
    }
}

// ------------------------------------------------------------------------------------------------ helpers

/// `proj` of a row on columns `cols`: position `k` is the row's column `cols[k]`.
pub proof fn lemma_proj_at(rows: Seq<Row>, cols: Seq<nat>, i: int, k: int)
    requires 0 <= i < rows.len(), 0 <= k < cols.len(),
    ensures proj_all(rows, cols)[i][k] == rows[i][cols[k] as int], proj_all(rows, cols).len() == rows.len(),
{
}

/// A model group size satisfying `bs_ok` gives as many group bases as rows need.
pub proof fn lemma_bases_cover(nb: int, b: int, sb: int, n: int)
    requires
        bs_ok(b, sb, n), n >= 0, sb >= 1,
        nb == nblocks_of(n, sb),
    ensures
        nb * b >= n,
        nb * b < n + b,
{
    lemma_nblocks(n, sb);
    if nb > 0 {
        assert(nb * sb == (nb - 1) * sb + sb) by (nonlinear_arith);
    } else {
        assert(nb * b == 0) by (nonlinear_arith) requires nb == 0;
    }
    if b == sb {
    } else {
        if n > 0 {
            assert(nb >= 1) by (nonlinear_arith) requires nb * sb >= n, n > 0, sb >= 1, nb >= 0;
            assert(nb <= 1) by (nonlinear_arith) requires (nb - 1) * sb < n, n <= sb, nb >= 1, sb >= 1;
            assert(nb * b == b) by (nonlinear_arith) requires nb == 1;
        } else {
            assert(nb == 0);
        }
    }
}

/// A key index stays valid under a model group size that finds the same groups (`bs_ok`, sizes >= `n`).
pub proof fn lemma_keyidx_bs(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, sb: int, b: int, kind: u64, n: int)
    requires
        keyidx_ok(kc, kb, ic, ib, sb, kind, n),
        bs_ok(b, sb, n), sb >= 1,
        kb.len() * b >= n,
    ensures
        keyidx_ok(kc, kb, ic, ib, b, kind, n),
{
    if b != sb {
        assert forall|r: int| 0 <= r < n implies #[trigger] fidx(ic, ib, b, r) == fidx(ic, ib, sb, r) by {
            vstd::arithmetic::div_mod::lemma_basic_div(r, b);
            vstd::arithmetic::div_mod::lemma_basic_div(r, sb);
        }
        assert forall|r: int| 0 <= r < n implies #[trigger] fkey(kc, kb, b, r) == fkey(kc, kb, sb, r) by {
            vstd::arithmetic::div_mod::lemma_basic_div(r, b);
            vstd::arithmetic::div_mod::lemma_basic_div(r, sb);
        }
        if kind == 2 {
            assert(idx_map(ic, ib, b, n) =~= idx_map(ic, ib, sb, n));
            if n > 0 {
                assert(ib.len() >= 1) by (nonlinear_arith) requires ib.len() * sb >= n, n > 0, sb >= 1;
                assert(ib.len() * b >= b) by (nonlinear_arith) requires ib.len() >= 1, b >= 1;
            }
        }
        if kind >= 1 {
            assert forall|r: int| 0 <= r < n - 1 implies #[trigger] sorted_at(kc, kb, ic, ib, b, kind, r) by {
                assert(sorted_at(kc, kb, ic, ib, sb, kind, r));
                lemma_irow_bound(kc, kb, ic, ib, sb, kind, n, r);
                lemma_irow_bound(kc, kb, ic, ib, sb, kind, n, r + 1);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ decoding

/// Row `j` of a FOR column over uniform groups, under a model group size `b` (`bs_ok`).
pub proof fn lemma_for_col(gp: PartView, n: int, sb: int, b: int, base: PartView, codes: PartView, j: int)
    requires groups_part_ok(gp, n, sb), bs_ok(b, sb, n), 0 <= j < n,
    ensures
        for_at(u64s(gp), base, codes, j) == base_at(base, j / b) + code_at(codes, j),
        in_group(u64s(gp), j / sb, j),
        j / b == j / sb,
{
    lemma_for_row(gp, n, sb, base, codes, j);
    lemma_bs_group(b, sb, n, j);
}

/// Values of the lineitem table's typed columns.
pub open spec fn li_vals(r: Row) -> bool {
    &&& r.len() == 16
    &&& r[0] is Int && in_i64(r[0]->Int_0)
    &&& r[2] is Int && in_i64(r[2]->Int_0)
    &&& r[5] is Num && small15(r[5]->Num_coeff)
    &&& r[6] is Num && small15(r[6]->Num_coeff)
    &&& r[10] is Date && in_i64(r[10]->Date_0)
}

proof fn lemma_li_vals(db: Database)
    requires db.schema == crate::schema::schema_spec(), db_wf(db),
    ensures forall|i: int| 0 <= i < db.tables[0].len() ==> li_vals(#[trigger] db.tables[0][i]),
{
    lemma_tables_typed(db);
    assert(crate::spec::numeric::pow10(15) == 1_000_000_000_000_000) by (compute);
    let s = crate::schema::schema_spec();
    assert forall|i: int| 0 <= i < db.tables[0].len() implies li_vals(#[trigger] db.tables[0][i]) by {
        let r = db.tables[0][i];
        assert(li_typed(t_li(db)[i]));
        assert(row_in_table(r, db.schema[0]));
        assert(crate::spec::typing::value_in_column(r[0], s[0].columns[0]));
        assert(crate::spec::typing::value_in_column(r[2], s[0].columns[2]));
        assert(crate::spec::typing::value_in_column(r[5], s[0].columns[5]));
        assert(crate::spec::typing::value_in_column(r[6], s[0].columns[6]));
        assert(crate::spec::typing::value_in_column(r[10], s[0].columns[10]));
        assert(s[0].columns[0] == (crate::spec::types::Column { ty: crate::spec::types::SqlType::Int8, nullable: false })) by (compute);
        assert(s[0].columns[2] == (crate::spec::types::Column { ty: crate::spec::types::SqlType::Int8, nullable: false })) by (compute);
        assert(s[0].columns[5] == (crate::spec::types::Column { ty: crate::spec::types::SqlType::Numeric { precision: 15, scale: 2 }, nullable: false })) by (compute);
        assert(s[0].columns[6] == (crate::spec::types::Column { ty: crate::spec::types::SqlType::Numeric { precision: 15, scale: 2 }, nullable: false })) by (compute);
        assert(s[0].columns[10] == (crate::spec::types::Column { ty: crate::spec::types::SqlType::Date, nullable: false })) by (compute);
    }
}

/// The column predicates of the lineitem parts the scan reads.
pub open spec fn li_core(db: Database, p: Seq<PartView>, c: Cols) -> bool {
    let t = ltp(p);
    let rel = lrel(db);
    let n = rel.len() as int;
    let sb = u64s(t[LI_LAYOUT as int])[1] as int;
    let gp = t[LI_GROUPS as int];
    let gs = u64s(gp);
    let m = lineitem_map(t, n);
    let rows = lineitem_rows(t, rel);
    &&& n == db.tables[0].len()
    &&& n == c.n_l
    &&& sb >= 1
    &&& groups_part_ok(gp, n, sb)
    &&& is_perm(m, n)
    &&& rows == stored_rows(rel, m)
    &&& rel == proj_all(db.tables[0], crate::stores::facts::declaration::stored_cols_t0())
    &&& for_shape(gs, t[LI_SHIPDATE_BASE as int], t[LI_SHIPDATE_CODES as int], n)
    &&& int_col(rows, 0, gs, t[LI_ORDERKEY_BASE as int], t[LI_ORDERKEY_CODES as int])
    &&& int_col(rows, 2, gs, t[LI_SUPPKEY_BASE as int], t[LI_SUPPKEY_CODES as int])
    &&& num_col(rows, 5, 2, gs, t[LI_EXTENDEDPRICE_BASE as int], t[LI_EXTENDEDPRICE_CODES as int])
    &&& num_col(rows, 6, 2, gs, t[LI_DISCOUNT_BASE as int], t[LI_DISCOUNT_CODES as int])
    &&& date_col(rows, 10, gs, t[LI_SHIPDATE_BASE as int], t[LI_SHIPDATE_CODES as int])
    &&& zone_max_ok(gs, t[LI_SHIPDATE_BASE as int], t[LI_SHIPDATE_CODES as int], i64s(t[LI_SHIPDATE_ZMAX as int]))
    &&& part_len(t[LI_SUPPKEY_CODES as int]) == n && part_len(t[LI_LINENUMBER_CODES as int]) == n
    &&& part_len(t[LI_ORDERKEY_CODES as int]) == n && part_len(t[LI_EXTENDEDPRICE_CODES as int]) == n
    &&& part_len(t[LI_DISCOUNT_CODES as int]) == n
    &&& part_len(t[LI_SUPPKEY_BASE as int]) == gs.len() - 1 && part_len(t[LI_LINENUMBER_BASE as int]) == gs.len() - 1
    &&& part_len(t[LI_ORDERKEY_BASE as int]) == gs.len() - 1 && part_len(t[LI_EXTENDEDPRICE_BASE as int]) == gs.len() - 1
    &&& part_len(t[LI_DISCOUNT_BASE as int]) == gs.len() - 1
    &&& i64s(t[LI_SHIPDATE_ZMAX as int]).len() == gs.len() - 1
}

pub proof fn lemma_li_core(db: Database, p: Seq<PartView>, c: Cols)
    requires
        db.schema == crate::schema::schema_spec(), db_wf(db),
        represents(p, crate::stores::facts::declaration::stored_relations(db)),
        li_from_parts(c, p),
    ensures li_core(db, p, c),
{
    let t = ltp(p);
    let rel = lrel(db);
    crate::stores::facts::declaration::lemma_stored_relations(db);
    assert(lineitem_ok(t, rel));
    let rows = lineitem_rows(t, rel);
    assert(lineitem_cols_ok(t, rows));
    lemma_proj_all_len(db.tables[0], crate::stores::facts::declaration::stored_cols_t0());
}

pub proof fn lemma_proj_all_len(rows: Seq<Row>, cols: Seq<nat>)
    ensures proj_all(rows, cols).len() == rows.len(),
{
}

/// One lineitem row's values through the row map.
proof fn lemma_li_row(db: Database, p: Seq<PartView>, c: Cols, j: int)
    requires li_core(db, p, c), li_from_parts(c, p), 0 <= j < c.n_l,
    ensures ({
        let m = lmap(p, c.n_l as int);
        &&& 0 <= m[j] < c.n_l
        &&& db.tables[0][m[j]][0] == Val::Int(lkey(c, j))
        &&& db.tables[0][m[j]][2] == Val::Int(lsupp(c, j))
        &&& db.tables[0][m[j]][5] == (Val::Num { coeff: lprice(c, j), scale: 2 })
        &&& db.tables[0][m[j]][6] == (Val::Num { coeff: ldisc(c, j), scale: 2 })
        &&& db.tables[0][m[j]][10] == Val::Date(lship(c, j))
        &&& lship(c, j) <= c.ls_zmax@[j / c.bs_l as int]
    }),
{
    let t = ltp(p);
    let rel = lrel(db);
    let n = c.n_l as int;
    let sb = u64s(t[LI_LAYOUT as int])[1] as int;
    let b = c.bs_l as int;
    let gp = t[LI_GROUPS as int];
    let gs = u64s(gp);
    let m = lineitem_map(t, n);
    let rows = lineitem_rows(t, rel);
    let cols = crate::stores::facts::declaration::stored_cols_t0();
    assert(cols[0] == 0 && cols[2] == 2 && cols[5] == 5 && cols[6] == 6 && cols[10] == 10 && cols.len() == 15);
    assert(0 <= m[j] < n);
    assert(rows[j] == rel[m[j]]);
    lemma_proj_at(db.tables[0], cols, m[j], 0);
    lemma_proj_at(db.tables[0], cols, m[j], 2);
    lemma_proj_at(db.tables[0], cols, m[j], 5);
    lemma_proj_at(db.tables[0], cols, m[j], 6);
    lemma_proj_at(db.tables[0], cols, m[j], 10);
    lemma_for_col(gp, n, sb, b, t[LI_ORDERKEY_BASE as int], t[LI_ORDERKEY_CODES as int], j);
    lemma_for_col(gp, n, sb, b, t[LI_SUPPKEY_BASE as int], t[LI_SUPPKEY_CODES as int], j);
    lemma_for_col(gp, n, sb, b, t[LI_EXTENDEDPRICE_BASE as int], t[LI_EXTENDEDPRICE_CODES as int], j);
    lemma_for_col(gp, n, sb, b, t[LI_DISCOUNT_BASE as int], t[LI_DISCOUNT_CODES as int], j);
    lemma_for_col(gp, n, sb, b, t[LI_SHIPDATE_BASE as int], t[LI_SHIPDATE_CODES as int], j);
    assert(rows[j][0] == Val::Int(for_at(gs, t[LI_ORDERKEY_BASE as int], t[LI_ORDERKEY_CODES as int], j)));
    assert(rows[j][2] == Val::Int(for_at(gs, t[LI_SUPPKEY_BASE as int], t[LI_SUPPKEY_CODES as int], j)));
    assert(rows[j][5] == (Val::Num { coeff: for_at(gs, t[LI_EXTENDEDPRICE_BASE as int], t[LI_EXTENDEDPRICE_CODES as int], j), scale: 2 }));
    assert(rows[j][6] == (Val::Num { coeff: for_at(gs, t[LI_DISCOUNT_BASE as int], t[LI_DISCOUNT_CODES as int], j), scale: 2 }));
    assert(rows[j][10] == Val::Date(for_at(gs, t[LI_SHIPDATE_BASE as int], t[LI_SHIPDATE_CODES as int], j)));
    assert(in_group(gs, j / sb, j));
}

/// The lineitem slices: their facts, and their values are the lineitem table's through the row map.
pub proof fn lemma_li(db: Database, p: Seq<PartView>, c: Cols)
    requires
        db.schema == crate::schema::schema_spec(), db_wf(db),
        represents(p, crate::stores::facts::declaration::stored_relations(db)),
        li_from_parts(c, p),
    ensures
        li_ok(c),
        groups_ok(c),
        li_link(c, db, lmap(p, c.n_l as int)),
{
    hide(li_core);
    lemma_li_core(db, p, c);
    let t = ltp(p);
    let n = c.n_l as int;
    let m = lmap(p, n);
    let sb = u64s(t[LI_LAYOUT as int])[1] as int;
    let b = c.bs_l as int;
    assert(li_core(db, p, c) ==> groups_part_ok(t[LI_GROUPS as int], n, sb) && sb >= 1 && is_perm(m, n)
        && n == db.tables[0].len()) by { reveal(li_core); }
    lemma_uniform_groups(t[LI_GROUPS as int], n, sb);
    lemma_bases_cover(nblocks_of(n, sb), b, sb, n);
    assert(c.ls_bases@.len() == nblocks_of(n, sb) && c.ls_zmax@.len() == nblocks_of(n, sb)
        && c.ls_codes@.len() == n && c.lsk_codes@.len() == n && c.lln_codes@.len() == n
        && c.lok_codes@.len() == n && c.lp_codes@.len() == n && c.ld_codes@.len() == n
        && c.lsk_bases@.len() == c.ls_bases@.len() && c.lln_bases@.len() == c.ls_bases@.len()
        && c.lok_bases@.len() == c.ls_bases@.len() && c.lp_bases@.len() == c.ls_bases@.len()
        && c.ld_bases@.len() == c.ls_bases@.len()) by { reveal(li_core); }
    lemma_li_vals(db);
    assert forall|j: int| 0 <= j < n implies {
        &&& (#[trigger] db.tables[0][m[j]])[0] == Val::Int(lkey(c, j))
        &&& db.tables[0][m[j]][2] == Val::Int(lsupp(c, j))
        &&& db.tables[0][m[j]][5] == (Val::Num { coeff: lprice(c, j), scale: 2 })
        &&& db.tables[0][m[j]][6] == (Val::Num { coeff: ldisc(c, j), scale: 2 })
        &&& db.tables[0][m[j]][10] == Val::Date(lship(c, j))
    } by {
        lemma_li_row(db, p, c, j);
    }
    assert forall|j: int| 0 <= j < c.n_l implies in_i64(#[trigger] lship(c, j)) && lship(c, j) <= c.ls_zmax@[j / c.bs_l as int] by {
        lemma_li_row(db, p, c, j);
        assert(li_vals(db.tables[0][m[j]]));
    }
    assert forall|j: int| 0 <= j < c.n_l implies in_i64(#[trigger] lsupp(c, j)) by {
        lemma_li_row(db, p, c, j);
        assert(li_vals(db.tables[0][m[j]]));
    }
    assert forall|j: int| 0 <= j < c.n_l implies in_i64(#[trigger] lkey(c, j)) by {
        lemma_li_row(db, p, c, j);
        assert(li_vals(db.tables[0][m[j]]));
    }
    assert forall|j: int| 0 <= j < c.n_l implies small15(#[trigger] lprice(c, j)) by {
        lemma_li_row(db, p, c, j);
        assert(li_vals(db.tables[0][m[j]]));
    }
    assert forall|j: int| 0 <= j < c.n_l implies small15(#[trigger] ldisc(c, j)) by {
        lemma_li_row(db, p, c, j);
        assert(li_vals(db.tables[0][m[j]]));
    }
}

// ------------------------------------------------------------------------------------------------ orders

/// Number of group starts of uniform groups (isolated: `groups_wf` instantiates in chains).
proof fn lemma_gs_len(gp: PartView, n: int, sb: int)
    requires groups_part_ok(gp, n, sb),
    ensures u64s(gp).len() == nblocks_of(n, sb) + 1,
{
    lemma_uniform_groups(gp, n, sb);
}

/// The column predicates of the orders parts the scan reads.
pub open spec fn ord_core(db: Database, p: Seq<PartView>, c: Cols) -> bool {
    let t = otp(p);
    let rel = orel(db);
    let n = rel.len() as int;
    let sb = u64s(t[OR_LAYOUT as int])[1] as int;
    let gp = t[OR_GROUPS as int];
    let gs = u64s(gp);
    let m = orders_map(t, n);
    let rows = orders_rows(t, rel);
    &&& n == db.tables[1].len()
    &&& n == c.n_o
    &&& sb >= 1
    &&& groups_part_ok(gp, n, sb)
    &&& is_perm(m, n)
    &&& rows == stored_rows(rel, m)
    &&& rel == proj_all(db.tables[1], crate::stores::facts::declaration::stored_cols_t1())
    &&& int_col(rows, 0, gs, t[OR_ORDERKEY_BASE as int], t[OR_ORDERKEY_CODES as int])
    &&& int_col(rows, 1, gs, t[OR_CUSTKEY_BASE as int], t[OR_CUSTKEY_CODES as int])
    &&& part_len(t[OR_ORDERKEY_CODES as int]) == n && part_len(t[OR_CUSTKEY_CODES as int]) == n
    &&& part_len(t[OR_ORDERKEY_BASE as int]) == gs.len() - 1 && part_len(t[OR_CUSTKEY_BASE as int]) == gs.len() - 1
    &&& keyidx_ok(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@, sb, c.oi_kind, n)
}

pub proof fn lemma_ord_core(db: Database, p: Seq<PartView>, c: Cols)
    requires
        db.schema == crate::schema::schema_spec(), db_wf(db),
        represents(p, crate::stores::facts::declaration::stored_relations(db)),
        ord_from_parts(c, p),
    ensures ord_core(db, p, c),
{
    let t = otp(p);
    let rel = orel(db);
    crate::stores::facts::declaration::lemma_stored_relations(db);
    assert(orders_ok(t, rel));
    let rows = orders_rows(t, rel);
    assert(orders_cols_ok(t, rows));
    lemma_proj_all_len(db.tables[1], crate::stores::facts::declaration::stored_cols_t1());
}

/// One orders row's values through the row map.
proof fn lemma_ord_row(db: Database, p: Seq<PartView>, c: Cols, q: int)
    requires ord_core(db, p, c), ord_from_parts(c, p), 0 <= q < c.n_o,
    ensures ({
        let m = omap(p, c.n_o as int);
        &&& 0 <= m[q] < c.n_o
        &&& db.tables[1][m[q]][0] == Val::Int(okey(c, q))
        &&& db.tables[1][m[q]][1] == Val::Int(ocust(c, q))
    }),
{
    let t = otp(p);
    let rel = orel(db);
    let n = c.n_o as int;
    let sb = u64s(t[OR_LAYOUT as int])[1] as int;
    let b = c.bs_o as int;
    let gp = t[OR_GROUPS as int];
    let gs = u64s(gp);
    let m = orders_map(t, n);
    let rows = orders_rows(t, rel);
    let cols = crate::stores::facts::declaration::stored_cols_t1();
    assert(cols[0] == 0 && cols[1] == 1 && cols.len() == 7);
    assert(0 <= m[q] < n);
    assert(rows[q] == rel[m[q]]);
    lemma_proj_at(db.tables[1], cols, m[q], 0);
    lemma_proj_at(db.tables[1], cols, m[q], 1);
    lemma_for_col(gp, n, sb, b, t[OR_ORDERKEY_BASE as int], t[OR_ORDERKEY_CODES as int], q);
    lemma_for_col(gp, n, sb, b, t[OR_CUSTKEY_BASE as int], t[OR_CUSTKEY_CODES as int], q);
    assert(rows[q][0] == Val::Int(for_at(gs, t[OR_ORDERKEY_BASE as int], t[OR_ORDERKEY_CODES as int], q)));
    assert(rows[q][1] == Val::Int(for_at(gs, t[OR_CUSTKEY_BASE as int], t[OR_CUSTKEY_CODES as int], q)));
}

/// The orders slices: their facts, and their values are the orders table's through the row map.
pub proof fn lemma_ord(db: Database, p: Seq<PartView>, c: Cols)
    requires
        db.schema == crate::schema::schema_spec(), db_wf(db),
        represents(p, crate::stores::facts::declaration::stored_relations(db)),
        ord_from_parts(c, p),
    ensures
        ord_ok(c),
        ord_link(c, db, omap(p, c.n_o as int)),
{
    hide(ord_core);
    hide(keyidx_ok);
    hide(is_perm);
    lemma_ord_core(db, p, c);
    let t = otp(p);
    let n = c.n_o as int;
    let m = omap(p, n);
    let sb = u64s(t[OR_LAYOUT as int])[1] as int;
    let b = c.bs_o as int;
    assert(groups_part_ok(t[OR_GROUPS as int], n, sb) && sb >= 1 && is_perm(m, n) && n == db.tables[1].len()
        && keyidx_ok(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@, sb, c.oi_kind, n)) by { reveal(ord_core); }
    lemma_gs_len(t[OR_GROUPS as int], n, sb);
    lemma_bases_cover(nblocks_of(n, sb), b, sb, n);
    assert(c.ok_bases@.len() == nblocks_of(n, sb) && c.oc_bases@.len() == nblocks_of(n, sb)
        && c.ok_codes@.len() == n && c.oc_codes@.len() == n) by { reveal(ord_core); }
    lemma_keyidx_bs(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@, sb, b, c.oi_kind, n);
    assert(crate::schema::schema_spec()[1].columns[0].ty == crate::spec::types::SqlType::Int8) by (compute);
    assert(crate::schema::schema_spec()[1].columns[1].ty == crate::spec::types::SqlType::Int8) by (compute);
    assert(crate::schema::schema_spec()[1].columns.len() == 9) by (compute);
    assert forall|q: int| 0 <= q < n implies {
        &&& (#[trigger] db.tables[1][m[q]])[0] == Val::Int(okey(c, q))
        &&& db.tables[1][m[q]][1] == Val::Int(ocust(c, q))
    } by {
        lemma_ord_row(db, p, c, q);
    }
    lemma_int8_vals(db, 1, 0);
    lemma_int8_vals(db, 1, 1);
    assert forall|q: int| 0 <= q < n implies in_i64(#[trigger] okey(c, q)) by {
        lemma_ord_row(db, p, c, q);
        assert(db.tables[1][m[q]][0] is Int);
    }
    assert forall|q: int| 0 <= q < n implies in_i64(#[trigger] ocust(c, q)) by {
        lemma_ord_row(db, p, c, q);
        assert(db.tables[1][m[q]][1] is Int);
    }
}

/// An Int8 column's values are `i64` integers.
pub proof fn lemma_int8_vals(db: Database, t: int, k: int)
    requires
        db.schema == crate::schema::schema_spec(), db_wf(db),
        0 <= t < 8, 0 <= k < crate::schema::schema_spec()[t].columns.len(),
        crate::schema::schema_spec()[t].columns[k].ty == crate::spec::types::SqlType::Int8,
    ensures forall|i: int| 0 <= i < db.tables[t].len() ==>
        (#[trigger] db.tables[t][i])[k] is Int && in_i64(db.tables[t][i][k]->Int_0),
{
    assert forall|i: int| 0 <= i < db.tables[t].len() implies
        (#[trigger] db.tables[t][i])[k] is Int && in_i64(db.tables[t][i][k]->Int_0) by {
        assert(row_in_table(db.tables[t][i], db.schema[t]));
        assert(crate::spec::typing::value_in_column(db.tables[t][i][k], db.schema[t].columns[k]));
    }
}

// ------------------------------------------------------------------------------------------------ supplier, customer

/// Row `j` of a FOR column of storage `suppliers` under a model group size.
proof fn lemma_for_col_s(gp: PartView, n: int, sb: int, b: int, base: PartView, codes: PartView, j: int)
    requires scf::groups_part_ok(gp, n, sb), bs_ok(b, sb, n), 0 <= j < n,
    ensures scf::for_at(scf::u64s(gp), base, codes, j) == scf::base_at(base, j / b) + scf::code_at(codes, j),
{
    crate::stores::suppliers::interface::common::read::lemma_for_row(gp, n, sb, base, codes, j);
    lemma_bs_group(b, sb, n, j);
}

proof fn lemma_for_col_c(gp: PartView, n: int, sb: int, b: int, base: PartView, codes: PartView, j: int)
    requires ccf::groups_part_ok(gp, n, sb), bs_ok(b, sb, n), 0 <= j < n,
    ensures ccf::for_at(ccf::u64s(gp), base, codes, j) == ccf::base_at(base, j / b) + ccf::code_at(codes, j),
{
    crate::stores::custpart::interface::common::read::lemma_for_row(gp, n, sb, base, codes, j);
    lemma_bs_group(b, sb, n, j);
}

/// A key index without index column (kinds 0 and 1) in another storage's copy of `keyidx` is one here; kinds other
/// than 1 are read as 0 (no order known).
proof fn lemma_keyidx_bridge_s(kc: Seq<u32>, kb: Seq<i64>, sb: int, stored: u64, kind: u64, n: int)
    requires
        skx::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, stored, n),
        kind == (if stored == 1 { 1u64 } else { 0u64 }),
    ensures keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, kind, n),
{
    if kind == 1 {
        assert forall|r: int| 0 <= r < n - 1 implies #[trigger] sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, kind, r) by {
            assert(skx::sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, stored, r));
        }
    }
}

proof fn lemma_keyidx_bridge_c(kc: Seq<u32>, kb: Seq<i64>, sb: int, stored: u64, kind: u64, n: int)
    requires
        ckx::keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, stored, n),
        kind == (if stored == 1 { 1u64 } else { 0u64 }),
    ensures keyidx_ok(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, kind, n),
{
    if kind == 1 {
        assert forall|r: int| 0 <= r < n - 1 implies #[trigger] sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, kind, r) by {
            assert(ckx::sorted_at(kc, kb, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, stored, r));
        }
    }
}

/// The supplier slices' kind as stored: 1 (rows sorted by key) or anything else, read as 0.
pub open spec fn sup_from_parts_kind(c: Cols, p: Seq<PartView>, stored: u64) -> bool {
    let t = stp(p);
    &&& p.len() == crate::stores::suppliers::interface::SUPPLIERS_PARTS
    &&& t[SU_LAYOUT as int] is U64 && scf::u64s(t[SU_LAYOUT as int]).len() == 2
    &&& c.n_s as int == scf::u64s(t[SU_LAYOUT as int])[0]
    &&& bs_ok(c.bs_s as int, scf::u64s(t[SU_LAYOUT as int])[1] as int, c.n_s as int)
    &&& t[SU_SUPPKEY_CODES as int] == PartView::U32(c.sk_codes@)
    &&& t[SU_SUPPKEY_BASE as int] == PartView::I64(c.sk_bases@)
    &&& t[SU_NATIONKEY_CODES as int] == PartView::U8(c.sn_codes@)
    &&& t[SU_NATIONKEY_BASE as int] == PartView::I64(c.sn_bases@)
    &&& t[SU_KEYIDX_KIND as int] is U64 && scf::u64s(t[SU_KEYIDX_KIND as int]).len() == 1
    &&& scf::u64s(t[SU_KEYIDX_KIND as int])[0] == stored
    &&& c.s_kind == (if stored == 1 { 1u64 } else { 0u64 })
    &&& c.no_codes@ == Seq::<u32>::empty() && c.no_bases@ == Seq::<u64>::empty()
}

pub open spec fn cus_from_parts_kind(c: Cols, p: Seq<PartView>, stored: u64) -> bool {
    let t = ctp(p);
    &&& p.len() == crate::stores::custpart::interface::CUSTPART_PARTS
    &&& t[CU_LAYOUT as int] is U64 && ccf::u64s(t[CU_LAYOUT as int]).len() == 2
    &&& c.n_c as int == ccf::u64s(t[CU_LAYOUT as int])[0]
    &&& bs_ok(c.bs_c as int, ccf::u64s(t[CU_LAYOUT as int])[1] as int, c.n_c as int)
    &&& t[CU_CUSTKEY_CODES as int] == PartView::U32(c.ck_codes@)
    &&& t[CU_CUSTKEY_BASE as int] == PartView::I64(c.ck_bases@)
    &&& t[CU_NATIONKEY_CODES as int] == PartView::U8(c.cn_codes@)
    &&& t[CU_NATIONKEY_BASE as int] == PartView::I64(c.cn_bases@)
    &&& t[CU_KEYIDX_KIND as int] is U64 && ccf::u64s(t[CU_KEYIDX_KIND as int]).len() == 1
    &&& ccf::u64s(t[CU_KEYIDX_KIND as int])[0] == stored
    &&& c.c_kind == (if stored == 1 { 1u64 } else { 0u64 })
    &&& c.no_codes@ == Seq::<u32>::empty() && c.no_bases@ == Seq::<u64>::empty()
}

/// The column predicates of the supplier parts the scan reads.
pub open spec fn sup_core(db: Database, p: Seq<PartView>, c: Cols, stored: u64) -> bool {
    let t = stp(p);
    let rel = srel(db);
    let n = rel.len() as int;
    let sb = scf::u64s(t[SU_LAYOUT as int])[1] as int;
    let gp = t[SU_GROUPS as int];
    let gs = scf::u64s(gp);
    &&& n == db.tables[5].len()
    &&& n == c.n_s
    &&& sb >= 1
    &&& scf::groups_part_ok(gp, n, sb)
    &&& rel == proj_all(db.tables[5], crate::stores::suppliers::declaration::stored_cols_t1())
    &&& scf::int_col(rel, 0, gs, t[SU_SUPPKEY_BASE as int], t[SU_SUPPKEY_CODES as int])
    &&& scf::int_col(rel, 3, gs, t[SU_NATIONKEY_BASE as int], t[SU_NATIONKEY_CODES as int])
    &&& part_len(t[SU_NATIONKEY_CODES as int]) == n
    &&& part_len(t[SU_NATIONKEY_BASE as int]) == gs.len() - 1
    &&& part_len(t[SU_SUPPKEY_BASE as int]) == gs.len() - 1
    &&& skx::keyidx_ok(c.sk_codes@, c.sk_bases@, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, stored, n)
}

proof fn lemma_sup_core(db: Database, p: Seq<PartView>, c: Cols, stored: u64)
    requires
        db.schema == crate::schema::schema_spec(), db_wf(db),
        crate::stores::suppliers::interface::represents(p, crate::stores::suppliers::declaration::stored_relations(db)),
        sup_from_parts_kind(c, p, stored),
    ensures sup_core(db, p, c, stored),
{
    crate::stores::suppliers::declaration::lemma_stored_relations(db);
    assert(supplier_ok(stp(p), srel(db)));
    lemma_proj_all_len(db.tables[5], crate::stores::suppliers::declaration::stored_cols_t1());
}

/// One supplier row's values.
proof fn lemma_sup_row(db: Database, p: Seq<PartView>, c: Cols, stored: u64, r: int)
    requires sup_core(db, p, c, stored), sup_from_parts_kind(c, p, stored), 0 <= r < c.n_s,
    ensures
        db.tables[5][r][0] == Val::Int(skey(c, r)),
        db.tables[5][r][3] == Val::Int(snat(c, r)),
{
    let t = stp(p);
    let rel = srel(db);
    let n = c.n_s as int;
    let sb = scf::u64s(t[SU_LAYOUT as int])[1] as int;
    let b = c.bs_s as int;
    let gp = t[SU_GROUPS as int];
    let cols = crate::stores::suppliers::declaration::stored_cols_t1();
    assert(cols[0] == 0 && cols[3] == 3 && cols.len() == 7);
    lemma_proj_at(db.tables[5], cols, r, 0);
    lemma_proj_at(db.tables[5], cols, r, 3);
    lemma_for_col_s(gp, n, sb, b, t[SU_SUPPKEY_BASE as int], t[SU_SUPPKEY_CODES as int], r);
    lemma_for_col_s(gp, n, sb, b, t[SU_NATIONKEY_BASE as int], t[SU_NATIONKEY_CODES as int], r);
}

/// The supplier slices: their facts, and their values are the supplier table's (canonical order).
pub proof fn lemma_sup(db: Database, p: Seq<PartView>, c: Cols, stored: u64)
    requires
        db.schema == crate::schema::schema_spec(), db_wf(db),
        crate::stores::suppliers::interface::represents(p, crate::stores::suppliers::declaration::stored_relations(db)),
        sup_from_parts_kind(c, p, stored),
    ensures
        sup_ok(c),
        sup_link(c, db),
{
    hide(sup_core);
    lemma_sup_core(db, p, c, stored);
    let t = stp(p);
    let n = c.n_s as int;
    let sb = scf::u64s(t[SU_LAYOUT as int])[1] as int;
    let b = c.bs_s as int;
    let gp = t[SU_GROUPS as int];
    assert(scf::groups_part_ok(gp, n, sb) && sb >= 1 && n == db.tables[5].len()
        && skx::keyidx_ok(c.sk_codes@, c.sk_bases@, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, stored, n)
        && c.sn_codes@.len() == n && c.sn_bases@.len() == scf::u64s(gp).len() - 1
        && c.sk_bases@.len() == scf::u64s(gp).len() - 1) by { reveal(sup_core); }
    scf::lemma_uniform_groups(gp, n, sb);
    scf::lemma_nblocks(n, sb);
    lemma_bases_cover(nblocks_of(n, sb), b, sb, n);
    lemma_keyidx_bridge_s(c.sk_codes@, c.sk_bases@, sb, stored, c.s_kind, n);
    lemma_keyidx_bs(c.sk_codes@, c.sk_bases@, c.no_codes@, c.no_bases@, sb, b, c.s_kind, n);
    assert(crate::schema::schema_spec()[5].columns[0].ty == crate::spec::types::SqlType::Int8) by (compute);
    assert(crate::schema::schema_spec()[5].columns[3].ty == crate::spec::types::SqlType::Int8) by (compute);
    assert(crate::schema::schema_spec()[5].columns.len() == 7) by (compute);
    lemma_int8_vals(db, 5, 0);
    lemma_int8_vals(db, 5, 3);
    assert forall|r: int| 0 <= r < n implies {
        &&& (#[trigger] db.tables[5][r])[0] == Val::Int(skey(c, r))
        &&& db.tables[5][r][3] == Val::Int(snat(c, r))
    } by {
        lemma_sup_row(db, p, c, stored, r);
    }
    assert forall|r: int| 0 <= r < n implies in_i64(#[trigger] skey(c, r)) by {
        lemma_sup_row(db, p, c, stored, r);
        assert(db.tables[5][r][0] is Int);
    }
    assert forall|r: int| 0 <= r < n implies in_i64(#[trigger] snat(c, r)) by {
        lemma_sup_row(db, p, c, stored, r);
        assert(db.tables[5][r][3] is Int);
    }
}

/// The column predicates of the customer parts the scan reads.
pub open spec fn cus_core(db: Database, p: Seq<PartView>, c: Cols, stored: u64) -> bool {
    let t = ctp(p);
    let rel = crel(db);
    let n = rel.len() as int;
    let sb = ccf::u64s(t[CU_LAYOUT as int])[1] as int;
    let gp = t[CU_GROUPS as int];
    let gs = ccf::u64s(gp);
    &&& n == db.tables[2].len()
    &&& n == c.n_c
    &&& sb >= 1
    &&& ccf::groups_part_ok(gp, n, sb)
    &&& rel == proj_all(db.tables[2], crate::stores::custpart::declaration::stored_cols_t0())
    &&& ccf::int_col(rel, 0, gs, t[CU_CUSTKEY_BASE as int], t[CU_CUSTKEY_CODES as int])
    &&& ccf::int_col(rel, 3, gs, t[CU_NATIONKEY_BASE as int], t[CU_NATIONKEY_CODES as int])
    &&& part_len(t[CU_NATIONKEY_CODES as int]) == n
    &&& part_len(t[CU_NATIONKEY_BASE as int]) == gs.len() - 1
    &&& part_len(t[CU_CUSTKEY_BASE as int]) == gs.len() - 1
    &&& ckx::keyidx_ok(c.ck_codes@, c.ck_bases@, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, stored, n)
}

proof fn lemma_cus_core(db: Database, p: Seq<PartView>, c: Cols, stored: u64)
    requires
        db.schema == crate::schema::schema_spec(), db_wf(db),
        crate::stores::custpart::interface::represents(p, crate::stores::custpart::declaration::stored_relations(db)),
        cus_from_parts_kind(c, p, stored),
    ensures cus_core(db, p, c, stored),
{
    crate::stores::custpart::declaration::lemma_stored_relations(db);
    assert(customer_ok(ctp(p), crel(db)));
    lemma_proj_all_len(db.tables[2], crate::stores::custpart::declaration::stored_cols_t0());
}

proof fn lemma_cus_row(db: Database, p: Seq<PartView>, c: Cols, stored: u64, r: int)
    requires cus_core(db, p, c, stored), cus_from_parts_kind(c, p, stored), 0 <= r < c.n_c,
    ensures
        db.tables[2][r][0] == Val::Int(ckey(c, r)),
        db.tables[2][r][3] == Val::Int(cnat(c, r)),
{
    let t = ctp(p);
    let rel = crel(db);
    let n = c.n_c as int;
    let sb = ccf::u64s(t[CU_LAYOUT as int])[1] as int;
    let b = c.bs_c as int;
    let gp = t[CU_GROUPS as int];
    let cols = crate::stores::custpart::declaration::stored_cols_t0();
    assert(cols[0] == 0 && cols[3] == 3 && cols.len() == 8);
    lemma_proj_at(db.tables[2], cols, r, 0);
    lemma_proj_at(db.tables[2], cols, r, 3);
    lemma_for_col_c(gp, n, sb, b, t[CU_CUSTKEY_BASE as int], t[CU_CUSTKEY_CODES as int], r);
    lemma_for_col_c(gp, n, sb, b, t[CU_NATIONKEY_BASE as int], t[CU_NATIONKEY_CODES as int], r);
}

/// The customer slices: their facts, and their values are the customer table's (canonical order).
pub proof fn lemma_cus(db: Database, p: Seq<PartView>, c: Cols, stored: u64)
    requires
        db.schema == crate::schema::schema_spec(), db_wf(db),
        crate::stores::custpart::interface::represents(p, crate::stores::custpart::declaration::stored_relations(db)),
        cus_from_parts_kind(c, p, stored),
    ensures
        cus_ok(c),
        cus_link(c, db),
{
    hide(cus_core);
    lemma_cus_core(db, p, c, stored);
    let t = ctp(p);
    let n = c.n_c as int;
    let sb = ccf::u64s(t[CU_LAYOUT as int])[1] as int;
    let b = c.bs_c as int;
    let gp = t[CU_GROUPS as int];
    assert(ccf::groups_part_ok(gp, n, sb) && sb >= 1 && n == db.tables[2].len()
        && ckx::keyidx_ok(c.ck_codes@, c.ck_bases@, Seq::<u32>::empty(), Seq::<u64>::empty(), sb, stored, n)
        && c.cn_codes@.len() == n && c.cn_bases@.len() == ccf::u64s(gp).len() - 1
        && c.ck_bases@.len() == ccf::u64s(gp).len() - 1) by { reveal(cus_core); }
    ccf::lemma_uniform_groups(gp, n, sb);
    ccf::lemma_nblocks(n, sb);
    lemma_bases_cover(nblocks_of(n, sb), b, sb, n);
    lemma_keyidx_bridge_c(c.ck_codes@, c.ck_bases@, sb, stored, c.c_kind, n);
    lemma_keyidx_bs(c.ck_codes@, c.ck_bases@, c.no_codes@, c.no_bases@, sb, b, c.c_kind, n);
    assert(crate::schema::schema_spec()[2].columns[0].ty == crate::spec::types::SqlType::Int8) by (compute);
    assert(crate::schema::schema_spec()[2].columns[3].ty == crate::spec::types::SqlType::Int8) by (compute);
    assert(crate::schema::schema_spec()[2].columns.len() == 8) by (compute);
    lemma_int8_vals(db, 2, 0);
    lemma_int8_vals(db, 2, 3);
    assert forall|r: int| 0 <= r < n implies {
        &&& (#[trigger] db.tables[2][r])[0] == Val::Int(ckey(c, r))
        &&& db.tables[2][r][3] == Val::Int(cnat(c, r))
    } by {
        lemma_cus_row(db, p, c, stored, r);
    }
    assert forall|r: int| 0 <= r < n implies in_i64(#[trigger] ckey(c, r)) by {
        lemma_cus_row(db, p, c, stored, r);
        assert(db.tables[2][r][0] is Int);
    }
    assert forall|r: int| 0 <= r < n implies in_i64(#[trigger] cnat(c, r)) by {
        lemma_cus_row(db, p, c, stored, r);
        assert(db.tables[2][r][3] is Int);
    }
}

} // verus!
