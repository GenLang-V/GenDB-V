//! facts' `represents` in this storage's terms. The interface copies facts' definitions under another module path
//! (`crate::stores::factsdir::interface` instead of `crate::stores::facts::interface`), so each conjunct is restated:
//! one lemma per column format (FOR values agree once both copies reduce `for_at` to `base[j / bsize] + code[j]`;
//! dictionaries, text, zone maps, key indexes and row maps follow), then one lemma per table and the clustering flag.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::gendb_entry::storage::stored_relations;
use crate::spec::value::{Database, Row, Val};
use crate::stores::facts::interface as F;
use crate::stores::facts::interface::common::colfmt as FC;
use crate::stores::facts::interface::common::keyidx as FK;
use crate::stores::facts::interface::cluster as FL;
use crate::stores::facts::declaration as FD;
use crate::stores::factsdir::interface as M;
use crate::stores::factsdir::interface::common::colfmt as MC;
use crate::stores::factsdir::interface::common::keyidx as MK;
use crate::stores::factsdir::interface::cluster as ML;

verus! {

// ------------------------------------------------------------------------------------------------ column formats

/// The layout facts of `facts` in this storage's terms.
proof fn lemma_layout(tp: Seq<PartView>, n: int)
    requires F::table_layout_ok(tp, n),
    ensures
        M::table_layout_ok(tp, n),
        MC::groups_part_ok(tp[1], n, MC::u64s(tp[0])[1] as int),
        FC::groups_part_ok(tp[1], n, FC::u64s(tp[0])[1] as int),
{
}

/// A frame-of-reference value is the same under both copies of the column format.
proof fn lemma_for_at_same(gp: PartView, n: int, bs: int, base: PartView, codes: PartView, j: int)
    requires
        FC::groups_part_ok(gp, n, bs),
        0 <= j < n,
    ensures
        MC::for_at(MC::u64s(gp), base, codes, j) == FC::for_at(FC::u64s(gp), base, codes, j),
{
    assert(MC::groups_part_ok(gp, n, bs));
    M::common::read::lemma_for_row(gp, n, bs, base, codes, j);
    F::common::read::lemma_for_row(gp, n, bs, base, codes, j);
}

/// Both copies give the same row map of a FOR column of row indices.
proof fn lemma_for_map_same(tp: Seq<PartView>, n: int, cp: int, bp: int)
    requires F::table_layout_ok(tp, n),
    ensures MC::for_map(MC::gs_at(tp, 1), tp[bp], tp[cp], n) == FC::for_map(FC::gs_at(tp, 1), tp[bp], tp[cp], n),
{
    let bs = FC::u64s(tp[0])[1] as int;
    let a = MC::for_map(MC::gs_at(tp, 1), tp[bp], tp[cp], n);
    let b = FC::for_map(FC::gs_at(tp, 1), tp[bp], tp[cp], n);
    assert forall|j: int| 0 <= j < n implies a[j] == b[j] by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
    }
    assert(a =~= b);
}

/// A bijection under facts' copy is one under this storage's copy.
proof fn lemma_is_perm_same(m: Seq<int>, n: int)
    requires FC::is_perm(m, n),
    ensures MC::is_perm(m, n),
{
    assert forall|i: int| 0 <= i < n implies #[trigger] MC::covered(m, i) by {
        assert(FC::covered(m, i));
    }
}

/// A FOR shape carries over (same definitions).
proof fn lemma_shape_same(tp: Seq<PartView>, cp: int, bp: int, n: int)
    ensures
        FC::for_i64_shape(tp, 1, cp, bp, n) ==> MC::for_i64_shape(tp, 1, cp, bp, n),
        FC::for_u64_shape(tp, 1, cp, bp, n) ==> MC::for_u64_shape(tp, 1, cp, bp, n),
{
}

/// The row map column carries over, and so do the stored rows it gives.
proof fn lemma_perm_same(tp: Seq<PartView>, n: int, cp: int, bp: int, rel: Seq<Row>)
    requires
        F::table_layout_ok(tp, n),
        rel.len() == n,
        FC::perm_col_at(tp, 1, cp, bp, n),
    ensures
        MC::perm_col_at(tp, 1, cp, bp, n),
        MC::perm_rows(tp, 1, cp, bp, rel) == FC::perm_rows(tp, 1, cp, bp, rel),
{
    lemma_for_map_same(tp, n, cp, bp);
    lemma_is_perm_same(FC::for_map(FC::gs_at(tp, 1), tp[bp], tp[cp], n), n);
    lemma_shape_same(tp, cp, bp, n);
    let m = MC::for_map(MC::gs_at(tp, 1), tp[bp], tp[cp], n);
    assert(MC::stored_rows(rel, m) =~= FC::stored_rows(rel, m));
}

/// An integer column carries over.
proof fn lemma_int_col(tp: Seq<PartView>, n: int, cp: int, bp: int, rows: Seq<Row>, c: int)
    requires
        F::table_layout_ok(tp, n),
        rows.len() == n,
        FC::int_col_at(tp, 1, cp, bp, rows, c),
    ensures
        MC::int_col_at(tp, 1, cp, bp, rows, c),
{
    let bs = FC::u64s(tp[0])[1] as int;
    lemma_shape_same(tp, cp, bp, n);
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j][c] == Val::Int(MC::for_at(MC::gs_at(tp, 1), tp[bp], tp[cp], j)) by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
        assert(rows[j][c] == Val::Int(FC::for_at(FC::gs_at(tp, 1), tp[bp], tp[cp], j)));
    }
}

/// A numeric column carries over.
proof fn lemma_num_col(tp: Seq<PartView>, n: int, cp: int, bp: int, rows: Seq<Row>, c: int, scale: nat)
    requires
        F::table_layout_ok(tp, n),
        rows.len() == n,
        FC::num_col_at(tp, 1, cp, bp, rows, c, scale),
    ensures
        MC::num_col_at(tp, 1, cp, bp, rows, c, scale),
{
    let bs = FC::u64s(tp[0])[1] as int;
    lemma_shape_same(tp, cp, bp, n);
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j][c] == (Val::Num { coeff: MC::for_at(MC::gs_at(tp, 1), tp[bp], tp[cp], j), scale }) by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
        assert(rows[j][c] == (Val::Num { coeff: FC::for_at(FC::gs_at(tp, 1), tp[bp], tp[cp], j), scale }));
    }
}

/// A date column carries over.
proof fn lemma_date_col(tp: Seq<PartView>, n: int, cp: int, bp: int, rows: Seq<Row>, c: int)
    requires
        F::table_layout_ok(tp, n),
        rows.len() == n,
        FC::date_col_at(tp, 1, cp, bp, rows, c),
    ensures
        MC::date_col_at(tp, 1, cp, bp, rows, c),
{
    let bs = FC::u64s(tp[0])[1] as int;
    lemma_shape_same(tp, cp, bp, n);
    assert forall|j: int| 0 <= j < rows.len() implies #[trigger] rows[j][c] == Val::Date(MC::for_at(MC::gs_at(tp, 1), tp[bp], tp[cp], j)) by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
        assert(rows[j][c] == Val::Date(FC::for_at(FC::gs_at(tp, 1), tp[bp], tp[cp], j)));
    }
}

/// A dictionary column carries over.
proof fn lemma_dict_col(tp: Seq<PartView>, n: int, cp: int, bp: int, op: int, yp: int, rows: Seq<Row>, c: int)
    requires
        F::table_layout_ok(tp, n),
        rows.len() == n,
        FC::dict_col_at(tp, 1, cp, bp, op, yp, rows, c),
    ensures
        MC::dict_col_at(tp, 1, cp, bp, op, yp, rows, c),
{
    let bs = FC::u64s(tp[0])[1] as int;
    lemma_shape_same(tp, cp, bp, n);
    let (doffs, dbytes) = (FC::u64s(tp[op]), FC::u8s(tp[yp]));
    let k = doffs.len() - 1;
    assert forall|j: int| 0 <= j < k implies #[trigger] MC::text_range_ok(doffs, dbytes, j) by {
        assert(FC::text_range_ok(doffs, dbytes, j));
    }
    assert forall|a: int| 0 <= a < k - 1 implies #[trigger] crate::spec::text::lex_cmp(MC::text_of(doffs, dbytes, a),
        MC::text_of(doffs, dbytes, a + 1)) < 0 by {
        assert(crate::spec::text::lex_cmp(FC::text_of(doffs, dbytes, a), FC::text_of(doffs, dbytes, a + 1)) < 0);
    }
    assert forall|j: int| 0 <= j < rows.len() implies {
        &&& 0 <= MC::for_at(MC::gs_at(tp, 1), tp[bp], tp[cp], j) < doffs.len() - 1
        &&& #[trigger] rows[j][c] == Val::Text(MC::text_of(doffs, dbytes, MC::for_at(MC::gs_at(tp, 1), tp[bp], tp[cp], j)))
    } by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
        assert(rows[j][c] == Val::Text(FC::text_of(doffs, dbytes, FC::for_at(FC::gs_at(tp, 1), tp[bp], tp[cp], j))));
    }
}

/// A zone map carries over.
proof fn lemma_zone(tp: Seq<PartView>, cp: int, bp: int, zp: int)
    requires FC::zone_at(tp, 1, cp, bp, zp),
    ensures MC::zone_at(tp, 1, cp, bp, zp),
{
    let gs = MC::gs_at(tp, 1);
    let z = MC::i64s(tp[zp]);
    assert forall|g: int, j: int| #[trigger] MC::in_group(gs, g, j) implies MC::base_at(tp[bp], g) + MC::code_at(tp[cp], j) <= z[g] by {
        assert(FC::in_group(FC::gs_at(tp, 1), g, j));
    }
}

/// A key index carries over.
proof fn lemma_keyidx(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bs: int, kind: u64, n: int)
    requires FK::keyidx_ok(kc, kb, ic, ib, bs, kind, n),
    ensures MK::keyidx_ok(kc, kb, ic, ib, bs, kind, n),
{
    if kind == 2 {
        assert(MK::idx_map(ic, ib, bs, n) =~= FK::idx_map(ic, ib, bs, n));
        lemma_is_perm_same(FK::idx_map(ic, ib, bs, n), n);
    }
    if kind >= 1 {
        assert forall|r: int| 0 <= r < n - 1 implies #[trigger] MK::sorted_at(kc, kb, ic, ib, bs, kind, r) by {
            assert(FK::sorted_at(kc, kb, ic, ib, bs, kind, r));
        }
    }
}

/// Every row of `rel` has `w` columns, in both copies.
proof fn lemma_width(rel: Seq<Row>, w: int)
    requires FC::rows_width(rel, w),
    ensures MC::rows_width(rel, w),
{
    assert forall|i: int| 0 <= i < rel.len() implies #[trigger] rel[i].len() == w by {
        assert(rel[i].len() == w);
    }
}

// ------------------------------------------------------------------------------------------------ tables

/// The lineitem parts of facts.
pub open spec fn li_tp(fp: Seq<PartView>) -> Seq<PartView> {
    fp.subrange(F::LINEITEM_FIRST as int, (F::LINEITEM_FIRST + F::LI_PARTS) as int)
}

/// The orders parts of facts.
pub open spec fn or_tp(fp: Seq<PartView>) -> Seq<PartView> {
    fp.subrange(F::ORDERS_FIRST as int, (F::ORDERS_FIRST + F::OR_PARTS) as int)
}

/// The lineitem columns carry over, over the same stored rows.
proof fn lemma_li_cols(tp: Seq<PartView>, n: int, rows: Seq<Row>)
    requires
        F::table_layout_ok(tp, n),
        rows.len() == n,
        F::lineitem_cols_ok(tp, rows),
    ensures
        M::lineitem_cols_ok(tp, rows),
{
    hide(FC::int_col_at);
    hide(FC::num_col_at);
    hide(FC::date_col_at);
    hide(FC::dict_col_at);
    hide(FC::zone_at);
    hide(FK::keyidx_ok);
    hide(MC::int_col_at);
    hide(MC::num_col_at);
    hide(MC::date_col_at);
    hide(MC::dict_col_at);
    hide(MC::zone_at);
    hide(MK::keyidx_ok);
    lemma_int_col(tp, n, 4, 5, rows, 0);
    lemma_int_col(tp, n, 6, 7, rows, 1);
    lemma_int_col(tp, n, 8, 9, rows, 2);
    lemma_int_col(tp, n, 10, 11, rows, 3);
    lemma_num_col(tp, n, 12, 13, rows, 4, 2);
    lemma_num_col(tp, n, 14, 15, rows, 5, 2);
    lemma_num_col(tp, n, 16, 17, rows, 6, 2);
    lemma_num_col(tp, n, 18, 19, rows, 7, 2);
    lemma_dict_col(tp, n, 20, 21, 22, 23, rows, 8);
    lemma_dict_col(tp, n, 24, 25, 26, 27, rows, 9);
    lemma_date_col(tp, n, 28, 29, rows, 10);
    lemma_zone(tp, 28, 29, 30);
    lemma_date_col(tp, n, 31, 32, rows, 11);
    lemma_zone(tp, 31, 32, 33);
    lemma_date_col(tp, n, 34, 35, rows, 12);
    lemma_zone(tp, 34, 35, 36);
    lemma_dict_col(tp, n, 37, 38, 39, 40, rows, 13);
    lemma_dict_col(tp, n, 41, 42, 43, 44, rows, 14);
    lemma_keyidx(FC::u32s(tp[6]), FC::i64s(tp[7]), FC::u32s(tp[45]), FC::u64s(tp[46]), FC::u64s(tp[0])[1] as int,
        FC::u64s(tp[47])[0], n);
}

/// The orders columns carry over, over the same stored rows.
proof fn lemma_or_cols(tp: Seq<PartView>, n: int, rows: Seq<Row>)
    requires
        F::table_layout_ok(tp, n),
        rows.len() == n,
        F::orders_cols_ok(tp, rows),
    ensures
        M::orders_cols_ok(tp, rows),
{
    hide(FC::int_col_at);
    hide(FC::num_col_at);
    hide(FC::date_col_at);
    hide(FC::dict_col_at);
    hide(FC::zone_at);
    hide(FK::keyidx_ok);
    hide(MC::int_col_at);
    hide(MC::num_col_at);
    hide(MC::date_col_at);
    hide(MC::dict_col_at);
    hide(MC::zone_at);
    hide(MK::keyidx_ok);
    lemma_int_col(tp, n, 4, 5, rows, 0);
    lemma_int_col(tp, n, 6, 7, rows, 1);
    lemma_dict_col(tp, n, 8, 9, 10, 11, rows, 2);
    lemma_num_col(tp, n, 12, 13, rows, 3, 2);
    lemma_date_col(tp, n, 14, 15, rows, 4);
    lemma_zone(tp, 14, 15, 16);
    lemma_dict_col(tp, n, 17, 18, 19, 20, rows, 5);
    lemma_int_col(tp, n, 21, 22, rows, 6);
    let (kc, kb, ic, ib) = (FC::u32s(tp[4]), FC::i64s(tp[5]), FC::u32s(tp[23]), FC::u64s(tp[24]));
    let (bs, kind) = (FC::u64s(tp[0])[1] as int, FC::u64s(tp[25])[0]);
    lemma_keyidx(kc, kb, ic, ib, bs, kind, n);
    if kind == 2 {
        lemma_for_map_same(tp, n, 2, 3);
        assert(M::orders_map(tp, n) == F::orders_map(tp, n));
        assert forall|r: int| 0 <= r < n implies #[trigger] M::orders_map(tp, n)[MK::fidx(ic, ib, bs, r)] == r by {
            assert(F::orders_map(tp, n)[FK::fidx(ic, ib, bs, r)] == r);
        }
    }
}

/// Table lineitem carries over, with the same stored rows.
proof fn lemma_li(tp: Seq<PartView>, rel: Seq<Row>)
    requires F::lineitem_ok(tp, rel),
    ensures
        M::lineitem_ok(tp, rel),
        M::lineitem_rows(tp, rel) == F::lineitem_rows(tp, rel),
{
    let n = rel.len() as int;
    lemma_layout(tp, n);
    lemma_width(rel, 15);
    lemma_perm_same(tp, n, 2, 3, rel);
    let rows = F::lineitem_rows(tp, rel);
    assert(rows.len() == n);
    lemma_li_cols(tp, n, rows);
}

/// Table orders carries over, with the same stored rows.
proof fn lemma_or(tp: Seq<PartView>, rel: Seq<Row>)
    requires F::orders_ok(tp, rel),
    ensures
        M::orders_ok(tp, rel),
        M::orders_rows(tp, rel) == F::orders_rows(tp, rel),
{
    let n = rel.len() as int;
    lemma_layout(tp, n);
    lemma_width(rel, 7);
    lemma_perm_same(tp, n, 2, 3, rel);
    let rows = F::orders_rows(tp, rel);
    assert(rows.len() == n);
    lemma_or_cols(tp, n, rows);
}

// ------------------------------------------------------------------------------------------------ clustering

proof fn lemma_first_key_same(orows: Seq<Row>, k: Val, i: int)
    ensures ML::first_key_from(orows, k, i) == FL::first_key_from(orows, k, i),
    decreases orows.len() - i,
{
    if 0 <= i < orows.len() && orows[i][0] != k {
        lemma_first_key_same(orows, k, i + 1);
    }
}

/// The clustering of the stored rows carries over.
proof fn lemma_cluster(lrows: Seq<Row>, orows: Seq<Row>)
    requires FL::clustered(lrows, orows),
    ensures ML::clustered(lrows, orows),
{
    assert forall|j: int| 0 <= j < lrows.len() - 1 implies #[trigger] ML::cluster_step(lrows, orows, j) by {
        assert(FL::cluster_step(lrows, orows, j));
        lemma_first_key_same(orows, lrows[j][0], 0);
        lemma_first_key_same(orows, lrows[j + 1][0], 0);
    }
}

/// facts' `represents` gives this storage's `base_represents` over the same parts and relations.
pub proof fn lemma_base_of(fp: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires F::represents(fp, rels),
    ensures M::base_represents(fp, rels),
{
    hide(F::lineitem_ok);
    hide(F::orders_ok);
    hide(M::lineitem_ok);
    hide(M::orders_ok);
    let (lt, ot) = (li_tp(fp), or_tp(fp));
    lemma_li(lt, rels[0]);
    lemma_or(ot, rels[1]);
    if FC::u64s(fp[F::FACTS_CLUSTER as int])[0] == 1 {
        lemma_cluster(F::lineitem_rows(lt, rels[0]), F::orders_rows(ot, rels[1]));
    }
}

/// For a database bound to `facts`, the source parts meet this storage's `base_represents`.
pub proof fn lemma_base(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures M::base_represents(sv.facts, stored_relations(db)),
{
    super::src::lemma_src(sv, db);
    assert(F::represents(sv.facts, FD::stored_relations(db)));
    lemma_base_of(sv.facts, FD::stored_relations(db));
}

} // verus!
