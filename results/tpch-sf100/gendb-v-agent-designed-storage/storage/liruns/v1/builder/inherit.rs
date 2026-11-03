//! The inherited parts of `facts` in this storage's terms: for every database bound to `facts`, they satisfy
//! `inherited_ok` (lineitem `[l_orderkey, l_quantity]`, orders `[o_orderkey, o_custkey, o_totalprice,
//! o_orderdate]` with the o_orderkey key index, and the co-clustering flag). `facts` states the same layouts over all
//! its stored columns with the same definitions under another module path (`common`, `cluster` are copies), so each
//! lemma here unfolds one definition under both paths.
use vstd::prelude::*;
use crate::gendb_entry::sources_bound;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::spec::value::*;
use crate::link::query::proj;
use crate::link::source::lemma_proj_all_index;
use crate::stores::liruns::interface::*;
use crate::stores::liruns::interface::common::colfmt::*;
use crate::stores::liruns::interface::common::keyidx as sk;
use crate::stores::liruns::interface::cluster as sc;
use crate::stores::liruns::declaration::{stored_relations, stored_cols_t0, stored_cols_t1};
use crate::stores::facts::interface as fi;
use crate::stores::facts::declaration as fd;
use fi::common::colfmt as fc;

verus! {

/// The lineitem parts of `facts`.
pub open spec fn ftl(sv: StoresView) -> Seq<PartView> {
    sv.facts.subrange(0, LI_PARTS as int)
}

/// The orders parts of `facts`.
pub open spec fn fto(sv: StoresView) -> Seq<PartView> {
    sv.facts.subrange(ORDERS_FIRST as int, (ORDERS_FIRST + OR_PARTS) as int)
}

/// What `facts` states for a bound database.
pub proof fn lemma_facts(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        sv.facts.len() == fi::FACTS_PARTS,
        fi::lineitem_ok(ftl(sv), fd::stored_relations(db)[0]),
        fi::orders_ok(fto(sv), fd::stored_relations(db)[1]),
        sv.facts[FACTS_CLUSTER as int] is U64 && fc::u64s(sv.facts[FACTS_CLUSTER as int]).len() == 1,
        fc::u64s(sv.facts[FACTS_CLUSTER as int])[0] == 1 ==> fi::cluster::clustered(
            fi::lineitem_rows(ftl(sv), fd::stored_relations(db)[0]), fi::orders_rows(fto(sv), fd::stored_relations(db)[1])),
{
    assert(fi::represents(sv.facts, fd::stored_relations(db)));
}

/// The number of parts of `facts`.
pub proof fn lemma_facts_len(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures sv.facts.len() == fi::FACTS_PARTS,
{
    assert(fi::represents(sv.facts, fd::stored_relations(db)));
}

// ------------------------------------------------------------------------------------------------ one definition, two paths

/// A frame-of-reference value is the same under both copies of the column format.
proof fn lemma_for_at_same(gp: PartView, n: int, bs: int, base: PartView, codes: PartView, j: int)
    requires
        groups_part_ok(gp, n, bs),
        0 <= j < n,
    ensures
        for_at(u64s(gp), base, codes, j) == fc::for_at(fc::u64s(gp), base, codes, j),
{
    crate::stores::liruns::interface::common::read::lemma_for_row(gp, n, bs, base, codes, j);
    assert(fc::groups_part_ok(gp, n, bs));
    fi::common::read::lemma_for_row(gp, n, bs, base, codes, j);
}

/// The layout facts of `facts` in this storage's terms.
proof fn lemma_layout(tp: Seq<PartView>, n: int)
    requires fi::table_layout_ok(tp, n),
    ensures
        table_layout_ok(tp, n),
        groups_part_ok(tp[1], n, u64s(tp[0])[1] as int),
{
}

/// A bijection under the `facts` copy of the definitions is one under this storage's copy.
proof fn lemma_is_perm_same(m: Seq<int>, n: int)
    requires fc::is_perm(m, n),
    ensures is_perm(m, n),
{
    assert forall|i: int| 0 <= i < n implies #[trigger] covered(m, i) by {
        assert(fc::covered(m, i));
    }
}

/// A row map column of `facts` is this storage's row map column.
proof fn lemma_map_same(tp: Seq<PartView>, n: int, cp: int, bp: int)
    requires fi::table_layout_ok(tp, n),
    ensures
        for_map(gs_at(tp, 1), tp[bp], tp[cp], n) == fc::for_map(fc::gs_at(tp, 1), tp[bp], tp[cp], n),
{
    lemma_layout(tp, n);
    let bs = u64s(tp[0])[1] as int;
    let a = for_map(gs_at(tp, 1), tp[bp], tp[cp], n);
    let b = fc::for_map(fc::gs_at(tp, 1), tp[bp], tp[cp], n);
    assert forall|j: int| 0 <= j < n implies a[j] == b[j] by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
    }
    assert(a =~= b);
}

/// The row map column property carries over.
proof fn lemma_perm_col(tp: Seq<PartView>, n: int, cp: int, bp: int)
    requires
        fi::table_layout_ok(tp, n),
        fc::perm_col_at(tp, 1, cp, bp, n),
    ensures
        perm_col_at(tp, 1, cp, bp, n),
{
    lemma_map_same(tp, n, cp, bp);
    lemma_is_perm_same(for_map(gs_at(tp, 1), tp[bp], tp[cp], n), n);
}

/// Column `cs` of this storage's stored rows is column `cf` of the stored rows of `facts`.
pub open spec fn col_from(srows: Seq<Row>, frows: Seq<Row>, cs: int, cf: int) -> bool {
    &&& srows.len() == frows.len()
    &&& forall|j: int| 0 <= j < srows.len() ==> #[trigger] srows[j][cs] == frows[j][cf]
}

/// An integer column carries over.
proof fn lemma_int_col(tp: Seq<PartView>, n: int, cp: int, bp: int, srows: Seq<Row>, frows: Seq<Row>, cs: int, cf: int)
    requires
        fi::table_layout_ok(tp, n),
        frows.len() == n,
        col_from(srows, frows, cs, cf),
        fc::int_col_at(tp, 1, cp, bp, frows, cf),
    ensures
        int_col_at(tp, 1, cp, bp, srows, cs),
{
    lemma_layout(tp, n);
    let bs = u64s(tp[0])[1] as int;
    assert(for_i64_shape(tp, 1, cp, bp, srows.len() as int));
    assert forall|j: int| 0 <= j < srows.len() implies #[trigger] srows[j][cs] == Val::Int(for_at(gs_at(tp, 1), tp[bp], tp[cp], j)) by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
        assert(frows[j][cf] == Val::Int(fc::for_at(fc::gs_at(tp, 1), tp[bp], tp[cp], j)));
    }
}

/// A numeric column carries over.
proof fn lemma_num_col(tp: Seq<PartView>, n: int, cp: int, bp: int, srows: Seq<Row>, frows: Seq<Row>, cs: int, cf: int, scale: nat)
    requires
        fi::table_layout_ok(tp, n),
        frows.len() == n,
        col_from(srows, frows, cs, cf),
        fc::num_col_at(tp, 1, cp, bp, frows, cf, scale),
    ensures
        num_col_at(tp, 1, cp, bp, srows, cs, scale),
{
    lemma_layout(tp, n);
    let bs = u64s(tp[0])[1] as int;
    assert(for_i64_shape(tp, 1, cp, bp, srows.len() as int));
    assert forall|j: int| 0 <= j < srows.len() implies #[trigger] srows[j][cs] == (Val::Num { coeff: for_at(gs_at(tp, 1), tp[bp], tp[cp], j), scale }) by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
        assert(frows[j][cf] == (Val::Num { coeff: fc::for_at(fc::gs_at(tp, 1), tp[bp], tp[cp], j), scale }));
    }
}

/// A date column carries over.
proof fn lemma_date_col(tp: Seq<PartView>, n: int, cp: int, bp: int, srows: Seq<Row>, frows: Seq<Row>, cs: int, cf: int)
    requires
        fi::table_layout_ok(tp, n),
        frows.len() == n,
        col_from(srows, frows, cs, cf),
        fc::date_col_at(tp, 1, cp, bp, frows, cf),
    ensures
        date_col_at(tp, 1, cp, bp, srows, cs),
{
    lemma_layout(tp, n);
    let bs = u64s(tp[0])[1] as int;
    assert(for_i64_shape(tp, 1, cp, bp, srows.len() as int));
    assert forall|j: int| 0 <= j < srows.len() implies #[trigger] srows[j][cs] == Val::Date(for_at(gs_at(tp, 1), tp[bp], tp[cp], j)) by {
        lemma_for_at_same(tp[1], n, bs, tp[bp], tp[cp], j);
        assert(frows[j][cf] == Val::Date(fc::for_at(fc::gs_at(tp, 1), tp[bp], tp[cp], j)));
    }
}

/// A key index of `facts` is one under this storage's copy of the definitions.
proof fn lemma_keyidx_same(kc: Seq<u32>, kb: Seq<i64>, ic: Seq<u32>, ib: Seq<u64>, bsize: int, kind: u64, n: int)
    requires fi::common::keyidx::keyidx_ok(kc, kb, ic, ib, bsize, kind, n),
    ensures sk::keyidx_ok(kc, kb, ic, ib, bsize, kind, n),
{
    if kind == 2 {
        let a = sk::idx_map(ic, ib, bsize, n);
        let b = fi::common::keyidx::idx_map(ic, ib, bsize, n);
        assert(a =~= b);
        lemma_is_perm_same(a, n);
    }
    if kind >= 1 {
        assert forall|r: int| 0 <= r < n - 1 implies #[trigger] sk::sorted_at(kc, kb, ic, ib, bsize, kind, r) by {
            assert(fi::common::keyidx::sorted_at(kc, kb, ic, ib, bsize, kind, r));
        }
    }
}

// ------------------------------------------------------------------------------------------------ the stored relations

/// The stored relations of this storage and of `facts`: lineitem on 2 and 15 columns, orders on 4 and 7.
proof fn lemma_rels(db: Database)
    ensures
        stored_relations(db)[0].len() == db.tables[0].len(),
        fd::stored_relations(db)[0].len() == db.tables[0].len(),
        stored_relations(db)[1].len() == db.tables[1].len(),
        fd::stored_relations(db)[1].len() == db.tables[1].len(),
        forall|i: int| 0 <= i < db.tables[0].len() ==> (#[trigger] stored_relations(db)[0][i]).len() == 2
            && stored_relations(db)[0][i][0] == fd::stored_relations(db)[0][i][0]
            && stored_relations(db)[0][i][1] == fd::stored_relations(db)[0][i][4],
        forall|i: int| 0 <= i < db.tables[1].len() ==> (#[trigger] stored_relations(db)[1][i]).len() == 4
            && stored_relations(db)[1][i][0] == fd::stored_relations(db)[1][i][0]
            && stored_relations(db)[1][i][1] == fd::stored_relations(db)[1][i][1]
            && stored_relations(db)[1][i][2] == fd::stored_relations(db)[1][i][3]
            && stored_relations(db)[1][i][3] == fd::stored_relations(db)[1][i][4],
{
    let t = db.tables[0];
    lemma_proj_all_index(t, stored_cols_t0());
    lemma_proj_all_index(t, fd::stored_cols_t0());
    assert forall|i: int| 0 <= i < t.len() implies (#[trigger] stored_relations(db)[0][i]).len() == 2
        && stored_relations(db)[0][i][0] == fd::stored_relations(db)[0][i][0]
        && stored_relations(db)[0][i][1] == fd::stored_relations(db)[0][i][4] by {
        assert(stored_relations(db)[0][i] == proj(t[i], stored_cols_t0()));
        assert(fd::stored_relations(db)[0][i] == proj(t[i], fd::stored_cols_t0()));
    }
    let u = db.tables[1];
    lemma_proj_all_index(u, stored_cols_t1());
    lemma_proj_all_index(u, fd::stored_cols_t1());
    assert forall|i: int| 0 <= i < u.len() implies (#[trigger] stored_relations(db)[1][i]).len() == 4
        && stored_relations(db)[1][i][0] == fd::stored_relations(db)[1][i][0]
        && stored_relations(db)[1][i][1] == fd::stored_relations(db)[1][i][1]
        && stored_relations(db)[1][i][2] == fd::stored_relations(db)[1][i][3]
        && stored_relations(db)[1][i][3] == fd::stored_relations(db)[1][i][4] by {
        assert(stored_relations(db)[1][i] == proj(u[i], stored_cols_t1()));
        assert(fd::stored_relations(db)[1][i] == proj(u[i], fd::stored_cols_t1()));
    }
}

// ------------------------------------------------------------------------------------------------ the tables

/// For every database bound to `facts`, its lineitem parts hold this storage's two lineitem columns, and the stored
/// rows of both agree on l_orderkey (column 0).
pub proof fn lemma_li_ok(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        lineitem_ok(ftl(sv), stored_relations(db)[0]),
        col_from(lineitem_rows(ftl(sv), stored_relations(db)[0]), fi::lineitem_rows(ftl(sv), fd::stored_relations(db)[0]), 0, 0),
{
    lemma_facts(sv, db);
    lemma_rels(db);
    let tp = ftl(sv);
    let frel = fd::stored_relations(db)[0];
    let srel = stored_relations(db)[0];
    let n = srel.len() as int;
    assert(fi::table_layout_ok(tp, n));
    lemma_layout(tp, n);
    lemma_map_same(tp, n, 2, 3);
    let m = lineitem_map(tp, n);
    assert(fc::perm_col_at(tp, 1, 2, 3, n));
    lemma_perm_col(tp, n, 2, 3);
    let srows = lineitem_rows(tp, srel);
    let frows = fi::lineitem_rows(tp, frel);
    assert(srows == stored_rows(srel, m));
    assert(frows == fc::stored_rows(frel, fi::lineitem_map(tp, n)));
    assert(frows.len() == n);
    assert forall|j: int| 0 <= j < n implies 0 <= #[trigger] m[j] < n by {
        assert(is_perm(m, n));
    }
    assert(col_from(srows, frows, 0, 0) && col_from(srows, frows, 1, 4)) by {
        assert forall|j: int| 0 <= j < n implies #[trigger] srows[j] == srel[m[j]] && frows[j] == frel[m[j]] by {}
    }
    assert(fi::lineitem_cols_ok(tp, frows));
    lemma_int_col(tp, n, LI_ORDERKEY_CODES as int, LI_ORDERKEY_BASE as int, srows, frows, 0, 0);
    lemma_num_col(tp, n, LI_QUANTITY_CODES as int, LI_QUANTITY_BASE as int, srows, frows, 1, 4, 2);
    assert(rows_width(srel, 2));
}

/// For every database bound to `facts`, its orders parts hold this storage's four orders columns and key index, and
/// the stored rows of both agree on o_orderkey (column 0).
pub proof fn lemma_or_ok(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        orders_ok(fto(sv), stored_relations(db)[1]),
        col_from(orders_rows(fto(sv), stored_relations(db)[1]), fi::orders_rows(fto(sv), fd::stored_relations(db)[1]), 0, 0),
{
    lemma_facts(sv, db);
    lemma_rels(db);
    let tp = fto(sv);
    let frel = fd::stored_relations(db)[1];
    let srel = stored_relations(db)[1];
    let n = srel.len() as int;
    assert(fi::table_layout_ok(tp, n));
    lemma_layout(tp, n);
    lemma_map_same(tp, n, 2, 3);
    let m = orders_map(tp, n);
    assert(fc::perm_col_at(tp, 1, 2, 3, n));
    lemma_perm_col(tp, n, 2, 3);
    let srows = orders_rows(tp, srel);
    let frows = fi::orders_rows(tp, frel);
    assert(srows == stored_rows(srel, m));
    assert(frows == fc::stored_rows(frel, fi::orders_map(tp, n)));
    assert(frows.len() == n);
    assert forall|j: int| 0 <= j < n implies 0 <= #[trigger] m[j] < n by {
        assert(is_perm(m, n));
    }
    assert(col_from(srows, frows, 0, 0) && col_from(srows, frows, 1, 1) && col_from(srows, frows, 2, 3)
        && col_from(srows, frows, 3, 4)) by {
        assert forall|j: int| 0 <= j < n implies #[trigger] srows[j] == srel[m[j]] && frows[j] == frel[m[j]] by {}
    }
    assert(fi::orders_cols_ok(tp, frows));
    lemma_int_col(tp, n, OR_ORDERKEY_CODES as int, OR_ORDERKEY_BASE as int, srows, frows, 0, 0);
    lemma_int_col(tp, n, OR_CUSTKEY_CODES as int, OR_CUSTKEY_BASE as int, srows, frows, 1, 1);
    lemma_num_col(tp, n, OR_TOTALPRICE_CODES as int, OR_TOTALPRICE_BASE as int, srows, frows, 2, 3, 2);
    lemma_date_col(tp, n, OR_ORDERDATE_CODES as int, OR_ORDERDATE_BASE as int, srows, frows, 3, 4);
    let kc = u32s(tp[OR_ORDERKEY_CODES as int]);
    let kb = i64s(tp[OR_ORDERKEY_BASE as int]);
    let ic = u32s(tp[OR_KEYIDX_CODES as int]);
    let ib = u64s(tp[OR_KEYIDX_BASE as int]);
    let bs = u64s(tp[OR_LAYOUT as int])[1] as int;
    let kind = u64s(tp[OR_KEYIDX_KIND as int])[0];
    assert(fi::common::keyidx::keyidx_ok(kc, kb, ic, ib, bs, kind, n));
    lemma_keyidx_same(kc, kb, ic, ib, bs, kind, n);
    if kind == 2 {
        assert forall|r: int| 0 <= r < n implies #[trigger] m[sk::fidx(ic, ib, bs, r)] == r by {
            assert(fi::orders_map(tp, n)[fi::common::keyidx::fidx(ic, ib, bs, r)] == r);
        }
    }
    assert(rows_width(srel, 4));
}

// ------------------------------------------------------------------------------------------------ the cluster flag

/// `first_key_from` reads only column 0, which both copies of the stored orders rows share.
proof fn lemma_first_key_same(so: Seq<Row>, fo: Seq<Row>, k: Val, i: int)
    requires col_from(so, fo, 0, 0), 0 <= i,
    ensures sc::first_key_from(so, k, i) == fi::cluster::first_key_from(fo, k, i),
    decreases so.len() - i,
{
    if i < so.len() && so[i][0] != k {
        lemma_first_key_same(so, fo, k, i + 1);
    }
}

/// The co-clustering of `facts` holds for this storage's stored rows.
pub proof fn lemma_cluster(sl: Seq<Row>, fl: Seq<Row>, so: Seq<Row>, fo: Seq<Row>)
    requires
        col_from(sl, fl, 0, 0),
        col_from(so, fo, 0, 0),
        fi::cluster::clustered(fl, fo),
    ensures
        sc::clustered(sl, so),
{
    assert forall|j: int| 0 <= j < sl.len() - 1 implies #[trigger] sc::cluster_step(sl, so, j) by {
        assert(fi::cluster::cluster_step(fl, fo, j));
        lemma_first_key_same(so, fo, sl[j][0], 0);
        lemma_first_key_same(so, fo, sl[j + 1][0], 0);
        assert(sl[j][0] == fl[j][0]);
        assert(sl[j + 1][0] == fl[j + 1][0]);
    }
}

/// The inherited parts satisfy `inherited_ok` for every database bound to `facts` (any parts after them).
pub proof fn lemma_inherited(sv: StoresView, db: Database, all: Seq<PartView>)
    requires
        sources_bound(sv, db),
        all.len() >= FACTS_PARTS,
        all.subrange(0, FACTS_PARTS as int) == sv.facts,
    ensures
        inherited_ok(all, stored_relations(db)),
{
    lemma_facts(sv, db);
    lemma_li_ok(sv, db);
    lemma_or_ok(sv, db);
    assert(li_tp(all) =~= ftl(sv)) by {
        assert forall|i: int| 0 <= i < LI_PARTS implies li_tp(all)[i] == ftl(sv)[i] by {
            assert(all.subrange(0, FACTS_PARTS as int)[i] == all[i]);
        }
    }
    assert(or_tp(all) =~= fto(sv)) by {
        assert forall|i: int| 0 <= i < OR_PARTS implies or_tp(all)[i] == fto(sv)[i] by {
            assert(all.subrange(0, FACTS_PARTS as int)[ORDERS_FIRST + i] == all[ORDERS_FIRST + i]);
        }
    }
    assert(all[FACTS_CLUSTER as int] == sv.facts[FACTS_CLUSTER as int]) by {
        assert(all.subrange(0, FACTS_PARTS as int)[FACTS_CLUSTER as int] == all[FACTS_CLUSTER as int]);
    }
    let rels = stored_relations(db);
    if u64s(all[FACTS_CLUSTER as int])[0] == 1 {
        lemma_cluster(lineitem_rows(li_tp(all), rels[0]), fi::lineitem_rows(ftl(sv), fd::stored_relations(db)[0]),
            orders_rows(or_tp(all), rels[1]), fi::orders_rows(fto(sv), fd::stored_relations(db)[1]));
    }
}

} // verus!
