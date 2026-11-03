//! What the builder reads from storage `facts`: the stored lineitem rows' l_orderkey, frame-of-reference coded
//! (U32 codes, I64 bases, uniform groups of `bs` rows). For a database bound to the source, `src_ok` states the part
//! shapes and that stored row `j` has l_orderkey `kb[j / bs] + kc[j]` (inside `i64`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::sources::StoresView;
use crate::gendb_entry::sources_bound;
use crate::spec::value::{Database, Row, Val};
use crate::spec::int::{int_in_range, IntKind};
use crate::link::source::lemma_proj_all_index;
use crate::stores::facts::interface as F;
use crate::stores::facts::interface::common::colfmt as FC;
use crate::stores::facts::interface::common::read as FR;
use crate::stores::facts::interface::common::keyidx as FK;
use crate::stores::facts::declaration as FD;
use crate::stores::li_ordruns::declaration as D;
use crate::stores::li_ordruns::interface::*;

verus! {

/// The lineitem parts of facts.
pub open spec fn li_tp(fp: Seq<PartView>) -> Seq<PartView> {
    fp.subrange(F::LINEITEM_FIRST as int, (F::LINEITEM_FIRST + F::LI_PARTS) as int)
}

/// Rows and block size of the stored lineitem rows.
pub open spec fn n_rows(fp: Seq<PartView>) -> int {
    FC::u64s(fp[F::LI_LAYOUT as int])[0] as int
}

pub open spec fn bsize(fp: Seq<PartView>) -> int {
    FC::u64s(fp[F::LI_LAYOUT as int])[1] as int
}

/// l_orderkey of stored lineitem row `j` (codes and bases of facts).
pub open spec fn key_at(fp: Seq<PartView>, j: int) -> int {
    FC::i64s(fp[F::LI_ORDERKEY_BASE as int])[j / bsize(fp)] + FC::u32s(fp[F::LI_ORDERKEY_CODES as int])[j]
}

/// The stored lineitem rows of a database bound to facts.
pub open spec fn src_rows(fp: Seq<PartView>, rels: Seq<Seq<Row>>) -> Seq<Row> {
    F::lineitem_rows(li_tp(fp), rels[0])
}

/// What the builder uses: part shapes and the stored l_orderkey of every stored lineitem row.
pub open spec fn src_ok(fp: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    let n = n_rows(fp);
    let bs = bsize(fp);
    &&& fp.len() == F::FACTS_PARTS
    &&& fp[F::LI_LAYOUT as int] is U64 && FC::u64s(fp[F::LI_LAYOUT as int]).len() == 2
    &&& bs >= 1
    &&& fp[F::LI_ORDERKEY_CODES as int] is U32 && FC::u32s(fp[F::LI_ORDERKEY_CODES as int]).len() == n
    &&& fp[F::LI_ORDERKEY_BASE as int] is I64 && FC::i64s(fp[F::LI_ORDERKEY_BASE as int]).len() * bs >= n
    &&& src_rows(fp, rels).len() == n
    &&& forall|j: int| 0 <= j < n ==> #[trigger] src_rows(fp, rels)[j][0] == Val::Int(key_at(fp, j))
    &&& forall|j: int| 0 <= j < n ==> i64::MIN <= #[trigger] key_at(fp, j) <= i64::MAX
}

/// The lineitem parts are the first parts of facts.
proof fn lemma_tp(fp: Seq<PartView>)
    requires fp.len() == F::FACTS_PARTS,
    ensures forall|k: int| 0 <= k < F::LI_PARTS ==> #[trigger] li_tp(fp)[k] == fp[k],
{
}

/// facts' `represents` gives the lineitem table conjunct.
proof fn lemma_li_ok(fp: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires F::represents(fp, rels),
    ensures F::lineitem_ok(li_tp(fp), rels[0]), fp.len() == F::FACTS_PARTS,
{
    hide(F::lineitem_ok);
    hide(F::orders_ok);
}

/// The lineitem conjunct gives the layout and the l_orderkey column of the stored rows.
proof fn lemma_key_col(tp: Seq<PartView>, rel: Seq<Row>)
    requires F::lineitem_ok(tp, rel),
    ensures ({
        let n = rel.len() as int;
        let bs = FC::u64s(tp[F::LI_LAYOUT as int])[1] as int;
        let rows = F::lineitem_rows(tp, rel);
        &&& tp.len() == F::LI_PARTS
        &&& tp[F::LI_LAYOUT as int] is U64 && FC::u64s(tp[F::LI_LAYOUT as int]).len() == 2
        &&& FC::u64s(tp[F::LI_LAYOUT as int])[0] == n
        &&& FC::groups_part_ok(tp[F::LI_GROUPS as int], n, bs)
        &&& tp[F::LI_ORDERKEY_CODES as int] is U32
        &&& FC::for_i64_shape(tp, F::LI_GROUPS as int, F::LI_ORDERKEY_CODES as int, F::LI_ORDERKEY_BASE as int, n)
        &&& rows.len() == n
        &&& FC::int_col(rows, 0, FC::u64s(tp[F::LI_GROUPS as int]), tp[F::LI_ORDERKEY_BASE as int], tp[F::LI_ORDERKEY_CODES as int])
        &&& FC::is_perm(F::lineitem_map(tp, n), n)
        &&& rows == FC::stored_rows(rel, F::lineitem_map(tp, n))
    }),
{
    hide(FC::num_col_at);
    hide(FC::dict_col_at);
    hide(FC::date_col_at);
    hide(FC::zone_at);
    hide(FK::keyidx_ok);
    let n = rel.len() as int;
    let rows = F::lineitem_rows(tp, rel);
    assert(F::lineitem_cols_ok(tp, rows));
    assert(FC::int_col_at(tp, F::LI_GROUPS as int, F::LI_ORDERKEY_CODES as int, F::LI_ORDERKEY_BASE as int, rows, 0));
}

/// Stored l_orderkey values are Int8 values of the relation.
proof fn lemma_key_range(db: Database, rel: Seq<Row>, rows: Seq<Row>, m: Seq<int>, j: int)
    requires
        db.schema == crate::schema::schema_spec(),
        crate::spec::typing::db_wf(db),
        rel == FD::stored_relations(db)[0],
        FC::is_perm(m, rel.len() as int),
        rows == FC::stored_rows(rel, m),
        0 <= j < rel.len(),
    ensures
        rows[j][0] is Int ==> int_in_range(IntKind::Int8, rows[j][0]->Int_0),
{
    FD::lemma_stored_relations(db);
    let r = m[j];
    assert(0 <= r < rel.len());
    assert(rows[j] == rel[r]);
    assert(crate::spec::typing::value_in_column(rel[r][0], FD::stored_columns_t0()[0]));
}

/// Stored row `j`'s l_orderkey is `key_at(fp, j)`, inside `i64`.
proof fn lemma_rows_keys_at(fp: Seq<PartView>, db: Database, rel: Seq<Row>, rows: Seq<Row>, m: Seq<int>, j: int)
    requires
        db.schema == crate::schema::schema_spec(),
        crate::spec::typing::db_wf(db),
        rel == FD::stored_relations(db)[0],
        FC::is_perm(m, rel.len() as int),
        rows == FC::stored_rows(rel, m),
        rows.len() == rel.len(),
        FC::groups_part_ok(fp[F::LI_GROUPS as int], rel.len() as int, bsize(fp)),
        FC::int_col(rows, 0, FC::u64s(fp[F::LI_GROUPS as int]), fp[F::LI_ORDERKEY_BASE as int], fp[F::LI_ORDERKEY_CODES as int]),
        fp[F::LI_ORDERKEY_CODES as int] is U32,
        fp[F::LI_ORDERKEY_BASE as int] is I64,
        0 <= j < rel.len(),
    ensures
        rows[j][0] == Val::Int(key_at(fp, j)),
        i64::MIN <= key_at(fp, j) <= i64::MAX,
{
    let gp = fp[F::LI_GROUPS as int];
    let (kcp, kbp) = (fp[F::LI_ORDERKEY_CODES as int], fp[F::LI_ORDERKEY_BASE as int]);
    FR::lemma_for_row(gp, rel.len() as int, bsize(fp), kbp, kcp, j);
    assert(rows[j][0] == Val::Int(FC::for_at(FC::u64s(gp), kbp, kcp, j)));
    lemma_key_range(db, rel, rows, m, j);
}

/// The stored l_orderkey of every stored lineitem row, from the lineitem conjunct.
proof fn lemma_rows_keys(fp: Seq<PartView>, db: Database)
    requires
        db.schema == crate::schema::schema_spec(),
        crate::spec::typing::db_wf(db),
        fp.len() == F::FACTS_PARTS,
        F::lineitem_ok(li_tp(fp), FD::stored_relations(db)[0]),
    ensures
        src_ok(fp, FD::stored_relations(db)),
{
    hide(F::lineitem_ok);
    hide(F::lineitem_rows);
    hide(FC::stored_rows);
    hide(FC::is_perm);
    hide(FC::int_col);
    let rels = FD::stored_relations(db);
    let tp = li_tp(fp);
    lemma_tp(fp);
    let rel = rels[0];
    let n = rel.len() as int;
    lemma_key_col(tp, rel);
    let rows = F::lineitem_rows(tp, rel);
    let m = F::lineitem_map(tp, n);
    let gp = tp[F::LI_GROUPS as int];
    let bs = FC::u64s(tp[F::LI_LAYOUT as int])[1] as int;
    assert(bsize(fp) == bs);
    assert(n_rows(fp) == n);
    assert(FC::u64s(gp).len() == FC::nblocks_of(n, bs) + 1);
    FC::lemma_nblocks(n, bs);
    assert forall|j: int| 0 <= j < n implies #[trigger] rows[j][0] == Val::Int(key_at(fp, j)) by {
        lemma_rows_keys_at(fp, db, rel, rows, m, j);
    }
    assert forall|j: int| 0 <= j < n implies i64::MIN <= #[trigger] key_at(fp, j) <= i64::MAX by {
        lemma_rows_keys_at(fp, db, rel, rows, m, j);
    }
    assert(src_rows(fp, rels) == rows);
    assert(FC::i64s(fp[F::LI_ORDERKEY_BASE as int]).len() == FC::nblocks_of(n, bs));
}

/// For a database bound to `facts`: facts represents this storage's relations, and `src_ok` holds.
pub proof fn lemma_src(sv: StoresView, db: Database)
    requires sources_bound(sv, db),
    ensures
        D::stored_relations(db) == FD::stored_relations(db),
        F::represents(sv.facts, D::stored_relations(db)),
        src_ok(sv.facts, D::stored_relations(db)),
{
    hide(F::represents);
    hide(F::lineitem_ok);
    hide(src_ok);
    let fp = sv.facts;
    let rels = FD::stored_relations(db);
    assert(D::stored_relations(db) =~= rels);
    assert(F::represents(fp, rels));
    lemma_li_ok(fp, rels);
    lemma_rows_keys(fp, db);
}

} // verus!
