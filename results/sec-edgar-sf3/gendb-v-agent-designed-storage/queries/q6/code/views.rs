//! The stored data seen through the three storages' parts (`StoresView`), at the positions the algorithm reads:
//! stored `num` rows `i` (in stored order), `sub` rows `j` (canonical order) and stored `pre` rows `l`. A joined
//! triple `(i, j, l)` qualifies (`pq`) and has a group key (`pkey`) as a function of the parts only; for every
//! database bound to the parts, the stored rows' concatenation `SN(i) ++ S(j) ++ SP(l)` qualifies and has its key
//! exactly as the parts say (`lemma_joined_row`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::typing::db_wf;
use crate::schema::schema_spec;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::layout::PartView;
use crate::link::query::{proj, proj_all};
use crate::stores::num::interface as ni;
use crate::stores::pre::interface as pi;
use crate::stores::sub::interface as si;
use crate::stores::num::interface::common::runs as nruns;
use crate::stores::pre::interface::common::runs as pruns;
use crate::stores::num::interface::common::text::{text_entry, u64_part, u8_part};
use crate::stores::num::interface::common::cols::{i128_part, i32_part};
use crate::stores::pre::interface::common::cols::u64s as pu64s;
use crate::agent::meaning::*;

verus! {

// ------------------------------------------------------------------------------------------------ num (stored order)

pub open spec fn n_count(sv: StoresView) -> int {
    ni::row_count(sv.num)
}

pub open spec fn n_start(sv: StoresView) -> Seq<u64> {
    ni::u64s(sv.num, ni::P_RUN_START)
}

/// The run of stored `num` row `i`.
pub open spec fn n_run(sv: StoresView, i: int) -> int {
    nruns::run_of(n_start(sv), ni::run_count(sv.num), i)
}

pub open spec fn n_adsh(sv: StoresView, i: int) -> Seq<u8> {
    ni::run_adsh_of(sv.num, n_run(sv, i))
}

pub open spec fn n_uom(sv: StoresView, i: int) -> Seq<u8> {
    ni::run_uom_of(sv.num, n_run(sv, i))
}

pub open spec fn n_tag(sv: StoresView, i: int) -> Seq<u8> {
    ni::tag_of(sv.num, i)
}

pub open spec fn n_ver(sv: StoresView, i: int) -> Seq<u8> {
    ni::version_of(sv.num, i)
}

pub open spec fn n_tv(sv: StoresView, i: int) -> u64 {
    ni::u64s(sv.num, ni::P_TV)[i]
}

pub open spec fn n_val(sv: StoresView, i: int) -> int {
    i128_part(sv.num[ni::P_VALUE as int])[i] as int
}

// ------------------------------------------------------------------------------------------------ pre (stored order)

pub open spec fn p_count(sv: StoresView) -> int {
    pi::row_count(sv.pre)
}

pub open spec fn p_start(sv: StoresView) -> Seq<u64> {
    pu64s(sv.pre, pi::P_SUB_START)
}

/// The sub-run of stored `pre` row `l`.
pub open spec fn p_sub(sv: StoresView, l: int) -> int {
    pruns::run_of(p_start(sv), pi::sub_count(sv.pre), l)
}

pub open spec fn p_adsh(sv: StoresView, l: int) -> Seq<u8> {
    pi::sub_adsh_of(sv.pre, p_sub(sv, l))
}

pub open spec fn sub_stmt(sv: StoresView, s: int) -> Val {
    pi::group_stmt_of(sv.pre, pu64s(sv.pre, pi::P_SUB_GROUP)[s] as int)
}

pub open spec fn p_stmt_val(sv: StoresView, l: int) -> Val {
    sub_stmt(sv, p_sub(sv, l))
}

pub open spec fn p_tag(sv: StoresView, l: int) -> Seq<u8> {
    pi::tag_of(sv.pre, l)
}

pub open spec fn p_ver(sv: StoresView, l: int) -> Seq<u8> {
    pi::version_of(sv.pre, l)
}

pub open spec fn p_plabel(sv: StoresView, l: int) -> Val {
    crate::stores::pre::interface::common::cols::coded_text_at(sv.pre, pi::P_PLABEL_CODES, pi::P_PLABEL_VALID as int,
        pi::P_PLABEL_OFF, l)
}

// ------------------------------------------------------------------------------------------------ sub (canonical)

pub open spec fn s_count(sv: StoresView) -> int {
    si::row_count(sv.sub)
}

pub open spec fn s_adsh(sv: StoresView, j: int) -> Seq<u8> {
    si::adsh_bytes(sv.sub, j)
}

pub open spec fn s_name(sv: StoresView, j: int) -> Val {
    crate::stores::sub::interface::common::cols::dict_text_at(sv.sub, si::P_NAME_CODES as int,
        si::P_NAME_DICT_OFF as int, si::P_NAME_DICT_BYTES as int, j)
}

pub open spec fn s_fy(sv: StoresView, j: int) -> Val {
    crate::stores::sub::interface::common::cols::or_null_at(sv.sub, si::P_FY_VALID as int, j,
        crate::stores::sub::interface::common::cols::int_at(sv.sub, si::P_FY as int, j))
}

// ------------------------------------------------------------------------------------------------ joined triples

/// Triple `(i, j, l)` qualifies: the join and WHERE conditions on the stored values.
pub open spec fn pq(sv: StoresView, ps: Seq<Literal>, i: int, j: int, l: int) -> bool {
    &&& n_adsh(sv, i) == s_adsh(sv, j)
    &&& n_adsh(sv, i) == p_adsh(sv, l)
    &&& n_tag(sv, i) == p_tag(sv, l)
    &&& n_ver(sv, i) == p_ver(sv, l)
    &&& n_uom(sv, i) == p_uom(ps)
    &&& p_stmt_val(sv, l) == Val::Text(p_stmt(ps))
    &&& s_fy(sv, j) == Val::Int(p_fy(ps))
}

/// The group key of triple `(i, j, l)`.
pub open spec fn pkey(sv: StoresView, i: int, j: int, l: int) -> Row {
    seq![s_name(sv, j), p_stmt_val(sv, l), Val::Text(n_tag(sv, i)), p_plabel(sv, l)]
}

// ------------------------------------------------------------------------------------------------ bound databases

/// The parts of the three storages represent `db`'s stored relations (part of `bound_db`).
pub open spec fn reps(sv: StoresView, db: Database) -> bool {
    &&& ni::represents(sv.num, crate::stores::num::declaration::stored_relations(db))
    &&& si::represents(sv.sub, crate::stores::sub::declaration::stored_relations(db))
    &&& pi::represents(sv.pre, crate::stores::pre::declaration::stored_relations(db))
}

pub open spec fn base(sv: StoresView, db: Database) -> bool {
    &&& db.schema == schema_spec()
    &&& db_wf(db)
    &&& reps(sv, db)
}

/// Stored `num` row `i` (the canonical row stored at position `i`).
pub open spec fn sn(sv: StoresView, db: Database, i: int) -> Row {
    ni::stored_row(sv.num, crate::stores::num::declaration::stored_relations(db), i)
}

pub open spec fn sp(sv: StoresView, db: Database, l: int) -> Row {
    pi::stored_row(sv.pre, crate::stores::pre::declaration::stored_relations(db), l)
}

/// Projecting rows of `k` values on all `k` columns keeps them.
pub proof fn lemma_proj_all_full(rows: Seq<Row>, cols: Seq<nat>, k: nat)
    requires
        cols.len() == k,
        forall|c: int| 0 <= c < k ==> #[trigger] cols[c] == c,
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == k,
    ensures proj_all(rows, cols) == rows,
{
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] proj_all(rows, cols)[i] == rows[i] by {
        assert(proj(rows[i], cols) =~= rows[i]);
    }
    assert(proj_all(rows, cols) =~= rows);
}

/// The stored relations of the three storages are the tables themselves.
pub proof fn lemma_stored_tables(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        crate::stores::num::declaration::stored_relations(db)[0] == db.tables[1],
        crate::stores::sub::declaration::stored_relations(db)[0] == db.tables[0],
        crate::stores::pre::declaration::stored_relations(db)[0] == db.tables[3],
        tables_ok(db),
{
    lemma_tables_ok(db);
    let cn = crate::stores::num::declaration::stored_cols_t0();
    assert forall|c: int| 0 <= c < 9 implies #[trigger] cn[c] == c by {
        if c == 0 {} else if c == 1 {} else if c == 2 {} else if c == 3 {} else if c == 4 {}
        else if c == 5 {} else if c == 6 {} else if c == 7 {} else {}
    }
    assert forall|i: int| 0 <= i < db.tables[1].len() implies (#[trigger] db.tables[1][i]).len() == 9 by {
        assert(num_ok(db.tables[1][i]));
    }
    lemma_proj_all_full(db.tables[1], cn, 9);
    let cs = crate::stores::sub::declaration::stored_cols_t0();
    assert forall|c: int| 0 <= c < 20 implies #[trigger] cs[c] == c by {
        if c == 0 {} else if c == 1 {} else if c == 2 {} else if c == 3 {} else if c == 4 {}
        else if c == 5 {} else if c == 6 {} else if c == 7 {} else if c == 8 {} else if c == 9 {}
        else if c == 10 {} else if c == 11 {} else if c == 12 {} else if c == 13 {} else if c == 14 {}
        else if c == 15 {} else if c == 16 {} else if c == 17 {} else if c == 18 {} else {}
    }
    assert forall|i: int| 0 <= i < db.tables[0].len() implies (#[trigger] db.tables[0][i]).len() == 20 by {
        assert(sub_ok(db.tables[0][i]));
    }
    lemma_proj_all_full(db.tables[0], cs, 20);
    let cp = crate::stores::pre::declaration::stored_cols_t0();
    assert forall|c: int| 0 <= c < 10 implies #[trigger] cp[c] == c by {
        if c == 0 {} else if c == 1 {} else if c == 2 {} else if c == 3 {} else if c == 4 {}
        else if c == 5 {} else if c == 6 {} else if c == 7 {} else if c == 8 {} else {}
    }
    assert forall|i: int| 0 <= i < db.tables[3].len() implies (#[trigger] db.tables[3][i]).len() == 10 by {
        assert(pre_ok(db.tables[3][i]));
    }
    lemma_proj_all_full(db.tables[3], cp, 10);
}

/// The values of stored `num` row `i` that the query reads.
pub proof fn lemma_num_row(sv: StoresView, db: Database, i: int)
    requires base(sv, db), 0 <= i < n_count(sv),
    ensures
        sn(sv, db, i).len() == 9,
        sn(sv, db, i)[0] == Val::Text(n_adsh(sv, i)),
        sn(sv, db, i)[1] == Val::Text(n_tag(sv, i)),
        sn(sv, db, i)[2] == Val::Text(n_ver(sv, i)),
        sn(sv, db, i)[5] == Val::Text(n_uom(sv, i)),
        sn(sv, db, i)[7] == (Val::Num { coeff: n_val(sv, i), scale: 4 }),
{
    let rels = crate::stores::num::declaration::stored_relations(db);
    let parts = sv.num;
    assert(ni::stored_cols_ok(parts, ni::stored_row(parts, rels, i), i));
    let start = n_start(sv);
    nruns::lemma_run_of(start, ni::run_count(parts), ni::row_count(parts), i);
    let r = n_run(sv, i);
    assert(ni::run_cols_ok(parts, ni::stored_row(parts, rels, i), r));
}

/// The values of stored `pre` row `l` that the query reads.
pub proof fn lemma_pre_row(sv: StoresView, db: Database, l: int)
    requires base(sv, db), 0 <= l < p_count(sv),
    ensures
        sp(sv, db, l).len() == 10,
        sp(sv, db, l)[0] == Val::Text(p_adsh(sv, l)),
        sp(sv, db, l)[3] == p_stmt_val(sv, l),
        sp(sv, db, l)[6] == Val::Text(p_tag(sv, l)),
        sp(sv, db, l)[7] == Val::Text(p_ver(sv, l)),
        sp(sv, db, l)[8] == p_plabel(sv, l),
{
    let rels = crate::stores::pre::declaration::stored_relations(db);
    let parts = sv.pre;
    assert(pi::stored_cols_ok(parts, pi::stored_row(parts, rels, l), l));
    let start = p_start(sv);
    pruns::lemma_run_of(start, pi::sub_count(parts), pi::row_count(parts), l);
    let s = p_sub(sv, l);
    assert(pi::sub_cols_ok(parts, pi::stored_row(parts, rels, l), s));
}

/// The values of `sub` row `j` that the query reads.
pub proof fn lemma_sub_row(sv: StoresView, db: Database, j: int)
    requires base(sv, db), 0 <= j < s_count(sv),
    ensures
        db.tables[0][j].len() == 20,
        db.tables[0][j][0] == Val::Text(s_adsh(sv, j)),
        db.tables[0][j][2] == s_name(sv, j),
        db.tables[0][j][10] == s_fy(sv, j),
{
    lemma_stored_tables(db);
    let rels = crate::stores::sub::declaration::stored_relations(db);
    assert(si::sub_row_ok(sv.sub, rels[0][j], j));
}

/// A stored joined triple qualifies, and has its key and SUM argument, as the parts say.
pub proof fn lemma_joined_row(sv: StoresView, db: Database, ps: Seq<Literal>, i: int, j: int, l: int)
    requires base(sv, db), 0 <= i < n_count(sv), 0 <= j < s_count(sv), 0 <= l < p_count(sv),
    ensures ({
        let x = sn(sv, db, i) + db.tables[0][j] + sp(sv, db, l);
        &&& qual(ps, x) == pq(sv, ps, i, j, l)
        &&& key_of(x) == pkey(sv, i, j, l)
        &&& coeff_of(x[7]) == n_val(sv, i)
    }),
{
    lemma_num_row(sv, db, i);
    lemma_pre_row(sv, db, l);
    lemma_sub_row(sv, db, j);
    let (a, b, c) = (sn(sv, db, i), db.tables[0][j], sp(sv, db, l));
    let x = a + b + c;
    assert(x.len() == 39);
    assert(x[0] == a[0] && x[1] == a[1] && x[2] == a[2] && x[5] == a[5] && x[7] == a[7]);
    assert(x[9] == b[0] && x[11] == b[2] && x[19] == b[10]);
    assert(x[29] == c[0] && x[32] == c[3] && x[35] == c[6] && x[36] == c[7] && x[37] == c[8]);
    assert(key_of(x) =~= pkey(sv, i, j, l));
}

} // verus!
