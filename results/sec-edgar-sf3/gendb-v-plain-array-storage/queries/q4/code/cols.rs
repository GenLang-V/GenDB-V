//! The ghost context of one call (the parts of the four flat storages, their row counts and the binding), the
//! column values the query reads (`n_*` num, `s_*` sub, `t_*` tag, `p_*` pre), the whole-part reads (`Cols`),
//! and the database facts every bound database gives (`lemma_bound`): its tables are the stored rows, and the
//! primary keys of `sub` (adsh) and `tag` (tag, version) identify rows.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::link::query::{text_at, text_wf, TextCol, TextView, proj};
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::IntKind;
use crate::spec::constraints::*;
use crate::spec::types::Constraint;
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::link::source::lemma_proj_all_index;
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_tag::interface as ti;
use crate::stores::flat_pre::interface as pi;

verus! {

/// The ghost context: parts and row counts of `num` (`np`, `n`), `sub` (`sp`, `m`), `tag` (`tp`, `nt`), `pre`
/// (`pp`, `npre`), and the binding `$1 = uom`, `$2 = stmt`, `$3 = lo`, `$4 = hi`.
pub ghost struct Ctx {
    pub np: Seq<PartView>,
    pub n: int,
    pub sp: Seq<PartView>,
    pub m: int,
    pub tp: Seq<PartView>,
    pub nt: int,
    pub pp: Seq<PartView>,
    pub npre: int,
    pub uom: Seq<u8>,
    pub stmt: Seq<u8>,
    pub lo: int,
    pub hi: int,
}

/// The parts are well formed for their row counts, and the keys of `sub` and `tag` identify rows (hidden: use
/// `lemma_views` and `lemma_keys`).
#[verifier::opaque]
pub open spec fn ctx_ok(c: Ctx) -> bool {
    &&& ni::parts_wf(c.np, c.n)
    &&& si::parts_wf(c.sp, c.m)
    &&& ti::parts_wf(c.tp, c.nt)
    &&& pi::parts_wf(c.pp, c.npre)
    &&& sub_key(c)
    &&& tag_key(c)
}

// ------------------------------------------------------------------------------------------------ column views

pub open spec fn n_uom_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::UOM_OFFSETS as int, ni::UOM_BYTES as int) }
pub open spec fn n_adsh_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int) }
pub open spec fn n_tag_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::TAG_OFFSETS as int, ni::TAG_BYTES as int) }
pub open spec fn n_ver_v(c: Ctx) -> TextView { ni::text_view(c.np, ni::VERSION_OFFSETS as int, ni::VERSION_BYTES as int) }
pub open spec fn n_val_s(c: Ctx) -> Seq<i128> { ni::i128s(c.np[ni::VALUE as int]) }
pub open spec fn s_adsh_v(c: Ctx) -> TextView { si::text_view(c.sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int) }
pub open spec fn s_cik_s(c: Ctx) -> Seq<i32> { si::i32s(c.sp[si::CIK as int]) }
pub open spec fn s_sic_s(c: Ctx) -> Seq<i32> { si::i32s(c.sp[si::SIC as int]) }
pub open spec fn s_sicv_s(c: Ctx) -> Seq<u8> { si::u8s(c.sp[si::SIC_VALIDITY as int]) }
pub open spec fn t_tag_v(c: Ctx) -> TextView { ti::text_view(c.tp, ti::TAG_OFFSETS as int, ti::TAG_BYTES as int) }
pub open spec fn t_ver_v(c: Ctx) -> TextView { ti::text_view(c.tp, ti::VERSION_OFFSETS as int, ti::VERSION_BYTES as int) }
pub open spec fn t_abs_s(c: Ctx) -> Seq<i32> { ti::i32s(c.tp[ti::ABSTRACT as int]) }
pub open spec fn t_label_v(c: Ctx) -> TextView { ti::text_view(c.tp, ti::TLABEL_OFFSETS as int, ti::TLABEL_BYTES as int) }
pub open spec fn t_labelv_s(c: Ctx) -> Seq<u8> { ti::u8s(c.tp[ti::TLABEL_VALIDITY as int]) }
pub open spec fn p_adsh_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::ADSH_OFFSETS as int, pi::ADSH_BYTES as int) }
pub open spec fn p_stmt_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::STMT_OFFSETS as int, pi::STMT_BYTES as int) }
pub open spec fn p_stmtv_s(c: Ctx) -> Seq<u8> { pi::u8s(c.pp[pi::STMT_VALIDITY as int]) }
pub open spec fn p_tag_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::TAG_OFFSETS as int, pi::TAG_BYTES as int) }
pub open spec fn p_ver_v(c: Ctx) -> TextView { pi::text_view(c.pp, pi::VERSION_OFFSETS as int, pi::VERSION_BYTES as int) }

// ------------------------------------------------------------------------------------------------ cell values

pub open spec fn n_uom(c: Ctx, i: int) -> Seq<u8> { text_at(n_uom_v(c), i) }
pub open spec fn n_adsh(c: Ctx, i: int) -> Seq<u8> { text_at(n_adsh_v(c), i) }
pub open spec fn n_tag(c: Ctx, i: int) -> Seq<u8> { text_at(n_tag_v(c), i) }
pub open spec fn n_ver(c: Ctx, i: int) -> Seq<u8> { text_at(n_ver_v(c), i) }
/// The `value` coefficient of num row `i` (scale 4).
pub open spec fn n_val(c: Ctx, i: int) -> int { n_val_s(c)[i] as int }
pub open spec fn s_adsh(c: Ctx, s: int) -> Seq<u8> { text_at(s_adsh_v(c), s) }
pub open spec fn s_cik(c: Ctx, s: int) -> int { s_cik_s(c)[s] as int }
pub open spec fn s_sic_valid(c: Ctx, s: int) -> bool { s_sicv_s(c)[s] != 0 }
pub open spec fn s_sic(c: Ctx, s: int) -> int { s_sic_s(c)[s] as int }
pub open spec fn t_tag(c: Ctx, k: int) -> Seq<u8> { text_at(t_tag_v(c), k) }
pub open spec fn t_ver(c: Ctx, k: int) -> Seq<u8> { text_at(t_ver_v(c), k) }
pub open spec fn t_abs(c: Ctx, k: int) -> int { t_abs_s(c)[k] as int }
/// `tag.tlabel` of tag row `k` as a value (NULL or text).
pub open spec fn t_label(c: Ctx, k: int) -> Val {
    if t_labelv_s(c)[k] == 0 { Val::Null } else { Val::Text(text_at(t_label_v(c), k)) }
}
pub open spec fn p_adsh(c: Ctx, l: int) -> Seq<u8> { text_at(p_adsh_v(c), l) }
pub open spec fn p_stmt_valid(c: Ctx, l: int) -> bool { p_stmtv_s(c)[l] != 0 }
pub open spec fn p_stmt(c: Ctx, l: int) -> Seq<u8> { text_at(p_stmt_v(c), l) }
pub open spec fn p_tag(c: Ctx, l: int) -> Seq<u8> { text_at(p_tag_v(c), l) }
pub open spec fn p_ver(c: Ctx, l: int) -> Seq<u8> { text_at(p_ver_v(c), l) }

/// `sub.adsh` identifies sub rows.
pub open spec fn sub_key(c: Ctx) -> bool {
    forall|s1: int, s2: int| 0 <= s1 < c.m && 0 <= s2 < c.m && #[trigger] s_adsh(c, s1) == #[trigger] s_adsh(c, s2)
        ==> s1 == s2
}

/// `(tag.tag, tag.version)` identifies tag rows.
pub open spec fn tag_key(c: Ctx) -> bool {
    forall|k1: int, k2: int| 0 <= k1 < c.nt && 0 <= k2 < c.nt && #[trigger] t_tag(c, k1) == #[trigger] t_tag(c, k2)
        && t_ver(c, k1) == t_ver(c, k2) ==> k1 == k2
}

// ------------------------------------------------------------------------------------------------ table rows

/// Stored row `i` of num, sub, tag and pre (hidden: the cell lemmas below state what the proofs use).
#[verifier::opaque]
pub open spec fn nrow(c: Ctx, i: int) -> Row { ni::row_at(c.np, i) }
#[verifier::opaque]
pub open spec fn srow(c: Ctx, s: int) -> Row { si::row_at(c.sp, s) }
#[verifier::opaque]
pub open spec fn trow(c: Ctx, k: int) -> Row { ti::row_at(c.tp, k) }
#[verifier::opaque]
pub open spec fn prow(c: Ctx, l: int) -> Row { pi::row_at(c.pp, l) }

/// The cells of the four tables' rows that the statement reads.
pub proof fn lemma_cells(c: Ctx, i: int, s: int, k: int, l: int)
    ensures
        nrow(c, i).len() == 9,
        nrow(c, i)[0] == Val::Text(n_adsh(c, i)),
        nrow(c, i)[1] == Val::Text(n_tag(c, i)),
        nrow(c, i)[2] == Val::Text(n_ver(c, i)),
        nrow(c, i)[5] == Val::Text(n_uom(c, i)),
        nrow(c, i)[7] == (Val::Num { coeff: n_val(c, i), scale: 4 }),
        srow(c, s).len() == 20,
        srow(c, s)[0] == Val::Text(s_adsh(c, s)),
        srow(c, s)[1] == Val::Int(s_cik(c, s)),
        srow(c, s)[3] == (if s_sic_valid(c, s) { Val::Int(s_sic(c, s)) } else { Val::Null }),
        trow(c, k).len() == 9,
        trow(c, k)[0] == Val::Text(t_tag(c, k)),
        trow(c, k)[1] == Val::Text(t_ver(c, k)),
        trow(c, k)[3] == Val::Int(t_abs(c, k)),
        trow(c, k)[7] == t_label(c, k),
        prow(c, l).len() == 10,
        prow(c, l)[0] == Val::Text(p_adsh(c, l)),
        prow(c, l)[3] == (if p_stmt_valid(c, l) { Val::Text(p_stmt(c, l)) } else { Val::Null }),
        prow(c, l)[6] == Val::Text(p_tag(c, l)),
        prow(c, l)[7] == Val::Text(p_ver(c, l)),
{
    reveal(nrow);
    reveal(srow);
    reveal(trow);
    reveal(prow);
}

/// The database's tables are the stored rows (and it has the four tables of the schema).
pub open spec fn db_ok(db: Database, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& db.tables.len() == 4
    &&& db.tables[1].len() == c.n
    &&& db.tables[0].len() == c.m
    &&& db.tables[2].len() == c.nt
    &&& db.tables[3].len() == c.npre
    &&& forall|i: int| 0 <= i < c.n ==> #[trigger] db.tables[1][i] == nrow(c, i)
    &&& forall|s: int| 0 <= s < c.m ==> #[trigger] db.tables[0][s] == srow(c, s)
    &&& forall|k: int| 0 <= k < c.nt ==> #[trigger] db.tables[2][k] == trow(c, k)
    &&& forall|l: int| 0 <= l < c.npre ==> #[trigger] db.tables[3][l] == prow(c, l)
}

/// The context of the parts of `sv` (row counts from the parts).
pub open spec fn ctx_of(sv: StoresView, ps: Seq<Literal>, n: int, m: int, nt: int, npre: int) -> Ctx {
    Ctx {
        np: sv.flat_num, n, sp: sv.flat_sub, m, tp: sv.flat_tag, nt, pp: sv.flat_pre, npre,
        uom: ps[0]->Text_0, stmt: ps[1]->Text_0, lo: ps[2]->Int_v, hi: ps[3]->Int_v,
    }
}

/// The stored-relation facts of a bound database for the four tables.
pub open spec fn rels_ok(sv: StoresView, db: Database, c: Ctx) -> bool {
    &&& c.np == sv.flat_num && c.sp == sv.flat_sub && c.tp == sv.flat_tag && c.pp == sv.flat_pre
    &&& c.n == crate::stores::flat_num::declaration::stored_relations(db)[0].len()
    &&& c.m == crate::stores::flat_sub::declaration::stored_relations(db)[0].len()
    &&& c.nt == crate::stores::flat_tag::declaration::stored_relations(db)[0].len()
    &&& c.npre == crate::stores::flat_pre::declaration::stored_relations(db)[0].len()
}

/// num rows of a bound database.
#[verifier::spinoff_prover]
proof fn lemma_bound_num(sv: StoresView, db: Database, c: Ctx)
    requires crate::gendb_entry::bound_db(sv, db), rels_ok(sv, db, c),
    ensures
        ni::parts_wf(c.np, c.n), db.tables.len() == 4, db.tables[1].len() == c.n,
        forall|i: int| 0 <= i < c.n ==> #[trigger] db.tables[1][i] == nrow(c, i),
{
    reveal(nrow);
    let rels = crate::stores::flat_num::declaration::stored_relations(db);
    crate::stores::flat_num::declaration::lemma_declared_schema();
    let cols = crate::stores::flat_num::declaration::stored_cols_t0();
    lemma_proj_all_index(db.tables[1], cols);
    assert forall|i: int| 0 <= i < c.n implies #[trigger] db.tables[1][i] == nrow(c, i) by {
        assert(crate::spec::typing::row_in_table(db.tables[1][i], db.schema[1]));
        assert(rels[0][i] == ni::row_at(c.np, i));
        assert(proj(db.tables[1][i], cols) =~= db.tables[1][i]);
    }
}

/// sub rows of a bound database.
#[verifier::spinoff_prover]
proof fn lemma_bound_sub(sv: StoresView, db: Database, c: Ctx)
    requires crate::gendb_entry::bound_db(sv, db), rels_ok(sv, db, c),
    ensures
        si::parts_wf(c.sp, c.m), db.tables[0].len() == c.m,
        forall|s: int| 0 <= s < c.m ==> #[trigger] db.tables[0][s] == srow(c, s),
{
    reveal(srow);
    let rels = crate::stores::flat_sub::declaration::stored_relations(db);
    crate::stores::flat_sub::declaration::lemma_declared_schema();
    let cols = crate::stores::flat_sub::declaration::stored_cols_t0();
    lemma_proj_all_index(db.tables[0], cols);
    assert forall|s: int| 0 <= s < c.m implies #[trigger] db.tables[0][s] == srow(c, s) by {
        assert(crate::spec::typing::row_in_table(db.tables[0][s], db.schema[0]));
        assert(rels[0][s] == si::row_at(c.sp, s));
        assert(proj(db.tables[0][s], cols) =~= db.tables[0][s]);
    }
}

/// tag rows of a bound database.
#[verifier::spinoff_prover]
proof fn lemma_bound_tag(sv: StoresView, db: Database, c: Ctx)
    requires crate::gendb_entry::bound_db(sv, db), rels_ok(sv, db, c),
    ensures
        ti::parts_wf(c.tp, c.nt), db.tables[2].len() == c.nt,
        forall|k: int| 0 <= k < c.nt ==> #[trigger] db.tables[2][k] == trow(c, k),
{
    reveal(trow);
    let rels = crate::stores::flat_tag::declaration::stored_relations(db);
    crate::stores::flat_tag::declaration::lemma_declared_schema();
    let cols = crate::stores::flat_tag::declaration::stored_cols_t0();
    lemma_proj_all_index(db.tables[2], cols);
    assert forall|k: int| 0 <= k < c.nt implies #[trigger] db.tables[2][k] == trow(c, k) by {
        assert(crate::spec::typing::row_in_table(db.tables[2][k], db.schema[2]));
        assert(rels[0][k] == ti::row_at(c.tp, k));
        assert(proj(db.tables[2][k], cols) =~= db.tables[2][k]);
    }
}

/// pre rows of a bound database.
#[verifier::spinoff_prover]
proof fn lemma_bound_pre(sv: StoresView, db: Database, c: Ctx)
    requires crate::gendb_entry::bound_db(sv, db), rels_ok(sv, db, c),
    ensures
        pi::parts_wf(c.pp, c.npre), db.tables[3].len() == c.npre,
        forall|l: int| 0 <= l < c.npre ==> #[trigger] db.tables[3][l] == prow(c, l),
{
    reveal(prow);
    let rels = crate::stores::flat_pre::declaration::stored_relations(db);
    crate::stores::flat_pre::declaration::lemma_declared_schema();
    let cols = crate::stores::flat_pre::declaration::stored_cols_t0();
    lemma_proj_all_index(db.tables[3], cols);
    assert forall|l: int| 0 <= l < c.npre implies #[trigger] db.tables[3][l] == prow(c, l) by {
        assert(crate::spec::typing::row_in_table(db.tables[3][l], db.schema[3]));
        assert(rels[0][l] == pi::row_at(c.pp, l));
        assert(proj(db.tables[3][l], cols) =~= db.tables[3][l]);
    }
}

/// The primary keys of sub (adsh) and tag (tag, version) identify rows.
#[verifier::spinoff_prover]
proof fn lemma_bound_keys(db: Database, c: Ctx)
    requires
        constraints_hold(crate::gendb_constraints::declared_db(db)),
        db.tables.len() == 4, db.tables[0].len() == c.m, db.tables[2].len() == c.nt,
        forall|s: int| 0 <= s < c.m ==> #[trigger] db.tables[0][s] == srow(c, s),
        forall|k: int| 0 <= k < c.nt ==> #[trigger] db.tables[2][k] == trow(c, k),
    ensures sub_key(c), tag_key(c),
{
    let ddb = crate::gendb_constraints::declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(ddb.schema[0].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }));
    assert(ddb.schema[2].constraints[0] == (Constraint::Key { cols: seq![0nat, 1nat], primary: true, nulls_distinct: true }));
    assert forall|s1: int, s2: int| 0 <= s1 < c.m && 0 <= s2 < c.m && #[trigger] s_adsh(c, s1) == #[trigger] s_adsh(c, s2)
        implies s1 == s2 by {
        lemma_cells(c, 0, s1, 0, 0);
        lemma_cells(c, 0, s2, 0, 0);
        assert(ddb.tables[0][s1][0] == ddb.tables[0][s2][0]);
        let k1 = key_of(ddb.tables[0][s1], seq![0nat]);
        let k2 = key_of(ddb.tables[0][s2], seq![0nat]);
        assert(k1 =~= k2);
        lemma_row_not_distinct_refl(k1);
        crate::bridge::constraints::lemma_primary_key_identifies(ddb, 0, 0, seq![0nat], true, s1, s2);
    }
    assert forall|k1: int, k2: int| 0 <= k1 < c.nt && 0 <= k2 < c.nt && #[trigger] t_tag(c, k1) == #[trigger] t_tag(c, k2)
        && t_ver(c, k1) == t_ver(c, k2) implies k1 == k2 by {
        lemma_cells(c, 0, 0, k1, 0);
        lemma_cells(c, 0, 0, k2, 0);
        assert(ddb.tables[2][k1][0] == ddb.tables[2][k2][0]);
        assert(ddb.tables[2][k1][1] == ddb.tables[2][k2][1]);
        let a1 = key_of(ddb.tables[2][k1], seq![0nat, 1nat]);
        let a2 = key_of(ddb.tables[2][k2], seq![0nat, 1nat]);
        assert(a1 =~= a2);
        lemma_row_not_distinct_refl(a1);
        crate::bridge::constraints::lemma_primary_key_identifies(ddb, 2, 0, seq![0nat, 1nat], true, k1, k2);
    }
}

/// Every database bound to the parts satisfies `db_ok` (and the parts are well formed for the row counts).
pub proof fn lemma_bound(sv: StoresView, db: Database, c: Ctx)
    requires crate::gendb_entry::bound_db(sv, db), rels_ok(sv, db, c),
    ensures db_ok(db, c),
{
    lemma_bound_num(sv, db, c);
    lemma_bound_sub(sv, db, c);
    lemma_bound_tag(sv, db, c);
    lemma_bound_pre(sv, db, c);
    lemma_bound_keys(db, c);
    reveal(ctx_ok);
}

// ------------------------------------------------------------------------------------------------ the reads

/// The whole parts the query reads.
pub struct Cols {
    pub n_uom: TextCol,
    pub n_adsh: TextCol,
    pub n_tag: TextCol,
    pub n_ver: TextCol,
    pub n_val: &'static [i128],
    pub s_adsh: TextCol,
    pub s_cik: &'static [i32],
    pub s_sic: &'static [i32],
    pub s_sicv: &'static [u8],
    pub t_tag: TextCol,
    pub t_ver: TextCol,
    pub t_abs: &'static [i32],
    pub t_label: TextCol,
    pub t_labelv: &'static [u8],
    pub p_adsh: TextCol,
    pub p_stmt: TextCol,
    pub p_stmtv: &'static [u8],
    pub p_tag: TextCol,
    pub p_ver: TextCol,
}

pub open spec fn cols_ok(k: &Cols, c: Ctx) -> bool {
    &&& k.n_uom@ == n_uom_v(c) && k.n_adsh@ == n_adsh_v(c) && k.n_tag@ == n_tag_v(c) && k.n_ver@ == n_ver_v(c)
    &&& k.n_val@ == n_val_s(c)
    &&& k.s_adsh@ == s_adsh_v(c) && k.s_cik@ == s_cik_s(c) && k.s_sic@ == s_sic_s(c) && k.s_sicv@ == s_sicv_s(c)
    &&& k.t_tag@ == t_tag_v(c) && k.t_ver@ == t_ver_v(c) && k.t_abs@ == t_abs_s(c)
    &&& k.t_label@ == t_label_v(c) && k.t_labelv@ == t_labelv_s(c)
    &&& k.p_adsh@ == p_adsh_v(c) && k.p_stmt@ == p_stmt_v(c) && k.p_stmtv@ == p_stmtv_s(c)
    &&& k.p_tag@ == p_tag_v(c) && k.p_ver@ == p_ver_v(c)
}

/// The text views of a well-formed context are well formed for the row counts; the fixed-width parts have them.
pub proof fn lemma_views(c: Ctx)
    requires ctx_ok(c),
    ensures
        text_wf(n_uom_v(c), c.n), text_wf(n_adsh_v(c), c.n), text_wf(n_tag_v(c), c.n), text_wf(n_ver_v(c), c.n),
        n_val_s(c).len() == c.n,
        text_wf(s_adsh_v(c), c.m), s_cik_s(c).len() == c.m, s_sic_s(c).len() == c.m, s_sicv_s(c).len() == c.m,
        text_wf(t_tag_v(c), c.nt), text_wf(t_ver_v(c), c.nt), t_abs_s(c).len() == c.nt,
        text_wf(t_label_v(c), c.nt), t_labelv_s(c).len() == c.nt,
        text_wf(p_adsh_v(c), c.npre), text_wf(p_stmt_v(c), c.npre), p_stmtv_s(c).len() == c.npre,
        text_wf(p_tag_v(c), c.npre), text_wf(p_ver_v(c), c.npre),
{
    reveal(ctx_ok);
}

/// The keys of sub and tag.
pub proof fn lemma_keys(c: Ctx)
    requires ctx_ok(c),
    ensures sub_key(c), tag_key(c),
{
    reveal(ctx_ok);
}

/// The row counts are below `usize::MAX` (each table has an offsets part of one element more, a slice).
pub proof fn lemma_sizes(k: &Cols, c: Ctx)
    requires cols_ok(k, c), ctx_ok(c),
    ensures c.n < usize::MAX, c.m < usize::MAX, c.nt < usize::MAX, c.npre < usize::MAX,
{
    lemma_views(c);
    assert(k.n_adsh.offsets@.len() == k.n_adsh.offsets.len() as int);
    assert(k.s_adsh.offsets@.len() == k.s_adsh.offsets.len() as int);
    assert(k.t_tag.offsets@.len() == k.t_tag.offsets.len() as int);
    assert(k.p_adsh.offsets@.len() == k.p_adsh.offsets.len() as int);
}

fn read_text(s: &mut crate::gendb_entry::stored::StoredParts, off: usize, bytes: usize) -> (r: TextCol)
    requires
        off < old(s)@.len(), bytes < old(s)@.len(), old(s)@[off as int] is I64, old(s)@[bytes as int] is U8,
    ensures
        final(s)@ == old(s)@,
        r@ == (TextView { offsets: ni::i64s(old(s)@[off as int]), bytes: ni::u8s(old(s)@[bytes as int]) }),
{
    let n1 = s.part_len(off);
    let o = s.extent_i64(off, 0, n1);
    let bl = s.part_len(bytes);
    let b = s.extent_u8(bytes, 0, bl);
    proof {
        assert(o@ =~= ni::i64s(old(s)@[off as int]));
        assert(b@ =~= ni::u8s(old(s)@[bytes as int]));
    }
    TextCol { offsets: o, bytes: b }
}

/// Read the whole parts the query uses (one or two requests per column).
pub fn read_cols(stores: &mut Stores, Ghost(c): Ghost<Ctx>) -> (k: Cols)
    requires
        ctx_ok(c),
        c.np == old(stores)@.flat_num, c.sp == old(stores)@.flat_sub,
        c.tp == old(stores)@.flat_tag, c.pp == old(stores)@.flat_pre,
    ensures
        final(stores)@ == old(stores)@,
        cols_ok(&k, c),
{
    proof {
        lemma_views(c);
        reveal(ctx_ok);
    }
    let n_uom = read_text(&mut stores.flat_num, ni::UOM_OFFSETS, ni::UOM_BYTES);
    let n_adsh = read_text(&mut stores.flat_num, ni::ADSH_OFFSETS, ni::ADSH_BYTES);
    let n_tag = read_text(&mut stores.flat_num, ni::TAG_OFFSETS, ni::TAG_BYTES);
    let n_ver = read_text(&mut stores.flat_num, ni::VERSION_OFFSETS, ni::VERSION_BYTES);
    let nn = stores.flat_num.part_len(ni::VALUE);
    let n_val = stores.flat_num.extent_i128(ni::VALUE, 0, nn);
    let s_adsh = read_text(&mut stores.flat_sub, si::ADSH_OFFSETS, si::ADSH_BYTES);
    let ns = stores.flat_sub.part_len(si::CIK);
    let s_cik = stores.flat_sub.extent_i32(si::CIK, 0, ns);
    let s_sic = stores.flat_sub.extent_i32(si::SIC, 0, ns);
    let s_sicv = stores.flat_sub.extent_u8(si::SIC_VALIDITY, 0, ns);
    let t_tag = read_text(&mut stores.flat_tag, ti::TAG_OFFSETS, ti::TAG_BYTES);
    let t_ver = read_text(&mut stores.flat_tag, ti::VERSION_OFFSETS, ti::VERSION_BYTES);
    let nt = stores.flat_tag.part_len(ti::ABSTRACT);
    let t_abs = stores.flat_tag.extent_i32(ti::ABSTRACT, 0, nt);
    let t_label = read_text(&mut stores.flat_tag, ti::TLABEL_OFFSETS, ti::TLABEL_BYTES);
    let t_labelv = stores.flat_tag.extent_u8(ti::TLABEL_VALIDITY, 0, nt);
    let p_adsh = read_text(&mut stores.flat_pre, pi::ADSH_OFFSETS, pi::ADSH_BYTES);
    let p_stmt = read_text(&mut stores.flat_pre, pi::STMT_OFFSETS, pi::STMT_BYTES);
    let np = stores.flat_pre.part_len(pi::STMT_VALIDITY);
    let p_stmtv = stores.flat_pre.extent_u8(pi::STMT_VALIDITY, 0, np);
    let p_tag = read_text(&mut stores.flat_pre, pi::TAG_OFFSETS, pi::TAG_BYTES);
    let p_ver = read_text(&mut stores.flat_pre, pi::VERSION_OFFSETS, pi::VERSION_BYTES);
    proof {
        assert(n_val@ =~= n_val_s(c));
        assert(s_cik@ =~= s_cik_s(c));
        assert(s_sic@ =~= s_sic_s(c));
        assert(s_sicv@ =~= s_sicv_s(c));
        assert(t_abs@ =~= t_abs_s(c));
        assert(t_labelv@ =~= t_labelv_s(c));
        assert(p_stmtv@ =~= p_stmtv_s(c));
        assert(n_uom@ == n_uom_v(c));
        assert(s_adsh@ == s_adsh_v(c));
        assert(t_tag@ == t_tag_v(c));
        assert(p_adsh@ == p_adsh_v(c));
    }
    Cols {
        n_uom, n_adsh, n_tag, n_ver, n_val, s_adsh, s_cik, s_sic, s_sicv, t_tag, t_ver, t_abs, t_label, t_labelv,
        p_adsh, p_stmt, p_stmtv, p_tag, p_ver,
    }
}

/// A copy of a text column handle (the same view).
pub fn tc(t: &TextCol) -> (r: TextCol)
    ensures r@ == t@,
{
    TextCol { offsets: t.offsets, bytes: t.bytes }
}

} // verus!
