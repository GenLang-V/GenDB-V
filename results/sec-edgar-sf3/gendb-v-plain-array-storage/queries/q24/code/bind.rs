//! Every database bound to the call's parts (`gendb_entry::bound_db`) matches the context: its `num`, `pre`, `sub`
//! and `tag` tables are the rows of the parts (`lemma_bound`), and the declared foreign keys hold on the parts
//! (`lemma_fk`: every `num`/`pre` `(tag, version)` is a `tag` row's, every `adsh` a `sub` row's).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::constraints::*;
use crate::spec::types::Constraint;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::link::query::{proj, proj_all, text_at};
use crate::link::source::lemma_proj_all_index;
use crate::gendb_entry::stores::StoresView;
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_pre::interface as pi;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_tag::interface as ti;
use crate::agent::spec::*;
use crate::agent::sem::*;

verus! {

/// The context of a call: its parts and row counts, and the binding.
pub open spec fn ctx_of(sv: StoresView, n: int, m: int, ns: int, nt: int, pv: Seq<u8>, dlo: int, dhi: int) -> Ctx {
    Ctx { np: sv.flat_num, n, pp: sv.flat_pre, m, sp: sv.flat_sub, ns, tp: sv.flat_tag, nt, pv, dlo, dhi }
}

/// The row counts of a bound database's stored relations.
pub open spec fn counts_ok(sv: StoresView, db: Database, c: Ctx) -> bool {
    &&& c.n == crate::stores::flat_num::declaration::stored_relations(db)[0].len()
    &&& c.m == crate::stores::flat_pre::declaration::stored_relations(db)[0].len()
    &&& c.ns == crate::stores::flat_sub::declaration::stored_relations(db)[0].len()
    &&& c.nt == crate::stores::flat_tag::declaration::stored_relations(db)[0].len()
}

/// `sub` and `tag` rows of the database are the parts' rows.
pub open spec fn ref_ok(db: Database, c: Ctx) -> bool {
    &&& db.tables[0].len() == c.ns
    &&& db.tables[2].len() == c.nt
    &&& forall|s: int| 0 <= s < c.ns ==> #[trigger] db.tables[0][s] == si::row_at(c.sp, s)
    &&& forall|a: int| 0 <= a < c.nt ==> #[trigger] db.tables[2][a] == ti::row_at(c.tp, a)
}

/// A bound database: the context is well formed and the tables are the parts' rows.
pub proof fn lemma_bound(sv: StoresView, db: Database, c: Ctx)
    requires
        crate::gendb_entry::bound_db(sv, db),
        c.np == sv.flat_num, c.pp == sv.flat_pre, c.sp == sv.flat_sub, c.tp == sv.flat_tag,
        c.n == ni::text_view(c.np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int).offsets.len() - 1,
        c.m == pi::text_view(c.pp, pi::ADSH_OFFSETS as int, pi::ADSH_BYTES as int).offsets.len() - 1,
        c.ns == si::text_view(c.sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int).offsets.len() - 1,
        c.nt == ti::text_view(c.tp, ti::TAG_OFFSETS as int, ti::TAG_BYTES as int).offsets.len() - 1,
    ensures
        ctx_ok(c), ref_ok(db, c),
        db.schema == crate::schema::schema_spec(),
        db.tables.len() == 4,
        db.tables[1].len() == c.n, db.tables[3].len() == c.m,
        forall|i: int| 0 <= i < c.n ==> #[trigger] db.tables[1][i] == ni::row_at(c.np, i),
        forall|j: int| 0 <= j < c.m ==> #[trigger] db.tables[3][j] == pi::row_at(c.pp, j),
{
    let nrels = crate::stores::flat_num::declaration::stored_relations(db);
    let prels = crate::stores::flat_pre::declaration::stored_relations(db);
    let srels = crate::stores::flat_sub::declaration::stored_relations(db);
    let trels = crate::stores::flat_tag::declaration::stored_relations(db);
    crate::stores::flat_num::declaration::lemma_declared_schema();
    crate::stores::flat_pre::declaration::lemma_declared_schema();
    crate::stores::flat_sub::declaration::lemma_declared_schema();
    crate::stores::flat_tag::declaration::lemma_declared_schema();
    let ncols = crate::stores::flat_num::declaration::stored_cols_t0();
    let pcols = crate::stores::flat_pre::declaration::stored_cols_t0();
    let scols = crate::stores::flat_sub::declaration::stored_cols_t0();
    let tcols = crate::stores::flat_tag::declaration::stored_cols_t0();
    lemma_proj_all_index(db.tables[1], ncols);
    lemma_proj_all_index(db.tables[3], pcols);
    lemma_proj_all_index(db.tables[0], scols);
    lemma_proj_all_index(db.tables[2], tcols);
    assert(c.n == nrels[0].len());
    assert(c.m == prels[0].len());
    assert(c.ns == srels[0].len());
    assert(c.nt == trels[0].len());
    assert forall|i: int| 0 <= i < c.n implies #[trigger] db.tables[1][i] == ni::row_at(c.np, i) by {
        assert(crate::spec::typing::row_in_table(db.tables[1][i], db.schema[1]));
        assert(nrels[0][i] == ni::row_at(c.np, i));
        assert(proj(db.tables[1][i], ncols) =~= db.tables[1][i]);
    }
    assert forall|j: int| 0 <= j < c.m implies #[trigger] db.tables[3][j] == pi::row_at(c.pp, j) by {
        assert(crate::spec::typing::row_in_table(db.tables[3][j], db.schema[3]));
        assert(prels[0][j] == pi::row_at(c.pp, j));
        assert(proj(db.tables[3][j], pcols) =~= db.tables[3][j]);
    }
    assert forall|s: int| 0 <= s < c.ns implies #[trigger] db.tables[0][s] == si::row_at(c.sp, s) by {
        assert(crate::spec::typing::row_in_table(db.tables[0][s], db.schema[0]));
        assert(srels[0][s] == si::row_at(c.sp, s));
        assert(proj(db.tables[0][s], scols) =~= db.tables[0][s]);
    }
    assert forall|a: int| 0 <= a < c.nt implies #[trigger] db.tables[2][a] == ti::row_at(c.tp, a) by {
        assert(crate::spec::typing::row_in_table(db.tables[2][a], db.schema[2]));
        assert(trels[0][a] == ti::row_at(c.tp, a));
        assert(proj(db.tables[2][a], tcols) =~= db.tables[2][a]);
    }
}

/// Two text keys that match (SQL comparison 0 per position) are equal.
proof fn lemma_text_match(a: Seq<u8>, b: Seq<u8>)
    requires compare(Val::Text(a), Val::Text(b)) == Some(0int),
    ensures a == b,
{
    lemma_lex_cmp_zero(a, b);
}

/// A foreign key from row `i` of table `t` (key columns `cols`) to table `rt` (columns `rcols`): some row of `rt`
/// matches.
proof fn lemma_fk_row(db: Database, t: int, k: int, cols: Seq<nat>, rt: nat, rcols: Seq<nat>, i: int)
    requires
        constraints_hold(crate::gendb_constraints::declared_db(db)),
        db.tables.len() == 4, 0 <= t < 4, 0 <= i < db.tables[t].len(),
        0 <= k < crate::gendb_constraints::declared_schema()[t].constraints.len(),
        crate::gendb_constraints::declared_schema()[t].constraints[k]
            == (Constraint::ForeignKey { cols, table: rt, ref_cols: rcols, match_full: false }),
        !has_null(key_of(db.tables[t][i], cols)),
    ensures
        rt < db.tables.len(),
        exists|a: int| 0 <= a < db.tables[rt as int].len()
            && key_matches(key_of(db.tables[t][i], cols), key_of(#[trigger] db.tables[rt as int][a], rcols)),
{
    hide(constraints_hold);
    let ddb = crate::gendb_constraints::declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    crate::bridge::constraints::lemma_foreign_key_target(ddb, t, k, cols, rt, rcols, false, i);
}

/// The declared foreign keys of `num` and `pre`, as stated in the declared schema.
proof fn lemma_fk_decls()
    ensures
        crate::gendb_constraints::declared_schema()[1].constraints.len() == 2,
        crate::gendb_constraints::declared_schema()[1].constraints[0]
            == (Constraint::ForeignKey { cols: seq![0nat], table: 0, ref_cols: seq![0nat], match_full: false }),
        crate::gendb_constraints::declared_schema()[1].constraints[1]
            == (Constraint::ForeignKey { cols: seq![1nat, 2], table: 2, ref_cols: seq![0nat, 1], match_full: false }),
        crate::gendb_constraints::declared_schema()[3].constraints.len() == 3,
        crate::gendb_constraints::declared_schema()[3].constraints[1]
            == (Constraint::ForeignKey { cols: seq![0nat], table: 0, ref_cols: seq![0nat], match_full: false }),
        crate::gendb_constraints::declared_schema()[3].constraints[2]
            == (Constraint::ForeignKey { cols: seq![6nat, 7], table: 2, ref_cols: seq![0nat, 1], match_full: false }),
{
}

/// `num` row `i`'s foreign keys.
proof fn lemma_fk_num(db: Database, c: Ctx, i: int)
    requires
        constraints_hold(crate::gendb_constraints::declared_db(db)), ref_ok(db, c),
        db.tables.len() == 4, db.tables[1].len() == c.n,
        forall|i2: int| 0 <= i2 < c.n ==> #[trigger] db.tables[1][i2] == ni::row_at(c.np, i2),
        0 <= i < c.n,
    ensures num_fk(c, i),
{
    lemma_fk_decls();
    let r = db.tables[1][i];
    assert(r == ni::row_at(c.np, i));
    let k1 = key_of(r, seq![1nat, 2]);
    assert(k1 =~= seq![Val::Text(ntag(c, i)), Val::Text(nver(c, i))]);
    assert(!has_null(k1));
    lemma_fk_row(db, 1, 1, seq![1nat, 2], 2, seq![0nat, 1], i);
    let a = choose|a: int| 0 <= a < db.tables[2].len() && key_matches(k1, key_of(#[trigger] db.tables[2][a], seq![0nat, 1]));
    let ka = key_of(db.tables[2][a], seq![0nat, 1]);
    assert(ka =~= seq![Val::Text(ttag(c, a)), Val::Text(tver(c, a))]);
    lemma_text_match(ntag(c, i), ttag(c, a));
    lemma_text_match(nver(c, i), tver(c, a));
    assert(in_tag(c, ntag(c, i), nver(c, i)));
    let k0 = key_of(r, seq![0nat]);
    assert(k0 =~= seq![Val::Text(nadsh(c, i))]);
    assert(!has_null(k0));
    lemma_fk_row(db, 1, 0, seq![0nat], 0, seq![0nat], i);
    let s = choose|s: int| 0 <= s < db.tables[0].len() && key_matches(k0, key_of(#[trigger] db.tables[0][s], seq![0nat]));
    assert(db.tables[0][s] == si::row_at(c.sp, s));
    let ks = key_of(db.tables[0][s], seq![0nat]);
    assert(ks =~= seq![Val::Text(sadsh(c, s))]);
    assert(compare(k0[0], ks[0]) == Some(0int));
    lemma_text_match(nadsh(c, i), sadsh(c, s));
    assert(in_sub(c, nadsh(c, i)));
}

/// `pre` row `j`'s foreign keys.
proof fn lemma_fk_pre(db: Database, c: Ctx, j: int)
    requires
        constraints_hold(crate::gendb_constraints::declared_db(db)), ref_ok(db, c),
        db.tables.len() == 4, db.tables[3].len() == c.m,
        forall|j2: int| 0 <= j2 < c.m ==> #[trigger] db.tables[3][j2] == pi::row_at(c.pp, j2),
        0 <= j < c.m,
    ensures pre_fk(c, j),
{
    lemma_fk_decls();
    let r = db.tables[3][j];
    assert(r == pi::row_at(c.pp, j));
    let k2 = key_of(r, seq![6nat, 7]);
    assert(k2 =~= seq![Val::Text(ptag(c, j)), Val::Text(pver(c, j))]);
    assert(!has_null(k2));
    lemma_fk_row(db, 3, 2, seq![6nat, 7], 2, seq![0nat, 1], j);
    let a = choose|a: int| 0 <= a < db.tables[2].len() && key_matches(k2, key_of(#[trigger] db.tables[2][a], seq![0nat, 1]));
    let ka = key_of(db.tables[2][a], seq![0nat, 1]);
    assert(ka =~= seq![Val::Text(ttag(c, a)), Val::Text(tver(c, a))]);
    lemma_text_match(ptag(c, j), ttag(c, a));
    lemma_text_match(pver(c, j), tver(c, a));
    assert(in_tag(c, ptag(c, j), pver(c, j)));
    let k0 = key_of(r, seq![0nat]);
    assert(k0 =~= seq![Val::Text(padsh(c, j))]);
    assert(!has_null(k0));
    lemma_fk_row(db, 3, 1, seq![0nat], 0, seq![0nat], j);
    let s = choose|s: int| 0 <= s < db.tables[0].len() && key_matches(k0, key_of(#[trigger] db.tables[0][s], seq![0nat]));
    assert(db.tables[0][s] == si::row_at(c.sp, s));
    let ks = key_of(db.tables[0][s], seq![0nat]);
    assert(ks =~= seq![Val::Text(sadsh(c, s))]);
    assert(compare(k0[0], ks[0]) == Some(0int));
    lemma_text_match(padsh(c, j), sadsh(c, s));
    assert(in_sub(c, padsh(c, j)));
}

/// The stores view of a context.
pub open spec fn c_view(c: Ctx) -> StoresView {
    StoresView { flat_num: c.np, flat_pre: c.pp, flat_sub: c.sp, flat_tag: c.tp }
}

/// The declared foreign keys hold on the parts.
pub proof fn lemma_fk(db: Database, c: Ctx)
    requires
        constraints_hold(crate::gendb_constraints::declared_db(db)), ctx_ok(c), ref_ok(db, c),
        db.tables.len() == 4, db.tables[1].len() == c.n, db.tables[3].len() == c.m,
        forall|i: int| 0 <= i < c.n ==> #[trigger] db.tables[1][i] == ni::row_at(c.np, i),
        forall|j: int| 0 <= j < c.m ==> #[trigger] db.tables[3][j] == pi::row_at(c.pp, j),
    ensures fk_ok(c),
{
    assert forall|i: int| 0 <= i < c.n implies #[trigger] num_fk(c, i) by {
        lemma_fk_num(db, c, i);
    }
    assert forall|j: int| 0 <= j < c.m implies #[trigger] pre_fk(c, j) by {
        lemma_fk_pre(db, c, j);
    }
}

/// The binding's literals.
pub proof fn lemma_lits(ps: Seq<Literal>, c: Ctx, p0: Seq<u8>, p1: int, p2: int)
    requires
        crate::query::param_domain(ps),
        ps == seq![Literal::Text(p0), Literal::Int { v: p1, kind: IntKind::Int4 }, Literal::Int { v: p2, kind: IntKind::Int4 }],
        c.pv == p0, c.dlo == p1, c.dhi == p2,
    ensures lits_ok(c, ps),
{
    assert(ps[1] == Literal::Int { v: p1, kind: IntKind::Int4 });
    assert(ps[2] == Literal::Int { v: p2, kind: IntKind::Int4 });
}

/// A bound database is `db_ok` for the call's context.
pub proof fn lemma_bound_ctx(sv: crate::gendb_entry::stores::StoresView, db: Database, c: Ctx)
    requires
        crate::gendb_entry::bound_db(sv, db), ctx_ok(c),
        c.np == sv.flat_num, c.pp == sv.flat_pre, c.sp == sv.flat_sub, c.tp == sv.flat_tag,
    ensures crate::agent::sem::db_ok(db, c),
{
    lemma_text_cols_wf(c);
    assert(ni::text_view(c.np, ni::ADSH_OFFSETS as int, ni::ADSH_BYTES as int).offsets.len() == c.n + 1);
    assert(pi::text_view(c.pp, pi::ADSH_OFFSETS as int, pi::ADSH_BYTES as int).offsets.len() == c.m + 1);
    assert(si::text_view(c.sp, si::ADSH_OFFSETS as int, si::ADSH_BYTES as int).offsets.len() == c.ns + 1);
    assert(ti::text_view(c.tp, ti::TAG_OFFSETS as int, ti::TAG_BYTES as int).offsets.len() == c.nt + 1);
    lemma_bound(sv, db, c);
}

} // verus!
