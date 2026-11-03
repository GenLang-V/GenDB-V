//! The SQL meaning of Q0 in normal form, over the canonical rows of `pre`.
//!
//! The statement reads columns adsh, line, stmt, rfile (table ordinals 0, 2, 3, 5); `xs` is `pre` projected onto
//! them (`qcols`), so a projected row is `[adsh, line, stmt, rfile]`. In the link toolkit's normal form (`gq`) a row
//! qualifies when stmt is not NULL, its group key is `[stmt, rfile]` and its argument is its line. The GROUP BY's
//! argument row of an input row is `[NULL, adsh, line]` (`args_of`: COUNT(*) has no argument).
//!
//! Proved here, for every well-formed database of the schema:
//! - `lemma_body`: the statement's body evaluates to `collect(group_results(..))` over the qualifying keys and
//!   arguments, and leaving the groups' domain (`fits_groups`) leaves the capacity domain;
//! - `lemma_groups`: the GROUP BY's groups are `gkeys(gq, xs)` (first-occurrence order) and each group's members
//!   are `members_of(xs, k)`;
//! - `lemma_members`: the three aggregate columns of a group: its count, its adsh values (exactly the
//!   `has_adsh(xs, k, _)`) and its lines (count, exact sum and absolute mass).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::limits::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::order::*;
use crate::schema::schema_spec;
use crate::query::query_spec;
use crate::link::query::*;
use crate::link::source::*;
use crate::bridge::collect::*;
use crate::link::capacity::lemma_group_prepared;
use crate::exec::relational::domain::*;
use crate::stores::pre::declaration::*;

verus! {

// ------------------------------------------------------------------------------------------- the statement's parts

pub open spec fn q_pred() -> Pred {
    Pred::Not(Box::new(Pred::IsNull(Expr::Col(3))))
}

pub open spec fn q_input() -> Query {
    Query::Filter { pred: q_pred(), input: Box::new(Query::Table(3)) }
}

pub open spec fn q_keys() -> Seq<Expr> {
    seq![Expr::Col(3), Expr::Col(5)]
}

pub open spec fn q_aggs() -> Seq<Agg> {
    seq![Agg::CountStar, Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(0)))), Agg::Avg { kind: NumKind::Int4, arg: Expr::Col(2) }]
}

pub open spec fn q_body() -> Query {
    Query::GroupBy { keys: q_keys(), aggs: q_aggs(), input: Box::new(q_input()) }
}

pub open spec fn q_order() -> Seq<OrderKey> {
    seq![OrderKey { col: 2, desc: true, nulls_first: true }]
}

/// The emitted statement is this body, ordered by column 2 (COUNT(*)) descending, without OFFSET/LIMIT.
pub proof fn lemma_statement()
    ensures
        query_spec().body == q_body(),
        query_spec().keys == q_order(),
        query_spec().offset == 0,
        query_spec().limit is None,
{
    assert(query_spec().keys =~= q_order());
}

// ------------------------------------------------------------------------------------------------- normal form

/// Table ordinals of adsh, line, stmt, rfile.
pub open spec fn qcols() -> Seq<nat> {
    seq![0nat, 2, 3, 5]
}

pub open spec fn line_of(x: Row) -> int {
    match x[1] {
        Val::Int(v) => v,
        _ => 0,
    }
}

pub open spec fn gq() -> QuerySpec {
    QuerySpec {
        qual: |x: Row| !(x[2] is Null),
        key: |x: Row| seq![x[2], x[3]],
        arg: |j: int, x: Row| line_of(x),
        aggs: Seq::empty(),
        outs: Seq::empty(),
        grouped: true,
    }
}

/// The GROUP BY argument row of a projected row: COUNT(*) (NULL), adsh, line.
pub open spec fn args_of(x: Row) -> Row {
    seq![Val::Null, x[0], x[1]]
}

pub open spec fn xs_of(db: Database) -> Seq<Row> {
    proj_all(db.tables[3], qcols())
}

pub open spec fn qk(db: Database) -> Seq<Row> {
    qkeys(gq(), xs_of(db))
}

pub open spec fn qa(db: Database) -> Seq<Row> {
    qrows(gq(), xs_of(db)).map_values(|x: Row| args_of(x))
}

/// A projected row of `pre` in its declared domain: adsh text, line int4, stmt text or NULL, rfile text.
pub open spec fn row_typed(x: Row) -> bool {
    &&& x.len() == 4
    &&& x[0] is Text
    &&& x[1] is Int && int_in_range(IntKind::Int4, x[1]->Int_0)
    &&& (x[2] is Null || x[2] is Text)
    &&& x[3] is Text
}

pub open spec fn rows_typed(xs: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < xs.len() ==> #[trigger] row_typed(xs[i])
}

/// Every row of `pre` has its 10 columns in their declared domains, so its projection is typed.
pub proof fn lemma_table_typed(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        db.tables.len() == 4,
        forall|i: int| 0 <= i < db.tables[3].len() ==> (#[trigger] db.tables[3][i]).len() == 10,
        rows_typed(xs_of(db)),
        xs_of(db).len() == db.tables[3].len(),
{
    lemma_declared_schema();
    lemma_stored_relations(db);
    let t = db.tables[3];
    let r = stored_relations(db)[0];
    let cs = stored_columns_t0();
    lemma_proj_all_index(t, stored_cols_t0());
    lemma_proj_all_index(t, qcols());
    assert forall|i: int| 0 <= i < t.len() implies (#[trigger] t[i]).len() == 10 by {
        assert(row_in_table(t[i], db.schema[3]));
    }
    assert forall|i: int| 0 <= i < xs_of(db).len() implies #[trigger] row_typed(xs_of(db)[i]) by {
        assert(r[i].len() == cs.len());
        assert(value_in_column(r[i][0], cs[0]));
        assert(value_in_column(r[i][2], cs[2]));
        assert(value_in_column(r[i][3], cs[3]));
        assert(value_in_column(r[i][5], cs[5]));
        assert(r[i][0] == t[i][0] && r[i][2] == t[i][2] && r[i][3] == t[i][3] && r[i][5] == t[i][5]);
        assert(xs_of(db)[i][0] == t[i][0] && xs_of(db)[i][1] == t[i][2]);
        assert(xs_of(db)[i][2] == t[i][3] && xs_of(db)[i][3] == t[i][5]);
    }
}

// ----------------------------------------------------------------------------------------- the body's evaluation

/// Per row of `pre`: the WHERE condition is the normal form's.
proof fn lemma_pred_agrees(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures pred_agrees(db, db.tables[3], qcols(), q_pred(), gq()),
{
    lemma_table_typed(db);
    let t = db.tables[3];
    assert forall|i: int| 0 <= i < t.len() implies
        eval_pred(db, #[trigger] t[i], q_pred()) == Ok::<Truth, SqlError>(truth_of((gq().qual)(proj(t[i], qcols())))) by {
        assert(t[i].len() == 10);
        assert(proj(t[i], qcols())[2] == t[i][3]);
        let b = t[i][3] is Null;
        assert(eval_expr(db, t[i], Expr::Col(3)) == Ok::<Val, SqlError>(t[i][3]));
        assert(eval_pred(db, t[i], Pred::IsNull(Expr::Col(3))) == Ok::<Truth, SqlError>(truth_of(b)));
        assert(truth_not(truth_of(b)) == truth_of(!b));
    }
}

/// The key tuple of a row: its stmt and rfile.
proof fn lemma_row_keys(db: Database, r: Row)
    requires r.len() == 10,
    ensures eval_exprs(db, r, q_keys()) == Ok::<Row, SqlError>((gq().key)(proj(r, qcols()))),
{
    assert(q_keys() =~= col_exprs(seq![3nat, 5]));
    lemma_eval_cols(db, r, seq![3nat, 5]);
    assert(select(r, seq![3nat, 5]) =~= (gq().key)(proj(r, qcols())));
}

/// A column reference evaluates to the column.
proof fn lemma_col(db: Database, r: Row, i: nat)
    requires i < r.len(),
    ensures eval_expr(db, r, Expr::Col(i)) == Ok::<Val, SqlError>(r[i as int]),
{
}

/// The argument of COUNT(DISTINCT adsh) is adsh.
proof fn lemma_arg_distinct(db: Database, r: Row)
    requires r.len() == 10,
    ensures agg_arg(db, r, Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(0))))) == Ok::<Val, SqlError>(r[0]),
{
    lemma_col(db, r, 0);
    reveal_with_fuel(agg_arg, 2);
}

/// The argument of AVG(line) is line.
proof fn lemma_arg_avg(db: Database, r: Row)
    requires r.len() == 10,
    ensures agg_arg(db, r, Agg::Avg { kind: NumKind::Int4, arg: Expr::Col(2) }) == Ok::<Val, SqlError>(r[2]),
{
    hide(eval_expr);
    lemma_col(db, r, 2);
    lemma_agg_arg_avg(db, r, NumKind::Int4, Expr::Col(2));
}

/// The per-aggregate argument outcomes of a row: NULL (COUNT(*)), adsh, line.
proof fn lemma_arg_results(db: Database, r: Row)
    requires r.len() == 10,
    ensures
        agg_arg_results(db, r, q_aggs()) == seq![Ok::<Val, SqlError>(Val::Null), Ok::<Val, SqlError>(r[0]), Ok::<Val, SqlError>(r[2])],
{
    hide(agg_arg);
    hide(agg_arg_results);
    let aggs = q_aggs();
    let rs = agg_arg_results(db, r, aggs);
    lemma_agg_arg_results_index(db, r, aggs);
    let a1 = Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(0))));
    let a2 = Agg::Avg { kind: NumKind::Int4, arg: Expr::Col(2) };
    assert(aggs.len() == 3 && aggs[0] == Agg::CountStar && aggs[1] == a1 && aggs[2] == a2);
    lemma_agg_arg_count(db, r);
    lemma_arg_distinct(db, r);
    lemma_arg_avg(db, r);
    let want = seq![Ok::<Val, SqlError>(Val::Null), Ok::<Val, SqlError>(r[0]), Ok::<Val, SqlError>(r[2])];
    assert(rs[0] == want[0]);
    assert(rs[1] == want[1]);
    assert(rs[2] == want[2]);
    assert(rs =~= want);
}

/// The argument of each aggregate in a row: NULL (COUNT(*)), adsh, line.
proof fn lemma_row_args(db: Database, r: Row)
    requires r.len() == 10,
    ensures agg_args(db, r, q_aggs()) == Ok::<Row, SqlError>(seq![Val::Null, r[0], r[2]]),
{
    hide(agg_arg_results);
    hide(agg_arg);
    hide(eval_expr);
    hide(eval_exprs);
    hide(eval_pred);
    hide(eval_query);
    hide(agg_args);
    lemma_arg_results(db, r);
    lemma_agg_args(db, r, q_aggs());
    let rs = seq![Ok::<Val, SqlError>(Val::Null), Ok::<Val, SqlError>(r[0]), Ok::<Val, SqlError>(r[2])];
    let vs = seq![Val::Null, r[0], r[2]];
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(vs[j]) by {
        if j == 0 {} else if j == 1 {} else {}
    }
    lemma_collect_all(rs, vs);
}

/// Per kept row: its key and arguments.
proof fn lemma_group_input(db: Database, r: Row)
    requires r.len() == 10,
    ensures
        group_input(db, Seq::<Val>::empty() + r, q_keys(), q_aggs())
            == Ok::<(Row, Row), SqlError>(((gq().key)(proj(r, qcols())), args_of(proj(r, qcols())))),
{
    hide(eval_exprs);
    hide(agg_args);
    let env = Seq::<Val>::empty() + r;
    assert(env =~= r);
    lemma_row_keys(db, r);
    lemma_row_args(db, r);
    let x = proj(r, qcols());
    assert(x[0] == r[0] && x[1] == r[2]);
    assert(args_of(x) =~= seq![Val::Null, r[0], r[2]]);
}

/// The statement's body is the collected group results over the qualifying keys and arguments; leaving the
/// groups' domain leaves the capacity domain.
pub proof fn lemma_body(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        eval_query(db, Seq::empty(), q_body()) == collect(group_results(q_aggs(), qk(db), qa(db))),
        !fits_groups(q_aggs(), qk(db), qa(db)) ==> !fits_query(db, Seq::empty(), q_body()),
{
    lemma_table_typed(db);
    let t = db.tables[3];
    let xs = xs_of(db);
    let ctx = Seq::<Val>::empty();
    assert(eval_query(db, ctx, Query::Table(3)) == Ok::<Relation, SqlError>(t));
    lemma_pred_agrees(db);
    lemma_filter_rows(db, Query::Table(3), t, qcols(), q_pred(), gq());
    let kept = keep_true(t, qual_truths(gq(), xs));
    assert(eval_query(db, ctx, q_input()) == Ok::<Relation, SqlError>(kept));
    lemma_kept_rows(gq(), t, qcols());
    let ks = Seq::new(kept.len(), |i: int| (gq().key)(proj(kept[i], qcols())));
    let avs = Seq::new(kept.len(), |i: int| args_of(proj(kept[i], qcols())));
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, ctx + kept[i], q_keys(), q_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], avs[i])) by {
        assert(t.contains(kept[i]));
        let m = choose|m: int| 0 <= m < t.len() && t[m] == kept[i];
        lemma_group_input(db, kept[i]);
    }
    let prepared = lemma_group_prepared(db, ctx, q_keys(), q_aggs(), kept, ks, avs);
    let q = qrows(gq(), xs);
    assert(proj_all(kept, qcols()) == q);
    assert(ks =~= qk(db)) by {
        assert forall|i: int| 0 <= i < kept.len() implies ks[i] == qk(db)[i] by {
            assert(proj(kept[i], qcols()) == q[i]);
        }
    }
    assert(avs =~= qa(db)) by {
        assert forall|i: int| 0 <= i < kept.len() implies avs[i] == qa(db)[i] by {
            assert(proj(kept[i], qcols()) == q[i]);
        }
    }
    lemma_eval_group_by(db, ctx, q_keys(), q_aggs(), Box::new(q_input()));
    lemma_fits_group_by(db, ctx, q_keys(), q_aggs(), Box::new(q_input()));
}

// ------------------------------------------------------------------------------------------- groups and members

/// Argument rows of the qualifying rows of group `k`, in order (the GROUP BY members).
pub open spec fn members_of(xs: Seq<Row>, k: Row) -> Seq<Row>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Seq::empty()
    } else if hit(gq(), xs.last(), k) {
        members_of(xs.drop_last(), k).push(args_of(xs.last()))
    } else {
        members_of(xs.drop_last(), k)
    }
}

/// On typed rows, SQL "not distinct" of qualifying keys is structural equality.
proof fn lemma_keys_exact(xs: Seq<Row>)
    requires rows_typed(xs),
    ensures keys_exact(gq(), xs),
{
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (gq().qual)(xs[a]) && (gq().qual)(xs[b])
        implies (row_not_distinct(#[trigger] (gq().key)(xs[a]), #[trigger] (gq().key)(xs[b])) <==> (gq().key)(xs[a]) == (gq().key)(xs[b])) by {
        assert(row_typed(xs[a]) && row_typed(xs[b]));
        let (ka, kb) = ((gq().key)(xs[a]), (gq().key)(xs[b]));
        assert forall|i: int| 0 <= i < ka.len() implies crate::bridge::equality::same_exact_type(#[trigger] ka[i], kb[i]) by {}
        lemma_row_exact(ka, kb);
    }
}

/// `group_members` of the qualifying keys and arguments is `members_of` (exact keys, `k` from the pool).
proof fn lemma_group_members_of(xs: Seq<Row>, k: Row, pool: Seq<Row>)
    requires
        forall|a: Row, b: Row| pool.contains(a) && pool.contains(b) ==> (#[trigger] row_not_distinct(a, b) <==> a == b),
        forall|i: int| 0 <= i < qkeys(gq(), xs).len() ==> pool.contains(#[trigger] qkeys(gq(), xs)[i]),
        pool.contains(k),
    ensures
        group_members(qkeys(gq(), xs), qrows(gq(), xs).map_values(|x: Row| args_of(x)), k) == members_of(xs, k),
    decreases xs.len(),
{
    let g = gq();
    let args = |x: Row| args_of(x);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        let qkx = qkeys(g, xs);
        let qki = qkeys(g, xi);
        let qax = qrows(g, xs).map_values(args);
        let qai = qrows(g, xi).map_values(args);
        if (g.qual)(x) {
            assert(qkx =~= qki.push((g.key)(x)));
            assert(qax =~= qai.push(args_of(x)));
            assert forall|i: int| 0 <= i < qki.len() implies pool.contains(#[trigger] qki[i]) by {
                assert(qkx[i] == qki[i]);
            }
            lemma_group_members_of(xi, k, pool);
            assert(qkx.drop_last() =~= qki);
            assert(qax.drop_last() =~= qai);
            assert(pool.contains(qkx[qkx.len() - 1]));
            assert(row_not_distinct((g.key)(x), k) <==> (g.key)(x) == k);
        } else {
            assert(qkx =~= qki);
            assert(qax =~= qai);
            lemma_group_members_of(xi, k, pool);
        }
    } else {
        assert(qkeys(g, xs) =~= Seq::<Row>::empty());
    }
}

/// The GROUP BY's groups are `gkeys(gq, xs)`, and each group's members are `members_of(xs, k)`.
pub proof fn lemma_groups(xs: Seq<Row>)
    requires rows_typed(xs),
    ensures
        distinct_rows(qkeys(gq(), xs)) == gkeys(gq(), xs),
        forall|k: Row| #[trigger] gkeys(gq(), xs).contains(k) ==>
            group_members(qkeys(gq(), xs), qrows(gq(), xs).map_values(|x: Row| args_of(x)), k) == members_of(xs, k),
{
    let g = gq();
    let pool = key_pool(g, xs);
    lemma_keys_exact(xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    assert forall|k: Row| #[trigger] gkeys(g, xs).contains(k) implies
        group_members(qkeys(g, xs), qrows(g, xs).map_values(|x: Row| args_of(x)), k) == members_of(xs, k) by {
        let i = choose|i: int| 0 <= i < gkeys(g, xs).len() && gkeys(g, xs)[i] == k;
        assert(pool.contains(gkeys(g, xs)[i]));
        lemma_group_members_of(xs, k, pool);
    }
}

// ----------------------------------------------------------------------------------------- one group's columns

/// Some qualifying row of group `k` has adsh `v`.
pub open spec fn has_adsh(xs: Seq<Row>, k: Row, v: Val) -> bool {
    exists|i: int| 0 <= i < xs.len() && #[trigger] hit(gq(), xs[i], k) && xs[i][0] == v
}

/// The members' columns: the count, the adsh values (all text; `v` is one exactly when `has_adsh`) and the lines (int4: kind,
/// count, exact sum, absolute mass).
pub proof fn lemma_members(xs: Seq<Row>, k: Row)
    requires rows_typed(xs),
    ensures ({
        let m = members_of(xs, k);
        let ad = column(m, 1);
        let ln = column(m, 2);
        &&& m.len() == gcount(gq(), xs, k)
        &&& column(m, 0).len() == gcount(gq(), xs, k)
        &&& forall|i: int| 0 <= i < ad.len() ==> #[trigger] ad[i] is Text
        &&& forall|v: Val| #[trigger] ad.contains(v) <==> has_adsh(xs, k, v)
        &&& all_of_kind(NumKind::Int4, ln)
        &&& count_non_null(ln) == gcount(gq(), xs, k)
        &&& int_sum(ln) == gsum(gq(), xs, k, 0)
        &&& int_mass(ln) <= 0x8000_0000 * gcount(gq(), xs, k)
    }),
    decreases xs.len(),
{
    let m = members_of(xs, k);
    let ad = column(m, 1);
    let ln = column(m, 2);
    if xs.len() == 0 {
        assert(ad =~= Seq::<Val>::empty());
        assert(column(m, 0) =~= Seq::<Val>::empty());
        assert(ln =~= Seq::<Val>::empty());
    } else {
        let xi = xs.drop_last();
        let x = xs.last();
        assert forall|i: int| 0 <= i < xi.len() implies #[trigger] row_typed(xi[i]) by {
            assert(xi[i] == xs[i]);
        }
        lemma_members(xi, k);
        let mi = members_of(xi, k);
        let adi = column(mi, 1);
        let lni = column(mi, 2);
        assert(row_typed(xs[xs.len() - 1]));
        if hit(gq(), x, k) {
            assert(m == mi.push(args_of(x)));
            assert(ad =~= adi.push(x[0]));
            assert(ln =~= lni.push(x[1]));
            assert(column(m, 0) =~= column(mi, 0).push(Val::Null));
            assert(ad.drop_last() =~= adi);
            assert(ln.drop_last() =~= lni);
            assert forall|i: int| 0 <= i < ad.len() implies #[trigger] ad[i] is Text by {
                if i < adi.len() { assert(ad[i] == adi[i]); }
            }
            assert forall|v: Val| #[trigger] ad.contains(v) <==> has_adsh(xs, k, v) by {
                    if ad.contains(v) {
                        let i = choose|i: int| 0 <= i < ad.len() && ad[i] == v;
                        if i < adi.len() {
                            assert(adi[i] == v);
                            assert(adi.contains(v));
                            assert(has_adsh(xi, k, v));
                            let j = choose|j: int| 0 <= j < xi.len() && #[trigger] hit(gq(), xi[j], k) && xi[j][0] == v;
                            assert(xs[j] == xi[j]);
                            assert(hit(gq(), xs[j], k));
                        } else {
                            assert(hit(gq(), xs[xs.len() - 1], k));
                        }
                    }
                    if has_adsh(xs, k, v) {
                        let j = choose|j: int| 0 <= j < xs.len() && #[trigger] hit(gq(), xs[j], k) && xs[j][0] == v;
                        if j < xi.len() {
                            assert(xi[j] == xs[j]);
                            assert(hit(gq(), xi[j], k));
                            assert(has_adsh(xi, k, v));
                            assert(adi.contains(v));
                            let i = choose|i: int| 0 <= i < adi.len() && adi[i] == v;
                            assert(ad[i] == v);
                            assert(ad.contains(v));
                        } else {
                            assert(ad[ad.len() - 1] == v);
                            assert(ad.contains(v));
                        }
                    }
            }
            let v = x[1]->Int_0;
            assert(line_of(x) == v);
            assert(-0x8000_0000 <= v <= 0x7fff_ffff);
        } else {
            assert(m == mi);
            assert forall|v: Val| has_adsh(xs, k, v) <==> has_adsh(xi, k, v) by {
                if has_adsh(xs, k, v) {
                    let j = choose|j: int| 0 <= j < xs.len() && #[trigger] hit(gq(), xs[j], k) && xs[j][0] == v;
                    assert(j < xi.len());
                    assert(xi[j] == xs[j]);
                    assert(hit(gq(), xi[j], k));
                }
                if has_adsh(xi, k, v) {
                    let j = choose|j: int| 0 <= j < xi.len() && #[trigger] hit(gq(), xi[j], k) && xi[j][0] == v;
                    assert(xi[j] == xs[j]);
                    assert(hit(gq(), xs[j], k));
                }
            }
        }
    }
}

} // verus!
