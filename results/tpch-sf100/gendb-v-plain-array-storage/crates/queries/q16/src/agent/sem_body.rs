//! The statement body over one database: `FROM partsupp, part` is the left-major product (`from_rows`, row
//! `c * |part| + a` is `prow(c, a)`); the WHERE either fails with the error of the first part row whose `LIKE`
//! fails (`lemma_body_err`), or keeps the rows satisfying `row_qual` (= `qual` on product rows), and the GROUP BY
//! then groups the kept rows by `(p_brand, p_type, p_size)` with argument `ps_suppkey` (`lemma_body_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::query::param_domain;
use crate::link::join::{keep, lemma_keep_true_keep, lemma_keep_members, lemma_product_index};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise, lemma_collect_first_err};
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::sem_sub::*;
use crate::agent::sem_row::*;
use crate::agent::common::group_distinct::count_distinct_aggs;

verus! {

/// The rows of `FROM partsupp, part`.
pub open spec fn from_rows(sv: StoresView) -> Seq<Row> {
    product_rows(ps_rows(sv), part_rows(sv))
}

/// The WHERE condition as a function of a product row's values (`qual` on `prow(c, a)`).
pub open spec fn row_qual(sv: StoresView, ps: Seq<Literal>, r: Row) -> bool {
    &&& r[0] == r[5]
    &&& r[8] != Val::Text(brand_lit(ps))
    &&& like_res(r[9]->Text_0, pat_lit(ps)) != Ok::<Val, SqlError>(Val::Bool(true))
    &&& size_match(ps, 8, r[10]->Int_0)
    &&& !excluded(sv, r[1]->Int_0)
}

/// The rows the WHERE keeps (when no `LIKE` fails).
pub open spec fn kept_rows(sv: StoresView, ps: Seq<Literal>) -> Seq<Row> {
    keep(from_rows(sv), |r: Row| row_qual(sv, ps, r))
}

/// The group key and the aggregate argument of a kept row.
pub open spec fn key_of_row(r: Row) -> Row { seq![r[8], r[9], r[10]] }
pub open spec fn arg_of_row(r: Row) -> Row { seq![r[1]] }

/// The GROUP BY input: keys and arguments of the kept rows.
pub open spec fn grp_keys(sv: StoresView, ps: Seq<Literal>) -> Seq<Row> {
    kept_rows(sv, ps).map_values(|r: Row| key_of_row(r))
}
pub open spec fn grp_args(sv: StoresView, ps: Seq<Literal>) -> Seq<Row> {
    kept_rows(sv, ps).map_values(|r: Row| arg_of_row(r))
}

/// The aggregate list is `COUNT(DISTINCT ps_suppkey)`.
pub proof fn lemma_group_aggs()
    ensures group_aggs() == count_distinct_aggs(Expr::Col(1)),
{
}

/// `row_qual` on product row `(c, a)` is `qual`.
pub proof fn lemma_row_qual(sv: StoresView, ps: Seq<Literal>, c: int, a: int)
    requires stores_wf(sv), 0 <= c < ps_n(sv), 0 <= a < part_n(sv),
    ensures row_qual(sv, ps, prow(sv, c, a)) == qual(sv, ps, c, a),
{
    lemma_prow(sv, c, a);
}

/// Row `i` of the product is `prow(i / |part|, i % |part|)`.
pub proof fn lemma_from_index(sv: StoresView, i: int)
    requires 0 <= i < from_rows(sv).len(),
    ensures
        part_n(sv) > 0,
        from_rows(sv).len() == ps_n(sv) * part_n(sv),
        0 <= i / (part_n(sv) as int) < ps_n(sv), 0 <= i % (part_n(sv) as int) < part_n(sv),
        from_rows(sv)[i] == prow(sv, i / (part_n(sv) as int), i % (part_n(sv) as int)),
{
    let (q, p) = (ps_rows(sv), part_rows(sv));
    lemma_product_index(q, p);
    let np = part_n(sv) as int;
    let nq = ps_n(sv) as int;
    assert(np > 0) by (nonlinear_arith) requires 0 <= i < nq * np, nq >= 0, np >= 0;
    let c = i / np;
    let a = i % np;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, np);
    vstd::arithmetic::div_mod::lemma_mod_bound(i, np);
    assert(0 <= c < nq) by (nonlinear_arith) requires 0 <= i < nq * np, np > 0, c == i / np, i == np * c + a, 0 <= a < np;
    assert(c * np + a == i) by (nonlinear_arith) requires i == np * c + a;
    assert(from_rows(sv)[c * p.len() + a] == q[c] + p[a]);
}

/// `FROM partsupp, part` evaluates to the product (in any context).
pub proof fn lemma_eval_from(db: Database, sv: StoresView)
    requires tables_of(sv, db),
    ensures eval_query(db, Seq::empty(), from_q()) == Ok::<Relation, SqlError>(from_rows(sv)),
{
    assert(eval_query(db, Seq::empty(), Query::Table(4)) == Ok::<Relation, SqlError>(ps_rows(sv)));
    assert(eval_query(db, Seq::empty(), Query::Table(3)) == Ok::<Relation, SqlError>(part_rows(sv)));
}

/// The WHERE of every product row, when no part's `LIKE` fails.
#[verifier::spinoff_prover]
proof fn lemma_where_all(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires
        tables_of(sv, db), stores_wf(sv), param_domain(ps),
        forall|a: int| 0 <= a < part_n(sv) ==> #[trigger] type_res(sv, ps, a) is Ok,
    ensures
        eval_query(db, Seq::empty(), filtered(ps)) == Ok::<Relation, SqlError>(kept_rows(sv, ps)),
{
    let rows = from_rows(sv);
    let f = |r: Row| row_qual(sv, ps, r);
    lemma_eval_from(db, sv);
    let ctx = Seq::<Val>::empty();
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], where_pred(ps)));
    let truths = Seq::new(rows.len(), |i: int| truth_of(f(rows[i])));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        lemma_from_index(sv, i);
        let np = part_n(sv) as int;
        let (c, a) = (i / np, i % np);
        assert(ctx + rows[i] =~= rows[i]);
        assert(type_res(sv, ps, a) is Ok);
        lemma_where_row(db, sv, ps, c, a);
        lemma_row_qual(sv, ps, c, a);
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    lemma_keep_true_keep(rows, truths, f);
}

/// The WHERE fails with the error of the first part row whose `LIKE` fails (partsupp non-empty).
#[verifier::spinoff_prover]
proof fn lemma_where_err(db: Database, sv: StoresView, ps: Seq<Literal>, a0: int)
    requires
        tables_of(sv, db), stores_wf(sv), param_domain(ps),
        ps_n(sv) > 0, 0 <= a0 < part_n(sv),
        type_res(sv, ps, a0) is Err,
        forall|a: int| 0 <= a < a0 ==> #[trigger] type_res(sv, ps, a) is Ok,
    ensures
        eval_query(db, Seq::empty(), filtered(ps)) == Err::<Relation, SqlError>(type_res(sv, ps, a0)->Err_0),
{
    let rows = from_rows(sv);
    lemma_eval_from(db, sv);
    let ctx = Seq::<Val>::empty();
    let np = part_n(sv) as int;
    lemma_product_index(ps_rows(sv), part_rows(sv));
    assert(rows.len() == ps_n(sv) * part_n(sv));
    assert(a0 < rows.len()) by (nonlinear_arith) requires a0 < np, ps_n(sv) >= 1, rows.len() == ps_n(sv) * np;
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], where_pred(ps)));
    assert forall|i: int| 0 <= i < a0 implies #[trigger] prs[i] is Ok by {
        assert(rows[0 * np + i] == ps_rows(sv)[0] + part_rows(sv)[i]);
        assert(ctx + rows[i] =~= rows[i]);
        lemma_where_row(db, sv, ps, 0, i);
    }
    assert(rows[0 * np + a0] == ps_rows(sv)[0] + part_rows(sv)[a0]);
    assert(ctx + rows[a0] =~= rows[a0]);
    lemma_where_row(db, sv, ps, 0, a0);
    assert(prs[a0] == Err::<Truth, SqlError>(type_res(sv, ps, a0)->Err_0));
    lemma_collect_first_err(prs, a0);
    lemma_collect_pointwise::<Truth>();
}

/// The group key of one kept row.
#[verifier::spinoff_prover]
proof fn lemma_group_key_row(db: Database, r: Row)
    requires r.len() == 14,
    ensures eval_exprs(db, r, group_keys()) == Ok::<Row, SqlError>(key_of_row(r)),
{
    let (e0, e1, e2) = (Expr::Col(8), Expr::Col(9), Expr::Col(10));
    let a1 = seq![e0];
    let a2 = seq![e0, e1];
    let a3 = seq![e0, e1, e2];
    lemma_eval_exprs_empty(db, r);
    assert(a1.drop_last() =~= Seq::<Expr>::empty());
    lemma_eval_exprs_step(db, r, a1);
    assert(eval_exprs(db, r, a1) == Ok::<Row, SqlError>(seq![r[8]])) by {
        assert(Seq::<Val>::empty().push(r[8]) =~= seq![r[8]]);
    }
    assert(a2.drop_last() =~= a1);
    lemma_eval_exprs_step(db, r, a2);
    assert(eval_exprs(db, r, a2) == Ok::<Row, SqlError>(seq![r[8], r[9]])) by {
        assert(seq![r[8]].push(r[9]) =~= seq![r[8], r[9]]);
    }
    assert(a3.drop_last() =~= a2);
    lemma_eval_exprs_step(db, r, a3);
    assert(seq![r[8], r[9]].push(r[10]) =~= key_of_row(r));
    assert(group_keys() == a3);
}

/// The aggregate argument of one kept row.
#[verifier::spinoff_prover]
proof fn lemma_group_arg_row(db: Database, r: Row)
    requires r.len() == 14,
    ensures agg_args(db, r, group_aggs()) == Ok::<Row, SqlError>(arg_of_row(r)),
{
    let aggs = group_aggs();
    let inner = Agg::Count(Expr::Col(1));
    assert(aggs[0] == Agg::DistinctAgg(Box::new(inner)));
    assert(agg_arg(db, r, inner) == Ok::<Val, SqlError>(r[1]));
    assert(agg_arg(db, r, aggs[0]) == Ok::<Val, SqlError>(r[1]));
    lemma_agg_arg_results_index(db, r, aggs);
    let ars = agg_arg_results(db, r, aggs);
    assert(ars.len() == 1);
    assert(ars[0] == Ok::<Val, SqlError>(r[1]));
    lemma_collect_all(ars, seq![r[1]]);
}

/// The GROUP BY inputs of one kept row: its key and its argument.
proof fn lemma_group_input_row(db: Database, r: Row)
    requires r.len() == 14,
    ensures
        eval_exprs(db, r, group_keys()) == Ok::<Row, SqlError>(key_of_row(r)),
        agg_args(db, r, group_aggs()) == Ok::<Row, SqlError>(arg_of_row(r)),
{
    lemma_group_key_row(db, r);
    lemma_group_arg_row(db, r);
}

/// The body when no part's `LIKE` fails: GROUP BY over the kept rows.
#[verifier::spinoff_prover]
pub proof fn lemma_body_ok(db: Database, sv: StoresView, ps: Seq<Literal>)
    requires
        tables_of(sv, db), stores_wf(sv), param_domain(ps),
        forall|a: int| 0 <= a < part_n(sv) ==> #[trigger] type_res(sv, ps, a) is Ok,
    ensures
        eval_query(db, Seq::empty(), body(ps)) == group_rows(group_aggs(), grp_keys(sv, ps), grp_args(sv, ps)),
{
    lemma_where_all(db, sv, ps);
    let rows = kept_rows(sv, ps);
    let ctx = Seq::<Val>::empty();
    let f = |r: Row| row_qual(sv, ps, r);
    lemma_keep_members(from_rows(sv), f);
    let ins = Seq::new(rows.len(), |i: int|
        match eval_exprs(db, ctx + rows[i], group_keys()) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, ctx + rows[i], group_aggs()) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        });
    let prepared = Seq::new(rows.len(), |i: int| (key_of_row(rows[i]), arg_of_row(rows[i])));
    assert forall|i: int| 0 <= i < ins.len() implies #[trigger] ins[i] == Ok::<(Row, Row), SqlError>(prepared[i]) by {
        assert(from_rows(sv).contains(rows[i]));
        let j = choose|j: int| 0 <= j < from_rows(sv).len() && from_rows(sv)[j] == rows[i];
        lemma_from_index(sv, j);
        let np = part_n(sv) as int;
        lemma_prow(sv, j / np, j % np);
        assert(ctx + rows[i] =~= rows[i]);
        lemma_group_input_row(db, rows[i]);
    }
    lemma_collect_all(ins, prepared);
    lemma_collect_pointwise::<(Row, Row)>();
    assert(prepared.map_values(|p: (Row, Row)| p.0) =~= grp_keys(sv, ps));
    assert(prepared.map_values(|p: (Row, Row)| p.1) =~= grp_args(sv, ps));
}

/// The body when the `LIKE` of part row `a0` fails first (partsupp non-empty): its error.
pub proof fn lemma_body_err(db: Database, sv: StoresView, ps: Seq<Literal>, a0: int)
    requires
        tables_of(sv, db), stores_wf(sv), param_domain(ps),
        ps_n(sv) > 0, 0 <= a0 < part_n(sv),
        type_res(sv, ps, a0) is Err,
        forall|a: int| 0 <= a < a0 ==> #[trigger] type_res(sv, ps, a) is Ok,
    ensures
        eval_query(db, Seq::empty(), body(ps)) == Err::<Relation, SqlError>(type_res(sv, ps, a0)->Err_0),
{
    lemma_where_err(db, sv, ps, a0);
}

} // verus!
