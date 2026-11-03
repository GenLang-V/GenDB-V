// Framework test fixture (hand-written framework test input, not an author output, not a
// TPC-H query): an agent module for the fixed entry v3 on
//   SELECT id + $3 AS shifted, reading, tag FROM sensor WHERE reading >= $1 AND day < $2
// over sensor(id integer, site integer, reading numeric(10,2), day date, tag varchar(8), note text) (table id 1),
// with `$1 numeric(10,2)` free (slot 0), `$2 = DATE '2020-06-30'` FIXED and `$3 integer` free (slot 1). Delivered
// columns: t0_f0 = id, t0_f1 = reading, t0_f2 = day, t0_f3 = tag.
//
// Everything below the fixed interface is this module's own choice, as it would be an author's: the representation
// (the delivered columns copied into parts), the intermediate specification `outs` (the qualifying rows' outputs,
// or the first SQL error, over the source relation), the bridge `lemma_meaning` from the VERUS_SQL meaning of the
// statement to `outs`, and a sequential scan. `id + $3` can leave `integer`: the statement's meaning is then EXACTLY
// the SQL error 22003 (`NumericValueOutOfRange`), which is what this module answers.
use vstd::prelude::*;
use crate::gendb_abi::{OwnedPart, Part};
use crate::gendb_source::*;
use crate::gendb_params::Params;
use crate::gendb_entry::layout::{owned_parts_view, parts_view, PartView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::work::{filled, text_bytes};
use crate::gendb_entry::{answer_meets, bound_db, built_from, outcome_ok, stored_asset, Answer};
use crate::gendb_entry::runtime::QueryError;
use crate::query::{param_domain, query_spec_at, schema_spec};
use crate::exec::value::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::{int_result, IntKind};
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::datetime::{date_from_civil, date_valid, valid_ymd};
use crate::spec::typing::{db_wf, row_in_table};
use crate::bridge::collect::{lemma_collect_all, lemma_collect_first_err};
use crate::exec::relational::domain::{filter_results, project_results, lemma_eval_filter, lemma_eval_project};
use crate::link::query::{proj, proj_all, view_rows, text_at};
use crate::link::expr::{lemma_expr_col, lemma_pred_cmp, lemma_pred_and, lemma_compare_num, lemma_compare_date};
use crate::link::source::lemma_proj_all_index;
use crate::link::outcome::{lemma_outcome_err, lemma_outcome_rows, lemma_view_rows_push};

verus! {

// ------------------------------------------------------------------------------------------ representation

pub open spec fn shaped(parts: Seq<PartView>) -> bool {
    parts.len() == 5 && parts[0] is I32 && parts[1] is I128 && parts[2] is I32 && parts[3] is I64 && parts[4] is U8
}

pub open spec fn view_of(parts: Seq<PartView>) -> SourceView {
    SourceView {
        t0_f0: parts[0]->I32_0,
        t0_f1: parts[1]->I128_0,
        t0_f2: parts[2]->I32_0,
        t0_f3: TextView { offsets: parts[3]->I64_0, bytes: parts[4]->U8_0 },
    }
}

pub open spec fn decode(parts: Seq<PartView>) -> Option<Seq<Seq<Row>>> {
    if shaped(parts) && source_wf(view_of(parts)) && in_domain(tables(view_of(parts))) {
        Some(tables(view_of(parts)))
    } else {
        None
    }
}

fn copy<T: Copy>(s: &[T]) -> (v: Vec<T>)
    ensures v@ == s@,
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant i <= s.len(), v@ == s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        v.push(s[i]);
        i = i + 1;
    }
    assert(v@ =~= s@);
    v
}

pub fn build(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires source_wf(src@), in_domain(tables(src@)),
    ensures r matches Ok(p) && decode(owned_parts_view(p@)) == Some(tables(src@)),
{
    let parts = vec![
        OwnedPart::I32(copy(src.t0_f0)),
        OwnedPart::I128(copy(src.t0_f1)),
        OwnedPart::I32(copy(src.t0_f2)),
        OwnedPart::I64(copy(src.t0_f3.offsets)),
        OwnedPart::U8(copy(src.t0_f3.bytes)),
    ];
    proof {
        let pv = owned_parts_view(parts@);
        assert(shaped(pv));
        assert(view_of(pv) == src@);
    }
    Ok(parts)
}

// ------------------------------------------------------------------------------------------ intermediate specification

/// Coefficient of a numeric value, day of a date value, value of an integer.
pub open spec fn num_coeff(v: Val) -> int { match v { Val::Num { coeff, .. } => coeff, _ => 0 } }
pub open spec fn date_day(v: Val) -> int { match v { Val::Date(d) => d, _ => 0 } }
pub open spec fn int_val(v: Val) -> int { match v { Val::Int(x) => x, _ => 0 } }

/// PostgreSQL day number of 2020-06-30 (the fixed `$2`).
pub open spec fn cutoff() -> int { 7486 }

/// Row `r = [id, reading, day, tag]` of the source relation qualifies at `$1 = p0` (coefficient at scale 2).
pub open spec fn qual_row(r: Row, p0: int) -> bool {
    num_coeff(r[1]) >= p0 && date_day(r[2]) < cutoff()
}

/// The output row of a qualifying source row at `$3 = p1`, or the SQL error of `id + $3` outside `integer`.
pub open spec fn out_row(r: Row, p1: int) -> Result<Row, SqlError> {
    let s = int_val(r[0]) + p1;
    if -2147483648 <= s <= 2147483647 {
        Ok(seq![Val::Int(s), r[1], r[3]])
    } else {
        Err(SqlError::NumericValueOutOfRange)
    }
}

/// The outputs of the qualifying rows among the first `k` source rows, in row order, or the first SQL error.
pub open spec fn outs(t: Seq<Row>, p0: int, p1: int, k: int) -> Result<Seq<Row>, SqlError>
    decreases k,
{
    if k <= 0 {
        Ok(Seq::empty())
    } else {
        match outs(t, p0, p1, k - 1) {
            Err(e) => Err(e),
            Ok(o) => if qual_row(t[k - 1], p0) {
                match out_row(t[k - 1], p1) {
                    Err(e) => Err(e),
                    Ok(r) => Ok(o.push(r)),
                }
            } else {
                Ok(o)
            },
        }
    }
}

proof fn lemma_outs_err_persists(t: Seq<Row>, p0: int, p1: int, k: int, m: int, e: SqlError)
    requires outs(t, p0, p1, k) == Err::<Seq<Row>, SqlError>(e), k <= m,
    ensures outs(t, p0, p1, m) == Err::<Seq<Row>, SqlError>(e),
    decreases m - k,
{
    if k < m {
        lemma_outs_err_persists(t, p0, p1, k, m - 1, e);
    }
}

// ------------------------------------------------------------------------------------------ bridge to the meaning

/// The binding of the free parameters: `$1` coefficient `p0`, `$3` value `p1`.
pub open spec fn binding(p0: int, p1: int) -> Seq<Literal> {
    seq![Literal::Num { coeff: p0, scale: 2 }, Literal::Int { v: p1, kind: IntKind::Int4 }]
}

pub open spec fn pred_at(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(2), b: Expr::Lit(ps[0]) }),
        Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(3), b: Expr::Lit(Literal::Date { y: 2020, m: 6, d: 30 }) }),
    )
}

pub open spec fn exprs_at(ps: Seq<Literal>) -> Seq<Expr> {
    seq![
        Expr::Arith { op: ArithOp::Add, kind: NumKind::Int4, a: Box::new(Expr::Col(0)), b: Box::new(Expr::Lit(ps[1])) },
        Expr::Col(2),
        Expr::Col(4),
    ]
}

proof fn lemma_statement(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == (Query::Project {
            exprs: exprs_at(ps),
            input: Box::new(Query::Filter { pred: pred_at(ps), input: Box::new(Query::Table(1)) }),
        }),
        query_spec_at(ps).keys.len() == 0,
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
    assert(query_spec_at(ps).keys =~= Seq::<OrderKey>::empty());
}

/// A full database row of `sensor` and its source-relation row.
proof fn lemma_row_parts(db: Database, v: SourceView, i: int)
    requires bound_db(v, db), 0 <= i < table_t0(v).len(),
    ensures
        db.tables.len() == 2,
        db.tables[1].len() == table_t0(v).len(),
        db.tables[1][i].len() == 6,
        db.tables[1][i][0] == table_t0(v)[i][0],
        db.tables[1][i][2] == table_t0(v)[i][1],
        db.tables[1][i][3] == table_t0(v)[i][2],
        db.tables[1][i][4] == table_t0(v)[i][3],
        table_t0(v)[i] == seq![Val::Int(v.t0_f0[i] as int), Val::Num { coeff: v.t0_f1[i] as int, scale: 2 }, date32_val(v.t0_f2[i]), Val::Text(text_at(v.t0_f3, i))],
{
    lemma_source_schema();
    let rows = db.tables[1];
    lemma_proj_all_index(rows, source_cols_t0());
    assert(row_in_table(rows[i], db.schema[1]));
}

/// The literals of the statement are values: `$1`, `$3` (typed by `param_domain`) and the fixed day 7486.
proof fn lemma_literals(ps: Seq<Literal>, p0: int, p1: int)
    requires ps == binding(p0, p1), param_domain(ps),
    ensures
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Num { coeff: p0, scale: 2 }),
        lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Int(p1)),
        lit_val(Literal::Date { y: 2020, m: 6, d: 30 }) == Ok::<Val, SqlError>(Val::Date(cutoff())),
{
    assert(valid_ymd(2020, 6, 30) && date_from_civil(2020, 6, 30) == cutoff() && date_valid(cutoff())) by (compute);
}

/// The condition of one row whose columns 2 and 3 are a scale-2 numeric and a date.
proof fn lemma_pred_row(db: Database, env: Row, ps: Seq<Literal>, p0: int, c: int, d: int)
    requires
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Num { coeff: p0, scale: 2 }),
        lit_val(Literal::Date { y: 2020, m: 6, d: 30 }) == Ok::<Val, SqlError>(Val::Date(cutoff())),
        env.len() == 6, env[2] == (Val::Num { coeff: c, scale: 2 }), env[3] == Val::Date(d),
    ensures eval_pred(db, env, pred_at(ps)) == Ok::<Truth, SqlError>(truth_of(c >= p0 && d < cutoff())),
{
    let date = Literal::Date { y: 2020, m: 6, d: 30 };
    lemma_expr_col(db, env, 2);
    lemma_expr_col(db, env, 3);
    assert(eval_expr(db, env, Expr::Lit(ps[0])) == lit_val(ps[0]));
    assert(eval_expr(db, env, Expr::Lit(date)) == lit_val(date));
    assert(crate::spec::numeric::pow10(0) == 1);
    lemma_compare_num(c, 2, p0, 2);
    lemma_pred_cmp(db, env, CmpOp::Ge, Expr::Col(2), Expr::Lit(ps[0]), env[2], Val::Num { coeff: p0, scale: 2 }, c, p0);
    lemma_compare_date(d, cutoff());
    lemma_pred_cmp(db, env, CmpOp::Lt, Expr::Col(3), Expr::Lit(date), env[3], Val::Date(cutoff()), d, cutoff());
    lemma_pred_and(db, env,
        Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(2), b: Expr::Lit(ps[0]) },
        Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(3), b: Expr::Lit(date) },
        c >= p0, d < cutoff());
}

/// `id + $3` at type `integer`.
proof fn lemma_add_row(db: Database, env: Row, ps: Seq<Literal>, p1: int, id: int)
    requires lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Int(p1)), env.len() == 6, env[0] == Val::Int(id),
    ensures exprs_at(ps)[0] == (Expr::Arith { op: ArithOp::Add, kind: NumKind::Int4, a: Box::new(Expr::Col(0)), b: Box::new(Expr::Lit(ps[1])) }),
        eval_expr(db, env, exprs_at(ps)[0]) == int_result(IntKind::Int4, id + p1),
{
    lemma_expr_col(db, env, 0);
    assert(eval_expr(db, env, Expr::Lit(ps[1])) == lit_val(ps[1]));
}

/// The projection of one row whose column 0 is an integer.
proof fn lemma_exprs_row(db: Database, env: Row, ps: Seq<Literal>, p1: int, id: int)
    requires lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Int(p1)), env.len() == 6, env[0] == Val::Int(id),
    ensures
        eval_exprs(db, env, exprs_at(ps)) == if -2147483648 <= id + p1 <= 2147483647 {
            Ok::<Row, SqlError>(seq![Val::Int(id + p1), env[2], env[4]])
        } else {
            Err::<Row, SqlError>(SqlError::NumericValueOutOfRange)
        },
{
    hide(eval_expr);
    hide(eval_pred);
    hide(eval_query);
    hide(collect);
    hide(int_result);
    let es = exprs_at(ps);
    lemma_add_row(db, env, ps, p1, id);
    lemma_expr_col(db, env, 2);
    lemma_expr_col(db, env, 4);
    let r0 = int_result(IntKind::Int4, id + p1);
    let rs = expr_results(db, env, es);
    assert(rs =~= seq![r0, Ok::<Val, SqlError>(env[2]), Ok::<Val, SqlError>(env[4])]);
    lemma_collect3(r0, env[2], env[4], id + p1);
}

/// `collect` of `[int_result(int4, s), Ok(a), Ok(b)]`.
proof fn lemma_collect3(r0: Result<Val, SqlError>, a: Val, b: Val, s: int)
    requires r0 == int_result(IntKind::Int4, s),
    ensures
        collect(seq![r0, Ok::<Val, SqlError>(a), Ok::<Val, SqlError>(b)]) == if -2147483648 <= s <= 2147483647 {
            Ok::<Row, SqlError>(seq![Val::Int(s), a, b])
        } else {
            Err::<Row, SqlError>(SqlError::NumericValueOutOfRange)
        },
{
    let rs = seq![r0, Ok::<Val, SqlError>(a), Ok::<Val, SqlError>(b)];
    if -2147483648 <= s <= 2147483647 {
        let o = seq![Val::Int(s), a, b];
        assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(o[j]) by {
            if j == 0 {} else if j == 1 {} else {}
        }
        lemma_collect_all(rs, o);
    } else {
        lemma_collect_first_err(rs, 0);
    }
}

/// Condition and projection of one database row, from its source-relation row.
proof fn lemma_row_meaning(db: Database, v: SourceView, ps: Seq<Literal>, p0: int, p1: int, i: int)
    requires bound_db(v, db), 0 <= i < table_t0(v).len(), ps == binding(p0, p1), param_domain(ps),
    ensures
        eval_pred(db, Seq::<Val>::empty() + db.tables[1][i], pred_at(ps)) == Ok::<Truth, SqlError>(truth_of(qual_row(table_t0(v)[i], p0))),
        eval_exprs(db, Seq::<Val>::empty() + db.tables[1][i], exprs_at(ps)) == out_row(table_t0(v)[i], p1),
{
    lemma_row_parts(db, v, i);
    let r = db.tables[1][i];
    let t = table_t0(v)[i];
    let env = Seq::<Val>::empty() + r;
    assert(env =~= r);
    lemma_literals(ps, p0, p1);
    lemma_pred_row(db, env, ps, p0, v.t0_f1[i] as int, v.t0_f2[i] as int - 10957);
    lemma_exprs_row(db, env, ps, p1, v.t0_f0[i] as int);
}

/// The projection of the kept rows among the first `k` database rows is `outs` of the first `k` source rows.
proof fn lemma_prefix(db: Database, v: SourceView, ps: Seq<Literal>, p0: int, p1: int, truths: Seq<Truth>, k: int)
    requires
        bound_db(v, db), ps == binding(p0, p1), param_domain(ps),
        0 <= k <= table_t0(v).len(),
        truths.len() == table_t0(v).len(),
        db.tables[1].len() == table_t0(v).len(),
        forall|i: int| 0 <= i < truths.len() ==> #[trigger] truths[i] == truth_of(qual_row(table_t0(v)[i], p0)),
    ensures
        collect(project_results(db, Seq::empty(), keep_true(db.tables[1].subrange(0, k), truths.subrange(0, k)), exprs_at(ps)))
            == outs(table_t0(v), p0, p1, k),
    decreases k,
{
    let rows = db.tables[1];
    let t = table_t0(v);
    let es = exprs_at(ps);
    if k == 0 {
        assert(rows.subrange(0, 0) =~= Seq::<Row>::empty() && truths.subrange(0, 0) =~= Seq::<Truth>::empty());
        assert(project_results(db, Seq::empty(), keep_true(rows.subrange(0, 0), truths.subrange(0, 0)), es) =~= Seq::<Result<Row, SqlError>>::empty());
    } else {
        let j = k - 1;
        lemma_prefix(db, v, ps, p0, p1, truths, j);
        let kept = keep_true(rows.subrange(0, j), truths.subrange(0, j));
        let (r1, t1) = (rows.subrange(0, k), truths.subrange(0, k));
        assert(r1.drop_last() =~= rows.subrange(0, j) && t1.drop_last() =~= truths.subrange(0, j));
        assert(r1.last() == rows[j] && t1.last() == truths[j]);
        let prev = project_results(db, Seq::empty(), kept, es);
        lemma_row_meaning(db, v, ps, p0, p1, j);
        if qual_row(t[j], p0) {
            assert(keep_true(r1, t1) == kept.push(rows[j]));
            let next = project_results(db, Seq::empty(), kept.push(rows[j]), es);
            assert(next.drop_last() =~= prev);
            assert(next.last() == eval_exprs(db, Seq::<Val>::empty() + rows[j], es));
        } else {
            assert(keep_true(r1, t1) == kept);
        }
    }
}

/// The meaning of the statement at binding `ps` on every database bound to the delivered columns `v`.
proof fn lemma_meaning(db: Database, v: SourceView, ps: Seq<Literal>, p0: int, p1: int)
    requires bound_db(v, db), ps == binding(p0, p1), param_domain(ps),
    ensures denote_body(db, query_spec_at(ps)) == outs(table_t0(v), p0, p1, table_t0(v).len() as int),
{
    lemma_statement(ps);
    lemma_source_schema();
    let t = table_t0(v);
    let n = t.len() as int;
    let rows = db.tables[1];
    let pred = pred_at(ps);
    let es = exprs_at(ps);
    assert(rows.len() == n) by {
        lemma_proj_all_index(rows, source_cols_t0());
    }
    // Filter: every condition is a value.
    let truths = Seq::new(n as nat, |i: int| truth_of(qual_row(t[i], p0)));
    let fr = filter_results(db, Seq::empty(), rows, pred);
    assert forall|i: int| 0 <= i < fr.len() implies #[trigger] fr[i] == Ok::<Truth, SqlError>(truths[i]) by {
        lemma_row_meaning(db, v, ps, p0, p1, i);
    }
    lemma_collect_all(fr, truths);
    lemma_eval_filter(db, Seq::empty(), pred, Box::new(Query::Table(1)));
    lemma_eval_project(db, Seq::empty(), es, Box::new(Query::Filter { pred, input: Box::new(Query::Table(1)) }));
    assert(eval_query(db, Seq::empty(), Query::Table(1)) == Ok::<Relation, SqlError>(rows));
    // Projection over the kept rows.
    lemma_prefix(db, v, ps, p0, p1, truths, n);
    assert(rows.subrange(0, n) =~= rows && truths.subrange(0, n) =~= truths);
}

// ------------------------------------------------------------------------------------------ query

/// The same row as `table_t0(w)[i]` for a copied source view.
proof fn lemma_facts(w: SourceView, i: int)
    requires source_wf(w), 0 <= i < source_rows_t0(w),
    ensures
        table_t0(w).len() == source_rows_t0(w),
        table_t0(w)[i] == seq![Val::Int(w.t0_f0[i] as int), Val::Num { coeff: w.t0_f1[i] as int, scale: 2 }, date32_val(w.t0_f2[i]), Val::Text(text_at(w.t0_f3, i))],
        i + 1 < w.t0_f3.offsets.len(),
        0 <= w.t0_f3.offsets[i],
        w.t0_f3.offsets[i] <= w.t0_f3.offsets[i + 1],
        w.t0_f3.offsets[i + 1] <= w.t0_f3.bytes.len(),
{
    assert(0 <= w.t0_f3.offsets[i] <= w.t0_f3.offsets[i + 1] <= w.t0_f3.bytes.len());
}

pub fn query(parts: &[Part], params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stored_asset(parts_view(parts@)),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        forall|v: SourceView| built_from(v, parts_view(parts@)) ==> answer_meets(v, params@, r),
{
    let ghost pv = parts_view(parts@);
    proof {
        let v0 = choose|v: SourceView| built_from(v, pv);
        assert(shaped(pv));
    }
    if parts.len() != 5 {
        return Err(QueryError::Malformed);
    }
    let ids: &[i32] = match &parts[0] { Part::I32(s) => *s, _ => return Err(QueryError::Malformed) };
    let readings: &[i128] = match &parts[1] { Part::I128(s) => *s, _ => return Err(QueryError::Malformed) };
    let days: &[i32] = match &parts[2] { Part::I32(s) => *s, _ => return Err(QueryError::Malformed) };
    let offsets: &[i64] = match &parts[3] { Part::I64(s) => *s, _ => return Err(QueryError::Malformed) };
    let bytes: &[u8] = match &parts[4] { Part::U8(s) => *s, _ => return Err(QueryError::Malformed) };
    let tag = TextCol { offsets, bytes };
    let ghost w = view_of(pv);
    let ghost t = table_t0(w);
    let ghost ps = params@;
    assert(w.t0_f0 == ids@ && w.t0_f1 == readings@ && w.t0_f2 == days@ && w.t0_f3 == tag@);
    assert(decode(pv) == Some(tables(w)));
    let p0 = params.p0;
    let shift = params.p1;
    assert(ps == binding(p0 as int, shift as int));
    assert(-2147483648 <= shift <= 2147483647);
    let n = ids.len();
    let mut out: Vec<Vec<EVal>> = Vec::new();
    let mut i: usize = 0;
    assert(view_rows(out@) =~= Seq::<Row>::empty());
    while i < n
        invariant
            pv == parts_view(parts@), w == view_of(pv), ps == params@, ps == binding(p0 as int, shift as int), param_domain(ps),
            decode(pv) == Some(tables(w)),
            source_wf(w), t == table_t0(w), n == source_rows_t0(w), i <= n,
            w.t0_f0 == ids@, w.t0_f1 == readings@, w.t0_f2 == days@, w.t0_f3 == tag@,
            -2147483648 <= shift <= 2147483647,
            outs(t, p0 as int, shift as int, i as int) == Ok::<Seq<Row>, SqlError>(view_rows(out@)),
        decreases n - i,
    {
        proof {
            lemma_facts(w, i as int);
        }
        if readings[i] >= p0 && days[i] < 18443 {
            let s: i64 = ids[i] as i64 + shift;
            if s < -2147483648 || s > 2147483647 {
                proof {
                    assert(outs(t, p0 as int, shift as int, i + 1) == Err::<Seq<Row>, SqlError>(SqlError::NumericValueOutOfRange));
                    lemma_outs_err_persists(t, p0 as int, shift as int, i + 1, n as int, SqlError::NumericValueOutOfRange);
                    assert forall|v: SourceView, db: Database| built_from(v, pv) && #[trigger] bound_db(v, db)
                        implies ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)) by {
                        assert(tables(v) == tables(w));
                        assert(table_t0(v) == tables(v)[0]);
                        lemma_meaning(db, v, ps, p0 as int, shift as int);
                        lemma_outcome_err(db, query_spec_at(ps), SqlError::NumericValueOutOfRange);
                    }
                }
                return Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));
            }
            let row: Vec<EVal> = vec![EVal::Int(s), EVal::Num { coeff: readings[i], scale: 2 }, EVal::Text(copy(text_bytes(&tag, i)))];
            proof {
                assert(view_row(row@) =~= seq![Val::Int(s as int), Val::Num { coeff: readings[i as int] as int, scale: 2 }, Val::Text(text_at(w.t0_f3, i as int))]);
                lemma_view_rows_push(out@, row);
            }
            out.push(row);
        }
        i = i + 1;
    }
    proof {
        assert forall|v: SourceView, db: Database| built_from(v, pv) && #[trigger] bound_db(v, db)
            implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(out@))) by {
            assert(tables(v) == tables(w));
            assert(table_t0(v) == tables(v)[0]);
            lemma_meaning(db, v, ps, p0 as int, shift as int);
            lemma_statement(ps);
            lemma_outcome_rows(db, query_spec_at(ps), view_rows(out@));
        }
    }
    Ok(Answer::Rows(out))
}

} // verus!
