// Framework test fixture (hand-written framework test input, not an author output, not a
// TPC-H query): the query module of the fixed query entry v4 for
//   SELECT id, reading FROM sensor WHERE day < $1          ($1 date free, slot 0)
// over storage `sensor_days` (stored relation t = [id, reading, day] of sensor, canonical row order, zone map of day
// per block of BLOCK rows; `stores/sensor_days/interface`).
//
// Everything below the fixed interface is this module's own choice, as it would be an author's: the intermediate
// specification `outs` (the [id, reading] of the qualifying rows of t, in row order), the bridge `lemma_meaning` from
// the SQL meaning of the statement on every bound database to `outs`, and the access path: read the block minima
// (`blocks_before`), then request only the id/reading/day extents of the marked blocks and filter them exactly. A block
// that is not marked holds no qualifying row, so skipping it leaves `outs` unchanged.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::CmpOp;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::typing::{db_wf, row_in_table, value_in_column, type_lit};
use crate::spec::types::{Column, SqlType};
use crate::exec::value::*;
use crate::exec::ast::{view_lit, ELiteral};
use crate::exec::expr::lit_exec;
use crate::gendb_params::Params;
use crate::gendb_entry::{answer_meets, bound_db, outcome_ok, stores_ready, Answer};
use crate::gendb_entry::stores::{stored_ok, Stores, StoresView};
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::source_check::date32_val;
use crate::query::{param_domain, query_spec_at};
use crate::schema::schema_spec;
use crate::stores::sensor_days::declaration::*;
use crate::stores::sensor_days::interface::*;
use crate::bridge::collect::lemma_collect_all;
use crate::exec::relational::domain::{filter_results, project_results, lemma_eval_filter, lemma_eval_project};
use crate::link::query::{proj, proj_all, view_rows};
use crate::link::expr::{lemma_expr_col, lemma_pred_cmp, lemma_compare_date};
use crate::link::source::{compose_cols, lemma_proj_all_compose, lemma_proj_all_index};
use crate::link::outcome::{lemma_outcome_rows, lemma_view_rows_push};

verus! {

// ------------------------------------------------------------------------------------------ intermediate specification

/// Day number of a date value.
pub open spec fn date_day(v: Val) -> int { match v { Val::Date(d) => d, _ => 0 } }

/// The output columns [id, reading] among the stored columns [id, reading, day].
pub open spec fn out_cols() -> Seq<nat> { seq![0nat, 1] }

/// Stored row `r = [id, reading, day]` qualifies when its day is before `bound` (PostgreSQL day number).
pub open spec fn qual_row(r: Row, bound: int) -> bool {
    date_day(r[2]) < bound
}

/// The outputs of the qualifying rows among the first `k` stored rows, in row order.
pub open spec fn outs(t: Seq<Row>, bound: int, k: int) -> Seq<Row>
    decreases k,
{
    if k <= 0 {
        Seq::empty()
    } else if qual_row(t[k - 1], bound) {
        outs(t, bound, k - 1).push(proj(t[k - 1], out_cols()))
    } else {
        outs(t, bound, k - 1)
    }
}

/// Rows `[lo, hi)` without a qualifying row leave `outs` unchanged.
proof fn lemma_outs_skip(t: Seq<Row>, bound: int, lo: int, hi: int)
    requires 0 <= lo <= hi, forall|i: int| lo <= i < hi ==> !qual_row(#[trigger] t[i], bound),
    ensures outs(t, bound, hi) == outs(t, bound, lo),
    decreases hi - lo,
{
    if lo < hi {
        lemma_outs_skip(t, bound, lo, hi - 1);
    }
}

/// The stored relation the parts spell (the same for every database bound to them).
pub open spec fn spelled(parts: Seq<PartView>) -> Seq<Row> {
    Seq::new(days(parts).len(), |i: int| stored_row(parts, i))
}

// ------------------------------------------------------------------------------------------ bridge to the meaning

pub open spec fn pred_at(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(3), b: Expr::Lit(ps[0]) }
}

/// SELECT id, reading: sensor's columns 0 and 2 (= `compose_cols(stored_cols_t0(), out_cols())`).
pub open spec fn exprs() -> Seq<Expr> {
    seq![Expr::Col(0), Expr::Col(2)]
}

proof fn lemma_statement(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == (Query::Project {
            exprs: exprs(),
            input: Box::new(Query::Filter { pred: pred_at(ps), input: Box::new(Query::Table(1)) }),
        }),
        query_spec_at(ps).keys.len() == 0,
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
    assert(query_spec_at(ps).keys =~= Seq::<OrderKey>::empty());
}

/// Sensor's row `i`: six values, day a date, and its stored row and output are its projections.
proof fn lemma_row(db: Database, i: int)
    requires db.schema == schema_spec(), db_wf(db), 0 <= i < db.tables[1].len(),
    ensures
        db.tables[1][i].len() == 6,
        db.tables[1][i][3] is Date,
        stored_relations(db)[0].len() == db.tables[1].len(),
        stored_relations(db)[0][i] == proj(db.tables[1][i], stored_cols_t0()),
        stored_relations(db)[0][i][2] == db.tables[1][i][3],
        proj(stored_relations(db)[0][i], out_cols()) == seq![db.tables[1][i][0], db.tables[1][i][2]],
{
    lemma_declared_schema();
    lemma_stored_relations(db);
    let rows = db.tables[1];
    let t = stored_relations(db)[0];
    lemma_proj_all_index(rows, stored_cols_t0());
    assert(row_in_table(rows[i], db.schema[1]));
    assert(value_in_column(rows[i][3], db.schema[1].columns[3]));
    assert(db.schema[1].columns[3] == Column { ty: SqlType::Date, nullable: false });
    // Positions [0, 1] of the stored columns [0, 2, 3] are sensor's columns [0, 2].
    lemma_proj_all_compose(rows, stored_cols_t0(), out_cols());
    assert(compose_cols(stored_cols_t0(), out_cols()) =~= seq![0nat, 2]);
    lemma_proj_all_index(t, out_cols());
    lemma_proj_all_index(rows, seq![0nat, 2]);
    assert(proj(t[i], out_cols()) =~= seq![rows[i][0], rows[i][2]]);
}

/// The condition of a row whose column 3 is the date `d`.
proof fn lemma_pred_row(db: Database, env: Row, ps: Seq<Literal>, bound: int, d: int)
    requires lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(bound)), env.len() == 6, env[3] == Val::Date(d),
    ensures eval_pred(db, env, pred_at(ps)) == Ok::<Truth, SqlError>(truth_of(d < bound)),
{
    lemma_expr_col(db, env, 3);
    assert(eval_expr(db, env, Expr::Lit(ps[0])) == lit_val(ps[0]));
    lemma_compare_date(d, bound);
    lemma_pred_cmp(db, env, CmpOp::Lt, Expr::Col(3), Expr::Lit(ps[0]), env[3], Val::Date(bound), d, bound);
}

/// The projection `[id, reading]` of a row.
proof fn lemma_exprs_row(db: Database, env: Row)
    requires env.len() == 6,
    ensures eval_exprs(db, env, exprs()) == Ok::<Row, SqlError>(seq![env[0], env[2]]),
{
    hide(eval_expr);
    hide(eval_pred);
    hide(eval_query);
    hide(collect);
    assert(exprs().len() == 2 && exprs()[0] == Expr::Col(0) && exprs()[1] == Expr::Col(2));
    lemma_expr_col(db, env, 0);
    lemma_expr_col(db, env, 2);
    let rs = expr_results(db, env, exprs());
    assert(rs =~= seq![Ok::<Val, SqlError>(env[0]), Ok::<Val, SqlError>(env[2])]);
    lemma_collect_all(rs, seq![env[0], env[2]]);
}

/// Condition and projection of sensor's row `i` at `$1 = bound`.
proof fn lemma_row_meaning(db: Database, ps: Seq<Literal>, bound: int, i: int)
    requires
        db.schema == schema_spec(), db_wf(db), 0 <= i < db.tables[1].len(),
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(bound)),
    ensures
        eval_pred(db, Seq::<Val>::empty() + db.tables[1][i], pred_at(ps))
            == Ok::<Truth, SqlError>(truth_of(qual_row(stored_relations(db)[0][i], bound))),
        eval_exprs(db, Seq::<Val>::empty() + db.tables[1][i], exprs())
            == Ok::<Row, SqlError>(proj(stored_relations(db)[0][i], out_cols())),
{
    lemma_row(db, i);
    let r = db.tables[1][i];
    let env = Seq::<Val>::empty() + r;
    assert(env =~= r);
    lemma_pred_row(db, env, ps, bound, date_day(r[3]));
    lemma_exprs_row(db, env);
}

/// The projection of the kept rows among the first `k` rows of sensor is `outs` of the first `k` stored rows.
proof fn lemma_prefix(db: Database, ps: Seq<Literal>, bound: int, truths: Seq<Truth>, k: int)
    requires
        db.schema == schema_spec(), db_wf(db),
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(bound)),
        0 <= k <= db.tables[1].len(),
        truths.len() == db.tables[1].len(),
        forall|i: int| 0 <= i < truths.len() ==> #[trigger] truths[i] == truth_of(qual_row(stored_relations(db)[0][i], bound)),
    ensures
        collect(project_results(db, Seq::empty(), keep_true(db.tables[1].subrange(0, k), truths.subrange(0, k)), exprs()))
            == Ok::<Seq<Row>, SqlError>(outs(stored_relations(db)[0], bound, k)),
    decreases k,
{
    let rows = db.tables[1];
    let t = stored_relations(db)[0];
    let es = exprs();
    if k == 0 {
        assert(rows.subrange(0, 0) =~= Seq::<Row>::empty() && truths.subrange(0, 0) =~= Seq::<Truth>::empty());
        assert(project_results(db, Seq::empty(), keep_true(rows.subrange(0, 0), truths.subrange(0, 0)), es) =~= Seq::<Result<Row, SqlError>>::empty());
    } else {
        let j = k - 1;
        lemma_prefix(db, ps, bound, truths, j);
        let kept = keep_true(rows.subrange(0, j), truths.subrange(0, j));
        let (r1, t1) = (rows.subrange(0, k), truths.subrange(0, k));
        assert(r1.drop_last() =~= rows.subrange(0, j) && t1.drop_last() =~= truths.subrange(0, j));
        assert(r1.last() == rows[j] && t1.last() == truths[j]);
        let prev = project_results(db, Seq::empty(), kept, es);
        lemma_row_meaning(db, ps, bound, j);
        if qual_row(t[j], bound) {
            assert(keep_true(r1, t1) == kept.push(rows[j]));
            let next = project_results(db, Seq::empty(), kept.push(rows[j]), es);
            assert(next.drop_last() =~= prev);
            assert(next.last() == eval_exprs(db, Seq::<Val>::empty() + rows[j], es));
        } else {
            assert(keep_true(r1, t1) == kept);
        }
    }
}

/// The meaning of the statement at binding `ps` on a well-formed database of the schema.
proof fn lemma_meaning(db: Database, ps: Seq<Literal>, bound: int)
    requires db.schema == schema_spec(), db_wf(db), lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(bound)),
    ensures denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(outs(stored_relations(db)[0], bound, db.tables[1].len() as int)),
{
    lemma_statement(ps);
    let rows = db.tables[1];
    let n = rows.len() as int;
    let t = stored_relations(db)[0];
    let pred = pred_at(ps);
    let truths = Seq::new(n as nat, |i: int| truth_of(qual_row(t[i], bound)));
    let fr = filter_results(db, Seq::empty(), rows, pred);
    assert forall|i: int| 0 <= i < fr.len() implies #[trigger] fr[i] == Ok::<Truth, SqlError>(truths[i]) by {
        lemma_row_meaning(db, ps, bound, i);
    }
    lemma_collect_all(fr, truths);
    lemma_eval_filter(db, Seq::empty(), pred, Box::new(Query::Table(1)));
    lemma_eval_project(db, Seq::empty(), exprs(), Box::new(Query::Filter { pred, input: Box::new(Query::Table(1)) }));
    assert(eval_query(db, Seq::empty(), Query::Table(1)) == Ok::<Relation, SqlError>(rows));
    lemma_prefix(db, ps, bound, truths, n);
    assert(rows.subrange(0, n) =~= rows && truths.subrange(0, n) =~= truths);
}

/// Every database bound to the parts has the stored relation the parts spell.
proof fn lemma_bound_relation(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        stored_relations(db)[0] == spelled(sv.sensor_days),
        db.tables[1].len() == days(sv.sensor_days).len(),
{
    let parts = sv.sensor_days;
    let t = stored_relations(db)[0];
    assert(represents(parts, stored_relations(db)));
    lemma_stored_relations(db);
    assert(t =~= spelled(parts));
}

/// The date parameter is a date value of the declared domain.
proof fn lemma_date_parameter(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures lit_val(ps[0]) is Ok,
{
    assert(type_lit(ps[0]) is Some);
}

// ------------------------------------------------------------------------------------------ query

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost parts = sv.sensor_days;
    let ghost db0 = choose|db: Database| bound_db(sv, db);
    let ghost rels0 = stored_relations(db0);
    let ghost t = spelled(parts);
    proof {
        assert(bound_db(sv, db0));
        lemma_bound_relation(sv, db0);
        lemma_date_parameter(ps);
    }
    // $1 as a PostgreSQL day number, then as Date32 (days since 1970-01-01).
    let date = params.p0;
    let bound: i64 = match lit_exec(&ELiteral::Date { y: date.y, m: date.m, d: date.d }) {
        Ok(EVal::Date(x)) => x as i64,
        _ => {
            proof {
                assert(view_lit(ELiteral::Date { y: date.y, m: date.m, d: date.d }) == ps[0]);
            }
            return Err(QueryError::Malformed);
        },
    };
    proof {
        assert(view_lit(ELiteral::Date { y: date.y, m: date.m, d: date.d }) == ps[0]);
        assert(lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(bound as int)));
    }
    let bound32 = bound + 10957;
    let marked = blocks_before(&mut stores.sensor_days, bound32, Ghost(rels0));
    let n = stores.sensor_days.part_len(4);
    let blocks = marked.len();
    let mut out: Vec<Vec<EVal>> = Vec::new();
    let mut b: usize = 0;
    let mut lo: usize = 0;
    assert(view_rows(out@) =~= Seq::<Row>::empty());
    while b < blocks
        invariant
            stores@ == sv,
            parts == sv.sensor_days,
            represents(parts, rels0),
            t == spelled(parts),
            n == days(parts).len(),
            n == rels0[0].len(),
            blocks == block_count(n as int),
            marked@.len() == blocks,
            forall|i: int| 0 <= i < n && (days(parts)[i] as int) < bound32 ==> #[trigger] marked@[i / (BLOCK as int)],
            bound32 == bound + 10957,
            b <= blocks,
            lo as int == if b < blocks { b as int * (BLOCK as int) } else { n as int },
            lo <= n,
            view_rows(out@) == outs(t, bound as int, lo as int),
        decreases blocks - b,
    {
        let hi = if n - lo > BLOCK { lo + BLOCK } else { n };
        proof {
            assert forall|i: int| lo <= i < hi implies #[trigger] (i / (BLOCK as int)) == b as int by {}
        }
        if marked[b] {
            let id_values = stores.sensor_days.extent_i32(2, lo, hi);
            let reading_values = stores.sensor_days.extent_i128(3, lo, hi);
            let day_values = stores.sensor_days.extent_i32(4, lo, hi);
            let mut i: usize = 0;
            while i < hi - lo
                invariant
                    lo + i <= hi, hi <= n,
                    id_values@ == ids(parts).subrange(lo as int, hi as int),
                    reading_values@ == readings(parts).subrange(lo as int, hi as int),
                    day_values@ == days(parts).subrange(lo as int, hi as int),
                    t == spelled(parts),
                    n == days(parts).len(),
                    represents(parts, rels0),
                    n == rels0[0].len(),
                    view_rows(out@) == outs(t, bound as int, lo + i),
                    bound32 == bound + 10957,
                decreases hi - lo - i,
            {
                let row = lo + i;
                proof {
                    assert(t[row as int] == stored_row(parts, row as int));
                    assert(id_values@[i as int] == ids(parts)[row as int]);
                    assert(reading_values@[i as int] == readings(parts)[row as int]);
                    assert(day_values@[i as int] == days(parts)[row as int]);
                }
                if (day_values[i] as i64) < bound32 {
                    let values: Vec<EVal> = vec![EVal::Int(id_values[i] as i64), EVal::Num { coeff: reading_values[i], scale: 2 }];
                    proof {
                        assert(qual_row(t[row as int], bound as int));
                        assert(view_row(values@) =~= proj(t[row as int], out_cols()));
                        lemma_view_rows_push(out@, values);
                    }
                    out.push(values);
                } else {
                    proof {
                        assert(!qual_row(t[row as int], bound as int));
                    }
                }
                i = i + 1;
            }
        } else {
            proof {
                assert forall|i: int| lo <= i < hi implies !qual_row(#[trigger] t[i], bound as int) by {
                    assert(t[i] == stored_row(parts, i));
                    if (days(parts)[i] as int) < bound32 {
                        assert(marked@[i / (BLOCK as int)]);
                    }
                }
                lemma_outs_skip(t, bound as int, lo as int, hi as int);
            }
        }
        b = b + 1;
        lo = hi;
    }
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db)
            implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(out))) by {
            lemma_bound_relation(sv, db);
            lemma_meaning(db, ps, bound as int);
            lemma_statement(ps);
            lemma_outcome_rows(db, query_spec_at(ps), view_rows(out@));
        }
    }
    Ok(Answer::Rows(out))
}

} // verus!
