//! TPC-H Q4 in the accumulator normal form of `link::query` (`QuerySpec`), and the per-row agreement of the
//! statement's AST with it.
//!
//! The FROM relation is `orders`; the normal form reads its projection onto `src_cols()` = (o_orderkey, o_orderdate,
//! o_orderpriority). A projected row qualifies (`q4_qual`) when its date `d` (days since 2000-01-01) satisfies
//! `d >= pd` and `d * usecs < t1` (`pd` the parameter, `t1` the timestamp `$1 + 3 months`) and its key has a late
//! `lineitem` row (`cols::has`, the EXISTS subquery). The group key is the priority; the one aggregate is COUNT(*).
//!
//! The executable window (`lists::Win`, stored days) is the same condition (`win_of`, `lemma_win_qual`), and the group
//! counts are the counts of the qualifying row lists (`lemma_gcount_list`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::scalar::*;
use crate::spec::datetime::*;
use crate::spec::equality::row_not_distinct;
use crate::spec::numeric::sign;
use crate::link::query::*;
use crate::link::expr::*;
use crate::link::exists::lemma_exists_filter_table;
use crate::bridge::equality::same_exact_type;
use crate::agent::cols::*;
use crate::agent::lists::*;

verus! {

/// Microseconds per day.
pub open spec fn usecs() -> int {
    86_400_000_000
}

/// `$1::timestamp + interval '3 month'` for the parameter day `pd` (days since 2000-01-01).
pub open spec fn hi_res(pd: int) -> Result<int, SqlError> {
    match date_to_ts(pd) {
        Ok(t) => ts_add_interval(t, 3, 0, 0),
        Err(e) => Err(e),
    }
}

/// Table columns of `orders` the normal form reads, in projected order.
pub open spec fn src_cols() -> Seq<nat> {
    seq![0nat, 4nat, 5nat]
}

/// WHERE of Q4 on a projected row: in the window and with a late `lineitem` row of its key.
pub open spec fn q4_qual(l: LCols, pd: int, t1: int, x: Row) -> bool {
    match (x[0], x[1]) {
        (Val::Int(k), Val::Date(d)) => d >= pd && d * usecs() < t1 && has(l, k),
        _ => false,
    }
}

/// GROUP BY key: the priority.
pub open spec fn q4_key(x: Row) -> Row {
    seq![x[2]]
}

pub open spec fn q4_spec(l: LCols, pd: int, t1: int) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q4_qual(l, pd, t1, x),
        key: |x: Row| q4_key(x),
        arg: |j: int, x: Row| 0,
        aggs: seq![AggKind::Count],
        outs: seq![0nat, 1nat],
        grouped: true,
    }
}

/// Projected row `i` of the `orders` columns.
pub open spec fn crow(o: OCols, i: int) -> Row {
    seq![Val::Int(o.okey@[i] as int), Val::Date(o.odate@[i] - 10957), Val::Text(prio(o, i))]
}

/// All projected rows.
pub open spec fn crows(o: OCols) -> Seq<Row> {
    Seq::new(o.no as nat, |i: int| crow(o, i))
}

/// The executable window is the statement's: `dlo` is the parameter (stored days) and `dhi` the first stored day
/// whose midnight is not below `t1`.
pub open spec fn win_of(w: Win, pd: int, t1: int) -> bool {
    &&& w.dlo == pd + 10957
    &&& (w.dhi - 10957) * usecs() >= t1
    &&& (w.dhi - 10957 - 1) * usecs() < t1
}

/// `d * usecs < t1` exactly when `d < dhi - 10957`.
pub proof fn lemma_win_hi(w: Win, pd: int, t1: int, d: int)
    requires win_of(w, pd, t1),
    ensures (d * usecs() < t1) == (d < w.dhi - 10957),
{
    let h = w.dhi - 10957;
    let u = usecs();
    if d < h {
        assert(d * u <= (h - 1) * u) by (nonlinear_arith) requires d <= h - 1, u > 0;
    } else {
        assert(d * u >= h * u) by (nonlinear_arith) requires d >= h, u > 0;
    }
}

/// The normal form's condition on row `i` is the executable qualifying condition.
pub proof fn lemma_win_qual(l: LCols, o: OCols, w: Win, pd: int, t1: int, i: int)
    requires win_of(w, pd, t1),
    ensures q4_qual(l, pd, t1, crow(o, i)) == qual_row(l, o, w, i),
{
    lemma_win_hi(w, pd, t1, o.odate@[i] - 10957);
}

/// The counts of the normal form over rows `[a, b)` are the counts of the qualifying list, for a priority key.
pub proof fn lemma_gcount_list(l: LCols, o: OCols, w: Win, pd: int, t1: int, a: int, b: int, kb: Seq<u8>)
    requires win_of(w, pd, t1), 0 <= a <= b <= o.no,
    ensures gcount(q4_spec(l, pd, t1), crows(o).subrange(a, b), seq![Val::Text(kb)]) == cnt_list(o, q_list(l, o, w, a, b), kb),
    decreases b - a,
{
    let g = q4_spec(l, pd, t1);
    let k = seq![Val::Text(kb)];
    if a < b {
        lemma_gcount_list(l, o, w, pd, t1, a, b - 1, kb);
        lemma_range_step(g, crows(o), a, b - 1, k, 0);
        lemma_win_qual(l, o, w, pd, t1, b - 1);
        let d = q_list(l, o, w, a, b - 1);
        assert(crows(o)[b - 1] == crow(o, b - 1));
        assert(q4_key(crow(o, b - 1)) == seq![Val::Text(prio(o, b - 1))]);
        if qual_row(l, o, w, b - 1) {
            lemma_cnt_push(o, d, (b - 1) as usize, kb);
            if prio(o, b - 1) != kb {
                assert(q4_key(crow(o, b - 1))[0] != k[0]);
            }
        }
    } else {
        lemma_empty(g, crows(o), a, k, 0);
    }
}

/// Keys of qualifying rows are one-text rows; any other key has no rows.
pub proof fn lemma_gcount_other(l: LCols, o: OCols, pd: int, t1: int, a: int, b: int, k: Row)
    requires
        0 <= a <= b <= o.no,
        !(k.len() == 1 && k[0] is Text),
    ensures gcount(q4_spec(l, pd, t1), crows(o).subrange(a, b), k) == 0,
    decreases b - a,
{
    let g = q4_spec(l, pd, t1);
    if a < b {
        lemma_gcount_other(l, o, pd, t1, a, b - 1, k);
        lemma_range_step(g, crows(o), a, b - 1, k, 0);
        assert(crows(o)[b - 1] == crow(o, b - 1));
        assert(q4_key(crow(o, b - 1)) =~= seq![Val::Text(prio(o, b - 1))]);
    } else {
        lemma_empty(g, crows(o), a, k, 0);
    }
}

// ------------------------------------------------------------------------------------------------ the statement's AST

/// `$1::timestamp + interval '3 month'`.
pub open spec fn hi_expr(p: Literal) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p)) }),
        months: 3i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `o_orderdate >= $1 AND o_orderdate < $1 + interval '3 month'`.
pub open spec fn ast_window(p: Literal) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(4), b: Expr::Lit(p) }),
        Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(4), b: hi_expr(p) }),
    )
}

/// `l_orderkey = o_orderkey AND l_commitdate < l_receiptdate` (orders row first, then the lineitem row).
pub open spec fn ast_inner() -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(9), b: Expr::Col(0) }),
        Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(20), b: Expr::Col(21) }),
    )
}

/// `EXISTS (SELECT * FROM lineitem WHERE ..)`.
pub open spec fn ast_exists() -> Pred {
    Pred::Exists(Box::new(Query::Filter { pred: ast_inner(), input: Box::new(Query::Table(0)) }))
}

/// The WHERE of Q4.
pub open spec fn ast_pred(p: Literal) -> Pred {
    Pred::And(Box::new(ast_window(p)), Box::new(ast_exists()))
}

pub open spec fn ast_input(p: Literal) -> Query {
    Query::Filter { pred: ast_pred(p), input: Box::new(Query::Table(1)) }
}

pub open spec fn ast_keys() -> Seq<Expr> {
    seq![Expr::Col(5)]
}

pub open spec fn ast_aggs() -> Seq<Agg> {
    seq![Agg::CountStar]
}

pub open spec fn ast_body(p: Literal) -> Query {
    Query::GroupBy { keys: ast_keys(), aggs: ast_aggs(), input: Box::new(ast_input(p)) }
}

pub open spec fn ast_order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The emitted statement is this AST.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        crate::query::query_spec_at(ps).body == ast_body(ps[0]),
        crate::query::query_spec_at(ps).keys == ast_order_keys(),
        crate::query::query_spec_at(ps).limit is None,
        crate::query::query_spec_at(ps).offset == 0,
{
}

// ------------------------------------------------------------------------------------------------ per-row agreement

/// The `lineitem` table of a bound database: its rows carry the column values of `l`.
pub open spec fn li_rows_ok(rows: Seq<Row>, l: LCols) -> bool {
    &&& rows.len() == l.nl
    &&& forall|j: int| 0 <= j < rows.len() ==> {
        &&& (#[trigger] rows[j]).len() == 16
        &&& rows[j][0] == Val::Int(l.lk@[j] as int)
        &&& rows[j][11] == Val::Date(l.cm@[j] - 10957)
        &&& rows[j][12] == Val::Date(l.rc@[j] - 10957)
    }
}

/// An `orders` row as the statement reads it: 9 columns, key, date and priority values.
pub open spec fn o_row_ok(r: Row) -> bool {
    &&& r.len() == 9
    &&& r[0] is Int
    &&& r[4] is Date
    &&& r[5] is Text
}

/// The upper bound expression evaluates to `hi_res` (independent of the row).
pub proof fn lemma_hi_expr(db: Database, env: Row, p: Literal, pd: int)
    requires lit_val(p) == Ok::<Val, SqlError>(Val::Date(pd)),
    ensures
        eval_expr(db, env, hi_expr(p)) == match hi_res(pd) {
            Ok(t1) => Ok::<Val, SqlError>(Val::Ts(t1)),
            Err(e) => Err::<Val, SqlError>(e),
        },
{
    let c = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p)) };
    assert(eval_expr(db, env, Expr::Lit(p)) == Ok::<Val, SqlError>(Val::Date(pd)));
    match date_to_ts(pd) {
        Ok(t) => {
            assert(eval_expr(db, env, c) == Ok::<Val, SqlError>(Val::Ts(t)));
        },
        Err(e) => {
            assert(eval_expr(db, env, c) == Err::<Val, SqlError>(e));
        },
    }
}

/// The inner condition on an orders row `r` (key `k`) and lineitem row `j`: whether row `j` has key `k` and is late.
pub proof fn lemma_inner_row(db: Database, r: Row, lrow: Row, l: LCols, k: int, j: int)
    requires
        r.len() == 9,
        r[0] == Val::Int(k),
        lrow.len() == 16,
        lrow[0] == Val::Int(l.lk@[j] as int),
        lrow[11] == Val::Date(l.cm@[j] - 10957),
        lrow[12] == Val::Date(l.rc@[j] - 10957),
    ensures eval_pred(db, r + lrow, ast_inner()) == Ok::<Truth, SqlError>(truth_of(hit_at(l, k, j))),
{
    let env = r + lrow;
    lemma_expr_col(db, env, 9);
    lemma_expr_col(db, env, 0);
    lemma_expr_col(db, env, 20);
    lemma_expr_col(db, env, 21);
    assert(env[9] == lrow[0]);
    assert(env[0] == r[0]);
    assert(env[20] == lrow[11]);
    assert(env[21] == lrow[12]);
    lemma_compare_int(l.lk@[j] as int, k);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(9), Expr::Col(0), env[9], env[0], l.lk@[j] as int, k);
    let (x, y) = (l.cm@[j] - 10957, l.rc@[j] - 10957);
    lemma_compare_date(x, y);
    lemma_pred_cmp(db, env, CmpOp::Lt, Expr::Col(20), Expr::Col(21), env[20], env[21], x, y);
    lemma_pred_and(db, env,
        Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(9), b: Expr::Col(0) },
        Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(20), b: Expr::Col(21) },
        l.lk@[j] as int == k, x < y);
}

/// EXISTS on an orders row with key `k`: whether `k` has a late lineitem row.
pub proof fn lemma_exists_row(db: Database, r: Row, l: LCols, k: int)
    requires
        db.tables.len() > 0,
        li_rows_ok(db.tables[0], l),
        r.len() == 9,
        r[0] == Val::Int(k),
    ensures eval_pred(db, r, ast_exists()) == Ok::<Truth, SqlError>(truth_of(has(l, k))),
{
    hide(eval_pred);
    let rows = db.tables[0];
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] eval_pred(db, r + rows[i], ast_inner()) is Ok by {
        lemma_inner_row(db, r, rows[i], l, k, i);
    }
    lemma_exists_filter_table(db, r, ast_inner(), 0);
    let w = exists|i: int| 0 <= i < rows.len() && #[trigger] eval_pred(db, r + rows[i], ast_inner()) == Ok::<Truth, SqlError>(Truth::True);
    if w {
        let i = choose|i: int| 0 <= i < rows.len() && #[trigger] eval_pred(db, r + rows[i], ast_inner()) == Ok::<Truth, SqlError>(Truth::True);
        lemma_inner_row(db, r, rows[i], l, k, i);
        assert(hit_at(l, k, i));
        assert(has_in(l, k, 0, l.nl as int));
    }
    if has(l, k) {
        let j = choose|j: int| 0 <= j < l.nl && #[trigger] hit_at(l, k, j);
        lemma_inner_row(db, r, rows[j], l, k, j);
        assert(eval_pred(db, r + rows[j], ast_inner()) == Ok::<Truth, SqlError>(Truth::True));
    }
}

/// The WHERE on one orders row, when the upper bound is the timestamp `t1`: the normal form's condition.
pub proof fn lemma_pred_row(db: Database, r: Row, p: Literal, pd: int, t1: int, l: LCols)
    requires
        db.tables.len() > 0,
        li_rows_ok(db.tables[0], l),
        o_row_ok(r),
        lit_val(p) == Ok::<Val, SqlError>(Val::Date(pd)),
        hi_res(pd) == Ok::<int, SqlError>(t1),
    ensures eval_pred(db, r, ast_pred(p)) == Ok::<Truth, SqlError>(truth_of(q4_qual(l, pd, t1, proj(r, src_cols())))),
{
    let k = r[0]->Int_0;
    let d = r[4]->Date_0;
    let x = proj(r, src_cols());
    assert(x =~= seq![r[0], r[4], r[5]]);
    lemma_expr_col(db, r, 4);
    lemma_compare_date(d, pd);
    lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(4), Expr::Lit(p), r[4], Val::Date(pd), d, pd);
    lemma_hi_expr(db, r, p, pd);
    assert(compare(Val::Date(d), Val::Ts(t1)) == Some(sign(d * usecs() - t1)));
    lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(4), hi_expr(p), r[4], Val::Ts(t1), d * usecs(), t1);
    lemma_pred_and(db, r,
        Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(4), b: Expr::Lit(p) },
        Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(4), b: hi_expr(p) },
        d >= pd, d * usecs() < t1);
    lemma_exists_row(db, r, l, k);
    lemma_pred_and(db, r, ast_window(p), ast_exists(), d >= pd && d * usecs() < t1, has(l, k));
}

/// AND whose first operand fails: that error.
pub proof fn lemma_and_err_left(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Err::<Truth, SqlError>(e),
{
}

/// AND whose first operand succeeds and second fails: that error.
pub proof fn lemma_and_err_right(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) is Ok, eval_pred(db, env, b) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Err::<Truth, SqlError>(e),
{
}

/// A comparison whose second operand fails: that error.
pub proof fn lemma_cmp_err_right(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, e: SqlError)
    requires eval_expr(db, env, a) is Ok, eval_expr(db, env, b) == Err::<Val, SqlError>(e),
    ensures eval_pred(db, env, Pred::Cmp { op, a, b }) == Err::<Truth, SqlError>(e),
{
}

/// The WHERE on one orders row, when the upper bound is the error `e`: the error.
pub proof fn lemma_pred_row_err(db: Database, r: Row, p: Literal, pd: int, e: SqlError)
    requires
        o_row_ok(r),
        lit_val(p) == Ok::<Val, SqlError>(Val::Date(pd)),
        hi_res(pd) == Err::<int, SqlError>(e),
    ensures eval_pred(db, r, ast_pred(p)) == Err::<Truth, SqlError>(e),
{
    let ge = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(4), b: Expr::Lit(p) };
    let lt = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(4), b: hi_expr(p) };
    lemma_expr_col(db, r, 4);
    lemma_hi_expr(db, r, p, pd);
    let d = r[4]->Date_0;
    lemma_compare_date(d, pd);
    lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(4), Expr::Lit(p), r[4], Val::Date(pd), d, pd);
    lemma_cmp_err_right(db, r, CmpOp::Lt, Expr::Col(4), hi_expr(p), e);
    lemma_and_err_right(db, r, ge, lt, e);
    lemma_and_err_left(db, r, ast_window(p), ast_exists(), e);
}

/// The GROUP BY key on one orders row is the normal form's key.
pub proof fn lemma_keys_row(db: Database, r: Row)
    requires o_row_ok(r),
    ensures eval_exprs(db, r, ast_keys()) == Ok::<Row, SqlError>(q4_key(proj(r, src_cols()))),
{
    let ks = ast_keys();
    assert(ks =~= col_exprs(seq![5nat]));
    lemma_eval_cols(db, r, seq![5nat]);
    assert(select(r, seq![5nat]) =~= q4_key(proj(r, src_cols())));
}

/// The COUNT(*) argument on one row (none: NULL stands in).
pub proof fn lemma_args_row(db: Database, r: Row, l: LCols, pd: int, t1: int)
    ensures agg_args(db, r, ast_aggs()) == Ok::<Row, SqlError>(arg_vals(q4_spec(l, pd, t1), proj(r, src_cols()))),
{
    let g = q4_spec(l, pd, t1);
    let rs = agg_arg_results(db, r, ast_aggs());
    let vs = arg_vals(g, proj(r, src_cols()));
    lemma_agg_arg_results_index(db, r, ast_aggs());
    assert(vs =~= seq![Val::Null]);
    assert(rs[0] == agg_arg(db, r, Agg::CountStar));
    crate::bridge::collect::lemma_collect_all(rs, vs);
}

/// The aggregate list matches the normal form.
pub proof fn lemma_aggs_match(l: LCols, pd: int, t1: int)
    ensures aggs_match(ast_aggs(), q4_spec(l, pd, t1)),
{
    let g = q4_spec(l, pd, t1);
    assert forall|j: int| 0 <= j < ast_aggs().len() implies agg_matches(#[trigger] ast_aggs()[j], g.aggs[j]) by {}
}

/// Keys of projected rows are single texts: SQL "not distinct" is equality.
pub proof fn lemma_keys_exact(l: LCols, pd: int, t1: int, xs: Seq<Row>)
    requires forall|i: int| 0 <= i < xs.len() ==> (#[trigger] xs[i]).len() == 3 && xs[i][2] is Text,
    ensures keys_exact(q4_spec(l, pd, t1), xs),
{
    let g = q4_spec(l, pd, t1);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let ka = (g.key)(xs[a]);
        let kb = (g.key)(xs[b]);
        assert(xs[a][2] is Text && xs[b][2] is Text);
        assert forall|i: int| 0 <= i < ka.len() implies same_exact_type(#[trigger] ka[i], kb[i]) by {}
        lemma_row_exact(ka, kb);
    }
}

} // verus!
