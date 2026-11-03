//! The statement's body in normal form: the outer GROUP BY is `gkeys(g_out)` mapped to its rows; the HAVING
//! subquery's value is AVG over the inner groups' SUMs (`avg_in`), the same under every group row; the body keeps
//! the group rows whose SUM compares above it (or is that AVG's error when there are group rows).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::aggs::avg::*;
use crate::spec::limits::*;
use crate::bridge::collect::*;
use crate::bridge::equality::same_exact_type;
use crate::exec::relational::domain::*;
use crate::link::query::{QuerySpec, AggKind, gsum, gcount, gkeys, hit, full_row, agg_outs, agg_out, arg_vals, keys_exact,
    lemma_gkeys, lemma_digits_in_range};
use crate::link::join::keep;
use crate::agent::nf::ast::*;
use crate::agent::nf::fromwhere::*;
use crate::agent::nf::group::*;
use crate::agent::nf::sums::*;

verus! {

/// Every value of `num` is numeric at scale 4 with a coefficient below `10^28`.
pub open spec fn vals_ok(db: Database) -> bool {
    &&& db.tables.len() >= 2
    &&& db.tables[1].len() < 0x1_0000_0000_0000_0000int
    &&& db.tables[0].len() < 0x1_0000_0000_0000_0000int
    &&& forall|i: int| 0 <= i < db.tables[1].len() ==> {
        &&& (#[trigger] db.tables[1][i])[7] is Num
        &&& db.tables[1][i][7]->Num_scale == 4
        &&& abs(db.tables[1][i][7]->Num_coeff) < pow10(28)
    }
}

/// Every joined row's value is a value of `num`.
pub proof fn lemma_joined_vals(db: Database)
    requires tables_shaped(db), vals_ok(db),
    ensures
        forall|p: int| 0 <= p < joined(db).len() ==> {
            &&& (#[trigger] joined(db)[p])[7] is Num
            &&& joined(db)[p][7]->Num_scale == 4
            &&& abs(joined(db)[p][7]->Num_coeff) < pow10(28)
        },
        joined(db).len() == db.tables[1].len() * db.tables[0].len(),
{
    let (a, b) = (db.tables[1], db.tables[0]);
    crate::link::join::lemma_product_index(a, b);
    lemma_joined_rows(db);
    assert forall|p: int| 0 <= p < joined(db).len() implies {
        &&& (#[trigger] joined(db)[p])[7] is Num
        &&& joined(db)[p][7]->Num_scale == 4
        &&& abs(joined(db)[p][7]->Num_coeff) < pow10(28)
    } by {
        let n = b.len() as int;
        assert(n > 0) by (nonlinear_arith) requires 0 <= p < a.len() * n, a.len() >= 0, n >= 0;
        let i = p / n;
        let j = p % n;
        assert(p == i * n + j && 0 <= j < n) by (nonlinear_arith) requires n > 0, i == p / n, j == p % n;
        assert(0 <= i < a.len()) by (nonlinear_arith) requires 0 <= p < a.len() * n, n > 0, i == p / n;
        assert(joined(db)[i * n + j] == a[i] + b[j]);
        assert(shape_num(a[i]));
        assert((a[i] + b[j])[7] == a[i][7]);
    }
}

/// `|gsum| <= |rows| * 10^28` when every row's argument is below `10^28`.
proof fn lemma_gsum_rows_bound(g: QuerySpec, xs: Seq<Row>, k: Row)
    requires forall|p: int| 0 <= p < xs.len() ==> abs(#[trigger] (g.arg)(0, xs[p])) < pow10(28),
    ensures abs(gsum(g, xs, k, 0)) <= xs.len() * pow10(28),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        assert forall|p: int| 0 <= p < xi.len() implies abs(#[trigger] (g.arg)(0, xi[p])) < pow10(28) by {
            assert(xi[p] == xs[p]);
        }
        lemma_gsum_rows_bound(g, xi, k);
        assert(abs((g.arg)(0, xs[xs.len() - 1])) < pow10(28));
        assert(xs.len() * pow10(28) == xi.len() * pow10(28) + pow10(28)) by (nonlinear_arith)
            requires xs.len() == xi.len() + 1;
    }
}

/// Every group SUM of a `sum_spec` over the joined rows is inside the numeric format.
pub proof fn lemma_sums_in_range_joined(db: Database, qual: spec_fn(Row) -> bool, key: spec_fn(Row) -> Row)
    requires tables_shaped(db), vals_ok(db),
    ensures sums_in_range(sum_spec(qual, key), joined(db)),
{
    let g = sum_spec(qual, key);
    let xs = joined(db);
    lemma_joined_vals(db);
    assert forall|p: int| 0 <= p < xs.len() implies abs(#[trigger] (g.arg)(0, xs[p])) < pow10(28) by {
        assert((g.arg)(0, xs[p]) == coeff(xs[p][7]));
    }
    let (na, nb) = (db.tables[1].len() as int, db.tables[0].len() as int);
    assert(xs.len() <= 0x1_0000_0000_0000_0000_0000_0000_0000_0000int) by (nonlinear_arith)
        requires xs.len() == na * nb, 0 <= na < 0x1_0000_0000_0000_0000int, 0 <= nb < 0x1_0000_0000_0000_0000int;
    assert(pow10(39) == 1000000000000000000000000000000000000000) by (compute);
    crate::bridge::order::lemma_pow10_add(39, 28);
    crate::spec::numeric::lemma_pow10_positive(28);
    assert forall|k: Row| #[trigger] num_in_range(gsum(g, xs, k, 0), 4) by {
        lemma_gsum_rows_bound(g, xs, k);
        assert(xs.len() * pow10(28) < pow10(39) * pow10(28)) by (nonlinear_arith)
            requires xs.len() <= 0x1_0000_0000_0000_0000_0000_0000_0000_0000int,
                pow10(39) == 1000000000000000000000000000000000000000int, pow10(28) >= 1;
        lemma_digits_in_range(gsum(g, xs, k, 0), 4, 67);
    }
}

/// Two-column (one-column) key lists of the joined rows have exact types.
pub proof fn lemma_keys_exact_joined(db: Database, qual: spec_fn(Row) -> bool, key: spec_fn(Row) -> Row)
    requires
        tables_shaped(db),
        forall|x: Row| shape_joined(x) ==> (#[trigger] key(x) == seq![x[11], x[10]] || key(x) == seq![x[10]]),
        forall|x: Row, y: Row| shape_joined(x) && shape_joined(y) ==> (#[trigger] key(x)).len() == (#[trigger] key(y)).len(),
    ensures keys_exact(sum_spec(qual, key), joined(db)),
{
    let g = sum_spec(qual, key);
    let xs = joined(db);
    lemma_joined_rows(db);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies ({
        let (ka, kb) = ((g.key)(#[trigger] xs[a]), (g.key)(#[trigger] xs[b]));
        &&& ka.len() == kb.len()
        &&& forall|i: int| 0 <= i < ka.len() ==> same_exact_type(#[trigger] ka[i], kb[i])
    }) by {
        let (x, y) = (xs[a], xs[b]);
        assert(shape_joined(x) && shape_joined(y));
    }
    lemma_keys_exact_from(g, xs);
}

/// One column of an environment.
proof fn lemma_col_val(db: Database, env: Row, c: nat)
    requires c < env.len(),
    ensures eval_expr(db, env, Expr::Col(c)) == Ok::<Val, SqlError>(env[c as int]),
{
}

/// A list of column expressions.
proof fn lemma_cols2(db: Database, env: Row, a: nat, b: nat)
    requires a < env.len(), b < env.len(),
    ensures eval_exprs(db, env, seq![Expr::Col(a), Expr::Col(b)]) == Ok::<Row, SqlError>(seq![env[a as int], env[b as int]]),
{
    hide(eval_expr);
    let es = seq![Expr::Col(a), Expr::Col(b)];
    let rs = expr_results(db, env, es);
    lemma_col_val(db, env, a);
    lemma_col_val(db, env, b);
    assert(rs[0] == eval_expr(db, env, es[0]));
    assert(rs[1] == eval_expr(db, env, es[1]));
    lemma_collect_all(rs, seq![env[a as int], env[b as int]]);
}

proof fn lemma_cols1(db: Database, env: Row, a: nat)
    requires a < env.len(),
    ensures eval_exprs(db, env, seq![Expr::Col(a)]) == Ok::<Row, SqlError>(seq![env[a as int]]),
{
    hide(eval_expr);
    let es = seq![Expr::Col(a)];
    let rs = expr_results(db, env, es);
    lemma_col_val(db, env, a);
    assert(rs[0] == eval_expr(db, env, es[0]));
    lemma_collect_all(rs, seq![env[a as int]]);
}

/// The outer GROUP BY's per-row keys and arguments.
pub proof fn lemma_agree_outer(db: Database, p0: Seq<u8>, p1: int)
    requires tables_shaped(db), vals_ok(db),
    ensures rows_agree(db, Seq::empty(), outer_keys(), outer_aggs(), g_out(p0, p1), joined(db)),
{
    let g = g_out(p0, p1);
    let xs = joined(db);
    lemma_joined_rows(db);
    lemma_joined_vals(db);
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(#[trigger] xs[i]) implies {
        &&& eval_exprs(db, Seq::<Val>::empty() + xs[i], outer_keys()) == Ok::<Row, SqlError>((g.key)(xs[i]))
        &&& agg_args(db, Seq::<Val>::empty() + xs[i], outer_aggs()) == Ok::<Row, SqlError>(arg_vals(g, xs[i]))
    } by {
        let x = xs[i];
        assert(Seq::<Val>::empty() + x =~= x);
        lemma_cols2(db, x, 11, 10);
        assert(outer_keys() =~= seq![Expr::Col(11), Expr::Col(10)]);
        assert((g.key)(x) =~= seq![x[11], x[10]]);
        lemma_sum_arg(db, x, 7);
        assert(outer_aggs() =~= seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(7) }]);
        lemma_arg_vals(jq_fn(p0, p1), g.key, x);
    }
}

/// The inner GROUP BY's per-row keys and arguments under a 3-column context.
proof fn lemma_agree_inner(db: Database, r: Row, p0: Seq<u8>, p1: int)
    requires tables_shaped(db), vals_ok(db), r.len() == 3,
    ensures rows_agree(db, r, inner_keys(), inner_aggs(), g_in(p0, p1), joined(db)),
{
    let g = g_in(p0, p1);
    let xs = joined(db);
    lemma_joined_rows(db);
    lemma_joined_vals(db);
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(#[trigger] xs[i]) implies {
        &&& eval_exprs(db, r + xs[i], inner_keys()) == Ok::<Row, SqlError>((g.key)(xs[i]))
        &&& agg_args(db, r + xs[i], inner_aggs()) == Ok::<Row, SqlError>(arg_vals(g, xs[i]))
    } by {
        let x = xs[i];
        let env = r + x;
        assert(env[13] == x[10] && env[10] == x[7]);
        lemma_cols1(db, env, 13);
        assert(inner_keys() =~= seq![Expr::Col(13)]);
        assert((g.key)(x) =~= seq![x[10]]);
        lemma_sum_arg(db, env, 10);
        assert(inner_aggs() =~= seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(10) }]);
        lemma_arg_vals(jq_fn(p0, p1), g.key, x);
    }
}

/// The outer GROUP BY's rows.
pub proof fn lemma_outer_rows(db: Database, ps: Seq<Literal>, p0: Seq<u8>, p1: int)
    requires binding(ps, p0, p1), tables_shaped(db), vals_ok(db),
    ensures
        eval_query(db, Seq::empty(), outer_gb(ps))
            == Ok::<Relation, SqlError>(gkeys(g_out(p0, p1), joined(db)).map_values(|k: Row| full_row(g_out(p0, p1), joined(db), k))),
{
    let g = g_out(p0, p1);
    lemma_where_rows(db, Seq::empty(), ps, p0, p1);
    lemma_agree_outer(db, p0, p1);
    lemma_keys_exact_joined(db, jq_fn(p0, p1), g.key);
    lemma_sums_in_range_joined(db, jq_fn(p0, p1), g.key);
    assert(one_sum(outer_aggs()));
    lemma_group_ctx(db, Seq::empty(), where_q(0, ps), outer_keys(), outer_aggs(), joined(db), jq_fn(p0, p1), g.key);
}

/// The inner GROUP BY's rows (under any 3-column context).
pub proof fn lemma_inner_rows(db: Database, r: Row, ps: Seq<Literal>, p0: Seq<u8>, p1: int)
    requires binding(ps, p0, p1), tables_shaped(db), vals_ok(db), r.len() == 3,
    ensures
        eval_query(db, r, inner_gb(ps))
            == Ok::<Relation, SqlError>(gkeys(g_in(p0, p1), joined(db)).map_values(|k: Row| full_row(g_in(p0, p1), joined(db), k))),
{
    let g = g_in(p0, p1);
    lemma_where_rows(db, r, ps, p0, p1);
    lemma_agree_inner(db, r, p0, p1);
    lemma_keys_exact_joined(db, jq_fn(p0, p1), g.key);
    lemma_sums_in_range_joined(db, jq_fn(p0, p1), g.key);
    assert(one_sum(inner_aggs()));
    lemma_group_ctx(db, r, where_q(3, ps), inner_keys(), inner_aggs(), joined(db), jq_fn(p0, p1), g.key);
}

// ------------------------------------------------------------------------------------------ the HAVING subquery

/// The SUMs of the inner groups.
pub open spec fn in_sums(db: Database, p0: Seq<u8>, p1: int) -> Seq<Val> {
    gkeys(g_in(p0, p1), joined(db)).map_values(|k: Row| Val::Num { coeff: gsum(g_in(p0, p1), joined(db), k, 0), scale: 4 })
}

/// The projected inner rows.
pub open spec fn in_proj(db: Database, p0: Seq<u8>, p1: int) -> Seq<Row> {
    in_sums(db, p0, p1).map_values(|v: Val| seq![v])
}

/// The AVG of the subquery.
pub open spec fn avg_in(db: Database, p0: Seq<u8>, p1: int) -> Result<Val, SqlError> {
    avg_value(NumKind::Numeric, in_sums(db, p0, p1))
}

/// An inner group's row is `[cik, SUM]`.
proof fn lemma_inner_row(db: Database, p0: Seq<u8>, p1: int, t: int)
    requires tables_shaped(db), 0 <= t < gkeys(g_in(p0, p1), joined(db)).len(),
    ensures ({
        let g = g_in(p0, p1);
        let k = gkeys(g, joined(db))[t];
        &&& full_row(g, joined(db), k).len() == 2
        &&& full_row(g, joined(db), k)[1] == (Val::Num { coeff: gsum(g, joined(db), k, 0), scale: 4 })
    }),
{
    let g = g_in(p0, p1);
    let xs = joined(db);
    let k = gkeys(g, xs)[t];
    lemma_gkeys(g, xs);
    assert(gkeys(g, xs).contains(k));
    assert(gcount(g, xs, k) > 0);
    crate::link::query::lemma_count_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    assert(k == (g.key)(xs[m]));
    assert(k.len() == 1);
    assert(agg_outs(g, xs, k)[0] == agg_out(AggKind::Sum { scale: 4 }, gcount(g, xs, k), gsum(g, xs, k, 0)));
}

/// The projection of the inner groups.
pub proof fn lemma_inner_proj(db: Database, r: Row, ps: Seq<Literal>, p0: Seq<u8>, p1: int)
    requires binding(ps, p0, p1), tables_shaped(db), vals_ok(db), r.len() == 3,
    ensures eval_query(db, r, inner_proj(ps)) == Ok::<Relation, SqlError>(in_proj(db, p0, p1)),
{
    let g = g_in(p0, p1);
    let xs = joined(db);
    let ks = gkeys(g, xs);
    let rows = ks.map_values(|k: Row| full_row(g, xs, k));
    lemma_inner_rows(db, r, ps, p0, p1);
    lemma_eval_project(db, r, seq![Expr::Col(4)], Box::new(inner_gb(ps)));
    let rs = project_results(db, r, rows, seq![Expr::Col(4)]);
    let pr = in_proj(db, p0, p1);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(pr[i]) by {
        lemma_inner_row(db, p0, p1, i);
        let env = r + rows[i];
        assert(env[4] == rows[i][1]);
        lemma_cols1(db, env, 4);
        assert(rs[i] == eval_exprs(db, env, seq![Expr::Col(4)]));
    }
    lemma_collect_all(rs, pr);
}

/// The subquery's value is `avg_in` (under any 3-column context).
pub proof fn lemma_subquery(db: Database, r: Row, ps: Seq<Literal>, p0: Seq<u8>, p1: int)
    requires binding(ps, p0, p1), tables_shaped(db), vals_ok(db), r.len() == 3,
    ensures eval_expr(db, r, Expr::Subquery(Box::new(avg_q(ps)))) == avg_in(db, p0, p1),
{
    let pr = in_proj(db, p0, p1);
    let vs = in_sums(db, p0, p1);
    lemma_inner_proj(db, r, ps, p0, p1);
    lemma_eval_aggregate(db, r, avg_aggs(), Box::new(inner_proj(ps)));
    let rs = agg_args_results(db, r, pr, avg_aggs());
    let args = pr;
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(args[i]) by {
        let env = r + pr[i];
        assert(env[3] == pr[i][0]);
        let ars = agg_arg_results(db, env, avg_aggs());
        assert(ars[0] == agg_arg(db, env, avg_aggs()[0]));
        assert(ars[0] == Ok::<Val, SqlError>(env[3]));
        lemma_collect_all(ars, seq![env[3]]);
        assert(seq![env[3]] =~= pr[i]);
    }
    lemma_collect_all(rs, args);
    assert(column(args, 0) =~= vs);
    let avs = Seq::new(avg_aggs().len(), |j: int| agg_value(avg_aggs()[j], column(args, j)));
    assert(avs[0] == avg_in(db, p0, p1));
    match avg_in(db, p0, p1) {
        Ok(v) => {
            lemma_collect_all(avs, seq![v]);
        },
        Err(e) => {
            lemma_collect_first_err(avs, 0);
        },
    }
}

/// The HAVING condition of a group row `[name, cik, Num(s, 4)]` against the AVG `Num(ac, asc)`.
pub proof fn lemma_having(db: Database, r: Row, ps: Seq<Literal>, p0: Seq<u8>, p1: int, s: int, ac: int, asc: nat)
    requires
        binding(ps, p0, p1), tables_shaped(db), vals_ok(db), r.len() == 3, r[2] == (Val::Num { coeff: s, scale: 4 }),
        avg_in(db, p0, p1) == Ok::<Val, SqlError>(Val::Num { coeff: ac, scale: asc }),
    ensures
        eval_pred(db, r, having_pred(ps)) == Ok::<Truth, SqlError>(truth_of(num_cmp(s, 4, ac, asc) > 0)),
{
    lemma_subquery(db, r, ps, p0, p1);
    lemma_col_val(db, r, 2);
    lemma_cmp_node(db, r, CmpOp::Gt, Expr::Col(2), Expr::Subquery(Box::new(avg_q(ps))), r[2],
        Val::Num { coeff: ac, scale: asc });
}

/// The HAVING condition when the AVG is an error.
pub proof fn lemma_having_err(db: Database, r: Row, ps: Seq<Literal>, p0: Seq<u8>, p1: int, e: SqlError)
    requires
        binding(ps, p0, p1), tables_shaped(db), vals_ok(db), r.len() == 3,
        avg_in(db, p0, p1) == Err::<Val, SqlError>(e),
    ensures eval_pred(db, r, having_pred(ps)) == Err::<Truth, SqlError>(e),
{
    lemma_subquery(db, r, ps, p0, p1);
    lemma_col_val(db, r, 2);
}

// ------------------------------------------------------------------------------------------------- the body

/// The outer group rows.
pub open spec fn gb_rows(db: Database, p0: Seq<u8>, p1: int) -> Seq<Row> {
    gkeys(g_out(p0, p1), joined(db)).map_values(|k: Row| full_row(g_out(p0, p1), joined(db), k))
}

/// A group row's SUM compares above `(ac, asc)`.
pub open spec fn above_fn(ac: int, asc: nat) -> spec_fn(Row) -> bool {
    |r: Row| num_cmp(coeff(r[2]), 4, ac, asc) > 0
}

/// An outer group's row is `[name, cik, Num(SUM, 4)]`.
pub proof fn lemma_outer_row(db: Database, p0: Seq<u8>, p1: int, t: int)
    requires tables_shaped(db), 0 <= t < gkeys(g_out(p0, p1), joined(db)).len(),
    ensures ({
        let g = g_out(p0, p1);
        let k = gkeys(g, joined(db))[t];
        &&& k.len() == 2
        &&& gcount(g, joined(db), k) > 0
        &&& full_row(g, joined(db), k) == seq![k[0], k[1], Val::Num { coeff: gsum(g, joined(db), k, 0), scale: 4 }]
    }),
{
    let g = g_out(p0, p1);
    let xs = joined(db);
    let k = gkeys(g, xs)[t];
    lemma_gkeys(g, xs);
    assert(gkeys(g, xs).contains(k));
    crate::link::query::lemma_count_witness(g, xs, k);
    let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
    assert(k == (g.key)(xs[m]));
    assert(agg_outs(g, xs, k)[0] == agg_out(AggKind::Sum { scale: 4 }, gcount(g, xs, k), gsum(g, xs, k, 0)));
    assert(full_row(g, xs, k) =~= seq![k[0], k[1], Val::Num { coeff: gsum(g, xs, k, 0), scale: 4 }]);
}

/// With an AVG value, the body keeps the group rows above it.
pub proof fn lemma_body_rows(db: Database, ps: Seq<Literal>, p0: Seq<u8>, p1: int, ac: int, asc: nat)
    requires
        binding(ps, p0, p1), tables_shaped(db), vals_ok(db),
        avg_in(db, p0, p1) == Ok::<Val, SqlError>(Val::Num { coeff: ac, scale: asc }),
    ensures eval_query(db, Seq::empty(), body_q(ps)) == Ok::<Relation, SqlError>(keep(gb_rows(db, p0, p1), above_fn(ac, asc))),
{
    let rows = gb_rows(db, p0, p1);
    let h = above_fn(ac, asc);
    lemma_outer_rows(db, ps, p0, p1);
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, Seq::<Val>::empty() + #[trigger] rows[i], having_pred(ps)) == Ok::<Truth, SqlError>(truth_of(h(rows[i]))) by {
        lemma_outer_row(db, p0, p1, i);
        let r = rows[i];
        assert(Seq::<Val>::empty() + r =~= r);
        let s = coeff(r[2]);
        lemma_having(db, r, ps, p0, p1, s, ac, asc);
    }
    lemma_filter_rows3(db, Seq::empty(), having_pred(ps), outer_gb(ps), rows, h);
}

/// With an AVG error and some group row, the body is that error.
pub proof fn lemma_body_err(db: Database, ps: Seq<Literal>, p0: Seq<u8>, p1: int, e: SqlError)
    requires
        binding(ps, p0, p1), tables_shaped(db), vals_ok(db),
        avg_in(db, p0, p1) == Err::<Val, SqlError>(e),
        gb_rows(db, p0, p1).len() > 0,
    ensures eval_query(db, Seq::empty(), body_q(ps)) == Err::<Relation, SqlError>(e),
{
    let rows = gb_rows(db, p0, p1);
    lemma_outer_rows(db, ps, p0, p1);
    assert forall|k: int| 0 <= k < rows.len() implies #[trigger] eval_pred(db, Seq::<Val>::empty() + rows[k], having_pred(ps)) is Ok
        || eval_pred(db, Seq::<Val>::empty() + rows[k], having_pred(ps)) == Err::<Truth, SqlError>(e) by {
        lemma_outer_row(db, p0, p1, k);
        assert(Seq::<Val>::empty() + rows[k] =~= rows[k]);
        lemma_having_err(db, rows[k], ps, p0, p1, e);
    }
    lemma_outer_row(db, p0, p1, 0);
    assert(Seq::<Val>::empty() + rows[0] =~= rows[0]);
    lemma_having_err(db, rows[0], ps, p0, p1, e);
    crate::link::capacity::lemma_filter_err(db, Seq::empty(), having_pred(ps), Box::new(outer_gb(ps)), rows, e, 0);
}

/// Without group rows the body is empty.
pub proof fn lemma_body_empty(db: Database, ps: Seq<Literal>, p0: Seq<u8>, p1: int)
    requires binding(ps, p0, p1), tables_shaped(db), vals_ok(db), gb_rows(db, p0, p1).len() == 0,
    ensures eval_query(db, Seq::empty(), body_q(ps)) == Ok::<Relation, SqlError>(Seq::empty()),
{
    let rows = gb_rows(db, p0, p1);
    lemma_outer_rows(db, ps, p0, p1);
    lemma_eval_filter(db, Seq::empty(), having_pred(ps), Box::new(outer_gb(ps)));
    let rs = filter_results(db, Seq::empty(), rows, having_pred(ps));
    lemma_collect_all(rs, Seq::<Truth>::empty());
    assert(keep_true(rows, Seq::<Truth>::empty()) =~= Seq::<Row>::empty());
}

} // verus!
