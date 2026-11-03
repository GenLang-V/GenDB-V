//! The inner GROUP BY (`inner_q`: c_custkey, COUNT(o_orderkey)) over the LEFT JOIN rows.
//!
//! The join rows are the blocks of the customer rows in order (`block(i)`: the matching orders rows appended to
//! customer row `i`, or that row padded with NULLs); every row of block `i` has key `c_custkey` of row `i`, and the
//! customer keys are distinct. So the groups are the customer rows in order (`lemma_keys_prefix`), the members of
//! group `i` are the arguments of block `i` (`lemma_members_prefix`), and COUNT(o_orderkey) counts the matching
//! orders rows (`lemma_block_count`): the inner rows are `[c_custkey_i, ccnt(i)]` (`lemma_inner_ok`), or 22003 when
//! a count leaves bigint (`lemma_inner_overflow`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::numeric::sign;
use crate::spec::limits::*;
use crate::link::expr::*;
use crate::link::query::lemma_groupby_unfold;
use crate::bridge::collect::*;
use crate::link::capacity::lemma_collect_uniform_err;
use crate::query::param_typed;
use super::sql::*;

verus! {

// ------------------------------------------------------------------------------------------------ key rows

/// The one-column key row of an integer.
pub open spec fn krow(x: int) -> Row {
    seq![Val::Int(x)]
}

/// Integer key rows are not distinct exactly when equal.
pub proof fn lemma_krow_nd(x: int, y: int)
    ensures row_not_distinct(krow(x), krow(y)) == (x == y),
{
    let (a, b) = (krow(x), krow(y));
    assert(val_not_distinct(a[0], b[0]) == (sign(x - y) == 0));
    if x == y {
        assert(row_not_distinct(a, b));
    }
}

/// `n` copies of row `b`.
pub open spec fn run(b: Row, n: nat) -> Seq<Row> {
    Seq::new(n, |_i: int| b)
}

/// `distinct_rows` of rows followed by a run of a new key: the new key is appended once.
pub proof fn lemma_distinct_run(a: Seq<Row>, b: Row, n: nat)
    requires
        n >= 1,
        !has_not_distinct(distinct_rows(a), b),
        row_not_distinct(b, b),
    ensures
        distinct_rows(a + run(b, n)) == distinct_rows(a).push(b),
    decreases n,
{
    if n == 1 {
        assert(a + run(b, 1) =~= a.push(b));
        assert(a.push(b).drop_last() =~= a);
    } else {
        lemma_distinct_run(a, b, (n - 1) as nat);
        let x = a + run(b, (n - 1) as nat);
        assert(a + run(b, n) =~= x.push(b));
        assert(x.push(b).drop_last() =~= x);
        let d = distinct_rows(x);
        assert(d.last() == b);
        assert(has_not_distinct(d, b));
    }
}

/// The key rows of the first `m` customers.
pub open spec fn ckeys(db: Database, m: int) -> Seq<Row> {
    Seq::new(m as nat, |i: int| krow(ival(ctab(db)[i][0])))
}

/// A customer key is distinct from the keys before it.
proof fn lemma_new_key(db: Database, m: int, k: int)
    requires
        db_facts(db),
        0 <= m <= k < ctab(db).len(),
    ensures
        !has_not_distinct(ckeys(db, m), krow(ival(ctab(db)[k][0]))),
    decreases m,
{
    if m > 0 {
        let d = ckeys(db, m);
        assert(d.drop_last() =~= ckeys(db, m - 1));
        lemma_new_key(db, m - 1, k);
        assert(ctab(db)[m - 1][0] != ctab(db)[k][0]);
        lemma_krow_nd(ival(ctab(db)[m - 1][0]), ival(ctab(db)[k][0]));
    }
}

// ------------------------------------------------------------------------------------------------ group members

/// `group_members` of concatenated keys and arguments.
pub proof fn lemma_members_append(ka: Seq<Row>, aa: Seq<Row>, kb: Seq<Row>, ab: Seq<Row>, k: Row)
    requires ka.len() == aa.len(), kb.len() == ab.len(),
    ensures group_members(ka + kb, aa + ab, k) == group_members(ka, aa, k) + group_members(kb, ab, k),
    decreases kb.len(),
{
    if kb.len() == 0 {
        assert(ka + kb =~= ka);
        assert(aa + ab =~= aa);
        assert(group_members(kb, ab, k) =~= Seq::<Row>::empty());
        assert(group_members(ka, aa, k) + Seq::<Row>::empty() =~= group_members(ka, aa, k));
    } else {
        lemma_members_append(ka, aa, kb.drop_last(), ab.drop_last(), k);
        assert((ka + kb).drop_last() =~= ka + kb.drop_last());
        assert((aa + ab).drop_last() =~= aa + ab.drop_last());
        assert((ka + kb).last() == kb.last());
        assert((aa + ab).last() == ab.last());
        let gm = group_members(ka, aa, k);
        if row_not_distinct(kb.last(), k) {
            assert(gm + group_members(kb.drop_last(), ab.drop_last(), k).push(ab.last())
                =~= (gm + group_members(kb.drop_last(), ab.drop_last(), k)).push(ab.last()));
        }
    }
}

/// `group_members` of a run of one key.
pub proof fn lemma_members_run(b: Row, args: Seq<Row>, k: Row)
    ensures group_members(run(b, args.len()), args, k) == if row_not_distinct(b, k) { args } else { Seq::<Row>::empty() },
    decreases args.len(),
{
    if args.len() > 0 {
        let ks = run(b, args.len());
        assert(ks.drop_last() =~= run(b, (args.len() - 1) as nat));
        lemma_members_run(b, args.drop_last(), k);
        if row_not_distinct(b, k) {
            assert(args.drop_last().push(args.last()) =~= args);
        }
    } else {
        assert(group_members(run(b, 0), args, k) =~= Seq::<Row>::empty());
    }
}

// ------------------------------------------------------------------------------------------------ the join blocks

/// The join rows of customer row `i`.
pub open spec fn block(db: Database, ps: Seq<Literal>, i: int) -> Seq<Row> {
    left_join_one(ctab(db)[i], otab(db), lj_truths(db, ps)[i], 9)
}

/// The join rows of the first `m` customer rows.
pub open spec fn lj_prefix(db: Database, ps: Seq<Literal>, m: int) -> Seq<Row> {
    left_join_rows(ctab(db).take(m), otab(db), lj_truths(db, ps).take(m), 9)
}

/// The key rows of join rows.
pub open spec fn jkeys(rows: Seq<Row>) -> Seq<Row> {
    rows.map_values(|x: Row| seq![x[0]])
}

/// The argument rows of join rows (o_orderkey or NULL).
pub open spec fn jargs(rows: Seq<Row>) -> Seq<Row> {
    rows.map_values(|x: Row| seq![x[8]])
}

/// One more customer row.
proof fn lemma_prefix_step(db: Database, ps: Seq<Literal>, m: int)
    requires 0 <= m < ctab(db).len(),
    ensures lj_prefix(db, ps, m + 1) == lj_prefix(db, ps, m) + block(db, ps, m),
{
    let (c, t) = (ctab(db).take(m + 1), lj_truths(db, ps).take(m + 1));
    assert(c.drop_last() =~= ctab(db).take(m));
    assert(t.drop_last() =~= lj_truths(db, ps).take(m));
    assert(c.last() == ctab(db)[m]);
    assert(t.last() == lj_truths(db, ps)[m]);
}

/// The rows matched by customer row `i`.
pub open spec fn matched(db: Database, ps: Seq<Literal>, i: int) -> Seq<Row> {
    keep_true(otab(db), lj_truths(db, ps)[i])
}

/// Rows kept from orders rows are orders-shaped (9 values, an integer o_orderkey).
proof fn lemma_keep_true_rows(rows: Seq<Row>, truths: Seq<Truth>)
    requires forall|j: int| 0 <= j < rows.len() ==> (#[trigger] rows[j]).len() == 9 && rows[j][0] is Int,
    ensures
        forall|q: int| 0 <= q < keep_true(rows, truths).len() ==>
            (#[trigger] keep_true(rows, truths)[q]).len() == 9 && keep_true(rows, truths)[q][0] is Int,
    decreases rows.len(),
{
    if rows.len() > 0 && truths.len() > 0 {
        let d = rows.drop_last();
        assert forall|j: int| 0 <= j < d.len() implies (#[trigger] d[j]).len() == 9 && d[j][0] is Int by {
            assert(d[j] == rows[j]);
        }
        lemma_keep_true_rows(d, truths.drop_last());
        let init = keep_true(d, truths.drop_last());
        let kt = keep_true(rows, truths);
        assert forall|q: int| 0 <= q < kt.len() implies (#[trigger] kt[q]).len() == 9 && kt[q][0] is Int by {
            if q < init.len() {
                assert(kt[q] == init[q]);
            } else {
                assert(kt[q] == rows[rows.len() - 1]);
            }
        }
    }
}

/// Every row of block `i` has 17 values, key `c_custkey` of row `i`, and argument o_orderkey (matched) or NULL.
proof fn lemma_block_rows(db: Database, ps: Seq<Literal>, i: int)
    requires db_facts(db), 0 <= i < ctab(db).len(),
    ensures
        block(db, ps, i).len() >= 1,
        forall|q: int| 0 <= q < block(db, ps, i).len() ==> (#[trigger] block(db, ps, i)[q]).len() == 17,
        jkeys(block(db, ps, i)) == run(krow(ival(ctab(db)[i][0])), block(db, ps, i).len()),
        matched(db, ps, i).len() == 0 ==> jargs(block(db, ps, i)) == seq![seq![Val::Null]],
        matched(db, ps, i).len() > 0 ==> jargs(block(db, ps, i)) == matched(db, ps, i).map_values(|o: Row| seq![o[0]]),
        forall|q: int| 0 <= q < matched(db, ps, i).len() ==> (#[trigger] matched(db, ps, i)[q])[0] is Int,
{
    let c = ctab(db)[i];
    let mt = matched(db, ps, i);
    let b = block(db, ps, i);
    let kr = krow(ival(c[0]));
    lemma_keep_true_rows(otab(db), lj_truths(db, ps)[i]);
    assert(c[0] == Val::Int(ival(c[0])));
    if mt.len() == 0 {
        assert(b == seq![c + null_row(9)]);
        assert((c + null_row(9))[0] == c[0]);
        assert((c + null_row(9))[8] == Val::Null);
        assert(jkeys(b) =~= run(kr, 1));
        assert(jargs(b) =~= seq![seq![Val::Null]]);
    } else {
        assert(b == mt.map_values(|o: Row| c + o));
        assert forall|q: int| 0 <= q < b.len() implies (#[trigger] b[q]).len() == 17 by {
            assert(b[q] == c + mt[q]);
        }
        assert forall|q: int| 0 <= q < b.len() implies #[trigger] jkeys(b)[q] == run(kr, b.len())[q] by {
            assert(b[q] == c + mt[q]);
            assert((c + mt[q])[0] == c[0]);
        }
        assert(jkeys(b) =~= run(kr, b.len()));
        assert forall|q: int| 0 <= q < b.len() implies #[trigger] jargs(b)[q] == mt.map_values(|o: Row| seq![o[0]])[q] by {
            assert(b[q] == c + mt[q]);
            assert((c + mt[q])[8] == mt[q][0]);
        }
        assert(jargs(b) =~= mt.map_values(|o: Row| seq![o[0]]));
    }
}

/// Over the first `m` customer rows: the distinct keys are theirs in order, the members of customer `k`'s key
/// are the arguments of its block (none before it is reached), and every join row has 17 values.
proof fn lemma_prefix(db: Database, ps: Seq<Literal>, m: int)
    requires db_facts(db), 0 <= m <= ctab(db).len(),
    ensures
        distinct_rows(jkeys(lj_prefix(db, ps, m))) == ckeys(db, m),
        forall|k: int| 0 <= k < ctab(db).len() ==> #[trigger] group_members(jkeys(lj_prefix(db, ps, m)), jargs(lj_prefix(db, ps, m)), krow(ival(ctab(db)[k][0])))
            == if k < m { jargs(block(db, ps, k)) } else { Seq::<Row>::empty() },
        forall|q: int| 0 <= q < lj_prefix(db, ps, m).len() ==> (#[trigger] lj_prefix(db, ps, m)[q]).len() == 17,
    decreases m,
{
    let c = ctab(db);
    if m == 0 {
        let p = lj_prefix(db, ps, 0);
        assert(c.take(0) =~= Seq::<Row>::empty());
        assert(p =~= Seq::<Row>::empty());
        assert(jkeys(p) =~= Seq::<Row>::empty());
        assert(jargs(p) =~= Seq::<Row>::empty());
        assert(ckeys(db, 0) =~= Seq::<Row>::empty());
        assert forall|k: int| 0 <= k < c.len() implies #[trigger] group_members(jkeys(p), jargs(p), krow(ival(c[k][0])))
            == Seq::<Row>::empty() by {}
    } else {
        lemma_prefix(db, ps, m - 1);
        lemma_prefix_step(db, ps, m - 1);
        lemma_block_rows(db, ps, m - 1);
        let p0 = lj_prefix(db, ps, m - 1);
        let b = block(db, ps, m - 1);
        let p = lj_prefix(db, ps, m);
        assert(jkeys(p) =~= jkeys(p0) + jkeys(b));
        assert(jargs(p) =~= jargs(p0) + jargs(b));
        let kr = krow(ival(c[m - 1][0]));
        lemma_new_key(db, m - 1, m - 1);
        lemma_krow_nd(ival(c[m - 1][0]), ival(c[m - 1][0]));
        lemma_distinct_run(jkeys(p0), kr, b.len());
        assert(ckeys(db, m - 1).push(kr) =~= ckeys(db, m));
        assert forall|k: int| 0 <= k < c.len() implies #[trigger] group_members(jkeys(p), jargs(p), krow(ival(c[k][0])))
            == if k < m { jargs(block(db, ps, k)) } else { Seq::<Row>::empty() } by {
            let kk = krow(ival(c[k][0]));
            lemma_members_append(jkeys(p0), jargs(p0), jkeys(b), jargs(b), kk);
            assert(jargs(b).len() == b.len());
            lemma_members_run(kr, jargs(b), kk);
            lemma_krow_nd(ival(c[m - 1][0]), ival(c[k][0]));
            if k != m - 1 {
                assert(c[m - 1][0] != c[k][0]);
                assert(c[m - 1][0] == Val::Int(ival(c[m - 1][0])));
                assert(c[k][0] == Val::Int(ival(c[k][0])));
            }
            if k < m - 1 {
                assert(group_members(jkeys(p0), jargs(p0), kk) + Seq::<Row>::empty() =~= jargs(block(db, ps, k)));
            } else if k == m - 1 {
                assert(Seq::<Row>::empty() + jargs(b) =~= jargs(b));
            } else {
                assert(Seq::<Row>::empty() + Seq::<Row>::empty() =~= Seq::<Row>::empty());
            }
        }
        assert forall|q: int| 0 <= q < p.len() implies (#[trigger] p[q]).len() == 17 by {
            if q < p0.len() {
                assert(p[q] == p0[q]);
            } else {
                assert(p[q] == b[q - p0.len()]);
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ counts

/// COUNT(o_orderkey) of customer row `i`: its matched orders rows.
pub open spec fn ccnt(db: Database, ps: Seq<Literal>, i: int) -> nat {
    matched(db, ps, i).len()
}

/// Non-NULL values all count.
proof fn lemma_count_all(vs: Seq<Val>)
    requires forall|q: int| 0 <= q < vs.len() ==> !(#[trigger] vs[q] is Null),
    ensures count_non_null(vs) == vs.len(),
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_count_all(vs.drop_last());
    }
}

/// COUNT(o_orderkey) over block `i` is `ccnt(i)`.
proof fn lemma_block_count(db: Database, ps: Seq<Literal>, i: int)
    requires db_facts(db), 0 <= i < ctab(db).len(),
    ensures count_non_null(column(jargs(block(db, ps, i)), 0)) == ccnt(db, ps, i),
{
    lemma_block_rows(db, ps, i);
    let mt = matched(db, ps, i);
    let col = column(jargs(block(db, ps, i)), 0);
    if mt.len() == 0 {
        assert(col =~= seq![Val::Null]);
        assert(col.drop_last() =~= Seq::<Val>::empty());
        assert(count_non_null(col.drop_last()) == 0);
        assert(count_non_null(col) == 0);
    } else {
        assert(col =~= mt.map_values(|o: Row| o[0]));
        assert(col.len() == mt.len());
        assert forall|q: int| 0 <= q < col.len() implies !(#[trigger] col[q] is Null) by {
            assert(col[q] == mt[q][0]);
        }
        lemma_count_all(col);
    }
}

/// The inner rows: `[c_custkey_i, ccnt(i)]` per customer row, in order.
pub open spec fn inner_rows(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    Seq::new(ctab(db).len(), |i: int| seq![ctab(db)[i][0], Val::Int(ccnt(db, ps, i) as int)])
}

/// The prepared (key, arguments) pairs of the inner GROUP BY.
pub open spec fn inner_prep(rows: Seq<Row>) -> Seq<(Row, Row)> {
    Seq::new(rows.len(), |r: int| (seq![rows[r][0]], seq![rows[r][8]]))
}

/// The per-row keys and arguments of the inner GROUP BY evaluate without error.
proof fn lemma_inner_prep(db: Database, rows: Seq<Row>)
    requires forall|q: int| 0 <= q < rows.len() ==> (#[trigger] rows[q]).len() == 17,
    ensures
        collect(Seq::new(rows.len(), |r: int|
            match eval_exprs(db, Seq::<Val>::empty() + rows[r], seq![Expr::Col(0)]) {
                Err(err) => Err(err),
                Ok(k) => match agg_args(db, Seq::<Val>::empty() + rows[r], seq![Agg::Count(Expr::Col(8))]) {
                    Err(err) => Err(err),
                    Ok(a) => Ok((k, a)),
                },
            })) == Ok::<Seq<(Row, Row)>, SqlError>(inner_prep(rows)),
{
    let rs = Seq::new(rows.len(), |r: int|
        match eval_exprs(db, Seq::<Val>::empty() + rows[r], seq![Expr::Col(0)]) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, Seq::<Val>::empty() + rows[r], seq![Agg::Count(Expr::Col(8))]) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        });
    assert forall|r: int| 0 <= r < rs.len() implies #[trigger] rs[r] == Ok::<(Row, Row), SqlError>(inner_prep(rows)[r]) by {
        let env = Seq::<Val>::empty() + rows[r];
        assert(env =~= rows[r]);
        let ks = seq![Expr::Col(0)];
        lemma_expr_col(db, env, 0);
        lemma_expr_results_index(db, env, ks);
        lemma_collect_all(expr_results(db, env, ks), seq![env[0]]);
        let ags = seq![Agg::Count(Expr::Col(8))];
        lemma_expr_col(db, env, 8);
        lemma_agg_arg_results_index(db, env, ags);
        lemma_collect_all(agg_arg_results(db, env, ags), seq![env[8]]);
    }
    lemma_collect_all(rs, inner_prep(rows));
}

/// The aggregates of group `i`: COUNT(o_orderkey) over its members.
proof fn lemma_group_agg(db: Database, ps: Seq<Literal>, i: int)
    requires db_facts(db), 0 <= i < ctab(db).len(),
    ensures
        agg_row(seq![Agg::Count(Expr::Col(8))], jargs(block(db, ps, i)))
            == collect(seq![int_result(IntKind::Int8, ccnt(db, ps, i) as int)]),
{
    lemma_block_count(db, ps, i);
    let aggs = seq![Agg::Count(Expr::Col(8))];
    assert(Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(jargs(block(db, ps, i)), j)))
        =~= seq![int_result(IntKind::Int8, ccnt(db, ps, i) as int)]);
}

/// The group outcomes of the inner GROUP BY, one per customer row.
pub open spec fn inner_results(db: Database, ps: Seq<Literal>) -> Seq<Result<Row, SqlError>> {
    Seq::new(ctab(db).len(), |g: int| match int_result(IntKind::Int8, ccnt(db, ps, g) as int) {
        Ok(v) => Ok::<Row, SqlError>(seq![ctab(db)[g][0], v]),
        Err(e) => Err(e),
    })
}

/// The join rows of all customer rows.
pub open spec fn lj_all(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    lj_prefix(db, ps, ctab(db).len() as int)
}

/// The inner GROUP BY as `group_rows` over the join rows' keys and arguments.
proof fn lemma_inner_group_rows(db: Database, ps: Seq<Literal>)
    requires
        db_facts(db),
        param_typed(ps),
        !(ctab(db).len() > 0 && some_err(db, ps)),
    ensures
        eval_query(db, Seq::empty(), inner_q(ps))
            == group_rows(seq![Agg::Count(Expr::Col(8))], jkeys(lj_all(db, ps)), jargs(lj_all(db, ps))),
{
    let c = ctab(db);
    lemma_lj_ok(db, ps);
    assert(c.take(c.len() as int) =~= c);
    assert(lj_truths(db, ps).take(c.len() as int) =~= lj_truths(db, ps));
    let rows = lj_all(db, ps);
    lemma_prefix(db, ps, c.len() as int);
    lemma_inner_prep(db, rows);
    let prep = inner_prep(rows);
    lemma_groupby_unfold(db, lj_q(ps), seq![Expr::Col(0)], seq![Agg::Count(Expr::Col(8))], rows, prep);
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= jkeys(rows));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= jargs(rows));
}

/// `group_rows` of the join rows is `collect` of the group outcomes.
proof fn lemma_group_rows_results(db: Database, ps: Seq<Literal>)
    requires db_facts(db),
    ensures
        group_rows(seq![Agg::Count(Expr::Col(8))], jkeys(lj_all(db, ps)), jargs(lj_all(db, ps))) == collect(inner_results(db, ps)),
{
    hide(agg_row);
    let c = ctab(db);
    let rows = lj_all(db, ps);
    lemma_prefix(db, ps, c.len() as int);
    let aggs = seq![Agg::Count(Expr::Col(8))];
    let ks = distinct_rows(jkeys(rows));
    assert(ks == ckeys(db, c.len() as int));
    let gs = Seq::new(ks.len(), |g: int|
        match agg_row(aggs, group_members(jkeys(rows), jargs(rows), ks[g])) {
            Ok(a) => Ok(ks[g] + a),
            Err(e) => Err(e),
        });
    assert forall|g: int| 0 <= g < c.len() implies #[trigger] gs[g] == inner_results(db, ps)[g] by {
        assert(ks[g] == krow(ival(c[g][0])));
        assert(group_members(jkeys(rows), jargs(rows), krow(ival(c[g][0]))) == jargs(block(db, ps, g)));
        lemma_group_agg(db, ps, g);
        let ir = int_result(IntKind::Int8, ccnt(db, ps, g) as int);
        assert(c[g][0] == Val::Int(ival(c[g][0])));
        match ir {
            Ok(v) => {
                lemma_collect_all(seq![ir], seq![v]);
                assert(ks[g] + seq![v] =~= seq![c[g][0], v]);
            },
            Err(e) => {
                lemma_collect_first_err(seq![ir], 0);
            },
        }
    }
    assert(gs =~= inner_results(db, ps));
    crate::bridge::collect::lemma_collect_pointwise::<Row>();
}

/// The inner GROUP BY is `collect` of the group outcomes (when the join has a value).
proof fn lemma_inner_unfold(db: Database, ps: Seq<Literal>)
    requires
        db_facts(db),
        param_typed(ps),
        !(ctab(db).len() > 0 && some_err(db, ps)),
    ensures
        eval_query(db, Seq::empty(), inner_q(ps)) == collect(inner_results(db, ps)),
{
    lemma_inner_group_rows(db, ps);
    lemma_group_rows_results(db, ps);
}

/// Without a matcher error and with every count in bigint, the inner GROUP BY is `inner_rows`.
pub proof fn lemma_inner_ok(db: Database, ps: Seq<Literal>)
    requires
        db_facts(db),
        param_typed(ps),
        !(ctab(db).len() > 0 && some_err(db, ps)),
        forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] ccnt(db, ps, i) <= int8_max(),
    ensures
        eval_query(db, Seq::empty(), inner_q(ps)) == Ok::<Relation, SqlError>(inner_rows(db, ps)),
{
    lemma_inner_unfold(db, ps);
    let rs = inner_results(db, ps);
    assert forall|g: int| 0 <= g < rs.len() implies #[trigger] rs[g] == Ok::<Row, SqlError>(inner_rows(db, ps)[g]) by {
        assert(ccnt(db, ps, g) <= int8_max());
        assert(int8_min() <= 0);
    }
    lemma_collect_all(rs, inner_rows(db, ps));
}

/// A count beyond bigint makes the inner GROUP BY raise 22003.
pub proof fn lemma_inner_overflow(db: Database, ps: Seq<Literal>, i: int)
    requires
        db_facts(db),
        param_typed(ps),
        !(ctab(db).len() > 0 && some_err(db, ps)),
        0 <= i < ctab(db).len(),
        ccnt(db, ps, i) > int8_max(),
    ensures
        eval_query(db, Seq::empty(), inner_q(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    lemma_inner_unfold(db, ps);
    let rs = inner_results(db, ps);
    assert forall|k: int| 0 <= k < rs.len() implies #[trigger] rs[k] is Ok || rs[k] == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange) by {}
    lemma_collect_uniform_err(rs, SqlError::NumericValueOutOfRange, i);
}

} // verus!
