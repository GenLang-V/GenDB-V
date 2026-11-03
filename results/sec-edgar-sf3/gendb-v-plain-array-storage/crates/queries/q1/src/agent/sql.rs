//! The link from the statement's SQL meaning to the normal form (`agent::spec`).
//!
//! `lemma_body`: the denotation is the GROUP BY of the rows kept by `stmt IS NOT NULL`, each with key (stmt, rfile)
//! and aggregate arguments (NULL for COUNT(*), adsh, line) (`myargs`). The link toolkit's filter and group-key
//! lemmas are used with a normal form whose condition and key are ours (`gq`). `lemma_members`: the members of a
//! group are `mm`, which `lemma_mm` relates to `cnt_r`, `sum_r` and `aset_r`; `lemma_agg_row` gives the three
//! aggregate values of a group.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::spec::equality::*;
use crate::spec::int::*;
use crate::spec::limits::*;
use crate::spec::aggs::avg::*;
use crate::spec::fns::div::*;
use crate::bridge::equality::*;
use crate::bridge::collect::lemma_collect_all;
use crate::link::query::{QuerySpec, proj, proj_all, qual_truths, qrows, qkeys, key_pool, keys_exact, gkeys, gcount,
    lemma_filter_rows, lemma_kept_rows, lemma_groupby_unfold, lemma_eval_cols, col_exprs, select, lemma_row_exact,
    lemma_pool_exact, lemma_distinct_gkeys, lemma_gkeys, pred_agrees, lemma_qrows_sub, lemma_avg_ok, avg_of};
use crate::query::query_spec;
use crate::agent::cols::*;
use crate::agent::spec::*;

verus! {

/// All columns of a `pre` row.
pub open spec fn c10() -> Seq<nat> {
    seq![0nat, 1, 2, 3, 4, 5, 6, 7, 8, 9]
}

/// The normal form of the link toolkit with our condition and key (arguments unused).
pub open spec fn gq() -> QuerySpec {
    QuerySpec { qual: |x: Row| qual(x), key: |x: Row| key_of(x), arg: |j: int, x: Row| 0int, aggs: Seq::empty(),
        outs: Seq::empty(), grouped: true }
}

/// The aggregate arguments of a row: NULL (COUNT(*)), adsh, line.
pub open spec fn myargs(r: Row) -> Row {
    seq![Val::Null, r[0], r[2]]
}

pub open spec fn q_keys() -> Seq<Expr> {
    seq![Expr::Col(3), Expr::Col(5)]
}

pub open spec fn q_aggs() -> Seq<Agg> {
    seq![Agg::CountStar, Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(0)))), Agg::Avg { kind: NumKind::Int4, arg: Expr::Col(2) }]
}

pub open spec fn q_pred() -> Pred {
    Pred::Not(Box::new(Pred::IsNull(Expr::Col(3))))
}

pub open spec fn q_input() -> Query {
    Query::Filter { pred: q_pred(), input: Box::new(Query::Table(3)) }
}

pub proof fn lemma_query_shape()
    ensures
        query_spec().body == (Query::GroupBy { keys: q_keys(), aggs: q_aggs(), input: Box::new(q_input()) }),
        query_spec().keys == seq![OrderKey { col: 2, desc: true, nulls_first: true }],
        query_spec().limit is None,
        query_spec().offset == 0,
{
    assert(q_keys() =~= seq![Expr::Col(3), Expr::Col(5)]);
}

/// Every row has the 10 columns of `pre`.
pub open spec fn rows10(t: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < t.len() ==> (#[trigger] t[i]).len() == 10
}

pub proof fn lemma_proj_id(r: Row)
    requires r.len() == 10,
    ensures proj(r, c10()) == r,
{
    assert(proj(r, c10()) =~= r);
}

pub proof fn lemma_proj_all_id(t: Seq<Row>)
    requires rows10(t),
    ensures proj_all(t, c10()) == t,
{
    assert forall|i: int| 0 <= i < t.len() implies #[trigger] proj_all(t, c10())[i] == t[i] by {
        lemma_proj_id(t[i]);
    }
    assert(proj_all(t, c10()) =~= t);
}

/// WHERE stmt IS NOT NULL over the table keeps the qualifying rows.
pub proof fn lemma_filter(db: Database, t: Seq<Row>)
    requires 3 < db.tables.len(), db.tables[3] == t, rows10(t),
    ensures eval_query(db, Seq::empty(), q_input()) == Ok::<Relation, SqlError>(keep_true(t, qual_truths(gq(), proj_all(t, c10())))),
{
    let src = Query::Table(3);
    assert(eval_query(db, Seq::empty(), src) == Ok::<Relation, SqlError>(t));
    assert forall|i: int| 0 <= i < t.len() implies
        eval_pred(db, #[trigger] t[i], q_pred()) == Ok::<Truth, SqlError>(truth_of((gq().qual)(proj(t[i], c10())))) by {
        lemma_proj_id(t[i]);
        let inner = Pred::IsNull(Expr::Col(3));
        assert(eval_expr(db, t[i], Expr::Col(3)) == Ok::<Val, SqlError>(t[i][3]));
        assert(eval_pred(db, t[i], inner) == Ok::<Truth, SqlError>(truth_of(t[i][3] is Null)));
        assert(truth_not(truth_of(t[i][3] is Null)) == truth_of(!(t[i][3] is Null)));
    }
    assert(pred_agrees(db, t, c10(), q_pred(), gq()));
    lemma_filter_rows(db, src, t, c10(), q_pred(), gq());
}

proof fn lemma_arg0(db: Database, r: Row)
    ensures agg_arg(db, r, Agg::CountStar) == Ok::<Val, SqlError>(Val::Null),
{
}

proof fn lemma_arg1(db: Database, r: Row)
    requires r.len() == 10,
    ensures agg_arg(db, r, Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(0))))) == Ok::<Val, SqlError>(r[0]),
{
    assert(agg_arg(db, r, Agg::Count(Expr::Col(0))) == eval_expr(db, r, Expr::Col(0)));
}

proof fn lemma_arg2(db: Database, r: Row)
    requires r.len() == 10,
    ensures agg_arg(db, r, Agg::Avg { kind: NumKind::Int4, arg: Expr::Col(2) }) == Ok::<Val, SqlError>(r[2]),
{
    assert(agg_arg(db, r, Agg::Avg { kind: NumKind::Int4, arg: Expr::Col(2) }) == eval_expr(db, r, Expr::Col(2)));
}

proof fn lemma_row_keys(db: Database, r: Row)
    requires r.len() == 10,
    ensures eval_exprs(db, r, q_keys()) == Ok::<Row, SqlError>(key_of(r)),
{
    let idxs = seq![3nat, 5nat];
    assert(col_exprs(idxs) =~= q_keys());
    lemma_eval_cols(db, r, idxs);
    assert(select(r, idxs) =~= key_of(r));
}

/// `collect` of three successes.
pub proof fn lemma_collect3<T>(rs: Seq<Result<T, SqlError>>, a: T, b: T, c: T)
    requires rs.len() == 3, rs[0] == Ok::<T, SqlError>(a), rs[1] == Ok::<T, SqlError>(b), rs[2] == Ok::<T, SqlError>(c),
    ensures collect(rs) == Ok::<Seq<T>, SqlError>(seq![a, b, c]),
{
    let r2 = rs.drop_last();
    let r1 = r2.drop_last();
    let r0 = r1.drop_last();
    assert(r0.len() == 0);
    assert(collect(r0) == Ok::<Seq<T>, SqlError>(Seq::empty()));
    assert(r1.last() == rs[0]);
    assert(collect(r1) == Ok::<Seq<T>, SqlError>(Seq::<T>::empty().push(a)));
    assert(r2.last() == rs[1]);
    assert(collect(r2) == Ok::<Seq<T>, SqlError>(Seq::<T>::empty().push(a).push(b)));
    assert(rs.last() == rs[2]);
    assert(Seq::<T>::empty().push(a).push(b).push(c) =~= seq![a, b, c]);
}

proof fn lemma_row_args(db: Database, r: Row)
    requires r.len() == 10,
    ensures agg_args(db, r, q_aggs()) == Ok::<Row, SqlError>(myargs(r)),
{
    hide(agg_arg);
    hide(eval_expr);
    lemma_arg0(db, r);
    lemma_arg1(db, r);
    lemma_arg2(db, r);
    let aggs = q_aggs();
    lemma_agg_arg_results_index(db, r, aggs);
    let rs = agg_arg_results(db, r, aggs);
    assert(rs[0] == agg_arg(db, r, aggs[0]));
    assert(rs[1] == agg_arg(db, r, aggs[1]));
    assert(rs[2] == agg_arg(db, r, aggs[2]));
    lemma_collect3(rs, Val::Null, r[0], r[2]);
}

/// Key and aggregate arguments of a row.
pub proof fn lemma_row_exprs(db: Database, r: Row)
    requires r.len() == 10,
    ensures
        eval_exprs(db, r, q_keys()) == Ok::<Row, SqlError>(key_of(r)),
        agg_args(db, r, q_aggs()) == Ok::<Row, SqlError>(myargs(r)),
{
    lemma_row_keys(db, r);
    lemma_row_args(db, r);
}

/// The kept rows are the qualifying rows (`qrows`), each a row of the table.
pub proof fn lemma_kept(t: Seq<Row>)
    requires rows10(t),
    ensures ({
        let kept = keep_true(t, qual_truths(gq(), proj_all(t, c10())));
        &&& kept == qrows(gq(), t)
        &&& rows10(kept)
    }),
{
    let xs = proj_all(t, c10());
    let kept = keep_true(t, qual_truths(gq(), xs));
    lemma_proj_all_id(t);
    lemma_kept_rows(gq(), t, c10());
    assert forall|i: int| 0 <= i < kept.len() implies (#[trigger] kept[i]).len() == 10 by {
        assert(t.contains(kept[i]));
        let m = choose|m: int| 0 <= m < t.len() && t[m] == kept[i];
    }
    lemma_proj_all_id(kept);
}

/// The denotation: GROUP BY over the qualifying rows' keys and arguments.
pub proof fn lemma_body(db: Database, t: Seq<Row>)
    requires 3 < db.tables.len(), db.tables[3] == t, rows10(t),
    ensures denote_body(db, query_spec()) == group_rows(q_aggs(), qkeys(gq(), t), qrows(gq(), t).map_values(|r: Row| myargs(r))),
{
    lemma_query_shape();
    lemma_filter(db, t);
    lemma_kept(t);
    let kept = qrows(gq(), t);
    let ctx = Seq::<Val>::empty();
    let prep = Seq::new(kept.len(), |i: int| (key_of(kept[i]), myargs(kept[i])));
    let pre = Seq::new(kept.len(), |i: int|
        match eval_exprs(db, ctx + kept[i], q_keys()) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, ctx + kept[i], q_aggs()) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        });
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<(Row, Row), SqlError>(prep[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        lemma_row_exprs(db, kept[i]);
    }
    lemma_collect_all(pre, prep);
    lemma_groupby_unfold(db, q_input(), q_keys(), q_aggs(), kept, prep);
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(gq(), t));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= kept.map_values(|r: Row| myargs(r)));
}

/// The keys of all rows (a pool on which SQL "not distinct" is equality).
pub open spec fn kpool(t: Seq<Row>) -> Seq<Row> {
    t.map_values(|r: Row| key_of(r))
}

/// Keys of the table's rows: stmt NULL or text, rfile text.
pub open spec fn keys_typed(t: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < t.len() ==> ((#[trigger] t[i])[3] is Null || t[i][3] is Text) && t[i][5] is Text && t[i].len() == 10
}

pub proof fn lemma_keys_typed(c: Cols, t: Seq<Row>)
    requires corr(c, t),
    ensures keys_typed(t), rows10(t),
{
    assert forall|i: int| 0 <= i < t.len() implies ((#[trigger] t[i])[3] is Null || t[i][3] is Text) && t[i][5] is Text && t[i].len() == 10 by {
        assert(row_corr(c, t[i], i));
    }
}

/// On the keys of the table, SQL "not distinct" is equality.
pub proof fn lemma_kpool_exact(t: Seq<Row>)
    requires keys_typed(t),
    ensures forall|a: Row, b: Row| kpool(t).contains(a) && kpool(t).contains(b) ==> (#[trigger] row_not_distinct(a, b) <==> a == b),
{
    let p = kpool(t);
    assert forall|a: Row, b: Row| p.contains(a) && p.contains(b) implies (#[trigger] row_not_distinct(a, b) <==> a == b) by {
        let i = choose|i: int| 0 <= i < p.len() && p[i] == a;
        let j = choose|j: int| 0 <= j < p.len() && p[j] == b;
        assert(a == key_of(t[i]) && b == key_of(t[j]));
        assert(t[i][3] is Null || t[i][3] is Text);
        assert(t[j][3] is Null || t[j][3] is Text);
        assert forall|q: int| 0 <= q < a.len() implies same_exact_type(#[trigger] a[q], b[q]) by {}
        lemma_row_exact(a, b);
    }
}

/// The keys of the qualifying rows of a prefix are in the pool.
pub proof fn lemma_qkeys_in_pool(t: Seq<Row>, hi: int)
    requires 0 <= hi <= t.len(),
    ensures forall|i: int| 0 <= i < qkeys(gq(), t.subrange(0, hi)).len() ==> kpool(t).contains(#[trigger] qkeys(gq(), t.subrange(0, hi))[i]),
{
    let xs = t.subrange(0, hi);
    lemma_qrows_sub(gq(), xs);
    assert forall|i: int| 0 <= i < qkeys(gq(), xs).len() implies kpool(t).contains(#[trigger] qkeys(gq(), xs)[i]) by {
        let x = qrows(gq(), xs)[i];
        assert(xs.contains(x));
        let m = choose|m: int| 0 <= m < xs.len() && xs[m] == x;
        assert(kpool(t)[m] == key_of(t[m]));
    }
}

/// Members (aggregate argument rows) of group `k` among `t[0..hi)`, in row order.
pub open spec fn mm(t: Seq<Row>, k: Row, hi: int) -> Seq<Row>
    decreases hi,
{
    if hi <= 0 {
        Seq::empty()
    } else if hit(t[hi - 1], k) {
        mm(t, k, hi - 1).push(myargs(t[hi - 1]))
    } else {
        mm(t, k, hi - 1)
    }
}

/// The GROUP BY members of a pool key are `mm`.
pub proof fn lemma_members(t: Seq<Row>, k: Row, hi: int)
    requires keys_typed(t), 0 <= hi <= t.len(), kpool(t).contains(k),
    ensures
        group_members(qkeys(gq(), t.subrange(0, hi)), qrows(gq(), t.subrange(0, hi)).map_values(|r: Row| myargs(r)), k)
            == mm(t, k, hi),
    decreases hi,
{
    let xs = t.subrange(0, hi);
    let ks = qkeys(gq(), xs);
    let ags = qrows(gq(), xs).map_values(|r: Row| myargs(r));
    if hi > 0 {
        let xi = t.subrange(0, hi - 1);
        assert(xs.drop_last() =~= xi);
        assert(xs.last() == t[hi - 1]);
        lemma_members(t, k, hi - 1);
        let ksi = qkeys(gq(), xi);
        let agi = qrows(gq(), xi).map_values(|r: Row| myargs(r));
        if qual(t[hi - 1]) {
            assert(qrows(gq(), xs) == qrows(gq(), xi).push(t[hi - 1]));
            assert(ks =~= ksi.push(key_of(t[hi - 1])));
            assert(ags =~= agi.push(myargs(t[hi - 1])));
            assert(ks.drop_last() =~= ksi);
            assert(ags.drop_last() =~= agi);
            lemma_kpool_exact(t);
            assert(kpool(t)[hi - 1] == key_of(t[hi - 1]));
            assert(row_not_distinct(key_of(t[hi - 1]), k) <==> key_of(t[hi - 1]) == k);
        } else {
            assert(qrows(gq(), xs) == qrows(gq(), xi));
            assert(ks =~= ksi);
            assert(ags =~= agi);
        }
    } else {
        assert(ks =~= Seq::<Row>::empty());
    }
}

/// `gcount` of the toolkit is `cnt_r`.
pub proof fn lemma_gcount(t: Seq<Row>, k: Row, hi: int)
    requires 0 <= hi <= t.len(),
    ensures gcount(gq(), t.subrange(0, hi), k) == cnt_r(t, k, 0, hi),
    decreases hi,
{
    if hi > 0 {
        let xs = t.subrange(0, hi);
        assert(xs.drop_last() =~= t.subrange(0, hi - 1));
        assert(xs.last() == t[hi - 1]);
        lemma_gcount(t, k, hi - 1);
    }
}

/// Every value is text.
pub open spec fn all_text(d: Seq<Val>) -> bool {
    forall|i: int| 0 <= i < d.len() ==> (#[trigger] d[i]) is Text
}

/// Among text values, "not distinct" is membership.
pub proof fn lemma_hvnd(d: Seq<Val>, x: Val)
    requires all_text(d), x is Text,
    ensures has_val_not_distinct(d, x) == d.contains(x),
    decreases d.len(),
{
    if d.len() > 0 {
        let di = d.drop_last();
        assert forall|i: int| 0 <= i < di.len() implies (#[trigger] di[i]) is Text by {
            assert(di[i] == d[i]);
        }
        lemma_hvnd(di, x);
        assert(d[d.len() - 1] is Text);
        lemma_val_not_distinct_structural(d.last(), x);
        if di.contains(x) {
            let i = choose|i: int| 0 <= i < di.len() && di[i] == x;
            assert(d[i] == x);
        }
        if d.contains(x) && d.last() != x {
            let i = choose|i: int| 0 <= i < d.len() && d[i] == x;
            assert(i != d.len() - 1);
            assert(di[i] == x);
        }
    }
}

/// Facts about the members of group `k` among `t[0..hi)`: count, distinct adsh values, line sum.
pub proof fn lemma_mm(c: Cols, t: Seq<Row>, k: Row, hi: int)
    requires corr(c, t), 0 <= hi <= t.len(),
    ensures ({
        let m = mm(t, k, hi);
        let d = distinct_vals(column(m, 1));
        let v2 = column(m, 2);
        &&& m.len() == cnt_r(t, k, 0, hi)
        &&& column(m, 0).len() == m.len()
        &&& d.no_duplicates() && all_text(d)
        &&& forall|v: Val| d.contains(v) <==> aset_r(t, k, 0, hi).contains(v)
        &&& count_non_null(d) == d.len()
        &&& all_of_kind(NumKind::Int4, v2)
        &&& count_non_null(v2) == m.len()
        &&& int_sum(v2) == sum_r(t, k, 0, hi)
    }),
    decreases hi,
{
    if hi > 0 {
        lemma_mm(c, t, k, hi - 1);
        let m0 = mm(t, k, hi - 1);
        let d0 = distinct_vals(column(m0, 1));
        let r = t[hi - 1];
        assert(row_corr(c, r, hi - 1));
        if hit(r, k) {
            let a = myargs(r);
            let m = m0.push(a);
            assert(column(m, 0) =~= column(m0, 0).push(a[0]));
            assert(column(m, 1) =~= column(m0, 1).push(a[1]));
            assert(column(m, 2) =~= column(m0, 2).push(a[2]));
            assert(column(m, 1).drop_last() =~= column(m0, 1));
            assert(column(m, 2).drop_last() =~= column(m0, 2));
            let x = r[0];
            assert(x is Text);
            lemma_hvnd(d0, x);
            let d = distinct_vals(column(m, 1));
            if d0.contains(x) {
                assert(d == d0);
                assert(aset_r(t, k, 0, hi) == aset_r(t, k, 0, hi - 1).insert(x));
            } else {
                assert(d == d0.push(x));
                assert(d.no_duplicates()) by {
                    assert forall|i: int, j: int| 0 <= i < j < d.len() implies d[i] != d[j] by {
                        if j == d.len() - 1 {
                            assert(d[i] == d0[i]);
                        } else {
                            assert(d[i] == d0[i] && d[j] == d0[j]);
                        }
                    }
                }
                assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]) is Text by {
                    if i < d0.len() {
                        assert(d[i] == d0[i]);
                    }
                }
                assert forall|v: Val| d.contains(v) <==> aset_r(t, k, 0, hi).contains(v) by {
                    if d.contains(v) && v != x {
                        let i = choose|i: int| 0 <= i < d.len() && d[i] == v;
                        assert(d0[i] == v);
                    }
                    if d0.contains(v) {
                        let i = choose|i: int| 0 <= i < d0.len() && d0[i] == v;
                        assert(d[i] == v);
                    }
                    assert(d[d.len() - 1] == x);
                }
                assert(d.drop_last() =~= d0);
            }
        } else {
            assert(mm(t, k, hi) == m0);
        }
    }
}

/// The three aggregate values of a group with `cnt` rows (`0 < cnt <= int8_max`) whose AVG division is inside the
/// executable domain.
pub open spec fn agg_vals(t: Seq<Row>, k: Row, n: int) -> Row {
    let cnt = cnt_r(t, k, 0, n) as int;
    seq![Val::Int(cnt), Val::Int(aset_r(t, k, 0, n).len() as int), avg_of(sum_r(t, k, 0, n), 0, cnt as nat)]
}

pub proof fn lemma_agg_row(c: Cols, t: Seq<Row>, k: Row)
    requires
        corr(c, t),
        0 < cnt_r(t, k, 0, t.len() as int) <= int8_max(),
        num_div_fits(sum_r(t, k, 0, t.len() as int), 0, cnt_r(t, k, 0, t.len() as int) as int, 0),
    ensures
        agg_row(q_aggs(), mm(t, k, t.len() as int)) == Ok::<Row, SqlError>(agg_vals(t, k, t.len() as int)),
{
    let n = t.len() as int;
    let m = mm(t, k, n);
    let cnt = cnt_r(t, k, 0, n) as int;
    let sum = sum_r(t, k, 0, n);
    lemma_mm(c, t, k, n);
    lemma_aset_finite(t, k, 0, n);
    let d = distinct_vals(column(m, 1));
    let a = aset_r(t, k, 0, n);
    d.unique_seq_to_set();
    assert(d.to_set() =~= a);
    assert(d.len() == a.len());
    let aggs = q_aggs();
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(m, j)));
    assert(rs[0] == agg_value(Agg::CountStar, column(m, 0)));
    assert(rs[0] == Ok::<Val, SqlError>(Val::Int(cnt)));
    assert(rs[1] == agg_value(Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(0)))), column(m, 1)));
    assert(agg_value(Agg::Count(Expr::Col(0)), d) == int_result(IntKind::Int8, count_non_null(d) as int));
    assert(rs[1] == Ok::<Val, SqlError>(Val::Int(a.len() as int)));
    let v2 = column(m, 2);
    assert(rs[2] == avg_value(NumKind::Int4, v2));
    assert(avg_sum(NumKind::Int4, v2) == (sum, 0nat));
    lemma_avg_ok(sum, 0, cnt);
    assert(rs[2] == Ok::<Val, SqlError>(avg_of(sum, 0, cnt as nat)));
    lemma_collect3(rs, Val::Int(cnt), Val::Int(a.len() as int), avg_of(sum, 0, cnt as nat));
}

/// The output row of group `k`: key, COUNT(*), COUNT(DISTINCT adsh), AVG(line).
pub open spec fn full_row(t: Seq<Row>, k: Row) -> Row {
    k + agg_vals(t, k, t.len() as int)
}

/// A group key whose aggregates are inside their domains (count in int8, AVG division executable).
pub open spec fn group_fits(t: Seq<Row>, k: Row) -> bool {
    &&& cnt_r(t, k, 0, t.len() as int) <= int8_max()
    &&& num_div_fits(sum_r(t, k, 0, t.len() as int), 0, cnt_r(t, k, 0, t.len() as int) as int, 0)
}

/// The groups of the toolkit normal form: no duplicates, exactly the keys with rows.
pub proof fn lemma_groups_keys(t: Seq<Row>)
    requires keys_typed(t),
    ensures
        distinct_rows(qkeys(gq(), t)) == gkeys(gq(), t),
        gkeys(gq(), t).no_duplicates(),
        forall|k: Row| #[trigger] gkeys(gq(), t).contains(k) <==> cnt_r(t, k, 0, t.len() as int) > 0,
        forall|i: int| 0 <= i < gkeys(gq(), t).len() ==> kpool(t).contains(#[trigger] gkeys(gq(), t)[i]),
{
    lemma_kpool_exact(t);
    lemma_qkeys_in_pool(t, t.len() as int);
    assert(t.subrange(0, t.len() as int) =~= t);
    lemma_distinct_gkeys(gq(), t, kpool(t));
    lemma_gkeys(gq(), t);
    assert forall|k: Row| #[trigger] gkeys(gq(), t).contains(k) <==> cnt_r(t, k, 0, t.len() as int) > 0 by {
        lemma_gcount(t, k, t.len() as int);
    }
}

/// The denotation: one full row per group, in the toolkit's first-occurrence order, when every group fits.
pub proof fn lemma_denote(c: Cols, db: Database, t: Seq<Row>)
    requires
        corr(c, t), 3 < db.tables.len(), db.tables[3] == t,
        forall|k: Row| #[trigger] gkeys(gq(), t).contains(k) ==> group_fits(t, k),
    ensures
        denote_body(db, query_spec()) == Ok::<Relation, SqlError>(gkeys(gq(), t).map_values(|k: Row| full_row(t, k))),
{
    lemma_keys_typed(c, t);
    lemma_body(db, t);
    lemma_groups_keys(t);
    let n = t.len() as int;
    let ks = qkeys(gq(), t);
    let ags = qrows(gq(), t).map_values(|r: Row| myargs(r));
    let ds = gkeys(gq(), t);
    let grs = Seq::new(ds.len(), |g: int|
        match agg_row(q_aggs(), group_members(ks, ags, ds[g])) {
            Ok(a) => Ok(ds[g] + a),
            Err(e) => Err(e),
        });
    let full = ds.map_values(|k: Row| full_row(t, k));
    assert(t.subrange(0, n) =~= t);
    assert forall|g: int| 0 <= g < grs.len() implies #[trigger] grs[g] == Ok::<Row, SqlError>(full[g]) by {
        let k = ds[g];
        assert(ds.contains(k));
        assert(kpool(t).contains(k));
        lemma_members(t, k, n);
        assert(group_fits(t, k));
        lemma_agg_row(c, t, k);
    }
    lemma_collect_all(grs, full);
}

} // verus!
