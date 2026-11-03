//! The derived table `m` of the statement, `SELECT adsh, tag, MAX(value) FROM num WHERE uom = $1 AND value IS NOT
//! NULL GROUP BY adsh, tag`, in normal form: one row `[adsh, tag, Num(max, 4)]` per group key of the `uom = $1`
//! rows (first-occurrence order, `link::query::gkeys`), where `max` is the largest coefficient of the group.
//!
//! The link toolkit's accumulator normal form (`link::query::QuerySpec`) describes the WHERE condition, the key
//! and the argument; its SUM kind at scale 4 makes the argument row `[Num(coeff, 4)]`, which is the `value`
//! column itself. The MAX over a group's members is proved here (`lemma_members_max`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::equality::*;
use crate::spec::aggs::minmax::*;
use crate::bridge::equality::*;
use crate::bridge::collect::lemma_collect_all;
use crate::link::query::*;
use crate::link::expr::lemma_compare_num;
use crate::agent::spec::*;

verus! {

/// The coefficient of a numeric value (0 for other values).
pub open spec fn vcoeff(v: Val) -> int {
    match v {
        Val::Num { coeff, .. } => coeff,
        _ => 0,
    }
}

/// A `num` row as the group subquery sees it: 9 columns, adsh, tag and uom text, value `Num(_, 4)`.
pub open spec fn num_row_ok(x: Row) -> bool {
    &&& x.len() == 9
    &&& x[0] is Text
    &&& x[1] is Text
    &&& x[7] is Num
    &&& x[7]->Num_scale == 4
}

/// The normal form of the group subquery at `$1 = pv`.
pub open spec fn gq(pv: Seq<u8>) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| x[5] == Val::Text(pv),
        key: |x: Row| seq![x[0], x[1]],
        arg: |j: int, x: Row| vcoeff(x[7]),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 1, 2],
        grouped: true,
    }
}

/// The largest coefficient of group `k` (any value when the group is empty).
pub open spec fn gmaxc(pv: Seq<u8>, xs: Seq<Row>, k: Row) -> int
    decreases xs.len(),
{
    if xs.len() == 0 {
        0
    } else {
        let g = gq(pv);
        let prev = gmaxc(pv, xs.drop_last(), k);
        let x = xs.last();
        if hit(g, x, k) && (gcount(g, xs.drop_last(), k) == 0 || vcoeff(x[7]) > prev) { vcoeff(x[7]) } else { prev }
    }
}

/// The row of group `k`.
pub open spec fn group_row(pv: Seq<u8>, xs: Seq<Row>, k: Row) -> Row {
    k + seq![(Val::Num { coeff: gmaxc(pv, xs, k), scale: 4 })]
}

/// The rows of the group subquery.
pub open spec fn group_rows_nf(pv: Seq<u8>, xs: Seq<Row>) -> Seq<Row> {
    gkeys(gq(pv), xs).map_values(|k: Row| group_row(pv, xs, k))
}

/// The argument row of a well-formed `num` row is its value.
pub proof fn lemma_arg_vals(pv: Seq<u8>, x: Row)
    requires num_row_ok(x),
    ensures arg_vals(gq(pv), x) == seq![x[7]],
{
    assert(arg_vals(gq(pv), x) =~= seq![x[7]]);
}

/// MAX over the members of group `k`: NULL for an empty group, otherwise `Num(gmaxc, 4)`, the coefficient of a
/// member that no member exceeds.
pub proof fn lemma_members_max(pv: Seq<u8>, xs: Seq<Row>, k: Row)
    requires forall|i: int| 0 <= i < xs.len() ==> num_row_ok(#[trigger] xs[i]),
    ensures
        extremum(true, column(members(gq(pv), xs, k), 0)) == if gcount(gq(pv), xs, k) == 0 {
            Ok::<Val, SqlError>(Val::Null)
        } else {
            Ok::<Val, SqlError>(Val::Num { coeff: gmaxc(pv, xs, k), scale: 4 })
        },
        gcount(gq(pv), xs, k) > 0 ==> exists|j: int| 0 <= j < xs.len() && #[trigger] hit(gq(pv), xs[j], k)
            && vcoeff(xs[j][7]) == gmaxc(pv, xs, k),
        forall|j: int| 0 <= j < xs.len() && #[trigger] hit(gq(pv), xs[j], k) ==> vcoeff(xs[j][7]) <= gmaxc(pv, xs, k),
    decreases xs.len(),
{
    let g = gq(pv);
    if xs.len() > 0 {
        let d = xs.drop_last();
        let x = xs.last();
        assert forall|i: int| 0 <= i < d.len() implies num_row_ok(#[trigger] d[i]) by {
            assert(d[i] == xs[i]);
        }
        lemma_members_max(pv, d, k);
        assert(num_row_ok(xs[xs.len() - 1]));
        let md = members(g, d, k);
        let prev = gmaxc(pv, d, k);
        if hit(g, x, k) {
            lemma_arg_vals(pv, x);
            assert(members(g, xs, k) == md.push(arg_vals(g, x)));
            assert(column(md.push(seq![x[7]]), 0) =~= column(md, 0).push(x[7]));
            assert(column(md.push(seq![x[7]]), 0).drop_last() =~= column(md, 0));
            if gcount(g, d, k) > 0 {
                lemma_compare_num(vcoeff(x[7]), 4, prev, 4);
                assert(max_nat(4, 4) == 4);
                crate::link::expr::lemma_align_same(vcoeff(x[7]), 4);
                crate::link::expr::lemma_align_same(prev, 4);
                assert(x[7] == (Val::Num { coeff: vcoeff(x[7]), scale: 4 }));
            } else {
                assert(x[7] == (Val::Num { coeff: vcoeff(x[7]), scale: 4 }));
            }
            assert(xs[xs.len() - 1] == x);
            assert forall|j: int| 0 <= j < xs.len() && #[trigger] hit(g, xs[j], k) implies vcoeff(xs[j][7]) <= gmaxc(pv, xs, k) by {
                if j < d.len() {
                    assert(xs[j] == d[j]);
                    assert(hit(g, d[j], k));
                    lemma_gcount_pos(g, d, k, j);
                }
            }
            if gcount(g, d, k) > 0 && vcoeff(x[7]) <= prev {
                let j = choose|j: int| 0 <= j < d.len() && #[trigger] hit(g, d[j], k) && vcoeff(d[j][7]) == prev;
                assert(xs[j] == d[j]);
            }
        } else {
            assert(members(g, xs, k) == md);
            assert forall|j: int| 0 <= j < xs.len() && #[trigger] hit(g, xs[j], k) implies vcoeff(xs[j][7]) <= gmaxc(pv, xs, k) by {
                if j < d.len() {
                    assert(xs[j] == d[j]);
                }
            }
            if gcount(g, d, k) > 0 {
                let j = choose|j: int| 0 <= j < d.len() && #[trigger] hit(g, d[j], k) && vcoeff(d[j][7]) == prev;
                assert(xs[j] == d[j]);
            }
        }
    } else {
        assert(column(members(g, xs, k), 0) =~= Seq::<Val>::empty());
    }
}

/// A row of the group counts toward it.
pub proof fn lemma_gcount_pos(g: QuerySpec, xs: Seq<Row>, k: Row, i: int)
    requires 0 <= i < xs.len(), hit(g, xs[i], k),
    ensures gcount(g, xs, k) > 0,
    decreases xs.len(),
{
    if i < xs.len() - 1 {
        assert(xs.drop_last()[i] == xs[i]);
        lemma_gcount_pos(g, xs.drop_last(), k, i);
    }
}

/// Keys of `num` rows are exact: SQL "not distinct" on them is equality (both columns are text).
pub proof fn lemma_keys_exact(pv: Seq<u8>, xs: Seq<Row>)
    requires forall|i: int| 0 <= i < xs.len() ==> num_row_ok(#[trigger] xs[i]),
    ensures keys_exact(gq(pv), xs),
{
    let g = gq(pv);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert(num_row_ok(xs[a]) && num_row_ok(xs[b]));
        assert forall|i: int| 0 <= i < ka.len() implies same_exact_type(#[trigger] ka[i], kb[i]) by {
            if i == 0 {} else {}
        }
        lemma_row_exact(ka, kb);
    }
}

/// The GROUP BY of the qualifying rows' (key, argument) sequences: one `group_row` per group key.
pub proof fn lemma_groups_max(pv: Seq<u8>, aggs: Seq<Agg>, xs: Seq<Row>)
    requires
        aggs == seq![Agg::Max(Expr::Col(7))],
        forall|i: int| 0 <= i < xs.len() ==> num_row_ok(#[trigger] xs[i]),
    ensures
        group_rows(aggs, qkeys(gq(pv), xs), qrows(gq(pv), xs).map_values(|x: Row| arg_vals(gq(pv), x)))
            == Ok::<Seq<Row>, SqlError>(group_rows_nf(pv, xs)),
{
    let g = gq(pv);
    let ks = qkeys(g, xs);
    let avs = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let pool = key_pool(g, xs);
    lemma_keys_exact(pv, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    lemma_gkeys(g, xs);
    let grs = Seq::new(ds.len(), |gi: int|
        match agg_row(aggs, group_members(ks, avs, ds[gi])) {
            Ok(a) => Ok(ds[gi] + a),
            Err(e) => Err(e),
        });
    let full = ds.map_values(|k: Row| group_row(pv, xs, k));
    assert forall|gi: int| 0 <= gi < grs.len() implies #[trigger] grs[gi] == Ok::<Row, SqlError>(full[gi]) by {
        let k = ds[gi];
        assert(pool.contains(k));
        lemma_group_members(g, xs, k, pool);
        assert(ds.contains(k));
        assert(gcount(g, xs, k) > 0);
        lemma_members_max(pv, xs, k);
        let ms = members(g, xs, k);
        let v = (Val::Num { coeff: gmaxc(pv, xs, k), scale: 4 });
        let vals = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(ms, j)));
        assert(vals =~= seq![Ok::<Val, SqlError>(v)]);
        lemma_collect_all(vals, seq![v]);
        assert(agg_row(aggs, ms) == Ok::<Row, SqlError>(seq![v]));
    }
    lemma_collect_all(grs, full);
}

/// The group subquery over `num` rows `xs` (9 columns each) evaluates to its normal form.
pub proof fn lemma_group_query_max(db: Database, xs: Seq<Row>, input: Query, keys: Seq<Expr>, aggs: Seq<Agg>, pv: Seq<u8>)
    requires
        forall|i: int| 0 <= i < xs.len() ==> num_row_ok(#[trigger] xs[i]),
        keys == seq![Expr::Col(0), Expr::Col(1)],
        aggs == seq![Agg::Max(Expr::Col(7))],
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(keep_true(xs, qual_truths(gq(pv), proj_all(xs, id_cols())))),
    ensures
        eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) })
            == Ok::<Relation, SqlError>(group_rows_nf(pv, xs)),
{
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let g = gq(pv);
    let cols = id_cols();
    lemma_proj_identity(xs);
    lemma_keys_agree(db, xs, keys, pv);
    lemma_args_agree(db, xs, aggs, pv);
    let kept = keep_true(xs, qual_truths(g, xs));
    lemma_kept_rows(g, xs, cols);
    lemma_prepared(db, xs, kept, cols, keys, aggs, g);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), arg_vals(g, proj(kept[i], cols))));
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, xs));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= qrows(g, xs).map_values(|x: Row| arg_vals(g, x)));
    lemma_groups_max(pv, aggs, xs);
    lemma_groupby_unfold(db, input, keys, aggs, kept, prep);
}

/// The keys `[Col 0, Col 1]` agree with the normal form's key on every row.
pub proof fn lemma_keys_agree(db: Database, xs: Seq<Row>, keys: Seq<Expr>, pv: Seq<u8>)
    requires
        forall|i: int| 0 <= i < xs.len() ==> num_row_ok(#[trigger] xs[i]),
        keys == seq![Expr::Col(0), Expr::Col(1)],
    ensures keys_agree(db, xs, id_cols(), keys, gq(pv)),
{
    let g = gq(pv);
    let cols = id_cols();
    lemma_proj_identity(xs);
    assert(keys =~= col_exprs(seq![0nat, 1]));
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(proj(#[trigger] xs[i], cols)) implies
        eval_exprs(db, xs[i], keys) == Ok::<Row, SqlError>((g.key)(proj(xs[i], cols))) by {
        assert(num_row_ok(xs[i]));
        assert(proj(xs[i], cols) == xs[i]);
        lemma_eval_cols(db, xs[i], seq![0nat, 1]);
        assert(select(xs[i], seq![0nat, 1]) =~= seq![xs[i][0], xs[i][1]]);
    }
}

/// The aggregate `[MAX(Col 7)]` has the normal form's argument row on every row.
pub proof fn lemma_args_agree(db: Database, xs: Seq<Row>, aggs: Seq<Agg>, pv: Seq<u8>)
    requires
        forall|i: int| 0 <= i < xs.len() ==> num_row_ok(#[trigger] xs[i]),
        aggs == seq![Agg::Max(Expr::Col(7))],
    ensures args_agree(db, xs, id_cols(), aggs, gq(pv)),
{
    let g = gq(pv);
    let cols = id_cols();
    lemma_proj_identity(xs);
    assert forall|i: int| 0 <= i < xs.len() && (g.qual)(proj(#[trigger] xs[i], cols)) implies
        agg_args(db, xs[i], aggs) == Ok::<Row, SqlError>(arg_vals(g, proj(xs[i], cols))) by {
        assert(num_row_ok(xs[i]));
        assert(proj(xs[i], cols) == xs[i]);
        lemma_arg_vals(pv, xs[i]);
        let rs = agg_arg_results(db, xs[i], aggs);
        assert(rs =~= seq![Ok::<Val, SqlError>(xs[i][7])]);
        lemma_collect_all(rs, seq![xs[i][7]]);
    }
}

/// The identity column list of a `num` row.
pub open spec fn id_cols() -> Seq<nat> {
    seq![0nat, 1, 2, 3, 4, 5, 6, 7, 8]
}

/// Projecting 9-column rows on all columns in order is the identity.
pub proof fn lemma_proj_identity(xs: Seq<Row>)
    requires forall|i: int| 0 <= i < xs.len() ==> (#[trigger] xs[i]).len() == 9,
    ensures
        proj_all(xs, id_cols()) == xs,
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] proj(xs[i], id_cols()) == xs[i],
{
    assert forall|i: int| 0 <= i < xs.len() implies #[trigger] proj(xs[i], id_cols()) == xs[i] by {
        assert(xs[i].len() == 9);
        assert(proj(xs[i], id_cols()) =~= xs[i]);
    }
    assert(proj_all(xs, id_cols()) =~= xs);
}

} // verus!
