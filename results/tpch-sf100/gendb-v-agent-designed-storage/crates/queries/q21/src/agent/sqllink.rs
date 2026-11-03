//! The relational link of Q21: the FROM product `supplier x lineitem x orders x nation` of a well-formed database,
//! projected on the eleven columns the statement reads (`q21_cols`), is the product of the four projected tables
//! (`lemma_xs_product`); the WHERE condition and the group key agree with the accumulator normal form `q21_g`
//! (`lemma_pred_agrees`, `lemma_keys_args_agree`), and a group's count factors per supplier row
//! (`lemma_gcount_factor`): the nation rows the supplier joins (`ncnt`) times the supplier's counted lines, each
//! weighted by its orders rows with status `F` (`lsum`, `ocnt`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::product_rows;
use crate::spec::equality::row_not_distinct;
use crate::link::query::*;
use crate::link::join::{sum_of, shift, lemma_sum_of_ext, lemma_proj_product, lemma_acc_sum_of, count_term};
use crate::link::expr::{ival, tval};
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::bridge::equality::same_exact_type;
use super::common::prod4::*;
use super::common::sums::lemma_sum_scale;
use super::sqlrow::*;
use super::typed::*;

verus! {

// ------------------------------------------------------------------------------------------------ the FROM rows

/// Positions read in the joined row: supplier 0, 1, 3 | lineitem 7, 9, 18, 19 | orders 23, 25 | nation 32, 33.
pub open spec fn q21_cols() -> Seq<nat> {
    seq![0nat, 1, 3, 7, 9, 18, 19, 23, 25, 32, 33]
}

pub open spec fn scols() -> Seq<nat> { seq![0nat, 1, 3] }
pub open spec fn lcols() -> Seq<nat> { seq![0nat, 2, 11, 12] }
pub open spec fn ocols() -> Seq<nat> { seq![0nat, 2] }
pub open spec fn ncols() -> Seq<nat> { seq![0nat, 1] }

pub open spec fn from_rows(db: Database) -> Seq<Row> {
    product_rows(product_rows(product_rows(db.tables[5], db.tables[0]), db.tables[1]), db.tables[6])
}

/// The projected tables: supplier `[s_suppkey, s_name, s_nationkey]`, lineitem `[l_orderkey, l_suppkey,
/// l_commitdate, l_receiptdate]`, orders `[o_orderkey, o_orderstatus]`, nation `[n_nationkey, n_name]`.
pub open spec fn srel(db: Database) -> Seq<Row> { proj_all(db.tables[5], scols()) }
pub open spec fn lrel(db: Database) -> Seq<Row> { proj_all(db.tables[0], lcols()) }
pub open spec fn orel(db: Database) -> Seq<Row> { proj_all(db.tables[1], ocols()) }
pub open spec fn nrel(db: Database) -> Seq<Row> { proj_all(db.tables[6], ncols()) }

/// The projected FROM rows.
pub open spec fn q21_xs(db: Database) -> Seq<Row> {
    proj_all(from_rows(db), q21_cols())
}

pub proof fn lemma_from_eval(db: Database)
    requires db.tables.len() == 8,
    ensures eval_query(db, Seq::empty(), q21_from()) == Ok::<Relation, SqlError>(from_rows(db)),
{
    let e = Seq::<Val>::empty();
    let t5 = Query::Table(5);
    let t0 = Query::Table(0);
    let t1 = Query::Table(1);
    let t6 = Query::Table(6);
    assert(eval_query(db, e, t5) == Ok::<Relation, SqlError>(db.tables[5]));
    assert(eval_query(db, e, t0) == Ok::<Relation, SqlError>(db.tables[0]));
    assert(eval_query(db, e, t1) == Ok::<Relation, SqlError>(db.tables[1]));
    assert(eval_query(db, e, t6) == Ok::<Relation, SqlError>(db.tables[6]));
    let p50 = Query::Product { left: Box::new(t5), right: Box::new(t0) };
    assert(eval_query(db, e, p50) == Ok::<Relation, SqlError>(product_rows(db.tables[5], db.tables[0])));
    let p501 = Query::Product { left: Box::new(p50), right: Box::new(t1) };
    assert(eval_query(db, e, p501) == Ok::<Relation, SqlError>(product_rows(product_rows(db.tables[5], db.tables[0]), db.tables[1])));
    assert(q21_from() == Query::Product { left: Box::new(p501), right: Box::new(t6) });
}

/// The projected FROM rows are the product of the projected tables.
pub proof fn lemma_xs_product(db: Database)
    requires tables_typed(db),
    ensures q21_xs(db) == product_rows(product_rows(product_rows(srel(db), lrel(db)), orel(db)), nrel(db)),
{
    let (t5, t0, t1, t6) = (db.tables[5], db.tables[0], db.tables[1], db.tables[6]);
    assert forall|i: int| 0 <= i < t5.len() implies (#[trigger] t5[i]).len() == 7 by { assert(srow_typed(t5[i])); }
    assert forall|i: int| 0 <= i < t0.len() implies (#[trigger] t0[i]).len() == 16 by { assert(lrow_typed(t0[i])); }
    assert forall|i: int| 0 <= i < t1.len() implies (#[trigger] t1[i]).len() == 9 by { assert(orow_typed(t1[i])); }
    assert forall|i: int| 0 <= i < t6.len() implies (#[trigger] t6[i]).len() == 4 by { assert(nrow_typed(t6[i])); }
    // supplier x lineitem
    let ca1 = scols() + shift(lcols(), 7);
    lemma_proj_product(t5, t0, scols(), lcols(), 7, 16);
    let a1 = product_rows(t5, t0);
    lemma_product_rows_elems(t5, t0);
    assert forall|i: int| 0 <= i < a1.len() implies (#[trigger] a1[i]).len() == 23 by {
        assert(is_concat(a1[i], t5, t0));
        let (x, y) = choose|x: int, y: int| 0 <= x < t5.len() && 0 <= y < t0.len() && a1[i] == #[trigger] t5[x] + #[trigger] t0[y];
    }
    assert forall|k: int| 0 <= k < ca1.len() implies #[trigger] ca1[k] < 23 by {}
    // x orders
    let ca2 = ca1 + shift(ocols(), 23);
    lemma_proj_product(a1, t1, ca1, ocols(), 23, 9);
    let a2 = product_rows(a1, t1);
    lemma_product_rows_elems(a1, t1);
    assert forall|i: int| 0 <= i < a2.len() implies (#[trigger] a2[i]).len() == 32 by {
        assert(is_concat(a2[i], a1, t1));
        let (x, y) = choose|x: int, y: int| 0 <= x < a1.len() && 0 <= y < t1.len() && a2[i] == #[trigger] a1[x] + #[trigger] t1[y];
    }
    assert forall|k: int| 0 <= k < ca2.len() implies #[trigger] ca2[k] < 32 by {}
    // x nation
    lemma_proj_product(a2, t6, ca2, ncols(), 32, 4);
    assert(ca2 + shift(ncols(), 32) =~= q21_cols());
}

/// A FROM row: one row of each table; its read columns are typed.
pub proof fn lemma_from_row(db: Database, i: int)
    requires
        tables_typed(db),
        0 <= i < from_rows(db).len(),
    ensures
        env_typed(from_rows(db)[i]),
{
    let (t5, t0, t1, t6) = (db.tables[5], db.tables[0], db.tables[1], db.tables[6]);
    let a1 = product_rows(t5, t0);
    let a2 = product_rows(a1, t1);
    lemma_product_rows_elems(a2, t6);
    let env = from_rows(db)[i];
    assert(is_concat(env, a2, t6));
    let (a2i, n) = choose|x: int, y: int| 0 <= x < a2.len() && 0 <= y < t6.len() && env == #[trigger] a2[x] + #[trigger] t6[y];
    lemma_product_rows_elems(a1, t1);
    assert(is_concat(a2[a2i], a1, t1));
    let (a1i, o) = choose|x: int, y: int| 0 <= x < a1.len() && 0 <= y < t1.len() && a2[a2i] == #[trigger] a1[x] + #[trigger] t1[y];
    lemma_product_rows_elems(t5, t0);
    assert(is_concat(a1[a1i], t5, t0));
    let (s, l) = choose|x: int, y: int| 0 <= x < t5.len() && 0 <= y < t0.len() && a1[a1i] == #[trigger] t5[x] + #[trigger] t0[y];
    let (rs, rl, ro, rn) = (t5[s], t0[l], t1[o], t6[n]);
    assert(srow_typed(rs) && lrow_typed(rl) && orow_typed(ro) && nrow_typed(rn));
    assert(env == rs + rl + ro + rn);
    assert(env.len() == 36);
    assert(env[0] == rs[0] && env[1] == rs[1] && env[3] == rs[3]);
    assert(env[7] == rl[0] && env[9] == rl[2] && env[18] == rl[11] && env[19] == rl[12]);
    assert(env[23] == ro[0] && env[25] == ro[2]);
    assert(env[32] == rn[0] && env[33] == rn[1]);
}

// ------------------------------------------------------------------------------------------------ the normal form

/// WHERE over the projected row `[sk, sname, snk | lk, ls, lc, lr | ok, ost | nk, nn]` (two-valued).
pub open spec fn q21_qual(db: Database, nm: Seq<u8>) -> spec_fn(Row) -> bool {
    |x: Row| ival(x[0]) == ival(x[4]) && ival(x[7]) == ival(x[3]) && tval(x[8]) == f_text() && ival(x[6]) > ival(x[5])
        && ex2_db(db, ival(x[3]), ival(x[4])) && !ex3_db(db, ival(x[3]), ival(x[4])) && ival(x[2]) == ival(x[9])
        && tval(x[10]) == nm
}

/// GROUP BY s_name over the projected row.
pub open spec fn q21_key() -> spec_fn(Row) -> Row {
    |x: Row| seq![x[1]]
}

/// Q21 in the accumulator normal form of `link::query`: one COUNT(*), the output `[s_name, COUNT]`.
pub open spec fn q21_g(db: Database, nm: Seq<u8>) -> QuerySpec {
    QuerySpec {
        qual: q21_qual(db, nm),
        key: q21_key(),
        arg: |j: int, x: Row| 0int,
        aggs: seq![AggKind::Count],
        outs: seq![0nat, 1],
        grouped: true,
    }
}

/// On a FROM row the normal form reads the row's columns.
pub proof fn lemma_qual_env(db: Database, nm: Seq<u8>, env: Row)
    requires env.len() == 36,
    ensures
        (q21_g(db, nm).qual)(proj(env, q21_cols())) == qual_env(db, nm, env),
        (q21_g(db, nm).key)(proj(env, q21_cols())) == seq![env[1]],
{
    let x = proj(env, q21_cols());
    assert(x[0] == env[0] && x[1] == env[1] && x[2] == env[3] && x[3] == env[7] && x[4] == env[9]);
    assert(x[5] == env[18] && x[6] == env[19] && x[7] == env[23] && x[8] == env[25] && x[9] == env[32] && x[10] == env[33]);
    assert((q21_g(db, nm).key)(x) =~= seq![env[1]]);
}

/// The WHERE of the statement agrees with the normal form on every FROM row.
pub proof fn lemma_pred_agrees(db: Database, ps: Seq<Literal>, nm: Seq<u8>)
    requires
        tables_typed(db),
        ps.len() >= 1,
        ps[0] == Literal::Text(nm),
    ensures pred_agrees(db, from_rows(db), q21_cols(), q21_pred(ps), q21_g(db, nm)),
{
    let rows = from_rows(db);
    assert(lines_typed(db));
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], q21_pred(ps)) == Ok::<Truth, SqlError>(truth_of((q21_g(db, nm).qual)(proj(rows[i], q21_cols())))) by {
        lemma_from_row(db, i);
        lemma_pred_eval(db, rows[i], ps, nm);
        lemma_qual_env(db, nm, rows[i]);
    }
}

/// The group key and the COUNT(*) argument agree with the normal form on every FROM row.
pub proof fn lemma_keys_args_agree(db: Database, nm: Seq<u8>)
    requires tables_typed(db),
    ensures
        keys_agree(db, from_rows(db), q21_cols(), q21_gkeys(), q21_g(db, nm)),
        args_agree(db, from_rows(db), q21_cols(), q21_aggs(), q21_g(db, nm)),
        aggs_match(q21_aggs(), q21_g(db, nm)),
{
    let g = q21_g(db, nm);
    let rows = from_rows(db);
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], q21_cols())) implies
        eval_exprs(db, rows[i], q21_gkeys()) == Ok::<Row, SqlError>((g.key)(proj(rows[i], q21_cols()))) by {
        lemma_from_row(db, i);
        lemma_qual_env(db, nm, rows[i]);
        lemma_eval_cols(db, rows[i], seq![1nat]);
        assert(col_exprs(seq![1nat]) =~= q21_gkeys());
        assert(select(rows[i], seq![1nat]) =~= seq![rows[i][1]]);
    }
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], q21_cols())) implies
        agg_args(db, rows[i], q21_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], q21_cols()))) by {
        let rs = agg_arg_results(db, rows[i], q21_aggs());
        lemma_agg_arg_results_index(db, rows[i], q21_aggs());
        lemma_agg_arg_count(db, rows[i]);
        crate::bridge::collect::lemma_collect_all(rs, seq![Val::Null]);
        assert(arg_vals(g, proj(rows[i], q21_cols())) =~= seq![Val::Null]);
    }
    assert(agg_matches(q21_aggs()[0], g.aggs[0]));
}

/// The group keys (s_name, a text) are exact: not distinct means equal.
pub proof fn lemma_keys_exact(db: Database, nm: Seq<u8>)
    requires tables_typed(db),
    ensures keys_exact(q21_g(db, nm), q21_xs(db)),
{
    let g = q21_g(db, nm);
    let rows = from_rows(db);
    let xs = q21_xs(db);
    crate::link::source::lemma_proj_all_index(rows, q21_cols());
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        lemma_from_row(db, a);
        lemma_from_row(db, b);
        lemma_qual_env(db, nm, rows[a]);
        lemma_qual_env(db, nm, rows[b]);
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert(ka == seq![rows[a][1]] && kb == seq![rows[b][1]]);
        assert(env_typed(rows[a]) && env_typed(rows[b]));
        assert(same_exact_type(ka[0], kb[0]));
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {}
        lemma_row_exact(ka, kb);
    }
}

// ------------------------------------------------------------------------------------------------ the group count

/// Nation row `n` joins supplier row `s` and has the name `nm`.
pub open spec fn cn(nm: Seq<u8>, s: Row, n: Row) -> int {
    if ival(s[2]) == ival(n[0]) && tval(n[1]) == nm { 1 } else { 0 }
}

/// Orders row `o` is line `l`'s order, with status `F`.
pub open spec fn co(l: Row, o: Row) -> int {
    if ival(o[0]) == ival(l[0]) && tval(o[1]) == f_text() { 1 } else { 0 }
}

/// Line `l` is supplier row `s`'s, late, passes both subqueries, and `s`'s name group is `k`.
pub open spec fn csl(db: Database, k: Row, s: Row, l: Row) -> int {
    if ival(s[0]) == ival(l[1]) && ival(l[3]) > ival(l[2]) && ex2_db(db, ival(l[0]), ival(l[1]))
        && !ex3_db(db, ival(l[0]), ival(l[1])) && seq![s[1]] == k { 1 } else { 0 }
}

/// The nation rows joining supplier row `s` with name `nm`.
pub open spec fn ncnt(db: Database, nm: Seq<u8>, s: Row) -> int {
    sum_of(nrel(db), |n: Row| cn(nm, s, n))
}

/// The orders rows with status `F` of line `l`.
pub open spec fn ocnt(db: Database, l: Row) -> int {
    sum_of(orel(db), |o: Row| co(l, o))
}

/// Supplier row `s`'s lines counted for group `k`, each weighted by its `F` orders rows.
pub open spec fn lsum(db: Database, k: Row, s: Row) -> int {
    sum_of(lrel(db), |l: Row| csl(db, k, s, l) * ocnt(db, l))
}

/// On a joined row the count term is the product of the three factors.
proof fn lemma_term(db: Database, nm: Seq<u8>, k: Row, s: Row, l: Row, o: Row, n: Row)
    requires s.len() == 3, l.len() == 4, o.len() == 2, n.len() == 2,
    ensures count_term(q21_g(db, nm), k)(s + l + o + n) == csl(db, k, s, l) * co(l, o) * cn(nm, s, n),
{
    let x = s + l + o + n;
    assert(x[0] == s[0] && x[1] == s[1] && x[2] == s[2]);
    assert(x[3] == l[0] && x[4] == l[1] && x[5] == l[2] && x[6] == l[3]);
    assert(x[7] == o[0] && x[8] == o[1] && x[9] == n[0] && x[10] == n[1]);
    assert((q21_g(db, nm).key)(x) =~= seq![s[1]]);
    let (a, b, c) = (csl(db, k, s, l), co(l, o), cn(nm, s, n));
    if a == 1 && b == 1 && c == 1 {
        assert(a * b * c == 1);
    } else {
        assert(a * b * c == 0) by (nonlinear_arith) requires a == 0 || b == 0 || c == 0;
    }
}

/// Widths of the projected tables' rows.
proof fn lemma_rel_widths(db: Database)
    ensures
        forall|i: int| 0 <= i < srel(db).len() ==> (#[trigger] srel(db)[i]).len() == 3,
        forall|i: int| 0 <= i < lrel(db).len() ==> (#[trigger] lrel(db)[i]).len() == 4,
        forall|i: int| 0 <= i < orel(db).len() ==> (#[trigger] orel(db)[i]).len() == 2,
        forall|i: int| 0 <= i < nrel(db).len() ==> (#[trigger] nrel(db)[i]).len() == 2,
{
    crate::link::source::lemma_proj_all_index(db.tables[5], scols());
    crate::link::source::lemma_proj_all_index(db.tables[0], lcols());
    crate::link::source::lemma_proj_all_index(db.tables[1], ocols());
    crate::link::source::lemma_proj_all_index(db.tables[6], ncols());
}

/// A group's count is the sum over supplier rows of their nation rows times their counted lines.
pub proof fn lemma_gcount_factor(db: Database, nm: Seq<u8>, k: Row)
    requires tables_typed(db),
    ensures gcount(q21_g(db, nm), q21_xs(db), k) == sum_of(srel(db), |s: Row| ncnt(db, nm, s) * lsum(db, k, s)),
{
    let g = q21_g(db, nm);
    let ct = count_term(g, k);
    let (sr, lr, or, nr) = (srel(db), lrel(db), orel(db), nrel(db));
    lemma_xs_product(db);
    lemma_acc_sum_of(g, q21_xs(db), k, 0);
    lemma_sum_prod4(sr, lr, or, nr, ct);
    lemma_rel_widths(db);
    assert forall|i: int| 0 <= i < sr.len() implies #[trigger] s_bcd(lr, or, nr, ct, sr[i]) == ncnt(db, nm, sr[i]) * lsum(db, k, sr[i]) by {
        let s = sr[i];
        let nc = ncnt(db, nm, s);
        assert forall|j: int| 0 <= j < lr.len() implies #[trigger] s_cd(or, nr, ct, s + lr[j])
            == nc * (csl(db, k, s, lr[j]) * ocnt(db, lr[j])) by {
            let l = lr[j];
            let a = csl(db, k, s, l);
            assert forall|q: int| 0 <= q < or.len() implies #[trigger] s_d(nr, ct, s + l + or[q]) == (a * nc) * co(l, or[q]) by {
                let o = or[q];
                let b = co(l, o);
                assert forall|m: int| 0 <= m < nr.len() implies (|w: Row| ct(s + l + o + w))(#[trigger] nr[m])
                    == (|w: Row| (a * b) * (|n: Row| cn(nm, s, n))(w))(nr[m]) by {
                    lemma_term(db, nm, k, s, l, o, nr[m]);
                }
                lemma_sum_of_ext(nr, |w: Row| ct(s + l + o + w), |w: Row| (a * b) * (|n: Row| cn(nm, s, n))(w));
                lemma_sum_scale(nr, a * b, |n: Row| cn(nm, s, n));
                assert((a * b) * nc == (a * nc) * b) by (nonlinear_arith);
            }
            lemma_sum_of_ext(or, |z: Row| s_d(nr, ct, s + l + z), |z: Row| (a * nc) * (|o: Row| co(l, o))(z));
            lemma_sum_scale(or, a * nc, |o: Row| co(l, o));
            assert((a * nc) * ocnt(db, l) == nc * (a * ocnt(db, l))) by (nonlinear_arith);
        }
        lemma_sum_of_ext(lr, |y: Row| s_cd(or, nr, ct, s + y), |y: Row| nc * (|l: Row| csl(db, k, s, l) * ocnt(db, l))(y));
        lemma_sum_scale(lr, nc, |l: Row| csl(db, k, s, l) * ocnt(db, l));
    }
    lemma_sum_of_ext(sr, |x: Row| s_bcd(lr, or, nr, ct, x), |s: Row| ncnt(db, nm, s) * lsum(db, k, s));
}

} // verus!
