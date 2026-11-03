//! `GROUP BY o_year` over the derived table, with `SUM(CASE WHEN nation = $1 THEN volume ELSE 0 END)` and
//! `SUM(volume)`.
//!
//! Every derived row `z` (shape `[year, volume, name]`, `bag::zrow_shape`) has the key `[z[0]]` and the argument row
//! `zargs(z) = [case, volume]`, where `case` is the volume (scale 4) when the name is `$1` and the numeric `0`
//! of scale 0 otherwise (`lemma_group_input`). The keys are exact (one numeric scale), so the groups are the
//! distinct keys in first-occurrence order (`dkeys`, the normal form's `gkeys` with every row qualifying) and each
//! group's members are the argument rows of its rows (`mem`, `lemma_members`). Over the members:
//! - the volume column sums to `s_all` at scale 4, with absolute mass `a_all`;
//! - the case column sums to `s_then`, at scale 4 when some row counts for `$1` and at scale 0 otherwise, with
//!   absolute mass `a_then` (`lemma_mem_cols`); the six sums are `bag::zsums`.
//! Inside the SUM capacity (`a_all <= i128::MAX`) the group's row is `key ++ [sum0, sum1]` (`lemma_group_value`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::text::lex_cmp;
use crate::exec::relational::domain::*;
use crate::query::param_domain;
use crate::link::join::sum_of;
use crate::link::query::{QuerySpec, AggKind, gkeys, gcount, qkeys, qrows, key_pool, lemma_gkeys, lemma_distinct_gkeys,
    lemma_pool_exact, lemma_row_exact, keys_exact};
use crate::link::expr::{ival, i128_max};
use crate::bridge::equality::{lemma_lex_cmp_zero, same_exact_type};
use crate::bridge::collect::lemma_collect_all;
use crate::agent::line::*;
use crate::agent::ast::*;
use crate::agent::pred::{lemma_eval_col, lemma_expr_list1, lemma_cmp_text};
use crate::agent::bag::*;

verus! {

// ------------------------------------------------------------------------------------------------ per-row input

/// The CASE value of a derived row.
pub open spec fn case_val(ps: Seq<Literal>, z: Row) -> Val {
    if zthen(ps, z) { z[1] } else { Val::Num { coeff: 0, scale: 0 } }
}

/// The aggregate arguments of a derived row.
pub open spec fn zargs(ps: Seq<Literal>, z: Row) -> Row { seq![case_val(ps, z), z[1]] }

/// One evaluation step of `CASE WHEN cond THEN a ELSE b END` (lazy: only the taken branch).
proof fn lemma_eval_if(db: Database, r: Row, cond: Pred, a: Expr, b: Expr, x: bool)
    requires eval_pred(db, r, cond) == Ok::<Truth, SqlError>(truth_of(x)),
    ensures
        eval_expr(db, r, Expr::If { cond: Box::new(cond), then_e: Box::new(a), else_e: Box::new(b) })
            == if x { eval_expr(db, r, a) } else { eval_expr(db, r, b) },
{
}

/// `CAST(0 AS numeric)`.
proof fn lemma_num_zero(db: Database, r: Row)
    ensures eval_expr(db, r, num_zero()) == Ok::<Val, SqlError>(Val::Num { coeff: 0, scale: 0 }),
{
    assert(lit_val(Literal::Int { v: 0, kind: IntKind::Int4 }) == Ok::<Val, SqlError>(Val::Int(0)));
    assert(eval_expr(db, r, Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 })) == Ok::<Val, SqlError>(Val::Int(0)));
}

/// `$1` is a text literal.
pub open spec fn nat_lit(ps: Seq<Literal>) -> bool { ps.len() == 3 && ps[0] == Literal::Text(nat_of(ps)) }

/// `nation = $1` on a derived row.
proof fn lemma_case_cond(db: Database, ps: Seq<Literal>, z: Row)
    requires nat_lit(ps), zrow_shape(z),
    ensures
        eval_pred(db, z, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(2), b: Expr::Lit(ps[0]) })
            == Ok::<Truth, SqlError>(truth_of(zthen(ps, z))),
{
    let name = z[2]->Text_0;
    lemma_eval_col(db, z, 2);
    assert(eval_expr(db, z, Expr::Lit(ps[0])) == Ok::<Val, SqlError>(Val::Text(nat_of(ps))));
    crate::agent::pred::lemma_eval_cmp(db, z, CmpOp::Eq, Expr::Col(2), Expr::Lit(ps[0]), Val::Text(name), Val::Text(nat_of(ps)));
    lemma_cmp_text(name, nat_of(ps));
}

/// The CASE expression on a derived row.
pub proof fn lemma_case(db: Database, ps: Seq<Literal>, z: Row)
    requires nat_lit(ps), zrow_shape(z),
    ensures eval_expr(db, z, case_expr(ps)) == Ok::<Val, SqlError>(case_val(ps, z)),
{
    let cond = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(2), b: Expr::Lit(ps[0]) };
    lemma_case_cond(db, ps, z);
    lemma_eval_if(db, z, cond, Expr::Col(1), num_zero(), zthen(ps, z));
    lemma_eval_col(db, z, 1);
    lemma_num_zero(db, z);
}


proof fn lemma_args_len(db: Database, ps: Seq<Literal>, z: Row)
    requires nat_lit(ps), zrow_shape(z),
    ensures agg_arg_results(db, z, group_aggs(ps)).len() == 2,
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    lemma_agg_arg_results_index(db, z, group_aggs(ps));
}

proof fn lemma_arg1(db: Database, ps: Seq<Literal>, z: Row)
    requires nat_lit(ps), zrow_shape(z),
    ensures agg_arg_results(db, z, group_aggs(ps))[1] == Ok::<Val, SqlError>(z[1]),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    lemma_eval_col(db, z, 1);
    let aggs = group_aggs(ps);
    assert(aggs[1] == Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(1) });
    crate::link::query::lemma_agg_arg_sum(db, z, NumKind::Numeric, Expr::Col(1));
    lemma_agg_arg_results_index(db, z, aggs);
}

proof fn lemma_arg0(db: Database, ps: Seq<Literal>, z: Row)
    requires nat_lit(ps), zrow_shape(z),
    ensures agg_arg_results(db, z, group_aggs(ps))[0] == Ok::<Val, SqlError>(case_val(ps, z)),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    lemma_case(db, ps, z);
    let aggs = group_aggs(ps);
    assert(aggs[0] == Agg::Sum { kind: NumKind::Numeric, arg: case_expr(ps) });
    crate::link::query::lemma_agg_arg_sum(db, z, NumKind::Numeric, case_expr(ps));
    lemma_agg_arg_results_index(db, z, aggs);
}

/// The argument results of a derived row collect to its argument row.
proof fn lemma_zargs_collect(db: Database, ps: Seq<Literal>, z: Row)
    requires nat_lit(ps), zrow_shape(z),
    ensures collect(agg_arg_results(db, z, group_aggs(ps))) == Ok::<Row, SqlError>(zargs(ps, z)),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    lemma_args_len(db, ps, z);
    lemma_arg0(db, ps, z);
    lemma_arg1(db, ps, z);
    let rs = agg_arg_results(db, z, group_aggs(ps));
    let vs = zargs(ps, z);
    assert(vs.len() == 2 && vs[0] == case_val(ps, z) && vs[1] == z[1]);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else { assert(i == 1); }
    }
    lemma_collect_all(rs, vs);
}

/// The two aggregate arguments of a derived row.
proof fn lemma_zargs(db: Database, ps: Seq<Literal>, z: Row)
    requires nat_lit(ps), zrow_shape(z),
    ensures agg_args(db, z, group_aggs(ps)) == Ok::<Row, SqlError>(zargs(ps, z)),
{
    lemma_zargs_collect(db, ps, z);
    crate::exec::relational::domain::lemma_agg_args(db, z, group_aggs(ps));
}

/// The GROUP BY input of a derived row: its key and its two arguments.
pub proof fn lemma_group_input(db: Database, ps: Seq<Literal>, z: Row)
    requires param_domain(ps), zrow_shape(z),
    ensures group_input(db, z, group_keys(), group_aggs(ps)) == Ok::<(Row, Row), SqlError>((zkey(z), zargs(ps, z))),
{
    lemma_eval_col(db, z, 0);
    lemma_expr_list1(db, z, Expr::Col(0), z[0]);
    assert(group_keys() == seq![Expr::Col(0)]);
    assert(nat_lit(ps));
    lemma_zargs(db, ps, z);
}

/// The keys and argument rows of the derived rows.
pub open spec fn zks(zs: Seq<Row>) -> Seq<Row> { zs.map_values(|z: Row| zkey(z)) }
pub open spec fn zas(ps: Seq<Literal>, zs: Seq<Row>) -> Seq<Row> { zs.map_values(|z: Row| zargs(ps, z)) }

/// Every row has the derived shape.
pub open spec fn all_shape(zs: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < zs.len() ==> zrow_shape(#[trigger] zs[i])
}

// ------------------------------------------------------------------------------------------------ groups

/// The grouping as a normal form: every row qualifies, the key is `[z[0]]`.
pub open spec fn gspec() -> QuerySpec {
    QuerySpec {
        qual: |z: Row| true,
        key: |z: Row| zkey(z),
        arg: |j: int, z: Row| 0int,
        aggs: Seq::empty(),
        outs: Seq::empty(),
        grouped: true,
    }
}

/// The distinct keys in first-occurrence order.
pub open spec fn dkeys(zs: Seq<Row>) -> Seq<Row> { gkeys(gspec(), zs) }

proof fn lemma_qrows_all(zs: Seq<Row>)
    ensures qrows(gspec(), zs) == zs, qkeys(gspec(), zs) == zks(zs),
    decreases zs.len(),
{
    if zs.len() > 0 {
        lemma_qrows_all(zs.drop_last());
        assert(zs.drop_last().push(zs.last()) =~= zs);
    } else {
        assert(qrows(gspec(), zs) =~= zs);
    }
    assert(qkeys(gspec(), zs) =~= zks(zs));
}

/// Keys of derived rows are exact (one numeric scale).
proof fn lemma_keys_exact(zs: Seq<Row>)
    requires all_shape(zs),
    ensures keys_exact(gspec(), zs),
{
    let g = gspec();
    assert forall|a: int, b: int| 0 <= a < zs.len() && 0 <= b < zs.len() && (g.qual)(zs[a]) && (g.qual)(zs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(zs[a]), #[trigger] (g.key)(zs[b])) <==> (g.key)(zs[a]) == (g.key)(zs[b])) by {
        assert(zrow_shape(zs[a]) && zrow_shape(zs[b]));
        let (ka, kb) = (zkey(zs[a]), zkey(zs[b]));
        assert forall|t: int| 0 <= t < ka.len() implies same_exact_type(#[trigger] ka[t], kb[t]) by {}
        lemma_row_exact(ka, kb);
    }
}

/// The GROUP BY's groups are `dkeys`, duplicate-free, holding exactly the keys of the rows.
pub proof fn lemma_dkeys(zs: Seq<Row>)
    requires all_shape(zs),
    ensures
        distinct_rows(zks(zs)) == dkeys(zs),
        dkeys(zs).no_duplicates(),
        forall|k: Row| #[trigger] dkeys(zs).contains(k) <==> gcount(gspec(), zs, k) > 0,
        forall|i: int| 0 <= i < dkeys(zs).len() ==> zks(zs).contains(#[trigger] dkeys(zs)[i]),
{
    let g = gspec();
    lemma_qrows_all(zs);
    lemma_keys_exact(zs);
    lemma_pool_exact(g, zs);
    let pool = key_pool(g, zs);
    assert forall|i: int| 0 <= i < qkeys(g, zs).len() implies pool.contains(#[trigger] qkeys(g, zs)[i]) by {
        assert(pool[i] == qkeys(g, zs)[i]);
    }
    lemma_distinct_gkeys(g, zs, pool);
    lemma_gkeys(g, zs);
}

/// A key `k` of the rows is a year key.
pub proof fn lemma_key_shape(zs: Seq<Row>, k: Row)
    requires all_shape(zs), zks(zs).contains(k),
    ensures k.len() == 1, k[0] is Num, k[0]->Num_scale == 0, k == ykey(k[0]->Num_coeff),
        k[0]->Num_coeff == 1995 || k[0]->Num_coeff == 1996,
{
    let i = choose|i: int| 0 <= i < zks(zs).len() && zks(zs)[i] == k;
    assert(zrow_shape(zs[i]));
    assert(k =~= ykey(k[0]->Num_coeff));
}

// ------------------------------------------------------------------------------------------------ members

/// The argument rows of the rows with key `k`, in order.
pub open spec fn mem(ps: Seq<Literal>, zs: Seq<Row>, k: Row) -> Seq<Row>
    decreases zs.len(),
{
    if zs.len() == 0 {
        Seq::empty()
    } else if zkey(zs.last()) == k {
        mem(ps, zs.drop_last(), k).push(zargs(ps, zs.last()))
    } else {
        mem(ps, zs.drop_last(), k)
    }
}

/// The GROUP BY members of a group of year key `k` are `mem`.
pub proof fn lemma_members(ps: Seq<Literal>, zs: Seq<Row>, k: Row)
    requires all_shape(zs), k.len() == 1, k[0] is Num, k[0]->Num_scale == 0,
    ensures group_members(zks(zs), zas(ps, zs), k) == mem(ps, zs, k),
    decreases zs.len(),
{
    if zs.len() > 0 {
        let zi = zs.drop_last();
        let z = zs.last();
        assert(all_shape(zi)) by {
            assert forall|i: int| 0 <= i < zi.len() implies zrow_shape(#[trigger] zi[i]) by { assert(zi[i] == zs[i]); }
        }
        lemma_members(ps, zi, k);
        assert(zks(zs).drop_last() =~= zks(zi));
        assert(zas(ps, zs).drop_last() =~= zas(ps, zi));
        assert(zks(zs).last() == zkey(z));
        assert(zas(ps, zs).last() == zargs(ps, z));
        assert(zrow_shape(zs[zs.len() - 1]));
        let kz = zkey(z);
        assert forall|t: int| 0 <= t < kz.len() implies same_exact_type(#[trigger] kz[t], k[t]) by {}
        lemma_row_exact(kz, k);
    } else {
        assert(zks(zs) =~= Seq::<Row>::empty());
    }
}

/// The member columns: counts, kinds, exact sums at their scales, and absolute masses.
pub proof fn lemma_mem_cols(ps: Seq<Literal>, zs: Seq<Row>, k: Row)
    requires all_shape(zs),
    ensures ({
        let m = mem(ps, zs, k);
        let t = zsums(ps, zs, k);
        let c0 = column(m, 0);
        let c1 = column(m, 1);
        let s0: nat = if t.n_then > 0 { 4 } else { 0 };
        let s1: nat = if t.cnt > 0 { 4 } else { 0 };
        &&& c0.len() == t.cnt && c1.len() == t.cnt
        &&& count_non_null(c0) == t.cnt && count_non_null(c1) == t.cnt
        &&& all_of_kind(NumKind::Numeric, c0) && all_of_kind(NumKind::Numeric, c1)
        &&& num_sum(c0) == (t.s_then, s0)
        &&& num_sum(c1) == (t.s_all, s1)
        &&& num_max_scale(c0) == s0 && num_max_scale(c1) == s1
        &&& num_mass_at(c0, 4) == t.a_then
        &&& num_mass_at(c1, 4) == t.a_all
        &&& t.n_then == 0 ==> num_mass_at(c0, 0) == 0
    }),
    decreases zs.len(),
{
    let m = mem(ps, zs, k);
    lemma_zsums_zero(ps, zs, k);
    if zs.len() > 0 {
        let zi = zs.drop_last();
        let z = zs.last();
        assert(all_shape(zi)) by {
            assert forall|i: int| 0 <= i < zi.len() implies zrow_shape(#[trigger] zi[i]) by { assert(zi[i] == zs[i]); }
        }
        assert(zrow_shape(zs[zs.len() - 1]));
        lemma_mem_cols(ps, zi, k);
        lemma_zsums_zero(ps, zi, k);
        let mi = mem(ps, zi, k);
        let ti = zsums(ps, zi, k);
        let v = ival(z[1]);
        assert(pow10(0) == 1);
        if zkey(z) == k {
            let a = zargs(ps, z);
            assert(m == mi.push(a));
            assert(column(m, 0) =~= column(mi, 0).push(a[0]));
            assert(column(m, 1) =~= column(mi, 1).push(a[1]));
            assert(column(m, 0).drop_last() =~= column(mi, 0));
            assert(column(m, 1).drop_last() =~= column(mi, 1));
            let si0: nat = if ti.n_then > 0 { 4 } else { 0 };
            let si1: nat = if ti.cnt > 0 { 4 } else { 0 };
            // the volume column: every value is at scale 4; an empty prefix sums to (0, 0)
            assert(a[1] == (Val::Num { coeff: v, scale: 4 }));
            assert(align(ti.s_all, si1, 4) == ti.s_all) by {
                if ti.cnt > 0 { assert((4 - si1) as nat == 0nat); }
            }
            assert(align(v, 4, 4) == v) by { assert((4 - 4) as nat == 0nat); }
            if zthen(ps, z) {
                assert(a[0] == (Val::Num { coeff: v, scale: 4 }));
                assert(align(ti.s_then, si0, 4) == ti.s_then) by {
                    if ti.n_then > 0 { assert((4 - si0) as nat == 0nat); }
                }
            } else {
                assert(a[0] == (Val::Num { coeff: 0, scale: 0 }));
                assert(align(ti.s_then, si0, si0) == ti.s_then) by { assert((si0 - si0) as nat == 0nat); }
                assert(align(0, 0, si0) == 0);
                assert(max_nat(si0, 0) == si0);
                assert(abs(0) * pow10((4 - 0) as nat) == 0);
                assert(abs(0) * pow10((0 - 0) as nat) == 0);
            }
        } else {
            assert(m == mi);
        }
    } else {
        assert(column(m, 0) =~= Seq::<Val>::empty());
        assert(column(m, 1) =~= Seq::<Val>::empty());
    }
}

/// Without counted rows the sums are zero.
proof fn lemma_zsums_zero(ps: Seq<Literal>, zs: Seq<Row>, k: Row)
    ensures
        zsums(ps, zs, k).cnt == 0 ==> zsums(ps, zs, k).s_all == 0 && zsums(ps, zs, k).a_all == 0 && zsums(ps, zs, k).n_then == 0,
        zsums(ps, zs, k).n_then == 0 ==> zsums(ps, zs, k).s_then == 0 && zsums(ps, zs, k).a_then == 0,
        zsums(ps, zs, k).cnt >= 0, zsums(ps, zs, k).n_then >= 0, zsums(ps, zs, k).a_all >= 0, zsums(ps, zs, k).a_then >= 0,
        zsums(ps, zs, k).n_then <= zsums(ps, zs, k).cnt,
        zsums(ps, zs, k).a_then <= zsums(ps, zs, k).a_all,
        -zsums(ps, zs, k).a_all <= zsums(ps, zs, k).s_all <= zsums(ps, zs, k).a_all,
        -zsums(ps, zs, k).a_then <= zsums(ps, zs, k).s_then <= zsums(ps, zs, k).a_then,
    decreases zs.len(),
{
    if zs.len() > 0 {
        lemma_zsums_zero(ps, zs.drop_last(), k);
    }
}

} // verus!
