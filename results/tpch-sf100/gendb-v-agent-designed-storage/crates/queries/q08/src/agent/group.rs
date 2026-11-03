//! SQL meaning of TPC-H Q8, part 2: `GROUP BY o_year` over the inner rows and the outer SELECT.
//!
//! An inner row is `[o_year (numeric scale 0), volume (numeric scale 4), nation (text)]` (`irow_ok`). Its group key
//! is `[o_year]` (`gkey`); its aggregate arguments are `[CASE WHEN nation = $1 THEN volume ELSE 0 END, volume]`
//! (`gargs`): the CASE value is the volume (scale 4) or the integer literal 0 cast to numeric (scale 0). So the
//! SUM of the CASE values has scale 4 when some row of the group has nation `$1`, else it is `0` at scale 0.
//!
//! Over a sequence of inner rows `zs` the accumulators of group `k` are `gcnt` (rows), `gsum1` (volume
//! coefficients), `hcnt` and `gsum0` (rows and volumes with nation `$1`). `lemma_groupby` evaluates the GROUP BY
//! node: one row `k ++ [SUM(CASE), SUM(volume)]` per distinct key in first-occurrence order, when every sum is
//! inside PostgreSQL's numeric format.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::link::expr::*;
use crate::bridge::collect::lemma_collect_all;
use super::sql::*;

verus! {

/// The group key of an inner row.
pub open spec fn gkey(z: Row) -> Row {
    seq![z[0]]
}

/// The CASE value of an inner row (nation `b0`).
pub open spec fn case_val(b0: Seq<u8>, z: Row) -> Val {
    if z[2] == Val::Text(b0) { z[1] } else { Val::Num { coeff: 0, scale: 0 } }
}

/// The aggregate arguments of an inner row.
pub open spec fn gargs(b0: Seq<u8>, z: Row) -> Row {
    seq![case_val(b0, z), z[1]]
}

/// The keys of the inner rows.
pub open spec fn gkeys(zs: Seq<Row>) -> Seq<Row> {
    zs.map_values(|z: Row| gkey(z))
}

/// The aggregate arguments of the inner rows.
pub open spec fn gargs_all(b0: Seq<u8>, zs: Seq<Row>) -> Seq<Row> {
    zs.map_values(|z: Row| gargs(b0, z))
}

/// An inner row's value kinds.
pub open spec fn irow_ok(z: Row) -> bool {
    &&& z.len() == 3
    &&& z[0] is Num && z[0]->Num_scale == 0
    &&& z[1] is Num && z[1]->Num_scale == 4
    &&& z[2] is Text
}

/// Group key of year `y`.
pub open spec fn ykey(y: int) -> Row {
    seq![Val::Num { coeff: y, scale: 0 }]
}

/// A key of the year form.
pub open spec fn is_ykey(k: Row) -> bool {
    k.len() == 1 && k[0] is Num && k[0]->Num_scale == 0
}

// ------------------------------------------------------------------------------------------------ accumulators

/// Rows of group `k`.
pub open spec fn gcnt(zs: Seq<Row>, k: Row) -> nat
    decreases zs.len(),
{
    if zs.len() == 0 { 0 } else { gcnt(zs.drop_last(), k) + if gkey(zs.last()) == k { 1nat } else { 0nat } }
}

/// Volume coefficients of group `k`.
pub open spec fn gsum1(zs: Seq<Row>, k: Row) -> int
    decreases zs.len(),
{
    if zs.len() == 0 { 0 } else { gsum1(zs.drop_last(), k) + if gkey(zs.last()) == k { ival(zs.last()[1]) } else { 0 } }
}

/// Rows of group `k` with nation `b0`.
pub open spec fn hcnt(b0: Seq<u8>, zs: Seq<Row>, k: Row) -> nat
    decreases zs.len(),
{
    if zs.len() == 0 {
        0
    } else {
        hcnt(b0, zs.drop_last(), k) + if gkey(zs.last()) == k && zs.last()[2] == Val::Text(b0) { 1nat } else { 0nat }
    }
}

/// Volume coefficients of group `k` with nation `b0`.
pub open spec fn gsum0(b0: Seq<u8>, zs: Seq<Row>, k: Row) -> int
    decreases zs.len(),
{
    if zs.len() == 0 {
        0
    } else {
        gsum0(b0, zs.drop_last(), k) + if gkey(zs.last()) == k && zs.last()[2] == Val::Text(b0) { ival(zs.last()[1]) } else { 0 }
    }
}

/// Absolute volume coefficients of group `k` (the SUM capacity mass).
pub open spec fn gmass(zs: Seq<Row>, k: Row) -> int
    decreases zs.len(),
{
    if zs.len() == 0 { 0 } else { gmass(zs.drop_last(), k) + if gkey(zs.last()) == k { abs(ival(zs.last()[1])) } else { 0 } }
}

/// The SUM(volume) mass of group `k` (largest scale 4) is `gmass`.
pub proof fn lemma_members_mass(b0: Seq<u8>, zs: Seq<Row>, k: Row)
    requires keys_ykeys(zs), is_ykey(k),
    ensures ({
        let m = group_members(gkeys(zs), gargs_all(b0, zs), k);
        &&& crate::exec::relational::domain::num_max_scale(column(m, 1)) == if gcnt(zs, k) > 0 { 4nat } else { 0nat }
        &&& crate::exec::relational::domain::num_mass_at(column(m, 1), 4) == gmass(zs, k)
        &&& gmass(zs, k) >= 0
    }),
    decreases zs.len(),
{
    let ks = gkeys(zs);
    let gs = gargs_all(b0, zs);
    let m = group_members(ks, gs, k);
    if zs.len() > 0 {
        let zi = zs.drop_last();
        let z = zs.last();
        assert forall|i: int| 0 <= i < zi.len() implies irow_ok(#[trigger] zi[i]) by {
            assert(zi[i] == zs[i]);
        }
        lemma_members_mass(b0, zi, k);
        let ki = gkeys(zi);
        let gi = gargs_all(b0, zi);
        assert(ks.drop_last() =~= ki);
        assert(gs.drop_last() =~= gi);
        let mi = group_members(ki, gi, k);
        assert(irow_ok(zs[zs.len() - 1]));
        lemma_ykey_exact(gkey(z), k);
        let c = ival(z[1]);
        assert(z[1] == Val::Num { coeff: c, scale: 4 });
        assert(pow10(0) == 1);
        if gkey(z) == k {
            assert(m == mi.push(gargs(b0, z)));
            let v1i = column(mi, 1);
            assert(column(m, 1) =~= v1i.push(z[1]));
            assert(column(m, 1).drop_last() =~= v1i);
            assert(abs(c) * pow10(0) == abs(c));
        } else {
            assert(m == mi);
        }
    } else {
        assert(ks =~= Seq::<Row>::empty());
        assert(m =~= Seq::<Row>::empty());
        assert(column(m, 1) =~= Seq::<Val>::empty());
    }
}

/// The scale of SUM(CASE ..) of group `k`.
pub open spec fn sc0(b0: Seq<u8>, zs: Seq<Row>, k: Row) -> nat {
    if hcnt(b0, zs, k) > 0 { 4 } else { 0 }
}

// ------------------------------------------------------------------------------------------------ keys

/// Year keys are exact: not distinct means equal.
pub proof fn lemma_ykey_exact(a: Row, b: Row)
    requires is_ykey(a), is_ykey(b),
    ensures row_not_distinct(a, b) <==> a == b,
{
    crate::link::query::lemma_row_exact(a, b);
}

/// Every key of the inner rows is a year key.
pub open spec fn keys_ykeys(zs: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < zs.len() ==> irow_ok(#[trigger] zs[i])
}

/// The distinct keys of the inner rows: no duplicate, exactly the keys that occur.
pub proof fn lemma_distinct_keys(zs: Seq<Row>)
    requires keys_ykeys(zs),
    ensures
        distinct_rows(gkeys(zs)).no_duplicates(),
        forall|k: Row| #[trigger] distinct_rows(gkeys(zs)).contains(k) <==> gcnt(zs, k) > 0,
        forall|i: int| 0 <= i < distinct_rows(gkeys(zs)).len()
            ==> is_ykey(#[trigger] distinct_rows(gkeys(zs))[i]),
    decreases zs.len(),
{
    let ks = gkeys(zs);
    let d = distinct_rows(ks);
    if zs.len() > 0 {
        let zi = zs.drop_last();
        let z = zs.last();
        assert forall|i: int| 0 <= i < zi.len() implies irow_ok(#[trigger] zi[i]) by {
            assert(zi[i] == zs[i]);
        }
        lemma_distinct_keys(zi);
        let ki = gkeys(zi);
        assert(ks.drop_last() =~= ki);
        assert(ks.last() == gkey(z));
        let di = distinct_rows(ki);
        assert(irow_ok(zs[zs.len() - 1]));
        let pool = di.push(gkey(z));
        assert forall|a: Row, b: Row| pool.contains(a) && pool.contains(b) implies (#[trigger] row_not_distinct(a, b) <==> a == b) by {
            let ia = choose|i: int| 0 <= i < pool.len() && pool[i] == a;
            let ib = choose|i: int| 0 <= i < pool.len() && pool[i] == b;
            if ia < di.len() {
                assert(is_ykey(di[ia]));
            }
            if ib < di.len() {
                assert(is_ykey(di[ib]));
            }
            lemma_ykey_exact(a, b);
        }
        assert forall|i: int| 0 <= i < di.len() implies pool.contains(#[trigger] di[i]) by {
            assert(pool[i] == di[i]);
        }
        assert(pool[di.len() as int] == gkey(z));
        crate::link::query::lemma_has_nd_contains(di, gkey(z), pool);
        if di.contains(gkey(z)) {
            assert(d == di);
            assert forall|k: Row| #[trigger] d.contains(k) <==> gcnt(zs, k) > 0 by {
                if k == gkey(z) {
                    assert(gcnt(zi, k) > 0);
                }
            }
        } else {
            assert(d == di.push(gkey(z)));
            assert forall|k: Row| #[trigger] d.contains(k) <==> gcnt(zs, k) > 0 by {
                if d.contains(k) {
                    let i = choose|i: int| 0 <= i < d.len() && d[i] == k;
                    if i < di.len() {
                        assert(di.contains(k));
                    }
                }
                if gcnt(zs, k) > 0 && k != gkey(z) {
                    assert(di.contains(k));
                    let i = choose|i: int| 0 <= i < di.len() && di[i] == k;
                    assert(d[i] == k);
                }
                if k == gkey(z) {
                    assert(d[di.len() as int] == k);
                }
            }
            assert(d.no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < d.len() && 0 <= j < d.len() && i != j implies d[i] != d[j] by {
                    if i < di.len() && j < di.len() {
                        assert(d[i] == di[i] && d[j] == di[j]);
                    } else if i < di.len() {
                        assert(d[i] == di[i]);
                        assert(di.contains(d[i]));
                    } else {
                        assert(d[j] == di[j]);
                        assert(di.contains(d[j]));
                    }
                }
            }
            assert forall|i: int| 0 <= i < d.len() implies is_ykey(#[trigger] d[i]) by {
                if i < di.len() {
                    assert(d[i] == di[i]);
                }
            }
        }
    } else {
        assert(ks =~= Seq::<Row>::empty());
        assert(d =~= Seq::<Row>::empty());
    }
}

// ------------------------------------------------------------------------------------------------ members

/// The members of group `k` (a year key): their argument columns, counts and exact sums.
pub proof fn lemma_members(b0: Seq<u8>, zs: Seq<Row>, k: Row)
    requires keys_ykeys(zs), is_ykey(k),
    ensures ({
        let m = group_members(gkeys(zs), gargs_all(b0, zs), k);
        let v0 = column(m, 0);
        let v1 = column(m, 1);
        &&& all_of_kind(NumKind::Numeric, v0) && all_of_kind(NumKind::Numeric, v1)
        &&& count_non_null(v0) == gcnt(zs, k) && count_non_null(v1) == gcnt(zs, k)
        &&& num_sum(v1) == (gsum1(zs, k), if gcnt(zs, k) > 0 { 4nat } else { 0nat })
        &&& num_sum(v0) == (gsum0(b0, zs, k), sc0(b0, zs, k))
        &&& gcnt(zs, k) == 0 ==> gsum1(zs, k) == 0
        &&& hcnt(b0, zs, k) == 0 ==> gsum0(b0, zs, k) == 0
    }),
    decreases zs.len(),
{
    let ks = gkeys(zs);
    let gs = gargs_all(b0, zs);
    let m = group_members(ks, gs, k);
    if zs.len() > 0 {
        let zi = zs.drop_last();
        let z = zs.last();
        assert forall|i: int| 0 <= i < zi.len() implies irow_ok(#[trigger] zi[i]) by {
            assert(zi[i] == zs[i]);
        }
        lemma_members(b0, zi, k);
        let ki = gkeys(zi);
        let gi = gargs_all(b0, zi);
        assert(ks.drop_last() =~= ki);
        assert(gs.drop_last() =~= gi);
        assert(ks.last() == gkey(z));
        assert(gs.last() == gargs(b0, z));
        let mi = group_members(ki, gi, k);
        assert(irow_ok(zs[zs.len() - 1]));
        lemma_ykey_exact(gkey(z), k);
        let (s1, s0) = (gsum1(zi, k), gsum0(b0, zi, k));
        let c = ival(z[1]);
        assert(z[1] == Val::Num { coeff: c, scale: 4 });
        assert(pow10(0) == 1);
        assert(pow10(4) == 10000) by (compute_only);
        if gkey(z) == k {
            assert(m == mi.push(gargs(b0, z)));
            let (v0i, v1i) = (column(mi, 0), column(mi, 1));
            assert(column(m, 0) =~= v0i.push(case_val(b0, z)));
            assert(column(m, 1) =~= v1i.push(z[1]));
            assert(column(m, 0).drop_last() =~= v0i);
            assert(column(m, 1).drop_last() =~= v1i);
            // SUM(volume): the running sum is (s1, 4), or (0, 0) before the first member.
            assert(align(s1, if gcnt(zi, k) > 0 { 4nat } else { 0nat }, 4) == s1) by {
                if gcnt(zi, k) == 0 {
                    assert(s1 == 0);
                    assert(align(0, 0, 4) == 0 * pow10(4));
                } else {
                    crate::link::expr::lemma_align_same(s1, 4);
                }
            }
            crate::link::expr::lemma_align_same(c, 4);
            if z[2] == Val::Text(b0) {
                assert(case_val(b0, z) == z[1]);
                assert(align(s0, sc0(b0, zi, k), 4) == s0) by {
                    if hcnt(b0, zi, k) == 0 {
                        assert(s0 == 0);
                        assert(align(0, 0, 4) == 0 * pow10(4));
                    } else {
                        crate::link::expr::lemma_align_same(s0, 4);
                    }
                }
            } else {
                assert(case_val(b0, z) == Val::Num { coeff: 0, scale: 0 });
                let sc = sc0(b0, zi, k);
                assert(max_nat(sc, 0) == sc);
                crate::link::expr::lemma_align_same(s0, sc);
                assert(align(0, 0, sc) == 0 * pow10(sc as nat));
            }
        } else {
            assert(m == mi);
        }
    } else {
        assert(ks =~= Seq::<Row>::empty());
        assert(m =~= Seq::<Row>::empty());
        assert(column(m, 0) =~= Seq::<Val>::empty());
        assert(column(m, 1) =~= Seq::<Val>::empty());
    }
}

// ------------------------------------------------------------------------------------------------ per-row inputs

/// One unfolding step: CASE.
pub proof fn lemma_expr_if(db: Database, env: Row, cond: Pred, t: Expr, e: Expr)
    ensures
        eval_expr(db, env, Expr::If { cond: Box::new(cond), then_e: Box::new(t), else_e: Box::new(e) })
            == match eval_pred(db, env, cond) {
                Err(err) => Err(err),
                Ok(Truth::True) => eval_expr(db, env, t),
                Ok(_) => eval_expr(db, env, e),
            },
{
}

/// The CASE value on an inner row.
pub proof fn lemma_case(db: Database, ps: Seq<Literal>, z: Row)
    requires param_domain_ok(ps), irow_ok(z),
    ensures eval_expr(db, z, case_e(ps)) == Ok::<Val, SqlError>(case_val(txt(ps[0]), z)),
{
    hide(eval_expr);
    hide(eval_pred);
    let b0 = txt(ps[0]);
    let zero = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 })) };
    lemma_ctext_row(db, z, 2, ps[0]);
    lemma_expr_col(db, z, 1);
    lemma_cast_int_lit(db, z, 0);
    lemma_expr_if(db, z, clit(CmpOp::Eq, 2, ps[0]), Expr::Col(1), zero);
}

/// The parameter facts the GROUP BY needs (`$1` is a text literal).
pub open spec fn param_domain_ok(ps: Seq<Literal>) -> bool {
    ps.len() == 3 && ps[0] is Text
}

/// The GROUP BY input of an inner row: its key and its two aggregate arguments.
pub proof fn lemma_group_input(db: Database, ps: Seq<Literal>, z: Row)
    requires param_domain_ok(ps), irow_ok(z),
    ensures
        group_input(db, z, group_keys(), group_aggs(ps)) == Ok::<(Row, Row), SqlError>((gkey(z), gargs(txt(ps[0]), z))),
{
    hide(eval_expr);
    hide(eval_exprs);
    hide(eval_pred);
    hide(agg_args);
    hide(agg_arg);
    lemma_expr_col(db, z, 0);
    lemma_exprs1(db, z, Expr::Col(0), z[0]);
    lemma_case(db, ps, z);
    lemma_expr_col(db, z, 1);
    let a0 = Agg::Sum { kind: NumKind::Numeric, arg: case_e(ps) };
    let a1 = Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(1) };
    crate::link::query::lemma_agg_arg_sum(db, z, NumKind::Numeric, case_e(ps));
    crate::link::query::lemma_agg_arg_sum(db, z, NumKind::Numeric, Expr::Col(1));
    lemma_agg_args2(db, z, a0, a1, case_val(txt(ps[0]), z), z[1]);
    assert(group_aggs(ps) == seq![a0, a1]);
}

/// Two aggregate arguments, each evaluated.
pub proof fn lemma_agg_args2(db: Database, env: Row, a0: Agg, a1: Agg, v0: Val, v1: Val)
    requires
        agg_arg(db, env, a0) == Ok::<Val, SqlError>(v0),
        agg_arg(db, env, a1) == Ok::<Val, SqlError>(v1),
    ensures agg_args(db, env, seq![a0, a1]) == Ok::<Row, SqlError>(seq![v0, v1]),
{
    hide(agg_arg);
    hide(agg_args);
    let aggs = seq![a0, a1];
    crate::exec::relational::domain::lemma_agg_args(db, env, aggs);
    crate::spec::eval::lemma_agg_arg_results_index(db, env, aggs);
    let rs = agg_arg_results(db, env, aggs);
    assert(rs[0] == agg_arg(db, env, a0));
    assert(rs[1] == agg_arg(db, env, a1));
    lemma_collect_all(rs, seq![v0, v1]);
}

// ------------------------------------------------------------------------------------------------ the GROUP BY node

/// SUM(CASE ..) of group `k`.
pub open spec fn agg0_val(b0: Seq<u8>, zs: Seq<Row>, k: Row) -> Val {
    Val::Num { coeff: gsum0(b0, zs, k), scale: sc0(b0, zs, k) }
}

/// SUM(volume) of group `k`.
pub open spec fn agg1_val(zs: Seq<Row>, k: Row) -> Val {
    Val::Num { coeff: gsum1(zs, k), scale: 4 }
}

/// The GROUP BY row of group `k`.
pub open spec fn grow(b0: Seq<u8>, zs: Seq<Row>, k: Row) -> Row {
    k + seq![agg0_val(b0, zs, k), agg1_val(zs, k)]
}

/// Both sums of every group are inside PostgreSQL's numeric format.
pub open spec fn sums_in_range(b0: Seq<u8>, zs: Seq<Row>) -> bool {
    forall|k: Row| #[trigger] gcnt(zs, k) > 0 ==> num_in_range(gsum0(b0, zs, k), sc0(b0, zs, k)) && num_in_range(gsum1(zs, k), 4)
}

/// The aggregate row of group `k`.
pub proof fn lemma_agg_row_k(ps: Seq<Literal>, zs: Seq<Row>, k: Row)
    requires param_domain_ok(ps), keys_ykeys(zs), is_ykey(k), gcnt(zs, k) > 0, sums_in_range(txt(ps[0]), zs),
    ensures
        agg_row(group_aggs(ps), group_members(gkeys(zs), gargs_all(txt(ps[0]), zs), k))
            == Ok::<Row, SqlError>(seq![agg0_val(txt(ps[0]), zs, k), agg1_val(zs, k)]),
{
    let b0 = txt(ps[0]);
    let aggs = group_aggs(ps);
    let m = group_members(gkeys(zs), gargs_all(b0, zs), k);
    lemma_members(b0, zs, k);
    crate::exec::relational::domain::lemma_agg_row(aggs, m);
    let rs = crate::exec::relational::domain::agg_value_results(aggs, m);
    assert(rs[0] == agg_value(aggs[0], column(m, 0)));
    assert(rs[1] == agg_value(aggs[1], column(m, 1)));
    assert(rs[0] == Ok::<Val, SqlError>(agg0_val(b0, zs, k)));
    assert(rs[1] == Ok::<Val, SqlError>(agg1_val(zs, k)));
    lemma_collect_all(rs, seq![agg0_val(b0, zs, k), agg1_val(zs, k)]);
}

/// The GROUP BY node over inner rows `zs`: one row per distinct key, first-occurrence order.
pub proof fn lemma_groupby(db: Database, ps: Seq<Literal>, input: Query, zs: Seq<Row>)
    requires
        param_domain_ok(ps),
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(zs),
        keys_ykeys(zs),
        sums_in_range(txt(ps[0]), zs),
    ensures
        eval_query(db, Seq::empty(), Query::GroupBy { keys: group_keys(), aggs: group_aggs(ps), input: Box::new(input) })
            == Ok::<Relation, SqlError>(distinct_rows(gkeys(zs)).map_values(|k: Row| grow(txt(ps[0]), zs, k))),
{
    hide(eval_query);
    hide(group_input);
    hide(agg_row);
    let b0 = txt(ps[0]);
    let ctx = Seq::<Val>::empty();
    let (keys, aggs) = (group_keys(), group_aggs(ps));
    let (ks, gs) = (gkeys(zs), gargs_all(b0, zs));
    crate::exec::relational::domain::lemma_eval_group_by(db, ctx, keys, aggs, Box::new(input));
    assert forall|i: int| 0 <= i < zs.len() implies #[trigger] group_input(db, ctx + zs[i], keys, aggs)
        == Ok::<(Row, Row), SqlError>((ks[i], gs[i])) by {
        assert(ctx + zs[i] =~= zs[i]);
        lemma_group_input(db, ps, zs[i]);
    }
    let prepared = crate::link::capacity::lemma_group_prepared(db, ctx, keys, aggs, zs, ks, gs);
    lemma_distinct_keys(zs);
    let ds = distinct_rows(ks);
    let rs = crate::exec::relational::domain::group_results(aggs, ks, gs);
    let out = ds.map_values(|k: Row| grow(b0, zs, k));
    assert forall|g: int| 0 <= g < rs.len() implies #[trigger] rs[g] == Ok::<Row, SqlError>(out[g]) by {
        let k = ds[g];
        assert(ds.contains(k));
        lemma_agg_row_k(ps, zs, k);
    }
    lemma_collect_all(rs, out);
}

// ------------------------------------------------------------------------------------------------ the outer SELECT

/// `SUM(..) / SUM(volume)` of group `k`.
pub open spec fn share(b0: Seq<u8>, zs: Seq<Row>, k: Row) -> Result<Val, SqlError> {
    crate::spec::fns::div::num_div(gsum0(b0, zs, k), sc0(b0, zs, k), gsum1(zs, k), 4)
}

/// The output row of group `k`, or its error.
pub open spec fn out_res(b0: Seq<u8>, zs: Seq<Row>, k: Row) -> Result<Row, SqlError> {
    match share(b0, zs, k) {
        Ok(v) => Ok(seq![k[0], v]),
        Err(e) => Err(e),
    }
}

/// The outer SELECT list on a GROUP BY row.
pub proof fn lemma_outer_row(db: Database, b0: Seq<u8>, zs: Seq<Row>, k: Row)
    requires is_ykey(k),
    ensures eval_exprs(db, grow(b0, zs, k), outer_exprs()) == out_res(b0, zs, k),
{
    hide(eval_expr);
    hide(eval_exprs);
    let r = grow(b0, zs, k);
    let (a0, a1) = (agg0_val(b0, zs, k), agg1_val(zs, k));
    assert(r.len() == 3 && r[0] == k[0] && r[1] == a0 && r[2] == a1);
    lemma_expr_col(db, r, 0);
    lemma_expr_col(db, r, 1);
    lemma_expr_col(db, r, 2);
    lemma_exprs2(db, r, Expr::Col(1), Expr::Col(2), a0, a1);
    let args = seq![Expr::Col(1), Expr::Col(2)];
    lemma_expr_call(db, r, ScalarFn::DivNumeric, args);
    let div = Expr::Call { f: ScalarFn::DivNumeric, args };
    assert(eval_expr(db, r, div) == share(b0, zs, k));
    let es = outer_exprs();
    assert(es =~= seq![Expr::Col(0), div]);
    lemma_exprs1(db, r, Expr::Col(0), k[0]);
    crate::spec::eval::lemma_eval_exprs_step(db, r, es);
    assert(es.drop_last() =~= seq![Expr::Col(0)]);
    assert(es.last() == div);
    match share(b0, zs, k) {
        Ok(v) => {
            assert(seq![k[0]].push(v) =~= seq![k[0], v]);
        },
        Err(e) => {},
    }
}

/// The statement's body over the GROUP BY rows: the output row or the first error, group by group.
pub proof fn lemma_body_groups(db: Database, ps: Seq<Literal>, input: Query, zs: Seq<Row>)
    requires
        param_domain_ok(ps),
        eval_query(db, Seq::empty(), Query::GroupBy { keys: group_keys(), aggs: group_aggs(ps), input: Box::new(input) })
            == Ok::<Relation, SqlError>(distinct_rows(gkeys(zs)).map_values(|k: Row| grow(txt(ps[0]), zs, k))),
        keys_ykeys(zs),
    ensures
        eval_query(db, Seq::empty(), Query::Project { exprs: outer_exprs(), input: Box::new(
            Query::GroupBy { keys: group_keys(), aggs: group_aggs(ps), input: Box::new(input) }) })
            == collect(distinct_rows(gkeys(zs)).map_values(|k: Row| out_res(txt(ps[0]), zs, k))),
{
    hide(eval_query);
    hide(eval_exprs);
    let b0 = txt(ps[0]);
    let ctx = Seq::<Val>::empty();
    let gq = Query::GroupBy { keys: group_keys(), aggs: group_aggs(ps), input: Box::new(input) };
    lemma_distinct_keys(zs);
    let ds = distinct_rows(gkeys(zs));
    let grows = ds.map_values(|k: Row| grow(b0, zs, k));
    crate::exec::relational::domain::lemma_eval_project(db, ctx, outer_exprs(), Box::new(gq));
    let rs = crate::exec::relational::domain::project_results(db, ctx, grows, outer_exprs());
    let os = ds.map_values(|k: Row| out_res(b0, zs, k));
    assert forall|g: int| 0 <= g < rs.len() implies #[trigger] rs[g] == os[g] by {
        assert(ctx + grows[g] =~= grows[g]);
        lemma_outer_row(db, b0, zs, ds[g]);
    }
    assert(rs =~= os);
}

} // verus!
