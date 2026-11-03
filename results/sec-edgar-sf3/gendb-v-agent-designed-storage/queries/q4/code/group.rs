//! GROUP BY s.sic, t.tlabel, p.stmt / HAVING over the kept joined rows `q = keep(joined(db), qual)`.
//!
//! Each kept row `x` has key `kq(x) = [sic, tlabel, stmt]` (int, text or NULL, the text `$2`) and aggregate arguments
//! `aq(x) = [cik, value, value]` (int4, numeric at scale 4). The keys are exact (SQL "not distinct" is equality), so
//! the groups are the distinct keys in first-occurrence order and each group's values are its rows' ciks
//! (`mciks`) and value coefficients (`mvals`). The aggregates of a group are then: the number of distinct ciks, the
//! sum of the coefficients at scale 4, and their AVG (`avg_of`); `lemma_eval_groups` states the GROUP BY's rows,
//! `lemma_eval_having` the HAVING's, and `lemma_group_capacity` the capacity violations (an absolute coefficient sum
//! beyond `i128`, or an AVG division outside its domain).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::spec::typing::*;
use crate::spec::limits::*;
use crate::spec::aggs::avg::*;
use crate::spec::fns::div::*;
use crate::schema::schema_spec;
use crate::bridge::equality::*;
use crate::bridge::collect::{lemma_collect_all, lemma_collect_pointwise};
use crate::exec::relational::domain::*;
use crate::link::join::{keep, lemma_keep_members, left_of, right_of, sum_of};
use crate::link::query::{lemma_row_exact, lemma_groupby_unfold, lemma_eval_cols, col_exprs, select, avg_of, lemma_avg_ok};
use crate::link::capacity::{lemma_group_by_capacity, lemma_first_input, lemma_sum_inside_ok, lemma_avg_inside_ok, aggs_ok_inside,
    lemma_count_value};
use crate::agent::sem::*;
use crate::agent::common::groups::*;
use vstd::set_lib::{set_int_range, lemma_int_range, lemma_len_subset};

verus! {

pub open spec fn kq(x: Row) -> Row { seq![x[12], x[36], x[41]] }
pub open spec fn aq(x: Row) -> Row { seq![x[10], x[7], x[7]] }

/// Coefficient of a numeric value (0 for others).
pub open spec fn coeff(v: Val) -> int { match v { Val::Num { coeff, .. } => coeff, _ => 0 } }

pub open spec fn num4(c: int) -> Val { Val::Num { coeff: c, scale: 4 } }

/// The shape of a kept joined row.
pub open spec fn qrow(b1: Seq<u8>, x: Row) -> bool {
    &&& x.len() == 48
    &&& x[12] is Int && (x[36] is Text || x[36] is Null) && x[41] == Val::Text(b1)
    &&& x[10] is Int && int_in_range(IntKind::Int4, ival(x[10]))
    &&& x[7] is Num && x[7]->Num_scale == 4
}

/// The kept rows.
pub open spec fn qrows(db: Database, b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int) -> Seq<Row> {
    keep(joined(db), |x: Row| qual(b0, b1, lo, hi, x))
}

/// Every kept row has the shape.
pub proof fn lemma_qrows_shape(db: Database, b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int)
    requires db.schema == schema_spec(), db_wf(db),
    ensures forall|i: int| 0 <= i < qrows(db, b0, b1, lo, hi).len() ==> qrow(b1, #[trigger] qrows(db, b0, b1, lo, hi)[i]),
{
    let q = qrows(db, b0, b1, lo, hi);
    lemma_joined_widths(db);
    lemma_keep_members(joined(db), |x: Row| qual(b0, b1, lo, hi, x));
    assert forall|i: int| 0 <= i < q.len() implies qrow(b1, #[trigger] q[i]) by {
        let x = q[i];
        assert(joined(db).contains(x));
        let m = choose|m: int| 0 <= m < joined(db).len() && joined(db)[m] == x;
        assert(x.len() == 48);
        assert(qual(b0, b1, lo, hi, x));
        let l = left_of(x, 38);
        let ll = left_of(l, 29);
        let n = left_of(ll, 9);
        let s = right_of(ll, 9);
        let tg = right_of(l, 29);
        assert(l.len() == 38 && ll.len() == 29);
        assert(n[7] == x[7]);
        assert(s[1] == x[10] && s[3] == x[12]);
        assert(tg[7] == x[36]);
    }
}

// ------------------------------------------------------------------------------------------------ members

/// The ciks of the rows of key `k`, in order.
pub open spec fn mciks(q: Seq<Row>, k: Row) -> Seq<int>
    decreases q.len(),
{
    if q.len() == 0 {
        Seq::empty()
    } else {
        let m = mciks(q.drop_last(), k);
        if kq(q.last()) == k { m.push(ival(q.last()[10])) } else { m }
    }
}

/// The value coefficients of the rows of key `k`, in order.
pub open spec fn mvals(q: Seq<Row>, k: Row) -> Seq<int>
    decreases q.len(),
{
    if q.len() == 0 {
        Seq::empty()
    } else {
        let m = mvals(q.drop_last(), k);
        if kq(q.last()) == k { m.push(coeff(q.last()[7])) } else { m }
    }
}

/// Sum and absolute sum of integers.
pub open spec fn isum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { isum(s.drop_last()) + s.last() }
}

pub open spec fn iabs(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { iabs(s.drop_last()) + abs(s.last()) }
}

pub open spec fn ints(s: Seq<int>) -> Seq<Val> { s.map_values(|c: int| Val::Int(c)) }
pub open spec fn nums(s: Seq<int>) -> Seq<Val> { s.map_values(|c: int| num4(c)) }

/// The members of key `k` (the denotation's `mem` of the prepared sequences): one row `[cik, value, value]` each.
pub proof fn lemma_mem_columns(q: Seq<Row>, b1: Seq<u8>, k: Row)
    requires forall|i: int| 0 <= i < q.len() ==> qrow(b1, #[trigger] q[i]),
    ensures ({
        let m = mem(q.map_values(|x: Row| kq(x)), q.map_values(|x: Row| aq(x)), k);
        &&& column(m, 0) == ints(mciks(q, k))
        &&& column(m, 1) == nums(mvals(q, k))
        &&& column(m, 2) == nums(mvals(q, k))
        &&& mciks(q, k).len() == mvals(q, k).len()
    }),
    decreases q.len(),
{
    let ks = q.map_values(|x: Row| kq(x));
    let as_ = q.map_values(|x: Row| aq(x));
    if q.len() > 0 {
        let qi = q.drop_last();
        assert forall|i: int| 0 <= i < qi.len() implies qrow(b1, #[trigger] qi[i]) by { assert(qi[i] == q[i]); }
        lemma_mem_columns(qi, b1, k);
        assert(ks.drop_last() =~= qi.map_values(|x: Row| kq(x)));
        assert(as_.drop_last() =~= qi.map_values(|x: Row| aq(x)));
        let x = q.last();
        assert(x == q[q.len() - 1]);
        assert(ks.last() == kq(x) && as_.last() == aq(x));
        let mi = mem(qi.map_values(|x: Row| kq(x)), qi.map_values(|x: Row| aq(x)), k);
        let m = mem(ks, as_, k);
        if kq(x) == k {
            assert(m == mi.push(aq(x)));
            assert(column(m, 0) =~= column(mi, 0).push(x[10]));
            assert(column(m, 1) =~= column(mi, 1).push(x[7]));
            assert(column(m, 2) =~= column(mi, 2).push(x[7]));
            assert(ints(mciks(q, k)) =~= ints(mciks(qi, k)).push(Val::Int(ival(x[10]))));
            assert(nums(mvals(q, k)) =~= nums(mvals(qi, k)).push(num4(coeff(x[7]))));
        } else {
            assert(m == mi);
        }
    } else {
        assert(column(mem(ks, as_, k), 0) =~= ints(mciks(q, k)));
        assert(column(mem(ks, as_, k), 1) =~= nums(mvals(q, k)));
        assert(column(mem(ks, as_, k), 2) =~= nums(mvals(q, k)));
    }
}

/// The numeric aggregates' views of `nums(s)`.
pub proof fn lemma_nums(s: Seq<int>)
    ensures
        all_of_kind(NumKind::Numeric, nums(s)),
        count_non_null(nums(s)) == s.len(),
        num_sum(nums(s)) == (if s.len() == 0 { (0int, 0nat) } else { (isum(s), 4nat) }),
        num_max_scale(nums(s)) == (if s.len() == 0 { 0nat } else { 4nat }),
        num_mass_at(nums(s), num_max_scale(nums(s))) == iabs(s),
        iabs(s) >= 0,
        abs(isum(s)) <= iabs(s),
    decreases s.len(),
{
    lemma_nums_mass_at4(s);
    if s.len() > 0 {
        let si = s.drop_last();
        lemma_nums(si);
        assert(nums(s).drop_last() =~= nums(si));
        assert(nums(s).last() == num4(s.last()));
        assert(pow10(0) == 1);
        assert((4nat - 4nat) as nat == 0nat);
        assert(align(s.last(), 4, 4) == s.last());
        if si.len() == 0 {
            assert(pow10(4) == 10000) by (compute);
            assert(align(0, 0, 4) == 0 * pow10(4));
            assert(0 * pow10(4) == 0);
            assert(num_sum(nums(si)) == (0int, 0nat));
            assert(num_add_coeff(0, 0, s.last(), 4) == s.last());
        } else {
            assert(align(isum(si), 4, 4) == isum(si));
            assert(num_add_coeff(isum(si), 4, s.last(), 4) == isum(si) + s.last());
        }
    } else {
        assert(nums(s) =~= Seq::<Val>::empty());
    }
}

/// `num_mass_at` at one scale over values all at that scale, as in `lemma_nums` (helper for the step).
pub proof fn lemma_nums_mass_at4(s: Seq<int>)
    ensures num_mass_at(nums(s), 4) == iabs(s),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_nums_mass_at4(s.drop_last());
        assert(nums(s).drop_last() =~= nums(s.drop_last()));
        assert(pow10(0) == 1);
        assert(abs(s.last()) * pow10((4nat - 4nat) as nat) == abs(s.last()));
    } else {
        assert(nums(s) =~= Seq::<Val>::empty());
    }
}

/// The distinct ciks: one value per distinct int, so their count is the size of the set of ciks.
pub proof fn lemma_distinct_ints(s: Seq<int>)
    ensures
        distinct_vals(ints(s)).no_duplicates(),
        forall|v: Val| #[trigger] distinct_vals(ints(s)).contains(v) <==> (v is Int && s.contains(ival(v))),
        count_non_null(distinct_vals(ints(s))) == distinct_vals(ints(s)).len(),
        distinct_vals(ints(s)).len() == s.to_set().len(),
    decreases s.len(),
{
    let d = distinct_vals(ints(s));
    if s.len() > 0 {
        let si = s.drop_last();
        lemma_distinct_ints(si);
        let di = distinct_vals(ints(si));
        assert(ints(s).drop_last() =~= ints(si));
        let v = Val::Int(s.last());
        assert(ints(s).last() == v);
        // `has_val_not_distinct` over ints is `contains`.
        assert forall|i: int| 0 <= i < di.len() implies (#[trigger] di[i]) is Int by {
            assert(di.contains(di[i]));
        }
        lemma_has_val_nd_ints(di, v);
        assert forall|w: Val| #[trigger] d.contains(w) <==> (w is Int && s.contains(ival(w))) by {
            if si.contains(ival(w)) {
                let i = choose|i: int| 0 <= i < si.len() && si[i] == ival(w);
                assert(s[i] == ival(w));
            }
            if s.contains(ival(w)) && ival(w) != s.last() {
                let i = choose|i: int| 0 <= i < s.len() && s[i] == ival(w);
                assert(si[i] == ival(w));
            }
            if !di.contains(v) {
                if d.contains(w) {
                    let i = choose|i: int| 0 <= i < d.len() && d[i] == w;
                    if i < di.len() { assert(di[i] == w); }
                }
                if di.contains(w) {
                    let i = choose|i: int| 0 <= i < di.len() && di[i] == w;
                    assert(d[i] == w);
                }
                assert(d[di.len() as int] == v);
            }
            assert(s[s.len() - 1] == s.last());
        }
        if !di.contains(v) {
            assert forall|i: int, j: int| 0 <= i < d.len() && 0 <= j < d.len() && i != j implies d[i] != d[j] by {
                if i < di.len() && j < di.len() {
                    assert(d[i] == di[i] && d[j] == di[j]);
                } else if i < di.len() {
                    assert(d[i] == di[i] && di.contains(di[i]));
                } else if j < di.len() {
                    assert(d[j] == di[j] && di.contains(di[j]));
                }
            }
            assert(d == di.push(v));
            assert(d.drop_last() =~= di);
            assert(count_non_null(d) == count_non_null(di) + 1);
        }
        // Set sizes: the new value is new exactly when it is not among the earlier ciks.
        assert(s.to_set() =~= si.to_set().insert(s.last())) by {
            assert forall|c: int| s.to_set().contains(c) <==> si.to_set().insert(s.last()).contains(c) by {
                if si.contains(c) {
                    let i = choose|i: int| 0 <= i < si.len() && si[i] == c;
                    assert(s[i] == c);
                }
                if s.contains(c) && c != s.last() {
                    let i = choose|i: int| 0 <= i < s.len() && s[i] == c;
                    assert(si[i] == c);
                }
                assert(s[s.len() - 1] == s.last());
            }
        }
        assert(di.contains(v) <==> si.contains(s.last()));
    } else {
        assert(ints(s) =~= Seq::<Val>::empty());
        assert(s.to_set() =~= Set::<int>::empty());
    }
}

proof fn lemma_has_val_nd_ints(d: Seq<Val>, v: Val)
    requires v is Int, forall|i: int| 0 <= i < d.len() ==> (#[trigger] d[i]) is Int,
    ensures has_val_not_distinct(d, v) <==> d.contains(v),
    decreases d.len(),
{
    if d.len() > 0 {
        let di = d.drop_last();
        assert forall|i: int| 0 <= i < di.len() implies (#[trigger] di[i]) is Int by { assert(di[i] == d[i]); }
        lemma_has_val_nd_ints(di, v);
        assert(d[d.len() - 1] == d.last());
        lemma_val_not_distinct_structural(d.last(), v);
        if di.contains(v) {
            let i = choose|i: int| 0 <= i < di.len() && di[i] == v;
            assert(d[i] == v);
        }
        if d.contains(v) && d.last() != v {
            let i = choose|i: int| 0 <= i < d.len() && d[i] == v;
            assert(di[i] == v);
        }
    }
}

/// At most 2^32 distinct int4 values.
pub proof fn lemma_int4_set_bound(s: Seq<int>)
    requires forall|i: int| 0 <= i < s.len() ==> int_in_range(IntKind::Int4, #[trigger] s[i]),
    ensures s.to_set().len() <= 0x1_0000_0000,
{
    let r = set_int_range(-0x8000_0000, 0x8000_0000);
    lemma_int_range(-0x8000_0000, 0x8000_0000);
    assert(s.to_set().subset_of(r)) by {
        assert forall|c: int| s.to_set().contains(c) implies r.contains(c) by {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == c;
            assert(int_in_range(IntKind::Int4, s[i]));
        }
    }
    lemma_len_subset(s.to_set(), r);
}

/// The ciks of a group are int4 values.
pub proof fn lemma_mciks_int4(q: Seq<Row>, b1: Seq<u8>, k: Row)
    requires forall|i: int| 0 <= i < q.len() ==> qrow(b1, #[trigger] q[i]),
    ensures forall|i: int| 0 <= i < mciks(q, k).len() ==> int_in_range(IntKind::Int4, #[trigger] mciks(q, k)[i]),
    decreases q.len(),
{
    if q.len() > 0 {
        let qi = q.drop_last();
        assert forall|i: int| 0 <= i < qi.len() implies qrow(b1, #[trigger] qi[i]) by { assert(qi[i] == q[i]); }
        lemma_mciks_int4(qi, b1, k);
        assert(qrow(b1, q[q.len() - 1]));
        let mi = mciks(qi, k);
        if kq(q.last()) == k {
            assert(mciks(q, k) == mi.push(ival(q.last()[10])));
            assert forall|i: int| 0 <= i < mciks(q, k).len() implies int_in_range(IntKind::Int4, #[trigger] mciks(q, k)[i]) by {
                if i < mi.len() {
                    assert(mciks(q, k)[i] == mi[i]);
                }
            }
        } else {
            assert(mciks(q, k) == mi);
        }
    }
}

// ------------------------------------------------------------------------------------------------ the aggregates

/// The aggregate values of a group: distinct ciks, sum and AVG of the value coefficients.
pub open spec fn gvals(q: Seq<Row>, k: Row) -> Row {
    let s = mvals(q, k);
    seq![Val::Int(mciks(q, k).to_set().len() as int), num4(isum(s)), avg_of(isum(s), 4, s.len())]
}

/// A group fits: absolute coefficient sum within `i128` and the AVG division inside its domain.
pub open spec fn group_fits(q: Seq<Row>, k: Row) -> bool {
    &&& iabs(mvals(q, k)) <= i128::MAX as int
    &&& num_div_fits(isum(mvals(q, k)), 4, mvals(q, k).len() as int, 0)
}

/// One group's aggregate row, inside its domain.
pub proof fn lemma_agg_row_group(q: Seq<Row>, b1: Seq<u8>, k: Row)
    requires
        forall|i: int| 0 <= i < q.len() ==> qrow(b1, #[trigger] q[i]),
        mvals(q, k).len() > 0,
        group_fits(q, k),
    ensures
        agg_row(gb_aggs(), mem(q.map_values(|x: Row| kq(x)), q.map_values(|x: Row| aq(x)), k)) == Ok::<Row, SqlError>(gvals(q, k)),
{
    let m = mem(q.map_values(|x: Row| kq(x)), q.map_values(|x: Row| aq(x)), k);
    lemma_mem_columns(q, b1, k);
    let (cs, vs) = (mciks(q, k), mvals(q, k));
    lemma_nums(vs);
    lemma_distinct_ints(cs);
    lemma_mciks_int4(q, b1, k);
    lemma_int4_set_bound(cs);
    let aggs = gb_aggs();
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(m, j)));
    let gv = gvals(q, k);
    // COUNT(DISTINCT cik).
    let dv = distinct_vals(ints(cs));
    assert(agg_value(aggs[0], column(m, 0)) == agg_value(Agg::Count(Expr::Col(10)), dv));
    lemma_count_value(Agg::Count(Expr::Col(10)), dv);
    assert(rs[0] == Ok::<Val, SqlError>(gv[0]));
    // SUM(value).
    let s = isum(vs);
    assert(abs(s) <= i128::MAX as int);
    lemma_num_in_range_small(s, 4);
    assert(rs[1] == Ok::<Val, SqlError>(gv[1]));
    // AVG(value).
    lemma_avg_ok(s, 4, vs.len() as int);
    assert(avg_sum(NumKind::Numeric, nums(vs)) == (s, 4nat));
    assert(rs[2] == Ok::<Val, SqlError>(gv[2]));
    lemma_collect_all(rs, gv);
}

// ------------------------------------------------------------------------------------------------ GROUP BY

/// The keys of the kept rows are exact.
pub proof fn lemma_exact_kq(q: Seq<Row>, b1: Seq<u8>)
    requires forall|i: int| 0 <= i < q.len() ==> qrow(b1, #[trigger] q[i]),
    ensures exact_keys(q.map_values(|x: Row| kq(x))),
{
    let ks = q.map_values(|x: Row| kq(x));
    assert forall|a: Row, b: Row| ks.contains(a) && ks.contains(b) implies (#[trigger] row_not_distinct(a, b) <==> a == b) by {
        let i = choose|i: int| 0 <= i < ks.len() && ks[i] == a;
        let j = choose|j: int| 0 <= j < ks.len() && ks[j] == b;
        assert(qrow(b1, q[i]) && qrow(b1, q[j]));
        assert(a == kq(q[i]) && b == kq(q[j]));
        assert forall|p: int| 0 <= p < a.len() implies same_exact_type(#[trigger] a[p], b[p]) by {}
        lemma_row_exact(a, b);
    }
}

proof fn lemma_agg_arg_distinct_count(db: Database, x: Row, i: nat)
    requires i < x.len(),
    ensures agg_arg(db, x, Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(i))))) == Ok::<Val, SqlError>(x[i as int]),
{
    assert(agg_arg(db, x, Agg::Count(Expr::Col(i))) == eval_expr(db, x, Expr::Col(i)));
    assert(eval_expr(db, x, Expr::Col(i)) == Ok::<Val, SqlError>(x[i as int]));
}

proof fn lemma_agg_arg_sum_col(db: Database, x: Row, i: nat)
    requires i < x.len(),
    ensures agg_arg(db, x, Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(i) }) == Ok::<Val, SqlError>(x[i as int]),
{
    assert(eval_expr(db, x, Expr::Col(i)) == Ok::<Val, SqlError>(x[i as int]));
}

proof fn lemma_agg_arg_avg_col(db: Database, x: Row, i: nat)
    requires i < x.len(),
    ensures agg_arg(db, x, Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(i) }) == Ok::<Val, SqlError>(x[i as int]),
{
    assert(eval_expr(db, x, Expr::Col(i)) == Ok::<Val, SqlError>(x[i as int]));
}

/// Arguments of three aggregates, from each one's argument.
proof fn lemma_agg_args3(db: Database, env: Row, a0: Agg, a1: Agg, a2: Agg, v0: Val, v1: Val, v2: Val)
    requires
        agg_arg(db, env, a0) == Ok::<Val, SqlError>(v0),
        agg_arg(db, env, a1) == Ok::<Val, SqlError>(v1),
        agg_arg(db, env, a2) == Ok::<Val, SqlError>(v2),
    ensures agg_args(db, env, seq![a0, a1, a2]) == Ok::<Row, SqlError>(seq![v0, v1, v2]),
{
    let aggs = seq![a0, a1, a2];
    lemma_agg_arg_results_index(db, env, aggs);
    let rs = agg_arg_results(db, env, aggs);
    let vs = seq![v0, v1, v2];
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(vs[j]) by {
        assert(rs[j] == agg_arg(db, env, aggs[j]));
    }
    lemma_collect_all(rs, vs);
}

/// The aggregate arguments of a row: `[cik, value, value]`.
pub proof fn lemma_agg_args_aq(db: Database, x: Row)
    requires x.len() == 48,
    ensures agg_args(db, x, gb_aggs()) == Ok::<Row, SqlError>(aq(x)),
{
    lemma_agg_arg_distinct_count(db, x, 10);
    lemma_agg_arg_sum_col(db, x, 7);
    lemma_agg_arg_avg_col(db, x, 7);
    lemma_agg_args3(db, x, Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(10)))),
        Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(7) }, Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(7) },
        x[10], x[7], x[7]);
}

/// The group keys of a row: `[sic, tlabel, stmt]`.
pub proof fn lemma_keys_kq(db: Database, x: Row)
    requires x.len() == 48,
    ensures eval_exprs(db, x, gb_keys()) == Ok::<Row, SqlError>(kq(x)),
{
    let idxs = seq![12nat, 36nat, 41nat];
    assert(col_exprs(idxs) =~= gb_keys());
    lemma_eval_cols(db, x, idxs);
    assert(select(x, idxs) =~= kq(x));
}

/// The GROUP BY's prepared (key, arguments) of each kept row.
pub proof fn lemma_group_input(db: Database, x: Row, b1: Seq<u8>)
    requires qrow(b1, x),
    ensures
        eval_exprs(db, Seq::<Val>::empty() + x, gb_keys()) == Ok::<Row, SqlError>(kq(x)),
        agg_args(db, Seq::<Val>::empty() + x, gb_aggs()) == Ok::<Row, SqlError>(aq(x)),
        group_input(db, Seq::<Val>::empty() + x, gb_keys(), gb_aggs()) == Ok::<(Row, Row), SqlError>((kq(x), aq(x))),
{
    assert(Seq::<Val>::empty() + x =~= x);
    lemma_keys_kq(db, x);
    lemma_agg_args_aq(db, x);
}

/// The GROUP BY output rows when every group fits.
pub open spec fn grows(q: Seq<Row>) -> Seq<Row> {
    dk(q.map_values(|x: Row| kq(x))).map_values(|k: Row| k + gvals(q, k))
}

/// Every key of the kept rows has members.
pub proof fn lemma_key_members(q: Seq<Row>, k: Row)
    requires q.map_values(|x: Row| kq(x)).contains(k),
    ensures mvals(q, k).len() > 0,
    decreases q.len(),
{
    let ks = q.map_values(|x: Row| kq(x));
    let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
    if i == q.len() - 1 {
        assert(kq(q.last()) == k);
    } else {
        let qi = q.drop_last();
        assert(qi.map_values(|x: Row| kq(x))[i] == k);
        lemma_key_members(qi, k);
    }
}

/// The GROUP BY evaluates to one row per group, `key ++ gvals`, when every group fits.
pub proof fn lemma_eval_groups(db: Database, b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int)
    requires
        db.schema == schema_spec(), db_wf(db), bind_ok(lo, hi),
        forall|k: Row| qrows(db, b0, b1, lo, hi).map_values(|x: Row| kq(x)).contains(k) ==> #[trigger] group_fits(qrows(db, b0, b1, lo, hi), k),
    ensures
        eval_query(db, Seq::empty(), q74(ps_of(b0, b1, lo, hi))) == Ok::<Relation, SqlError>(grows(qrows(db, b0, b1, lo, hi))),
{
    let q = qrows(db, b0, b1, lo, hi);
    let ps = ps_of(b0, b1, lo, hi);
    lemma_eval_where_rows(db, b0, b1, lo, hi);
    lemma_qrows_shape(db, b0, b1, lo, hi);
    let prep = Seq::new(q.len(), |i: int| (kq(q[i]), aq(q[i])));
    let pre = Seq::new(q.len(), |i: int|
        match eval_exprs(db, Seq::<Val>::empty() + q[i], gb_keys()) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, Seq::<Val>::empty() + q[i], gb_aggs()) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        });
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<(Row, Row), SqlError>(prep[i]) by {
        lemma_group_input(db, q[i], b1);
    }
    lemma_collect_all(pre, prep);
    lemma_groupby_unfold(db, q73(ps), gb_keys(), gb_aggs(), q, prep);
    let ks = q.map_values(|x: Row| kq(x));
    let as_ = q.map_values(|x: Row| aq(x));
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= ks);
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= as_);
    lemma_exact_kq(q, b1);
    lemma_distinct_rows_dk(ks);
    lemma_dk(ks);
    let ds = dk(ks);
    let grs = Seq::new(ds.len(), |g: int|
        match agg_row(gb_aggs(), group_members(ks, as_, ds[g])) {
            Ok(a) => Ok(ds[g] + a),
            Err(e) => Err(e),
        });
    let out = grows(q);
    assert forall|g: int| 0 <= g < grs.len() implies #[trigger] grs[g] == Ok::<Row, SqlError>(out[g]) by {
        let k = ds[g];
        assert(ds.contains(k));
        assert(ks.contains(k));
        lemma_group_members_mem(ks, as_, k);
        lemma_key_members(q, k);
        assert(group_fits(q, k));
        lemma_agg_row_group(q, b1, k);
    }
    lemma_collect_all(grs, out);
}

// ------------------------------------------------------------------------------------------------ HAVING

/// HAVING COUNT(DISTINCT cik) >= 2 on a GROUP BY output row.
pub open spec fn having_ok(r: Row) -> bool { ival(r[3]) >= 2 }

/// The HAVING condition on a row with an int at position 3.
pub proof fn lemma_eval_having_row(db: Database, r: Row)
    requires r.len() > 3, r[3] is Int,
    ensures eval_pred(db, r, pred_n3()) == Ok::<Truth, SqlError>(truth_of(having_ok(r))),
{
    let two = Literal::Int { v: 2, kind: IntKind::Int4 };
    assert(eval_expr(db, r, Expr::Col(3)) == Ok::<Val, SqlError>(r[3]));
    assert(lit_val(two) == Ok::<Val, SqlError>(Val::Int(2)));
    assert(eval_expr(db, r, Expr::Lit(two)) == Ok::<Val, SqlError>(Val::Int(2)));
    assert(compare(r[3], Val::Int(2)) == Some(sign(ival(r[3]) - 2)));
}

/// The GROUP BY rows have the distinct cik count (an int) at position 3.
pub proof fn lemma_grows_shape(q: Seq<Row>, b1: Seq<u8>)
    requires forall|i: int| 0 <= i < q.len() ==> qrow(b1, #[trigger] q[i]),
    ensures forall|i: int| 0 <= i < grows(q).len() ==> (#[trigger] grows(q)[i]).len() == 6 && grows(q)[i][3] is Int,
{
    let ks = q.map_values(|x: Row| kq(x));
    lemma_dk(ks);
    assert forall|i: int| 0 <= i < grows(q).len() implies (#[trigger] grows(q)[i]).len() == 6 && grows(q)[i][3] is Int by {
        let k = dk(ks)[i];
        assert(dk(ks).contains(k));
        let j = choose|j: int| 0 <= j < ks.len() && ks[j] == k;
        assert(k == kq(q[j]));
        assert(k.len() == 3);
        assert(grows(q)[i] == k + gvals(q, k));
        assert(grows(q)[i][3] == gvals(q, k)[0]);
    }
}

/// The statement's body: the GROUP BY rows whose distinct cik count is at least 2.
pub proof fn lemma_eval_having(db: Database, b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int)
    requires
        db.schema == schema_spec(), db_wf(db), bind_ok(lo, hi),
        forall|k: Row| qrows(db, b0, b1, lo, hi).map_values(|x: Row| kq(x)).contains(k) ==> #[trigger] group_fits(qrows(db, b0, b1, lo, hi), k),
    ensures
        eval_query(db, Seq::empty(), q75(ps_of(b0, b1, lo, hi)))
            == Ok::<Relation, SqlError>(keep(grows(qrows(db, b0, b1, lo, hi)), |r: Row| having_ok(r))),
{
    hide(eval_pred);
    hide(grows);
    let q = qrows(db, b0, b1, lo, hi);
    let ps = ps_of(b0, b1, lo, hi);
    lemma_eval_groups(db, b0, b1, lo, hi);
    lemma_qrows_shape(db, b0, b1, lo, hi);
    lemma_grows_shape(q, b1);
    let rows = grows(q);
    let ctx = Seq::<Val>::empty();
    let truths = Seq::new(rows.len(), |i: int| truth_of(having_ok(rows[i])));
    let prs = filter_results(db, ctx, rows, pred_n3());
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(ctx + rows[i] =~= rows[i]);
        lemma_eval_having_row(db, rows[i]);
    }
    lemma_collect_all(prs, truths);
    crate::exec::relational::domain::lemma_eval_filter(db, ctx, pred_n3(), Box::new(q74(ps)));
    crate::link::join::lemma_keep_true_keep(rows, truths, |r: Row| having_ok(r));
}

// ------------------------------------------------------------------------------------------------ capacity

/// A group outside its domain puts the statement outside the capacity domain.
pub proof fn lemma_group_capacity(db: Database, b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int, k: Row)
    requires
        db.schema == schema_spec(), db_wf(db), bind_ok(lo, hi),
        qrows(db, b0, b1, lo, hi).map_values(|x: Row| kq(x)).contains(k),
        !group_fits(qrows(db, b0, b1, lo, hi), k),
    ensures !fits_query(db, Seq::empty(), q75(ps_of(b0, b1, lo, hi))),
{
    let q = qrows(db, b0, b1, lo, hi);
    let ps = ps_of(b0, b1, lo, hi);
    lemma_eval_where_rows(db, b0, b1, lo, hi);
    lemma_qrows_shape(db, b0, b1, lo, hi);
    let ks = q.map_values(|x: Row| kq(x));
    let as_ = q.map_values(|x: Row| aq(x));
    assert forall|i: int| 0 <= i < q.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + q[i], gb_keys(), gb_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], as_[i])) by {
        lemma_group_input(db, q[i], b1);
    }
    lemma_exact_kq(q, b1);
    lemma_distinct_rows_dk(ks);
    lemma_dk(ks);
    let ds = dk(ks);
    let aggs = gb_aggs();
    // Every group's aggregates succeed inside their domains.
    assert forall|h: int| 0 <= h < distinct_rows(ks).len() implies #[trigger] aggs_ok_inside(aggs, group_members(ks, as_, distinct_rows(ks)[h])) by {
        let kh = ds[h];
        assert(ds.contains(kh));
        lemma_group_members_mem(ks, as_, kh);
        lemma_mem_columns(q, b1, kh);
        lemma_nums(mvals(q, kh));
        let m = group_members(ks, as_, kh);
        assert forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(m, j)) implies agg_value(aggs[j], column(m, j)) is Ok by {
            if j == 0 {
                let cs = mciks(q, kh);
                lemma_distinct_ints(cs);
                lemma_mciks_int4(q, b1, kh);
                lemma_int4_set_bound(cs);
                lemma_count_value(Agg::Count(Expr::Col(10)), distinct_vals(ints(cs)));
            } else if j == 1 {
                lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(7), column(m, 1));
            } else {
                lemma_avg_inside_ok(NumKind::Numeric, Expr::Col(7), column(m, 2));
            }
        }
    }
    // The failing group and aggregate.
    let g = ds.index_of(k);
    assert(ds.contains(k));
    lemma_group_members_mem(ks, as_, k);
    lemma_mem_columns(q, b1, k);
    let vs = mvals(q, k);
    lemma_nums(vs);
    let m = group_members(ks, as_, k);
    if iabs(vs) > i128::MAX as int {
        assert(!fits_agg_value(aggs[1], column(m, 1)));
        lemma_group_by_capacity(db, Seq::empty(), gb_keys(), aggs, Box::new(q73(ps)), q, ks, as_, g, 1);
    } else {
        assert(!fits_agg_value(aggs[2], column(m, 2)));
        lemma_group_by_capacity(db, Seq::empty(), gb_keys(), aggs, Box::new(q73(ps)), q, ks, as_, g, 2);
    }
    lemma_first_input(db, Seq::empty(), q75(ps));
}

} // verus!
