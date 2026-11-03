//! Aggregate values over evaluated argument columns (one argument value per member row of a group; the arguments
//! themselves are evaluated in `exec::relational::group`): COUNT(*), COUNT(e) and SUM at int4/int8/numeric here,
//! DISTINCT aggregates over `distinct_vals_exec`, MIN/MAX/AVG dispatched to `exec::aggs`.
//!
//! SUM follows the exact spec (`int_sum` / `num_sum`, unbounded); only the final value is range-checked, as in
//! the spec. The capacity condition of SUM/AVG is the absolute mass (`exec::relational::domain::sum_mass_fits`):
//! integer sums of a vector always meet it (fewer than 2^64 values of absolute value at most 2^63); numeric sums
//! refuse with `Capacity` exactly when the absolute mass at the result scale exceeds `i128::MAX`. The numeric sum
//! is accumulated directly at the result scale (`num_max_scale_exec`, first pass), skipping zero coefficients, so
//! no alignment outside the mass is ever computed.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::relation::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::exec::domain::*;
use crate::exec::numeric::*;
use crate::exec::scalar::*;
use crate::exec::equality::*;
use crate::exec::aggs::avg::*;
use crate::exec::aggs::minmax::*;
use crate::exec::relational::schema::*;
use crate::exec::relational::domain::*;
use crate::bridge::relation::*;
use crate::bridge::order::lemma_pow10_add;

verus! {

/// One loop step over a prefix: `vs.take(i + 1)` is `vs.take(i)` followed by `vs[i]`.
proof fn lemma_take_step(vs: Seq<Val>, i: int)
    requires 0 <= i < vs.len(),
    ensures vs.take(i + 1).drop_last() == vs.take(i), vs.take(i + 1).last() == vs[i],
{
    assert(vs.take(i + 1).drop_last() =~= vs.take(i));
}

// ------------------------------------------------------------------ COUNT and the SUM operand kind

pub fn count_non_null_exec(vs: &Vec<EVal>) -> (n: usize)
    ensures n as nat == count_non_null(view_row(vs@)),
{
    let ghost g = view_row(vs@);
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < vs.len()
        invariant
            i <= vs.len(), n <= i, g == view_row(vs@),
            n as nat == count_non_null(g.take(i as int)),
        decreases vs.len() - i,
    {
        proof { lemma_take_step(g, i as int); }
        if !matches!(vs[i], EVal::Null) {
            n = n + 1;
        }
        i = i + 1;
    }
    proof { assert(g.take(vs.len() as int) =~= g); }
    n
}

pub fn all_of_kind_exec(kind: NumKind, vs: &Vec<EVal>) -> (b: bool)
    ensures b == all_of_kind(kind, view_row(vs@)),
{
    let ghost g = view_row(vs@);
    let mut i: usize = 0;
    while i < vs.len()
        invariant
            i <= vs.len(), g == view_row(vs@),
            all_of_kind(kind, g.take(i as int)),
        decreases vs.len() - i,
    {
        proof { lemma_take_step(g, i as int); }
        let ok = match &vs[i] {
            EVal::Null => true,
            EVal::Int(_) => !matches!(kind, NumKind::Numeric),
            EVal::Num { .. } => matches!(kind, NumKind::Numeric),
            _ => false,
        };
        if !ok {
            proof {
                if all_of_kind(kind, g) {
                    lemma_all_of_kind_prefix(kind, g, i as int + 1);
                }
            }
            return false;
        }
        i = i + 1;
    }
    proof { assert(g.take(vs.len() as int) =~= g); }
    true
}

proof fn lemma_all_of_kind_prefix(kind: NumKind, vs: Seq<Val>, k: int)
    requires 0 <= k <= vs.len(), all_of_kind(kind, vs),
    ensures all_of_kind(kind, vs.take(k)),
    decreases vs.len(),
{
    if k < vs.len() {
        let d = vs.drop_last();
        assert(d.take(k) =~= vs.take(k));
        lemma_all_of_kind_prefix(kind, d, k);
    } else {
        assert(vs.take(k) =~= vs);
    }
}

// ------------------------------------------------------------------ exact sums

/// Exact integer sum; never overflows `i128` (at most `usize::MAX` terms of absolute value at most 2^63), and the
/// absolute mass meets the SUM/AVG capacity condition for the same reason.
pub fn int_sum_exec(vs: &Vec<EVal>) -> (s: i128)
    ensures
        s as int == int_sum(view_row(vs@)),
        int_mass(view_row(vs@)) <= i128::MAX as int,
{
    let ghost g = view_row(vs@);
    let mut acc: i128 = 0;
    let mut i: usize = 0;
    while i < vs.len()
        invariant
            i <= vs.len(), g == view_row(vs@),
            acc as int == int_sum(g.take(i as int)),
            -(i as int) * 0x8000_0000_0000_0000 <= acc <= (i as int) * 0x8000_0000_0000_0000,
            0 <= int_mass(g.take(i as int)) <= (i as int) * 0x8000_0000_0000_0000,
        decreases vs.len() - i,
    {
        proof { lemma_take_step(g, i as int); }
        let x: i64 = match &vs[i] {
            EVal::Int(x) => *x,
            _ => 0,
        };
        proof {
            let ii = i as int;
            assert(ii + 1 <= 0xffff_ffff_ffff_ffff);
            assert((ii + 1) * 0x8000_0000_0000_0000 <= 0x7fff_ffff_ffff_ffff_8000_0000_0000_0000) by (nonlinear_arith)
                requires ii + 1 <= 0xffff_ffff_ffff_ffff;
            assert((ii + 1) * 0x8000_0000_0000_0000 == ii * 0x8000_0000_0000_0000 + 0x8000_0000_0000_0000) by (nonlinear_arith);
        }
        acc = acc + x as i128;
        i = i + 1;
    }
    proof {
        assert(g.take(vs.len() as int) =~= g);
        let n = vs.len() as int;
        assert(n <= 0xffff_ffff_ffff_ffff);
        assert(n * 0x8000_0000_0000_0000 <= 0x7fff_ffff_ffff_ffff_8000_0000_0000_0000) by (nonlinear_arith)
            requires n <= 0xffff_ffff_ffff_ffff;
    }
    acc
}

/// Exact numeric sum at a scale `t` at least every value's scale: the sum of the aligned coefficients.
pub open spec fn num_sum_at(vs: Seq<Val>, t: nat) -> int
    decreases vs.len(),
{
    if vs.len() == 0 {
        0
    } else {
        num_sum_at(vs.drop_last(), t) + match vs.last() {
            Val::Num { coeff, scale } => align(coeff, scale, t),
            _ => 0,
        }
    }
}

/// Every numeric value's scale is at most `num_max_scale`.
pub proof fn lemma_num_max_scale_bound(vs: Seq<Val>, i: int)
    requires 0 <= i < vs.len(),
    ensures vs[i] matches Val::Num { coeff, scale } ==> scale <= num_max_scale(vs),
    decreases vs.len(),
{
    if i < vs.len() - 1 {
        lemma_num_max_scale_bound(vs.drop_last(), i);
        assert(vs.drop_last()[i] == vs[i]);
    }
}

/// `num_sum` accumulates at the running largest scale: its scale is `num_max_scale`, and aligned to any `t` at
/// least that scale its coefficient is `num_sum_at(vs, t)`.
pub proof fn lemma_num_sum_at(vs: Seq<Val>, t: nat)
    requires num_max_scale(vs) <= t,
    ensures
        num_sum(vs).1 == num_max_scale(vs),
        align(num_sum(vs).0, num_sum(vs).1, t) == num_sum_at(vs, t),
    decreases vs.len(),
{
    if vs.len() == 0 {
        assert(align(0, 0, t) == 0 * pow10(t)) by {}
        assert(0 * pow10(t) == 0) by (nonlinear_arith);
    } else {
        let d = vs.drop_last();
        assert(num_max_scale(d) <= num_max_scale(vs));
        lemma_num_sum_at(d, t);
        let (a, sa) = num_sum(d);
        match vs.last() {
            Val::Num { coeff, scale } => {
                let m = max_nat(sa, scale);
                let (x, y) = ((m - sa) as nat, (t - m) as nat);
                let (u, w) = ((m - scale) as nat, (t - m) as nat);
                lemma_pow10_add(x, y);
                lemma_pow10_add(u, w);
                assert((x + y) as nat == (t - sa) as nat);
                assert((u + w) as nat == (t - scale) as nat);
                let (px, py, pu) = (pow10(x), pow10(y), pow10(u));
                assert((a * px + coeff * pu) * py == a * (px * py) + coeff * (pu * py)) by (nonlinear_arith);
            },
            _ => {},
        }
    }
}

/// Every term of a numeric mass is nonnegative.
pub proof fn lemma_num_mass_term(coeff: int, k: nat)
    ensures abs(coeff) * pow10(k) >= 0, coeff != 0 ==> abs(coeff) * pow10(k) >= pow10(k) >= 1,
{
    lemma_pow10_positive(k);
    let (c, p) = (abs(coeff), pow10(k));
    assert(c * p >= 0) by (nonlinear_arith) requires c >= 0, p >= 1;
    if coeff != 0 {
        assert(c * p >= p) by (nonlinear_arith) requires c >= 1, p >= 1;
    }
}

pub proof fn lemma_num_mass_nonneg(vs: Seq<Val>, t: nat)
    ensures num_mass_at(vs, t) >= 0,
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_num_mass_nonneg(vs.drop_last(), t);
        if let Val::Num { coeff, scale } = vs.last() {
            lemma_num_mass_term(coeff, (t - scale) as nat);
        }
    }
}

/// Masses of prefixes grow: every term is nonnegative.
pub proof fn lemma_num_mass_prefix(vs: Seq<Val>, k: int, t: nat)
    requires 0 <= k <= vs.len(),
    ensures 0 <= num_mass_at(vs.take(k), t) <= num_mass_at(vs, t),
    decreases vs.len(),
{
    if k < vs.len() {
        let d = vs.drop_last();
        assert(d.take(k) =~= vs.take(k));
        lemma_num_mass_prefix(d, k, t);
        if let Val::Num { coeff, scale } = vs.last() {
            lemma_num_mass_term(coeff, (t - scale) as nat);
        }
    } else {
        assert(vs.take(k) =~= vs);
        lemma_num_mass_nonneg(vs, t);
    }
}

/// `num_max_scale`: the largest scale of the numeric values (0 when there is none), the result scale of the sum.
fn num_max_scale_exec(vs: &Vec<EVal>) -> (t: u32)
    ensures t as nat == num_max_scale(view_row(vs@)),
{
    let ghost g = view_row(vs@);
    let mut t: u32 = 0;
    let mut i: usize = 0;
    while i < vs.len()
        invariant
            i <= vs.len(), g == view_row(vs@),
            t as nat == num_max_scale(g.take(i as int)),
        decreases vs.len() - i,
    {
        proof { lemma_take_step(g, i as int); }
        match &vs[i] {
            EVal::Num { scale, .. } => {
                if *scale > t {
                    t = *scale;
                }
            },
            _ => {},
        }
        i = i + 1;
    }
    proof { assert(g.take(vs.len() as int) =~= g); }
    t
}

/// Exact numeric sum `(coefficient, scale)` of `spec::relation::num_sum`, or `Capacity` exactly outside the SUM
/// capacity condition (`sum_mass_fits(Numeric, ..)`). One pass after the result scale is known: the sum and the
/// absolute mass at that scale.
pub fn num_sum_exec(vs: &Vec<EVal>) -> (r: Result<(i128, u32), Capacity>)
    ensures
        match r {
            Ok((c, s)) => sum_mass_fits(NumKind::Numeric, view_row(vs@)) && (c as int, s as nat) == num_sum(view_row(vs@)),
            Err(_) => !sum_mass_fits(NumKind::Numeric, view_row(vs@)),
        },
{
    let ghost g = view_row(vs@);
    let t = num_max_scale_exec(vs);
    let ghost tn = t as nat;
    let mut c: i128 = 0;
    let mut m: i128 = 0;
    let mut i: usize = 0;
    while i < vs.len()
        invariant
            i <= vs.len(), g == view_row(vs@), tn == t as nat, tn == num_max_scale(g),
            m as int == num_mass_at(g.take(i as int), tn),
            c as int == num_sum_at(g.take(i as int), tn),
            0 <= m, -(m as int) <= c <= m,
        decreases vs.len() - i,
    {
        proof { lemma_take_step(g, i as int); }
        match &vs[i] {
            EVal::Num { coeff, scale } => {
                let ghost (cf, sc) = (*coeff as int, *scale as nat);
                proof {
                    lemma_num_max_scale_bound(g, i as int);
                    lemma_num_mass_prefix(g, i as int + 1, tn);
                }
                let ghost k = (tn - sc) as nat;
                if *coeff == 0 {
                    proof {
                        assert(abs(cf) * pow10(k) == 0) by (nonlinear_arith) requires cf == 0;
                        assert(align(cf, sc, tn) == 0) by (nonlinear_arith) requires cf == 0;
                    }
                } else {
                    proof { lemma_pow10_positive(k); }
                    let p = match pow10_exec(t - *scale) {
                        Some(p) => p,
                        None => {
                            proof { lemma_num_mass_term(cf, k); }
                            return Err(Capacity);
                        },
                    };
                    if *coeff == i128::MIN {
                        proof {
                            let (c1, p1) = (abs(cf), pow10(k));
                            assert(c1 * p1 >= c1) by (nonlinear_arith) requires c1 >= 1, p1 >= 1;
                        }
                        return Err(Capacity);
                    }
                    let a: i128 = if *coeff < 0 { -*coeff } else { *coeff };
                    proof {
                        assert(a as int * p as int >= 0) by (nonlinear_arith) requires a >= 1, p >= 1;
                    }
                    let term = match a.checked_mul(p) {
                        Some(x) => x,
                        None => return Err(Capacity),
                    };
                    let m2 = match m.checked_add(term) {
                        Some(x) => x,
                        None => return Err(Capacity),
                    };
                    proof {
                        assert(align(cf, sc, tn) == cf * pow10(k));
                        assert(a as int == abs(cf));
                        assert(cf * pow10(k) == (if cf < 0 { -(abs(cf) * pow10(k)) } else { abs(cf) * pow10(k) })) by (nonlinear_arith)
                            requires abs(cf) == (if cf < 0 { -cf } else { cf });
                    }
                    let st: i128 = if *coeff < 0 { -term } else { term };
                    c = c + st;
                    m = m2;
                }
            },
            _ => {},
        }
        i = i + 1;
    }
    proof {
        assert(g.take(vs.len() as int) =~= g);
        lemma_num_sum_at(g, tn);
        assert(align(num_sum(g).0, tn, tn) == num_sum(g).0 * pow10(0));
        assert(pow10(0) == 1);
    }
    Ok((c, t))
}

// ------------------------------------------------------------------ aggregate values of one group

/// `spec::relation::agg_value` of one aggregate over its argument column.
pub fn exec_agg_value(a: &EAgg, vs: &Vec<EVal>) -> (r: Outcome<EVal>)
    requires row_ts_ok(view_row(vs@)),
    ensures
        match r {
            Ok(res) => fits_agg_value(view_agg(*a), view_row(vs@))
                && view_result(res) == agg_value(view_agg(*a), view_row(vs@))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_agg_value(view_agg(*a), view_row(vs@)),
        },
    decreases a,
{
    let ghost g = view_row(vs@);
    match a {
        EAgg::CountStar => Ok(int_result_exec(IntKind::Int8, vs.len() as i128)),
        EAgg::Count(_) => {
            let n = count_non_null_exec(vs);
            Ok(int_result_exec(IntKind::Int8, n as i128))
        },
        EAgg::Sum { kind, arg } => {
            if !all_of_kind_exec(*kind, vs) {
                return Ok(Err(SqlError::TypeError));
            }
            match kind {
                NumKind::Numeric => {
                    let (c, s) = match num_sum_exec(vs) {
                        Ok(p) => p,
                        Err(cap) => return Err(cap),
                    };
                    if count_non_null_exec(vs) == 0 {
                        return Ok(Ok(EVal::Null));
                    }
                    proof { lemma_num_in_range_small(c as int, s as nat); }
                    Ok(Ok(EVal::Num { coeff: c, scale: s }))
                },
                _ => {
                    let sum = int_sum_exec(vs);
                    if count_non_null_exec(vs) == 0 {
                        return Ok(Ok(EVal::Null));
                    }
                    match kind {
                        NumKind::Int4 => Ok(int_result_exec(IntKind::Int8, sum)),
                        _ => {
                            proof { lemma_num_in_range_small(sum as int, 0); }
                            Ok(Ok(EVal::Num { coeff: sum, scale: 0 }))
                        },
                    }
                },
            }
        },
        EAgg::Min(_) => Ok(exec_min(vs)),
        EAgg::Max(_) => Ok(exec_max(vs)),
        EAgg::Avg { kind, .. } => exec_avg(*kind, vs),
        EAgg::DistinctAgg(inner) => {
            let d = distinct_vals_exec(vs);
            proof {
                // The distinct values are argument values, so they keep the timestamp invariant.
                let gd = view_row(d@);
                lemma_distinct_vals_sub(g);
                assert forall|m: int| 0 <= m < gd.len() implies val_ts_ok(#[trigger] gd[m]) by {
                    let i = choose|i: int| 0 <= i < g.len() && g[i] == gd[m];
                }
            }
            exec_agg_value(inner, &d)
        },
    }
}

/// Column `j` of the argument rows.
fn column_exec(args: &Vec<ERow>, j: usize) -> (col: Vec<EVal>)
    requires
        forall|i: int| 0 <= i < args.len() ==> j < (#[trigger] args@[i]).len(),
        rows_ts_ok(view_rows(args@)),
    ensures
        view_row(col@) == column(view_rows(args@), j as int),
        row_ts_ok(view_row(col@)),
{
    let ghost ga = view_rows(args@);
    let mut col: Vec<EVal> = Vec::new();
    let mut i: usize = 0;
    while i < args.len()
        invariant
            i <= args.len(), ga == view_rows(args@),
            forall|k: int| 0 <= k < args.len() ==> j < (#[trigger] args@[k]).len(),
            view_row(col@) == column(ga.take(i as int), j as int),
        decreases args.len() - i,
    {
        let ghost prev = view_row(col@);
        let v = clone_val(&args[i][j]);
        col.push(v);
        proof {
            assert(view_row(col@) =~= prev.push(ga[i as int][j as int]));
            assert(column(ga.take(i as int + 1), j as int) =~= column(ga.take(i as int), j as int).push(ga[i as int][j as int]));
        }
        i = i + 1;
    }
    proof {
        assert(ga.take(args.len() as int) =~= ga);
        assert forall|i: int| 0 <= i < view_row(col@).len() implies val_ts_ok(#[trigger] view_row(col@)[i]) by {
            assert(row_ts_ok(ga[i]));
            assert(view_row(col@)[i] == ga[i][j as int]);
        }
    }
    col
}

/// `spec::relation::agg_row`: all aggregates of one group, left to right.
pub fn exec_agg_row(aggs: &Vec<EAgg>, args: &Vec<ERow>) -> (r: Outcome<ERow>)
    requires
        forall|i: int| 0 <= i < args.len() ==> (#[trigger] args@[i]).len() == aggs.len(),
        rows_ts_ok(view_rows(args@)),
    ensures
        match r {
            Ok(res) => fits_agg_row(view_aggs(aggs@), view_rows(args@))
                && match res {
                    Ok(row) => agg_row(view_aggs(aggs@), view_rows(args@)) == Ok::<Row, SqlError>(view_row(row@))
                        && row_ts_ok(view_row(row@)),
                    Err(e) => agg_row(view_aggs(aggs@), view_rows(args@)) == Err::<Row, SqlError>(e),
                },
            Err(_) => !fits_agg_row(view_aggs(aggs@), view_rows(args@)),
        },
{
    let ghost ga = view_aggs(aggs@);
    let ghost gargs = view_rows(args@);
    let ghost rs = agg_value_results(ga, gargs);
    let ghost fs = agg_value_fs(ga, gargs);
    proof { lemma_agg_row(ga, gargs); }
    let mut out: ERow = Vec::new();
    let mut j: usize = 0;
    while j < aggs.len()
        invariant
            j <= aggs.len(), ga == view_aggs(aggs@), gargs == view_rows(args@),
            rs == agg_value_results(ga, gargs),
            fs == agg_value_fs(ga, gargs),
            forall|i: int| 0 <= i < args.len() ==> (#[trigger] args@[i]).len() == aggs.len(),
            rows_ts_ok(gargs),
            out.len() == j,
            forall|k: int| 0 <= k < j ==> #[trigger] rs[k] == Ok::<Val, SqlError>(view_row(out@)[k]),
            ok_before(rs, j as int), fits_before(fs, j as int),
            row_ts_ok(view_row(out@)),
        decreases aggs.len() - j,
    {
        let col = column_exec(args, j);
        proof { assert(ga[j as int] == view_agg(aggs@[j as int])); }
        match exec_agg_value(&aggs[j], &col) {
            Err(cap) => {
                proof { lemma_each_capacity(rs, fs, j as int); }
                return Err(cap);
            },
            Ok(Err(e)) => {
                proof { lemma_each_err(rs, fs, j as int); }
                return Ok(Err(e));
            },
            Ok(Ok(v)) => {
                let ghost prev = view_row(out@);
                out.push(v);
                proof {
                    assert(view_row(out@) =~= prev.push(v@));
                }
            },
        }
        j = j + 1;
    }
    proof { lemma_each_done(rs, fs, view_row(out@)); }
    Ok(Ok(out))
}

} // verus!
