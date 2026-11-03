//! The two SUM aggregates over the kept rows.
//!
//! The arguments of the kept rows are `[av0(z), av1(z)]` (`sqlrow::lemma_row_args`). Column 1 is the value at
//! scale 4 on every row: its exact sum is the sum accumulator at scale 4 (`lemma_col1`). Column 0 is the value at
//! scale 4 on promotion rows and the numeric 0 of scale 0 elsewhere: its exact sum is the promotion-sum accumulator,
//! at scale 4 when some promotion row is kept and at scale 0 otherwise (`lemma_col0`). Their absolute masses are the
//! mass accumulators. `lemma_agg_row` gives the aggregate row from the stored totals; `lemma_agg_capacity` the
//! capacity violation when the mass of the sum exceeds `i128`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::link::join::{sum_of, keep, lemma_keep_members};
use crate::link::expr::lemma_align_same;
use crate::link::capacity::{lemma_sum_inside_ok, aggs_ok_inside};
use crate::exec::relational::domain::*;
use crate::bridge::collect::lemma_collect_all;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use super::model::*;
use super::terms::*;
use super::sqlrow::*;
use super::joinsum::*;
use super::general::{Tot, tot_ok, lemma_sum_within};
use super::kernel::Win;
use super::answer::agg_row_of;

verus! {

/// Column 0 (the CASE) of the kept rows' arguments.
pub open spec fn col0(ks: Seq<Row>) -> Seq<Val> {
    ks.map_values(|x: Row| av0(zx(x)))
}

/// Column 1 (the value) of the kept rows' arguments.
pub open spec fn col1(ks: Seq<Row>) -> Seq<Val> {
    ks.map_values(|x: Row| av1(zx(x)))
}

/// The argument rows of the kept rows.
pub open spec fn args_of(ks: Seq<Row>) -> Seq<Row> {
    ks.map_values(|x: Row| seq![av0(zx(x)), av1(zx(x))])
}

/// Every row satisfies the condition.
pub open spec fn all_q(ks: Seq<Row>, lo: int, hi: int) -> bool {
    forall|i: int| 0 <= i < ks.len() ==> qx(lo, hi)(#[trigger] ks[i])
}

/// One row fewer.
pub proof fn lemma_all_q_prefix(ks: Seq<Row>, lo: int, hi: int)
    requires all_q(ks, lo, hi), ks.len() > 0,
    ensures all_q(ks.drop_last(), lo, hi), qx(lo, hi)(ks.last()),
{
    assert forall|i: int| 0 <= i < ks.drop_last().len() implies qx(lo, hi)(#[trigger] ks.drop_last()[i]) by {
        assert(ks.drop_last()[i] == ks[i]);
    }
}

pub proof fn lemma_pow10_zero()
    ensures pow10(0) == 1,
{
    assert(pow10(0) == 1) by (compute);
}

/// Column 1: every value numeric at scale 4; exact sum and mass are the sum and mass accumulators.
pub proof fn lemma_col1(ks: Seq<Row>, lo: int, hi: int)
    requires all_q(ks, lo, hi),
    ensures
        all_of_kind(NumKind::Numeric, col1(ks)),
        count_non_null(col1(ks)) == ks.len(),
        num_sum(col1(ks)) == (sum_of(ks, tx(3, lo, hi)), if ks.len() > 0 { 4nat } else { 0nat }),
        num_max_scale(col1(ks)) == if ks.len() > 0 { 4nat } else { 0nat },
        num_mass_at(col1(ks), 4) == sum_of(ks, tx(4, lo, hi)),
    decreases ks.len(),
{
    let vs = col1(ks);
    if ks.len() > 0 {
        let d = ks.drop_last();
        lemma_all_q_prefix(ks, lo, hi);
        lemma_col1(d, lo, hi);
        assert(vs.drop_last() =~= col1(d));
        let x = ks.last();
        let c = zv(zx(x));
        assert(vs.last() == Val::Num { coeff: c, scale: 4 });
        assert(tx(3, lo, hi)(x) == c);
        assert(tx(4, lo, hi)(x) == abs(c));
        lemma_pow10_zero();
        lemma_align_same(c, 4);
        let s = num_sum(col1(d));
        if d.len() == 0 {
            assert(s == (0int, 0nat));
            assert(align(0, 0, 4) == 0);
        } else {
            lemma_align_same(s.0, 4);
        }
    }
}

/// Column 0: every value numeric; exact sum is the promotion-sum accumulator at scale 4 when some promotion row is
/// kept, else 0 at scale 0; the mass at scale 4 is the promotion-mass accumulator.
pub proof fn lemma_col0(ks: Seq<Row>, lo: int, hi: int)
    requires all_q(ks, lo, hi),
    ensures
        all_of_kind(NumKind::Numeric, col0(ks)),
        count_non_null(col0(ks)) == ks.len(),
        sum_of(ks, tx(1, lo, hi)) >= 0,
        num_sum(col0(ks)) == (sum_of(ks, tx(2, lo, hi)), if sum_of(ks, tx(1, lo, hi)) > 0 { 4nat } else { 0nat }),
        num_max_scale(col0(ks)) == if sum_of(ks, tx(1, lo, hi)) > 0 { 4nat } else { 0nat },
        num_mass_at(col0(ks), 4) == sum_of(ks, tx(5, lo, hi)),
        sum_of(ks, tx(1, lo, hi)) == 0 ==> sum_of(ks, tx(2, lo, hi)) == 0 && num_mass_at(col0(ks), 0) == 0,
    decreases ks.len(),
{
    let vs = col0(ks);
    if ks.len() > 0 {
        let d = ks.drop_last();
        lemma_all_q_prefix(ks, lo, hi);
        lemma_col0(d, lo, hi);
        assert(vs.drop_last() =~= col0(d));
        let x = ks.last();
        let z = zx(x);
        let c = zv(z);
        lemma_pow10_zero();
        let s = num_sum(col0(d));
        if zp(z) {
            assert(vs.last() == Val::Num { coeff: c, scale: 4 });
            assert(tx(1, lo, hi)(x) == 1);
            assert(tx(2, lo, hi)(x) == c);
            assert(tx(5, lo, hi)(x) == abs(c));
            lemma_align_same(c, 4);
            assert(abs(c) * pow10((4 - 4) as nat) == abs(c));
            assert(num_mass_at(vs, 4) == num_mass_at(col0(d), 4) + abs(c) * pow10((4 - 4) as nat));
            if sum_of(d, tx(1, lo, hi)) > 0 {
                lemma_align_same(s.0, 4);
            } else {
                assert(s == (0int, 0nat));
                assert(align(0, 0, 4) == 0);
            }
        } else {
            assert(vs.last() == Val::Num { coeff: 0, scale: 0 });
            assert(tx(1, lo, hi)(x) == 0);
            assert(tx(2, lo, hi)(x) == 0);
            assert(tx(5, lo, hi)(x) == 0);
            lemma_align_same(s.0, s.1);
            let f = pow10((s.1 - 0) as nat);
            assert(0 * f == 0) by (nonlinear_arith);
            assert(align(0, 0, s.1) == 0);
            let f4 = pow10((4 - 0) as nat);
            assert(abs(0) * f4 == 0) by (nonlinear_arith);
            assert(num_mass_at(vs, 4) == num_mass_at(col0(d), 4) + abs(0) * f4);
            let f0 = pow10((0 - 0) as nat);
            assert(abs(0) * f0 == 0) by (nonlinear_arith);
            assert(num_mass_at(vs, 0) == num_mass_at(col0(d), 0) + abs(0) * f0);
        }
    }
}

/// The columns of the argument rows.
pub proof fn lemma_columns(ks: Seq<Row>)
    ensures
        column(args_of(ks), 0) == col0(ks),
        column(args_of(ks), 1) == col1(ks),
        args_of(ks).len() == ks.len(),
{
    assert(column(args_of(ks), 0) =~= col0(ks));
    assert(column(args_of(ks), 1) =~= col1(ks));
}

/// The promotion terms are within the promotion mass, and that mass within the mass.
pub proof fn lemma_term_bounds(lo: int, hi: int)
    ensures
        forall|x: Row| -tx(5, lo, hi)(x) <= #[trigger] tx(2, lo, hi)(x) <= tx(5, lo, hi)(x),
        forall|x: Row| -tx(4, lo, hi)(x) <= #[trigger] tx(5, lo, hi)(x) <= tx(4, lo, hi)(x),
        forall|x: Row| -tx(4, lo, hi)(x) <= #[trigger] tx(3, lo, hi)(x) <= tx(4, lo, hi)(x),
{
    assert forall|x: Row| -tx(5, lo, hi)(x) <= #[trigger] tx(2, lo, hi)(x) <= tx(5, lo, hi)(x) by {
        let z = zx(x);
        lemma_contrib_bounds(zq(lo, hi, z), zp(z), zv(z));
    }
    assert forall|x: Row| -tx(4, lo, hi)(x) <= #[trigger] tx(5, lo, hi)(x) <= tx(4, lo, hi)(x) by {
        let z = zx(x);
        lemma_contrib_bounds(zq(lo, hi, z), zp(z), zv(z));
    }
    assert forall|x: Row| -tx(4, lo, hi)(x) <= #[trigger] tx(3, lo, hi)(x) <= tx(4, lo, hi)(x) by {
        let z = zx(x);
        lemma_contrib_bounds(zq(lo, hi, z), zp(z), zv(z));
    }
}

/// The aggregate row of the kept rows is the aggregate row of the totals.
pub proof fn lemma_agg_row(sv: StoresView, db: Database, w: Win, t: Tot)
    requires
        bound_db(sv, db),
        tot_ok(t, sv.facts, sv.custpart, w),
    ensures ({
        let ks = kept_of(db, w.lo as int, w.hi as int);
        agg_row(aggs_q(), args_of(ks)) == Ok::<Row, SqlError>(agg_row_of(t))
    }),
{
    let (lo, hi) = (w.lo as int, w.hi as int);
    let (fp, cp) = (sv.facts, sv.custpart);
    let n = n_li(fp);
    let ks = kept_of(db, lo, hi);
    lemma_keep_members(prod_of(db), qx(lo, hi));
    assert(all_q(ks, lo, hi));
    lemma_col0(ks, lo, hi);
    lemma_col1(ks, lo, hi);
    lemma_columns(ks);
    lemma_kept_count(sv, db, lo, hi);
    lemma_sum_chain(sv, db, 1, lo, hi);
    lemma_sum_chain(sv, db, 2, lo, hi);
    lemma_sum_chain(sv, db, 3, lo, hi);
    lemma_sum_chain(sv, db, 4, lo, hi);
    lemma_term_bounds(lo, hi);
    lemma_sum_within(ks, tx(5, lo, hi), tx(4, lo, hi));
    let a0 = Agg::Sum { kind: NumKind::Numeric, arg: case_expr() };
    let a1 = Agg::Sum { kind: NumKind::Numeric, arg: val_expr() };
    let v0 = col0(ks);
    let v1 = col1(ks);
    // both masses fit: the values are Ok
    assert(fits_agg_value(a1, v1));
    assert(fits_agg_value(a0, v0)) by {
        if sum_of(ks, tx(1, lo, hi)) == 0 {
            assert(num_mass_at(v0, 0) == 0);
        }
    }
    lemma_sum_inside_ok(NumKind::Numeric, case_expr(), v0);
    lemma_sum_inside_ok(NumKind::Numeric, val_expr(), v1);
    let r0 = agg_value(a0, v0);
    let r1 = agg_value(a1, v1);
    let row = agg_row_of(t);
    assert(r0 == Ok::<Val, SqlError>(row[0]));
    assert(r1 == Ok::<Val, SqlError>(row[1]));
    let rs = Seq::new(2, |j: int| agg_value(aggs_q()[j], column(args_of(ks), j)));
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(row[j]) by {
        if j == 0 {
            assert(aggs_q()[0] == a0);
        } else {
            assert(aggs_q()[1] == a1);
        }
    }
    lemma_collect_all(rs, row);
    assert(row.len() == 2);
}

/// The mass of the sum beyond `i128`: the aggregate leaves its capacity domain on column 1, and column 0 is Ok
/// whenever it is inside its own.
pub proof fn lemma_agg_capacity(sv: StoresView, db: Database, w: Win)
    requires
        bound_db(sv, db),
        tot(sv.facts, sv.custpart, 4, w.lo as int, w.hi as int, 0, n_li(sv.facts)) > i128::MAX,
    ensures ({
        let ks = kept_of(db, w.lo as int, w.hi as int);
        &&& !fits_agg_value(aggs_q()[1], column(args_of(ks), 1))
        &&& aggs_ok_inside(aggs_q(), args_of(ks))
    }),
{
    let (lo, hi) = (w.lo as int, w.hi as int);
    let ks = kept_of(db, lo, hi);
    lemma_keep_members(prod_of(db), qx(lo, hi));
    assert(all_q(ks, lo, hi));
    lemma_col0(ks, lo, hi);
    lemma_col1(ks, lo, hi);
    lemma_columns(ks);
    lemma_sum_chain(sv, db, 4, lo, hi);
    assert(ks.len() > 0) by {
        if ks.len() == 0 {
            assert(sum_of(ks, tx(4, lo, hi)) == 0);
        }
    }
    let a0 = Agg::Sum { kind: NumKind::Numeric, arg: case_expr() };
    let a1 = Agg::Sum { kind: NumKind::Numeric, arg: val_expr() };
    assert(aggs_q()[1] == a1);
    assert(aggs_q()[0] == a0);
    assert(!fits_agg_value(a1, col1(ks)));
    assert forall|j: int| 0 <= j < aggs_q().len() && #[trigger] fits_agg_value(aggs_q()[j], column(args_of(ks), j))
        implies agg_value(aggs_q()[j], column(args_of(ks), j)) is Ok by {
        if j == 0 {
            lemma_sum_inside_ok(NumKind::Numeric, case_expr(), col0(ks));
        }
    }
}

} // verus!
