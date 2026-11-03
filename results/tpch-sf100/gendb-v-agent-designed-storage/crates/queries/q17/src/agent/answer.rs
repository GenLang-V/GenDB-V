//! The statement's outcome from the scan's totals, for every database bound to the parts.
//!
//! The scans compute the SUM and whether a row is kept as sums over the stored part rows of per-part totals over
//! the lineitem value rows in index order (fast path) or stored order (general path); both orders are
//! permutations of the database's lineitem value rows and the stored part rows are its part value rows, so the
//! totals are the statement's (`totals_ok`, `lemma_totals_*`). The aggregate row is then `aval(sum, any)` and the
//! statement divides it by `7.0` (`lemma_outcome`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::fns::div::*;
use crate::link::join::*;
use crate::exec::relational::domain::fits_query;
use crate::gendb_entry::{bound_db, capacity_domain};
use crate::gendb_entry::stores::StoresView;
use crate::query::*;
use crate::stores::li_pkqty::interface as LI;
use crate::stores::custpart::interface::common::colfmt as CF;
use super::vals::*;
use super::typed::*;
use super::sqlmain::*;
use super::bind::*;
use super::scan::{fsum, fcnt, fmass, mass_max};
use super::general::{gsum, gcnt, gmass};

verus! {

/// Every bound database's totals are `sum` and `any`.
pub open spec fn totals_ok(sv: StoresView, ps: Seq<Literal>, sum: int, any: bool) -> bool {
    forall|db: Database| #[trigger] bound_db(sv, db) ==> tot_sum(db, ps) == sum && (tot_cnt(db, ps) > 0) == any
}

/// The aggregate row's value from the totals.
pub open spec fn aval(sum: int, any: bool) -> Val {
    if any { Val::Num { coeff: sum, scale: 2 } } else { Val::Null }
}

/// Per part row, the totals over a permutation of the database's lineitem value rows are the database's.
proof fn lemma_perm_parts(db: Database, ys: Seq<Row>, zs: Seq<Row>, b: Seq<u8>, c: Seq<u8>)
    requires ys.to_multiset() == ys_of(db).to_multiset(),
    ensures
        sum_of(zs, |z: Row| psum(ys, b, c, z)) == sum_of(zs, |z: Row| psum(ys_of(db), b, c, z)),
        sum_of(zs, |z: Row| pcnt(ys, b, c, z)) == sum_of(zs, |z: Row| pcnt(ys_of(db), b, c, z)),
        sum_of(zs, |z: Row| pmass(ys, b, c, z)) == sum_of(zs, |z: Row| pmass(ys_of(db), b, c, z)),
{
    assert forall|i: int| 0 <= i < zs.len() implies (|z: Row| psum(ys, b, c, z))(#[trigger] zs[i]) == (|z: Row| psum(ys_of(db), b, c, z))(zs[i])
        && (|z: Row| pcnt(ys, b, c, z))(zs[i]) == (|z: Row| pcnt(ys_of(db), b, c, z))(zs[i])
        && (|z: Row| pmass(ys, b, c, z))(zs[i]) == (|z: Row| pmass(ys_of(db), b, c, z))(zs[i]) by {
        lemma_perm_part(ys, ys_of(db), b, c, zs[i]);
    }
    lemma_sum_of_ext(zs, |z: Row| psum(ys, b, c, z), |z: Row| psum(ys_of(db), b, c, z));
    lemma_sum_of_ext(zs, |z: Row| pcnt(ys, b, c, z), |z: Row| pcnt(ys_of(db), b, c, z));
    lemma_sum_of_ext(zs, |z: Row| pmass(ys, b, c, z), |z: Row| pmass(ys_of(db), b, c, z));
}

/// The fast path's totals (index order) are every bound database's.
pub proof fn lemma_totals_fast(sv: StoresView, ps: Seq<Literal>, sum: int, any: bool)
    requires
        LI::has_idx(sv.li_pkqty),
        sum == sum_of(zrows(sv.custpart), fsum(sv.li_pkqty, ptext(ps[0]), ptext(ps[1]))),
        any == (sum_of(zrows(sv.custpart), fcnt(sv.li_pkqty, ptext(ps[0]), ptext(ps[1]))) > 0),
    ensures totals_ok(sv, ps, sum, any),
{
    let (b, c) = (ptext(ps[0]), ptext(ps[1]));
    let (lp, cp) = (sv.li_pkqty, sv.custpart);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies tot_sum(db, ps) == sum && (tot_cnt(db, ps) > 0) == any by {
        lemma_li_link(sv, db);
        lemma_pa_link(sv, db);
        lemma_perm_parts(db, irows(lp), zrows(cp), b, c);
        lemma_sum_of_ext(zrows(cp), fsum(lp, b, c), |z: Row| psum(irows(lp), b, c, z));
        lemma_sum_of_ext(zrows(cp), fcnt(lp, b, c), |z: Row| pcnt(irows(lp), b, c, z));
    }
}

/// The general path's totals (stored order) are every bound database's.
pub proof fn lemma_totals_gen(sv: StoresView, ps: Seq<Literal>, sum: int, any: bool)
    requires
        sum == sum_of(zrows(sv.custpart), gsum(sv.li_pkqty, ptext(ps[0]), ptext(ps[1]))),
        any == (sum_of(zrows(sv.custpart), gcnt(sv.li_pkqty, ptext(ps[0]), ptext(ps[1]))) > 0),
    ensures totals_ok(sv, ps, sum, any),
{
    let (b, c) = (ptext(ps[0]), ptext(ps[1]));
    let (lp, cp) = (sv.li_pkqty, sv.custpart);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies tot_sum(db, ps) == sum && (tot_cnt(db, ps) > 0) == any by {
        lemma_li_link(sv, db);
        lemma_pa_link(sv, db);
        lemma_perm_parts(db, srows(lp), zrows(cp), b, c);
        lemma_sum_of_ext(zrows(cp), gsum(lp, b, c), |z: Row| psum(srows(lp), b, c, z));
        lemma_sum_of_ext(zrows(cp), gcnt(lp, b, c), |z: Row| pcnt(srows(lp), b, c, z));
    }
}

/// No dictionary entry is `$1` (or none is `$2`): no part row matches, the totals are 0 and nothing is kept.
pub proof fn lemma_totals_none(sv: StoresView, ps: Seq<Literal>)
    requires
        pa_facts(sv.custpart),
        (forall|e: int| 0 <= e < n_bd(sv.custpart) ==> CF::text_of(bd_o(sv.custpart), bd_y(sv.custpart), e) != ptext(ps[0]))
        || (forall|e: int| 0 <= e < n_cd(sv.custpart) ==> CF::text_of(cd_o(sv.custpart), cd_y(sv.custpart), e) != ptext(ps[1])),
    ensures totals_ok(sv, ps, 0, false),
{
    let (b, c) = (ptext(ps[0]), ptext(ps[1]));
    let cp = sv.custpart;
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies tot_sum(db, ps) == 0 && (tot_cnt(db, ps) > 0) == false by {
        lemma_pa_link(sv, db);
        let ys = ys_of(db);
        let zs = zs_of(db);
        assert forall|j: int| 0 <= j < zs.len() implies (|z: Row| psum(ys, b, c, z))(#[trigger] zs[j]) == 0
            && (|z: Row| pcnt(ys, b, c, z))(zs[j]) == 0 by {
            let z = zs[j];
            assert(z == zrow(cp, j));
            assert(0 <= bidx_at(cp, j) < n_bd(cp) && 0 <= cidx_at(cp, j) < n_cd(cp));
            assert(z[1] != Val::Text(b) || z[2] != Val::Text(c));
            assert forall|i: int| 0 <= i < ys.len() implies !kept(ys, b, c, #[trigger] ys[i], z) by {}
            lemma_sum_of_zero(ys, tsum(ys, b, c, z));
            lemma_sum_of_zero(ys, tcnt(ys, b, c, z));
        }
        lemma_sum_of_zero(zs, |z: Row| psum(ys, b, c, z));
        lemma_sum_of_zero(zs, |z: Row| pcnt(ys, b, c, z));
    }
}

/// The total masses are bounded: each typed lineitem row is kept by at most one part row.
pub proof fn lemma_masses(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db),
    ensures
        sum_of(zrows(sv.custpart), gmass(sv.li_pkqty, ptext(ps[0]), ptext(ps[1]))) <= mass_max(),
        LI::has_idx(sv.li_pkqty) ==> sum_of(zrows(sv.custpart), fmass(sv.li_pkqty, ptext(ps[0]), ptext(ps[1]))) <= mass_max(),
{
    let (b, c) = (ptext(ps[0]), ptext(ps[1]));
    let (lp, cp) = (sv.li_pkqty, sv.custpart);
    lemma_li_link(sv, db);
    lemma_pa_link(sv, db);
    lemma_totals(db, ps);
    assert(tot_mass(db, ps) <= 0xffff_ffff_ffff_ffff * p15()) by (nonlinear_arith)
        requires tot_mass(db, ps) <= db.tables[0].len() * p15(), db.tables[0].len() <= 0xffff_ffff_ffff_ffff,
            p15() == 1_000_000_000_000_000;
    lemma_perm_parts(db, srows(lp), zrows(cp), b, c);
    lemma_sum_of_ext(zrows(cp), gmass(lp, b, c), |z: Row| pmass(srows(lp), b, c, z));
    if LI::has_idx(lp) {
        lemma_perm_parts(db, irows(lp), zrows(cp), b, c);
        lemma_sum_of_ext(zrows(cp), fmass(lp, b, c), |z: Row| pmass(irows(lp), b, c, z));
    }
}

/// The statement for a bound database from the totals: the aggregate row is `aval`, divided by `7.0`.
pub proof fn lemma_outcome(sv: StoresView, db: Database, ps: Seq<Literal>, sum: int, any: bool)
    requires
        bound_db(sv, db),
        param_domain(ps),
        totals_ok(sv, ps, sum, any),
    ensures
        denote_body(db, query_spec_at(ps)) == match apply_div(ScalarFn::DivNumeric, seq![aval(sum, any), seven()]) {
            Ok(w) => Ok::<Relation, SqlError>(seq![seq![w]]),
            Err(e) => Err::<Relation, SqlError>(e),
        },
        !fits_div(ScalarFn::DivNumeric, seq![aval(sum, any), seven()]) ==> !capacity_domain(db, query_spec_at(ps)),
        query_spec_at(ps).keys.len() == 0,
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
    lemma_li_link(sv, db);
    lemma_totals(db, ps);
    lemma_eval_agg(db, ps);
    assert(tot_sum(db, ps) == sum && (tot_cnt(db, ps) > 0) == any);
    assert(agg_val(db, ps) == aval(sum, any));
    lemma_final(db, ps, aval(sum, any));
    lemma_ast(ps);
}

} // verus!
