//! The early exits of `query`, each as a statement about every bound database: the empty answer (no outer group),
//! and the five Capacity exits (a filing's run mass, an outer group's mass, a per-cik group's mass, the AVG's mass,
//! the AVG's division).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::aggs::avg::*;
use crate::spec::fns::div::num_div_fits;
use crate::exec::relational::domain::{fits_query, num_mass_at, num_max_scale, sum_mass_fits};
use crate::exec::aggs::avg::fits_avg_value;
use crate::query::query_spec_at;
use crate::link::query::{QuerySpec, gsum, gabs, gcount, gkeys, full_row, lemma_gkeys};
use crate::link::join::keep;
use crate::link::expr::i128_max;
use crate::link::capacity::lemma_num_mass_uniform;
use crate::stores::num::interface as num_if;
use crate::agent::common::sort::Filing;
use crate::agent::common::sums::*;
use crate::agent::ast::*;
use crate::agent::nf::*;
use crate::agent::numlink::*;
use crate::agent::scan::*;
use crate::agent::groups::*;
use crate::agent::link::*;
use crate::agent::eval::*;
use crate::agent::assemble::*;
use crate::agent::cap::*;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

// ------------------------------------------------------------------------------------------------ empty answers

/// No outer group: the statement's rows are empty.
pub proof fn lemma_empty_answer(db: Database, p0: Seq<u8>, p1: int)
    requires rows_ok(db), int_in_range(IntKind::Int4, p1), gkeys(g_top(p0, p1), joined(db)).len() == 0,
    ensures ordered_ok(db, query_spec_at(lits(p0, p1)), Ok::<Relation, SqlError>(Seq::empty())),
{
    let ps = lits(p0, p1);
    lemma_query_shape(ps);
    assert(sum_caps(g_top(p0, p1), joined(db)));
    lemma_eval_group_top(db, p0, p1);
    let grows = gkeys(g_top(p0, p1), joined(db)).map_values(|k: Row| full_row(g_top(p0, p1), joined(db), k));
    assert(grows =~= Seq::<Row>::empty());
    crate::agent::nf::lemma_filter_iff(db, Seq::<Val>::empty(), pred_having(ps), q_group_top(ps), grows, hv_none());
    assert(keep(grows, hv_none()) =~= Seq::<Row>::empty());
    let p = Seq::<Row>::empty();
    assert(sorted_by(query_spec_at(ps).keys, p));
    assert(slice_rows(p, 0, Some(100nat)) =~= Seq::<Row>::empty());
}

pub open spec fn hv_none() -> spec_fn(Row) -> bool {
    |r: Row| false
}

/// `$1` is not a unit of `num`: no outer group.
pub proof fn lemma_no_uom(db: Database, c: ScanCtx, p0: Seq<u8>)
    requires
        bound(db, c), num_if::num_layout_ok(c.np),
        forall|k: int| 0 <= k < num_if::uom_count(c.np) ==> num_if::dict_entry(c.np, num_if::P_UOM_OFF, k) != p0,
    ensures gkeys(g_top(p0, c.p1), joined(db)).len() == 0,
{
    let g = g_top(p0, c.p1);
    let xs = joined(db);
    lemma_gkeys(g, xs);
    if gkeys(g, xs).len() > 0 {
        let kk = gkeys(g, xs)[0];
        assert(gkeys(g, xs).contains(kk));
        assert(gcount(g, xs, kk) > 0);
        lemma_top_key(p0, c.p1);
        lemma_acc_by_sub(db, p0, c.p1, g, |s: Row| key_top_s(s), kk);
        let (nr, sr) = (num_rel(db), sub_rel(db));
        let st = sub_term(c.p1, p0, nr, |s: Row| key_top_s(s), kk, w_one());
        assert forall|j: int| 0 <= j < sr.len() implies st(#[trigger] sr[j]) == 0 by {
            assert(sub_row_ok(sr[j]));
            let a = sr[j][0]->Text_0;
            assert forall|r: int| 0 <= r < num_if::run_count(c.np) implies !#[trigger] run_key_is(c.np, r, p0, a) by {
                let ru = num_if::u64s(c.np, num_if::P_RUN_UOM);
                assert(ru[r] < num_if::uom_count(c.np));
            }
            lemma_fsum_none(db, c.np, p0, sr[j], a, w_one());
        }
        crate::link::join::lemma_sum_of_zero(sr, st);
        assert(false);
    }
}

/// No group of the sorted filings: no outer group.
pub proof fn lemma_no_filings(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(g, l, true), g.sum@.len() == 0,
    ensures gkeys(g_top(p0, c.p1), joined(db)).len() == 0,
{
    lemma_keys_multiset(db, c, p0, l, g, true);
}

// ------------------------------------------------------------------------------------------------ Capacity

/// The accumulators of any valid computed key over the sorted filings.
pub proof fn lemma_key_acc(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, k: (u64, u64), by_name: bool)
    requires bound(db, c), run_ok(c, p0, l), key_valid(c.sp, k, by_name), !by_name ==> k.1 == 0,
    ensures
        ssum(l, sum_f(k, by_name)) == gsum(gsel(p0, c.p1, by_name), joined(db), kspec(c.sp, k, by_name), 0),
        ssum(l, mass_f(k, by_name)) == gabs(gsel(p0, c.p1, by_name), joined(db), kspec(c.sp, k, by_name), 0),
{
    lemma_ssum_perm(l, filt(c, 0, n_sub(c)), sum_f(k, by_name));
    lemma_ssum_perm(l, filt(c, 0, n_sub(c)), mass_f(k, by_name));
    lemma_filt_total(c, k, by_name, 0);
    lemma_filt_total(c, k, by_name, 1);
    lemma_acc(db, c, p0, k, by_name, 0);
    lemma_acc(db, c, p0, k, by_name, 1);
}

/// The key of a filing of the sorted list is valid.
pub proof fn lemma_filing_key(c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, t: int, by_name: bool)
    requires run_ok(c, p0, l), 0 <= t < l.len(),
    ensures key_valid(c.sp, gkey(l[t], by_name), by_name), !by_name ==> gkey(l[t], by_name).1 == 0,
{
    lemma_l_member(c, p0, l, t);
    let p = choose|p: int| 0 <= p < n_sub(c) && qualifies(c, row_at(c, p)) && #[trigger] entry(c, row_at(c, p)) == l[t];
    crate::stores::sub_fy::interface::common::perm::lemma_permutation_facts(
        crate::stores::sub_fy::interface::fy_order(c.sp), n_sub(c) as nat);
    lemma_ekey_valid(c, row_at(c, p), by_name);
}

/// A filing whose run's mass exceeds `i128::MAX`.
pub proof fn lemma_cap_big(db: Database, c: ScanCtx, p0: Seq<u8>, p: int)
    requires bound(db, c), ctx_ok(c), uom_is(c, p0), int_in_range(IntKind::Int4, c.p1), 0 <= p < n_sub(c),
        big(c, row_at(c, p)),
    ensures !fits_query(db, Seq::empty(), q_body(lits(p0, c.p1))),
{
    crate::stores::sub_fy::interface::common::perm::lemma_permutation_facts(
        crate::stores::sub_fy::interface::fy_order(c.sp), n_sub(c) as nat);
    let j = row_at(c, p);
    let k = ekey(c, j, true);
    lemma_ekey_valid(c, j, true);
    lemma_acc(db, c, p0, k, true, 1);
    let f = tterm(c, k, true, 1);
    assert forall|i: int| 0 <= i < n_sub(c) implies #[trigger] f(i) >= 0 by {
        if qualifies(c, i) && ekey(c, i, true) == k {
            let r = the_run(c, i);
            assert forall|x: int| run_lo(c.np, r) <= x < run_hi(c.np, r) implies #[trigger] abs_term_at(c.np)(x) >= 0 by {}
            lemma_rsum_nonneg(run_lo(c.np, r), run_hi(c.np, r), abs_term_at(c.np));
        }
    }
    lemma_rsum_nonneg(0, n_sub(c), f);
    assert(f(j) == run_mass(c.np, the_run(c, j)));
    lemma_cap_top(db, p0, c.p1, kspec(c.sp, k, true));
}

/// An outer group whose mass exceeds `i128::MAX`.
pub proof fn lemma_cap_top_group(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, t: int)
    requires bound(db, c), run_ok(c, p0, l), int_in_range(IntKind::Int4, c.p1), 0 <= t < l.len(),
        ssum(l, mass_f(gkey(l[t], true), true)) > i128::MAX as int,
    ensures !fits_query(db, Seq::empty(), q_body(lits(p0, c.p1))),
{
    lemma_filing_key(c, p0, l, t, true);
    lemma_key_acc(db, c, p0, l, gkey(l[t], true), true);
    lemma_cap_top(db, p0, c.p1, kspec(c.sp, gkey(l[t], true), true));
}

/// The outer groups are nonempty and within their domain.
proof fn lemma_top_ready(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(g, l, true), l.len() > 0,
    ensures sum_caps(g_top(p0, c.p1), joined(db)), gkeys(g_top(p0, c.p1), joined(db)).len() > 0,
{
    lemma_sum_caps(db, c, p0, l, g, true);
    lemma_keys_multiset(db, c, p0, l, g, true);
    reveal(gf_cover);
    let h = choose|h: int| 0 <= h < g.sum@.len() && #[trigger] gk(g.cik@, g.name@, h, true) == gkey(l[0], true);
}

/// A per-cik group whose mass exceeds `i128::MAX`.
pub proof fn lemma_cap_cik_group(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups, t: int)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(g, l, true), int_in_range(IntKind::Int4, c.p1),
        0 <= t < l.len(),
        ssum(l, mass_f(gkey(l[t], false), false)) > i128::MAX as int,
    ensures !fits_query(db, Seq::empty(), q_body(lits(p0, c.p1))),
{
    lemma_filing_key(c, p0, l, t, false);
    lemma_key_acc(db, c, p0, l, gkey(l[t], false), false);
    let kk = kspec(c.sp, gkey(l[t], false), false);
    assert forall|ctx: Row| ctx.len() == 3 implies !#[trigger] fits_query(db, ctx, q_avg(lits(p0, c.p1))) by {
        lemma_inner_cik(db, p0, c.p1, ctx, kk);
    }
    lemma_top_ready(db, c, p0, l, g);
    lemma_cap_sub(db, p0, c.p1);
}

/// The mass of the per-cik sums.
proof fn lemma_mass_num4(keys: Seq<Row>, f: spec_fn(Row) -> int)
    ensures num_mass_at(keys.map_values(num4(f)), 4) == ssum(keys, |k: Row| abs(f(k))),
    decreases keys.len(),
{
    if keys.len() > 0 {
        let ki = keys.drop_last();
        lemma_mass_num4(ki, f);
        assert(keys.map_values(num4(f)).drop_last() =~= ki.map_values(num4(f)));
        assert(pow10(0) == 1);
        assert(abs(f(keys.last())) * pow10((4 - 4) as nat) == abs(f(keys.last()))) by {
            assert((4 - 4) as nat == 0nat);
        }
    } else {
        assert(keys.map_values(num4(f)) =~= Seq::<Val>::empty());
    }
}

/// The per-cik groups as the subquery's group keys: their total and the mass of their sums.
pub proof fn lemma_cik_totals(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, cg: Groups)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(cg, l, false),
    ensures
        cik_total(p0, c.p1, joined(db)) == rsum(0, cg.sum@.len() as int, |h: int| cg.sum@[h] as int),
        num_mass_at(cik_sums(p0, c.p1, joined(db)), 4) == rsum(0, cg.sum@.len() as int, |h: int| abs(cg.sum@[h] as int)),
        gkeys(g_cik(p0, c.p1), joined(db)).len() == cg.sum@.len(),
{
    let xs = joined(db);
    let gc = g_cik(p0, c.p1);
    lemma_keys_multiset(db, c, p0, l, cg, false);
    let kl = key_list(c.sp, cg, false);
    let f = cik_sum_fn(p0, c.p1, xs);
    lemma_ssum_perm(gkeys(gc, xs), kl, f);
    lemma_ssum_index(kl, f);
    assert forall|h: int| 0 <= h < kl.len() implies f(#[trigger] kl[h]) == cg.sum@[h] as int by {
        lemma_group_acc(db, c, p0, l, cg, false, h);
    }
    lemma_rsum_ext(0, kl.len() as int, |h: int| f(kl[h]), |h: int| cg.sum@[h] as int);
    let fa = |k: Row| abs(f(k));
    lemma_mass_num4(gkeys(gc, xs), f);
    lemma_ssum_perm(gkeys(gc, xs), kl, fa);
    lemma_ssum_index(kl, fa);
    assert forall|h: int| 0 <= h < kl.len() implies fa(#[trigger] kl[h]) == abs(cg.sum@[h] as int) by {
        lemma_group_acc(db, c, p0, l, cg, false, h);
    }
    lemma_rsum_ext(0, kl.len() as int, |h: int| fa(kl[h]), |h: int| abs(cg.sum@[h] as int));
}

/// A pass with a group has a filing.
proof fn lemma_l_nonempty(l: Seq<Filing>, g: Groups, by_name: bool)
    requires groups_ok(g, l, by_name), g.sum@.len() > 0,
    ensures l.len() > 0,
{
    reveal(gf_wit);
    let t = choose|i: int| 0 <= i < l.len() && gkey(#[trigger] l[i], by_name) == gk(g.cik@, g.name@, 0, by_name);
}

/// The per-cik sums before `h0` have mass above `i128::MAX`: the AVG leaves its domain.
proof fn lemma_avg_mass_violation(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, cg: Groups, h0: int)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(cg, l, false), 0 < h0 <= cg.sum@.len(),
        rsum(0, h0, |h: int| abs(cg.sum@[h] as int)) > i128::MAX as int,
    ensures !fits_avg_value(NumKind::Numeric, cik_sums(p0, c.p1, joined(db))),
{
    let xs = joined(db);
    let nc = cg.sum@.len() as int;
    lemma_cik_totals(db, c, p0, l, cg);
    assert forall|h: int| 0 <= h < nc implies abs(#[trigger] cg.sum@[h] as int) >= 0 by {}
    lemma_rsum_sub_range(0, 0, h0, nc, |h: int| abs(cg.sum@[h] as int));
    let vs = cik_sums(p0, c.p1, xs);
    lemma_num_sum_scale4(gkeys(g_cik(p0, c.p1), xs), cik_sum_fn(p0, c.p1, xs));
    assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale == 4) by {}
    lemma_num_mass_uniform(vs, 4);
    assert(vs[0] is Num);
    assert(!sum_mass_fits(NumKind::Numeric, vs));
}

/// The AVG's mass exceeds `i128::MAX` (the sums of the per-cik groups before `h0`).
pub proof fn lemma_cap_avg_mass(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups, cg: Groups, h0: int)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(g, l, true), groups_ok(cg, l, false),
        int_in_range(IntKind::Int4, c.p1), 0 < h0 <= cg.sum@.len(),
        rsum(0, h0, |h: int| abs(cg.sum@[h] as int)) > i128::MAX as int,
    ensures !fits_query(db, Seq::empty(), q_body(lits(p0, c.p1))),
{
    lemma_avg_mass_violation(db, c, p0, l, cg, h0);
    lemma_l_nonempty(l, cg, false);
    lemma_top_ready(db, c, p0, l, g);
    lemma_sum_caps(db, c, p0, l, cg, false);
    assert forall|ctx: Row| ctx.len() == 3 implies !#[trigger] fits_query(db, ctx, q_avg(lits(p0, c.p1))) by {
        lemma_inner_avg(db, p0, c.p1, ctx);
    }
    lemma_cap_sub(db, p0, c.p1);
}

/// The AVG's division is outside its domain.
pub proof fn lemma_cap_avg_div(db: Database, c: ScanCtx, p0: Seq<u8>, l: Seq<Filing>, g: Groups, cg: Groups, total: int)
    requires bound(db, c), run_ok(c, p0, l), groups_ok(g, l, true), groups_ok(cg, l, false),
        int_in_range(IntKind::Int4, c.p1), cg.sum@.len() > 0,
        total == rsum(0, cg.sum@.len() as int, |h: int| cg.sum@[h] as int),
        !num_div_fits(total, 4, cg.sum@.len() as int, 0),
    ensures !fits_query(db, Seq::empty(), q_body(lits(p0, c.p1))),
{
    let xs = joined(db);
    lemma_cik_totals(db, c, p0, l, cg);
    let vs = cik_sums(p0, c.p1, xs);
    lemma_num_sum_scale4(gkeys(g_cik(p0, c.p1), xs), cik_sum_fn(p0, c.p1, xs));
    assert(!fits_avg(NumKind::Numeric, vs));
    assert(!fits_avg_value(NumKind::Numeric, vs));
    lemma_l_nonempty(l, cg, false);
    lemma_top_ready(db, c, p0, l, g);
    lemma_sum_caps(db, c, p0, l, cg, false);
    assert forall|ctx: Row| ctx.len() == 3 implies !#[trigger] fits_query(db, ctx, q_avg(lits(p0, c.p1))) by {
        lemma_inner_avg(db, p0, c.p1, ctx);
    }
    lemma_cap_sub(db, p0, c.p1);
}

} // verus!
