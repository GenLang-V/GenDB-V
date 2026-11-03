//! The two outcomes outside the normal form's arithmetic domain: a group whose COUNT exceeds int8 makes the
//! statement the SQL error 22003 (`lemma_count_err`); otherwise a group whose SUM has an absolute mass beyond
//! `i128::MAX` puts the statement outside the capacity domain (`lemma_mass_cap`). Both are independent of the group
//! order (`link::capacity::lemma_group_by_err`, `lemma_group_by_capacity`), over the GROUP BY input rows of
//! `link::query` (`qrows`, `qkeys`, `members`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::numeric::*;
use crate::spec::scalar::NumKind;
use crate::spec::equality::*;
use crate::exec::relational::domain::*;
use crate::link::query::*;
use crate::link::join::*;
use crate::link::capacity::*;
use crate::agent::ctx::*;
use crate::agent::sem::*;
use crate::agent::nf::*;
use crate::agent::sums::*;

verus! {

/// The GROUP BY input of the statement in the toolkit's terms.
pub proof fn lemma_prep(db: Database, c: Ctx, ps: Seq<Literal>)
    requires db_ok(db, c), lits_ok(c, ps),
    ensures ({
        let g = qs(c);
        let xs = jrows(db);
        let kept = qrows(g, xs);
        let ks = qkeys(g, xs);
        let args = kept.map_values(|x: Row| arg_vals(g, x));
        &&& eval_query(db, Seq::empty(), q_input(ps[0], ps[1], ps[2])) == Ok::<Relation, SqlError>(kept)
        &&& ks.len() == kept.len() && args.len() == kept.len()
        &&& forall|i: int| 0 <= i < kept.len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], g_keys(), g_aggs())
                == Ok::<(Row, Row), SqlError>((ks[i], args[i]))
        &&& distinct_rows(ks) == gkeys(g, xs)
        &&& forall|k: Row| #[trigger] gkeys(g, xs).contains(k) ==> group_members(ks, args, k) == members(g, xs, k)
    }),
{
    let g = qs(c);
    let jr = jrows(db);
    let cols = id_cols();
    lemma_input(db, c, ps);
    lemma_proj_id(db, c);
    let xs = proj_all(jr, cols);
    lemma_keep_true_keep(jr, qual_truths(g, xs), g.qual);
    lemma_kept_rows(g, jr, cols);
    let kept0 = keep_true(jr, qual_truths(g, xs));
    assert forall|i: int| 0 <= i < kept0.len() implies proj(#[trigger] kept0[i], cols) == kept0[i] by {
        assert(jr.contains(kept0[i]));
        let (a, b, d) = lemma_jrow_of(db, c, kept0[i]);
        lemma_jcells(c, a, b, d);
        assert(proj(kept0[i], cols) =~= kept0[i]);
    }
    assert(proj_all(kept0, cols) =~= kept0);
    let kept = qrows(g, xs);
    let ks = qkeys(g, xs);
    let args = kept.map_values(|x: Row| arg_vals(g, x));
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], g_keys(), g_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
        assert(kept[i] == kept0[i]);
        assert(jr.contains(kept0[i]));
        let (a, b, d) = lemma_jrow_of(db, c, kept0[i]);
        lemma_row_agrees(db, c, a, b, d);
    }
    lemma_keys_exact(db, c);
    lemma_pool_exact(g, xs);
    let pool = key_pool(g, xs);
    assert forall|i: int| 0 <= i < ks.len() implies pool.contains(#[trigger] ks[i]) by {}
    lemma_distinct_gkeys(g, xs, pool);
    assert forall|k: Row| #[trigger] gkeys(g, xs).contains(k) implies group_members(ks, args, k) == members(g, xs, k) by {
        let t = choose|t: int| 0 <= t < gkeys(g, xs).len() && gkeys(g, xs)[t] == k;
        assert(pool.contains(gkeys(g, xs)[t]));
        lemma_group_members(g, xs, k, pool);
    }
}

/// Column 0 of a group's members: numerics at scale 4 whose mass at scale 4 is the group's absolute sum.
pub proof fn lemma_members_mass(c: Ctx, xs: Seq<Row>, k: Row)
    ensures ({
        let vs = column(members(qs(c), xs, k), 0);
        &&& forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i] matches Val::Num { coeff, scale } && scale == 4)
        &&& num_mass_at(vs, 4) == gabs(qs(c), xs, k, 0)
    }),
    decreases xs.len(),
{
    let g = qs(c);
    let vs = column(members(g, xs, k), 0);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_mass(c, xi, k);
        let vsi = column(members(g, xi, k), 0);
        if hit(g, x, k) {
            let av = arg_vals(g, x);
            assert(av[0] == (Val::Num { coeff: (g.arg)(0, x), scale: 4 }));
            assert(vs =~= vsi.push(av[0]));
            assert(vs.drop_last() =~= vsi);
            assert(pow10(0) == 1);
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// The aggregates of a group: SUM is a value or 22003, COUNT(*) is its count or 22003.
proof fn lemma_group_aggs(c: Ctx, xs: Seq<Row>, k: Row)
    requires gcount(qs(c), xs, k) > 0,
    ensures ({
        let m = members(qs(c), xs, k);
        &&& agg_value(g_aggs()[0], column(m, 0)) is Ok
            || agg_value(g_aggs()[0], column(m, 0)) == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange)
        &&& column(m, 1).len() == gcount(qs(c), xs, k)
        &&& all_of_kind(NumKind::Numeric, column(m, 0))
    }),
{
    let g = qs(c);
    lemma_members_col(g, xs, k, 0);
    lemma_members_col(g, xs, k, 1);
}

/// A group count beyond int8: the statement is the SQL error 22003.
#[verifier::spinoff_prover]
pub proof fn lemma_count_err(db: Database, c: Ctx, ps: Seq<Literal>, key: Row)
    requires db_ok(db, c), lits_ok(c, ps), gacc(c, 0, key, c.q) > crate::spec::limits::int8_max(),
    ensures eval_query(db, Seq::empty(), q_body(ps[0], ps[1], ps[2])) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    let g = qs(c);
    let xs = jrows(db);
    let kept = qrows(g, xs);
    let ks = qkeys(g, xs);
    let args = kept.map_values(|x: Row| arg_vals(g, x));
    let e = SqlError::NumericValueOutOfRange;
    lemma_prep(db, c, ps);
    lemma_gsums(db, c, key);
    lemma_gkeys(g, xs);
    let ds = distinct_rows(ks);
    assert(ds.contains(key));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == key;
    lemma_group_aggs(c, xs, key);
    lemma_count_value(Agg::CountStar, column(members(g, xs, key), 1));
    assert(agg_value(g_aggs()[1], column(group_members(ks, args, ds[gi]), 1)) == Err::<Val, SqlError>(e));
    assert forall|h: int, j: int| 0 <= h < ds.len() && 0 <= j < g_aggs().len() implies
        #[trigger] agg_value(g_aggs()[j], column(group_members(ks, args, ds[h]), j)) is Ok
            || agg_value(g_aggs()[j], column(group_members(ks, args, ds[h]), j)) == Err::<Val, SqlError>(e) by {
        let kk = ds[h];
        assert(gkeys(g, xs).contains(kk));
        lemma_group_aggs(c, xs, kk);
        lemma_count_value(Agg::CountStar, column(members(g, xs, kk), 1));
    }
    lemma_group_by_err(db, Seq::empty(), g_keys(), g_aggs(), Box::new(q_input(ps[0], ps[1], ps[2])), kept, ks, args, e, gi, 1);
}

/// All counts within int8 and a group mass beyond `i128::MAX`: the statement is outside the capacity domain.
#[verifier::spinoff_prover]
pub proof fn lemma_mass_cap(db: Database, c: Ctx, ps: Seq<Literal>, key: Row)
    requires
        db_ok(db, c), lits_ok(c, ps),
        forall|k: Row| #[trigger] gacc(c, 0, k, c.q) <= crate::spec::limits::int8_max(),
        gacc(c, 2, key, c.q) > crate::link::expr::i128_max(),
    ensures !fits_query(db, Seq::empty(), q_body(ps[0], ps[1], ps[2])),
{
    let g = qs(c);
    let xs = jrows(db);
    let kept = qrows(g, xs);
    let ks = qkeys(g, xs);
    let args = kept.map_values(|x: Row| arg_vals(g, x));
    lemma_prep(db, c, ps);
    lemma_gsums(db, c, key);
    lemma_acc_mass_count(db, c, key);
    lemma_gkeys(g, xs);
    let ds = distinct_rows(ks);
    assert(ds.contains(key));
    let gi = choose|gi: int| 0 <= gi < ds.len() && ds[gi] == key;
    let vs0 = column(members(g, xs, key), 0);
    lemma_members_mass(c, xs, key);
    lemma_group_aggs(c, xs, key);
    lemma_members_col(g, xs, key, 0);
    lemma_num_mass_uniform(vs0, 4);
    assert(vs0.len() > 0);
    assert(vs0[0] is Num);
    assert(num_max_scale(vs0) == 4);
    assert(!fits_agg_value(g_aggs()[0], column(group_members(ks, args, ds[gi]), 0)));
    assert forall|h: int| 0 <= h < ds.len() implies #[trigger] aggs_ok_inside(g_aggs(), group_members(ks, args, ds[h])) by {
        let kk = ds[h];
        assert(gkeys(g, xs).contains(kk));
        lemma_gsums(db, c, kk);
        lemma_group_aggs(c, xs, kk);
        let m = members(g, xs, kk);
        lemma_count_value(Agg::CountStar, column(m, 1));
        assert forall|j: int| 0 <= j < g_aggs().len() && #[trigger] fits_agg_value(g_aggs()[j], column(m, j)) implies
            agg_value(g_aggs()[j], column(m, j)) is Ok by {
            if j == 0 {
                lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(7), column(m, 0));
            }
        }
    }
    lemma_group_by_capacity(db, Seq::empty(), g_keys(), g_aggs(), Box::new(q_input(ps[0], ps[1], ps[2])), kept, ks, args, gi, 0);
}

/// A group with mass has rows.
pub proof fn lemma_acc_mass_count(db: Database, c: Ctx, key: Row)
    requires db_ok(db, c), gacc(c, 2, key, c.q) > 0,
    ensures gacc(c, 0, key, c.q) > 0,
{
    lemma_gacc_mass_count(c, key, c.q);
}

pub proof fn lemma_gacc_mass_count(c: Ctx, key: Row, hi: int)
    requires gacc(c, 2, key, hi) > 0,
    ensures gacc(c, 0, key, hi) > 0,
    decreases hi,
{
    if hi > 0 {
        lemma_gacc_nonneg(c, 0, key, hi - 1);
        lemma_acc_nonneg(c, 0, hi - 1, c.n);
        if gacc(c, 2, key, hi - 1) > 0 {
            lemma_gacc_mass_count(c, key, hi - 1);
        } else {
            lemma_acc_mass_count2(c, hi - 1, c.n);
        }
    }
}

pub proof fn lemma_acc_mass_count2(c: Ctx, k: int, hi: int)
    ensures acc(c, 2, k, hi) > 0 ==> acc(c, 0, k, hi) > 0,
    decreases hi,
{
    if hi > 0 {
        lemma_acc_mass_count2(c, k, hi - 1);
        lemma_acc_nonneg(c, 0, k, hi - 1);
        lemma_acc_nonneg(c, 2, k, hi - 1);
    }
}

} // verus!
