//! The capacity case: when some group's absolute SUM(value) coefficient sum leaves `i128`, the statement is outside
//! the capacity domain (`lemma_capacity`): the GROUP BY node violates its SUM capacity condition while every other
//! aggregate inside its condition succeeds (`link::capacity::lemma_group_by_capacity`), and the HAVING filter above
//! it needs its input inside the domain.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::distinct_rows;
use crate::spec::scalar::NumKind;
use crate::spec::numeric::{abs, pow10};
use crate::spec::limits::int8_max;
use crate::exec::relational::domain::*;
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::link::capacity::*;
use crate::gendb_entry::Answer;
use crate::gendb_entry::runtime::QueryError;
use crate::agent::spec::*;
use crate::agent::sem::*;
use crate::agent::group::xr;
use crate::agent::scan::{kept, lemma_keep_range_len};
use crate::agent::bind::lemma_bound_ctx;

verus! {

/// The SUM arguments of a group's members: numeric at scale 4, their mass the group's absolute sum.
pub proof fn lemma_members_mass(c: Ctx, xs: Seq<Row>, k: Row)
    ensures ({
        let vs = column(members(nf(c), xs, k), 1);
        &&& num_mass_at(vs, 4) == gabs(nf(c), xs, k, 1)
        &&& num_max_scale(vs) == if gcount(nf(c), xs, k) > 0 { 4nat } else { 0nat }
    }),
    decreases xs.len(),
{
    let g = nf(c);
    let vs = column(members(g, xs, k), 1);
    if xs.len() == 0 {
        assert(vs =~= Seq::<Val>::empty());
    } else {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_mass(c, xi, k);
        let vsi = column(members(g, xi, k), 1);
        if hit(g, x, k) {
            let a = arg_vals(g, x);
            assert(a[1] == Val::Num { coeff: nf_arg(1, x), scale: 4 });
            assert(vs =~= vsi.push(a[1]));
            assert(vs.drop_last() =~= vsi);
            assert(pow10(0) == 1);
        } else {
            assert(vs =~= vsi);
        }
    }
}

pub open spec fn cap_xs(c: Ctx) -> Seq<Row> {
    proj_all(lj_rows(c, c.n), cols())
}

/// The WHERE rows (the GROUP BY input).
pub open spec fn cap_rows(c: Ctx) -> Seq<Row> {
    keep_true(lj_rows(c, c.n), qual_truths(nf(c), cap_xs(c)))
}

pub open spec fn cap_ks(c: Ctx) -> Seq<Row> {
    qkeys(nf(c), cap_xs(c))
}

pub open spec fn cap_args(c: Ctx) -> Seq<Row> {
    qrows(nf(c), cap_xs(c)).map_values(|x: Row| arg_vals(nf(c), x))
}

/// The GROUP BY input evaluates to `cap_rows`, row `i` with key `cap_ks[i]` and arguments `cap_args[i]`.
proof fn lemma_cap_inputs(db: Database, c: Ctx, ps: Seq<Literal>)
    requires db_ok(db, c), lits_ok(c, ps),
    ensures
        eval_query(db, Seq::empty(), q_where(ps[0], ps[1], ps[2])) == Ok::<Relation, SqlError>(cap_rows(c)),
        cap_ks(c).len() == cap_rows(c).len(), cap_args(c).len() == cap_rows(c).len(),
        forall|i: int| 0 <= i < cap_rows(c).len() ==> #[trigger] group_input(db, Seq::<Val>::empty() + cap_rows(c)[i], group_keys(), group_aggs())
            == Ok::<(Row, Row), SqlError>((cap_ks(c)[i], cap_args(c)[i])),
{
    let g = nf(c);
    let lj = lj_rows(c, c.n);
    let xs = cap_xs(c);
    lemma_eval_lj(db, c);
    lemma_pred_agrees(db, c, ps);
    lemma_filter_rows(db, q_lj(), lj, cols(), p_where(ps[0], ps[1], ps[2]), g);
    let rows = cap_rows(c);
    lemma_kept_rows(g, lj, cols());
    lemma_lj_elems(c, c.n);
    let q = qrows(g, xs);
    assert(proj_all(rows, cols()).len() == rows.len());
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + rows[i], group_keys(), group_aggs())
        == Ok::<(Row, Row), SqlError>((cap_ks(c)[i], cap_args(c)[i])) by {
        assert(Seq::<Val>::empty() + rows[i] =~= rows[i]);
        assert(lj.contains(rows[i]));
        let m = choose|m: int| 0 <= m < lj.len() && lj[m] == rows[i];
        assert(lj_shape(c, lj[m]));
        assert(proj(rows[i], cols()) == q[i]);
        lemma_keys_row(db, c, rows[i]);
        lemma_args_row(db, c, rows[i]);
    }
}

/// The groups of the GROUP BY input: `gkeys` of the normal form, members the normal form's.
proof fn lemma_cap_groups(c: Ctx)
    requires ctx_ok(c),
    ensures
        distinct_rows(cap_ks(c)) == gkeys(nf(c), cap_xs(c)),
        forall|k: Row| #[trigger] gkeys(nf(c), cap_xs(c)).contains(k)
            ==> group_members(cap_ks(c), cap_args(c), k) == members(nf(c), cap_xs(c), k),
{
    let g = nf(c);
    let xs = cap_xs(c);
    lemma_keys_exact(c);
    lemma_pool_exact(g, xs);
    let pool = key_pool(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    assert forall|k: Row| #[trigger] gkeys(g, xs).contains(k) implies group_members(cap_ks(c), cap_args(c), k) == members(g, xs, k) by {
        let i = choose|i: int| 0 <= i < gkeys(g, xs).len() && gkeys(g, xs)[i] == k;
        assert(pool.contains(gkeys(g, xs)[i]));
        lemma_group_members(g, xs, k, pool);
    }
}

/// Every group's aggregates inside their conditions succeed.
proof fn lemma_cap_inside(c: Ctx)
    requires ctx_ok(c), c.n <= int8_max(),
    ensures
        forall|h: int| 0 <= h < distinct_rows(cap_ks(c)).len() ==>
            #[trigger] aggs_ok_inside(group_aggs(), group_members(cap_ks(c), cap_args(c), distinct_rows(cap_ks(c))[h])),
{
    let g = nf(c);
    let xs = cap_xs(c);
    let kx = xrows(c, keep_range(c, 0, c.n));
    lemma_cap_groups(c);
    lemma_lj_qrows(c, c.n);
    lemma_keep_range_len(c, 0, c.n);
    let ds = gkeys(g, xs);
    assert forall|h: int| 0 <= h < distinct_rows(cap_ks(c)).len() implies
        #[trigger] aggs_ok_inside(group_aggs(), group_members(cap_ks(c), cap_args(c), distinct_rows(cap_ks(c))[h])) by {
        let kh = ds[h];
        assert(ds.contains(kh));
        let mh = members(g, xs, kh);
        assert(group_members(cap_ks(c), cap_args(c), kh) == mh);
        lemma_members_col(g, xs, kh, 0);
        lemma_members_col(g, xs, kh, 1);
        lemma_qrows_same(g, xs, kh, 1);
        crate::agent::group::lemma_gcount_le(g, kx, kh);
        assert forall|j: int| 0 <= j < group_aggs().len() && #[trigger] fits_agg_value(group_aggs()[j], column(mh, j))
            implies agg_value(group_aggs()[j], column(mh, j)) is Ok by {
            if j == 0 {
                lemma_count_value(group_aggs()[0], column(mh, 0));
            } else {
                lemma_sum_inside_ok(NumKind::Numeric, Expr::Col(7), column(mh, 1));
            }
        }
    }
}

/// The overflowing group violates the SUM capacity condition.
proof fn lemma_cap_over(c: Ctx, key: Row) -> (gi: int)
    requires ctx_ok(c), gabs(nf(c), xrows(c, keep_range(c, 0, c.n)), key, 1) > i128_max(),
    ensures
        0 <= gi < distinct_rows(cap_ks(c)).len(),
        !fits_agg_value(group_aggs()[1], column(group_members(cap_ks(c), cap_args(c), distinct_rows(cap_ks(c))[gi]), 1)),
{
    let g = nf(c);
    let xs = cap_xs(c);
    lemma_cap_groups(c);
    lemma_lj_qrows(c, c.n);
    lemma_qrows_same(g, xs, key, 1);
    assert(gcount(g, xs, key) > 0) by {
        if gcount(g, xs, key) == 0 {
            lemma_zero_count(g, xs, key, 1);
        }
    }
    lemma_gkeys(g, xs);
    let ds = gkeys(g, xs);
    let gi = choose|i: int| 0 <= i < ds.len() && ds[i] == key;
    assert(ds.contains(key));
    lemma_members_mass(c, xs, key);
    lemma_members_col(g, xs, key, 1);
    gi
}

/// A group of the normal form whose absolute sum leaves `i128` puts the statement outside the capacity domain.
#[verifier::spinoff_prover]
pub proof fn lemma_capacity(db: Database, c: Ctx, ps: Seq<Literal>, key: Row)
    requires
        db_ok(db, c), lits_ok(c, ps), c.n <= int8_max(),
        gabs(nf(c), xrows(c, keep_range(c, 0, c.n)), key, 1) > i128_max(),
    ensures !crate::gendb_entry::capacity_domain(db, crate::query::query_spec_at(ps)),
{
    let input = q_where(ps[0], ps[1], ps[2]);
    lemma_cap_inputs(db, c, ps);
    lemma_cap_inside(c);
    let gi = lemma_cap_over(c, key);
    lemma_group_by_capacity(db, Seq::empty(), group_keys(), group_aggs(), Box::new(input), cap_rows(c), cap_ks(c),
        cap_args(c), gi, 1);
    lemma_query_shape(ps);
    assert(!fits_query(db, Seq::empty(), q_group(ps[0], ps[1], ps[2])));
}

/// The capacity answer on every database bound to the parts.
pub proof fn lemma_capacity_all(sv: crate::gendb_entry::stores::StoresView, c: Ctx, ps: Seq<Literal>, u: Seq<usize>, key: Row)
    requires
        ctx_ok(c), lits_ok(c, ps), c.n <= int8_max(), c.n <= usize::MAX,
        c.np == sv.flat_num, c.pp == sv.flat_pre, c.sp == sv.flat_sub, c.tp == sv.flat_tag,
        u == kept(c, 0, c.n),
        gabs(nf(c), xr(c, u), key, 1) > i128_max(),
    ensures crate::gendb_entry::answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    lemma_keep_range_elems(c, 0, c.n);
    assert(xr(c, u) =~= xrows(c, keep_range(c, 0, c.n)));
    assert forall|db2: Database| #[trigger] crate::gendb_entry::bound_db(sv, db2) implies
        crate::gendb_entry::outcome_ok(db2, crate::query::query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_bound_ctx(sv, db2, c);
        lemma_capacity(db2, c, ps, key);
    }
}

} // verus!
