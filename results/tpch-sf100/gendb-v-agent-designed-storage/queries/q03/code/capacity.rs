//! The Capacity answer of Q3: when some group's absolute revenue mass exceeds `i128::MAX` (the SUM capacity
//! condition `sum_mass_fits` of the canonical evaluation), the statement is outside its capacity domain
//! (`lemma_q3_capacity`). The other groups' SUMs succeed inside their condition, so the canonical GROUP BY reaches
//! that group whatever the group order (`link::capacity::lemma_group_by_capacity`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::distinct_rows;
use crate::spec::numeric::{abs, pow10};
use crate::spec::scalar::NumKind;
use crate::query::{query_spec_at, param_domain};
use crate::exec::relational::domain::*;
use crate::link::query::*;
use crate::link::capacity::{lemma_group_by_capacity, aggs_ok_inside, lemma_sum_inside_ok, lemma_num_mass_uniform};
use crate::link::expr::i128_max;
use crate::gendb_entry::capacity_domain;
use super::model::*;
use super::qspec::*;
use super::sqlrow::*;
use super::sqllink::*;
use super::answer::*;

verus! {

/// The absolute mass of a group's SUM arguments (all at scale 4) is its `gabs`.
proof fn lemma_members_mass(p: QP, xs: Seq<Row>, k: Row)
    ensures
        num_mass_at(column(members(q3_g(p), xs, k), 0), 4) == gabs(q3_g(p), xs, k, 0),
        forall|i: int| 0 <= i < column(members(q3_g(p), xs, k), 0).len() ==>
            (#[trigger] column(members(q3_g(p), xs, k), 0)[i]) is Num && column(members(q3_g(p), xs, k), 0)[i]->Num_scale == 4,
    decreases xs.len(),
{
    let g = q3_g(p);
    let vs = column(members(g, xs, k), 0);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_mass(p, xi, k);
        let vi = column(members(g, xi, k), 0);
        if hit(g, x, k) {
            assert(members(g, xs, k) == members(g, xi, k).push(arg_vals(g, x)));
            assert(vs =~= vi.push(arg_vals(g, x)[0]));
            assert(arg_vals(g, x)[0] == (Val::Num { coeff: (g.arg)(0, x), scale: 4 }));
            assert(vs.drop_last() =~= vi);
            assert(pow10(0) == 1);
            assert(abs((g.arg)(0, x)) * pow10((4 - 4) as nat) == abs((g.arg)(0, x)));
            assert forall|i: int| 0 <= i < vs.len() implies
                (#[trigger] vs[i]) is Num && vs[i]->Num_scale == 4 by {
                if i < vi.len() {
                    assert(vs[i] == vi[i]);
                }
            }
        } else {
            assert(members(g, xs, k) == members(g, xi, k));
        }
    } else {
        assert(vs.len() == 0);
    }
}

/// Over the members of every group: SUM succeeds inside its capacity condition; over the members of a group of
/// mass above `i128::MAX`, it is outside.
proof fn lemma_members_caps(p: QP, xs: Seq<Row>, k: Row)
    ensures
        aggs_ok_inside(q3_aggs(), members(q3_g(p), xs, k)),
        gcount(q3_g(p), xs, k) > 0 && gabs(q3_g(p), xs, k, 0) > i128_max() ==>
            !fits_agg_value(q3_aggs()[0], column(members(q3_g(p), xs, k), 0)),
{
    let g = q3_g(p);
    let mem = members(g, xs, k);
    let vs = column(mem, 0);
    lemma_members_col(g, xs, k, 0);
    assert(all_of_kind(NumKind::Numeric, vs));
    assert forall|j: int| 0 <= j < q3_aggs().len() && #[trigger] fits_agg_value(q3_aggs()[j], column(mem, j))
        implies agg_value(q3_aggs()[j], column(mem, j)) is Ok by {
        lemma_sum_inside_ok(NumKind::Numeric, q3_arg(), vs);
    }
    if gcount(g, xs, k) > 0 && gabs(g, xs, k, 0) > i128_max() {
        lemma_members_mass(p, xs, k);
        assert forall|i: int| 0 <= i < vs.len() implies (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale == 4) by {}
        lemma_num_mass_uniform(vs, 4);
        assert(vs.len() > 0);
        assert(vs[0] is Num);
        assert(num_max_scale(vs) == 4);
        assert(sum_mass(NumKind::Numeric, vs) > i128::MAX as int);
    }
}

/// A good order whose absolute revenue mass exceeds `i128::MAX` puts the statement outside its capacity domain.
pub proof fn lemma_q3_capacity(db: Database, m: M, ps: Seq<Literal>, q: int)
    requires
        bound_ok(db, m, ps),
        0 <= q < m.o_n,
        good(m, qp_of(ps), q),
        labs(m, qp_of(ps), q) > i128_max(),
    ensures !capacity_domain(db, query_spec_at(ps)),
{
    let p = qp_of(ps);
    let g = q3_g(p);
    let rows = from_rows(db);
    let cols = q3_cols();
    let xs = q3_xs(db);
    lemma_q3_shape(ps);
    lemma_widths(db);
    lemma_from_eval(db);
    lemma_pred_agrees(db, m, ps);
    lemma_filter_rows(db, q3_from(), rows, cols, q3_pred(ps), g);
    let kept = keep_true(rows, qual_truths(g, xs));
    lemma_kept_rows(g, rows, cols);
    lemma_keys_args_agree(db, m, ps);
    let qr = qrows(g, xs);
    let ks = qkeys(g, xs);
    let args = qr.map_values(|x: Row| arg_vals(g, x));
    assert(proj_all(kept, cols) == qr);
    assert(kept.len() == qr.len());
    // every kept row's GROUP BY input is its key and argument row
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] group_input(db, Seq::<Val>::empty() + kept[i], q3_gkeys(), q3_aggs())
        == Ok::<(Row, Row), SqlError>((ks[i], args[i])) by {
        assert(Seq::<Val>::empty() + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]) && (g.qual)(proj(kept[i], cols)));
        let t = choose|t: int| 0 <= t < rows.len() && rows[t] == kept[i];
        assert((g.qual)(proj(rows[t], cols)));
        assert(proj(kept[i], cols) == qr[i]);
    }
    // the groups are gkeys, and each group's members are its argument rows
    lemma_keys_exact(db, m, ps);
    lemma_pool_exact(g, xs);
    let pool = key_pool(g, xs);
    lemma_distinct_gkeys(g, xs, pool);
    lemma_groups_link(db, m, p);
    let kq = keyq(m, q);
    assert(gcount(g, xs, kq) == lcnt(m, p, q));
    assert(gabs(g, xs, kq, 0) == labs(m, p, q));
    lemma_gkeys(g, xs);
    let gk = gkeys(g, xs);
    assert(gk.contains(kq));
    let gi = choose|gi: int| 0 <= gi < gk.len() && gk[gi] == kq;
    assert(pool.contains(gk[gi]));
    lemma_group_members(g, xs, kq, pool);
    lemma_members_caps(p, xs, kq);
    assert forall|h: int| 0 <= h < distinct_rows(ks).len() implies #[trigger] aggs_ok_inside(q3_aggs(), group_members(ks, args, distinct_rows(ks)[h])) by {
        assert(pool.contains(gk[h]));
        lemma_group_members(g, xs, gk[h], pool);
        lemma_members_caps(p, xs, gk[h]);
    }
    lemma_group_by_capacity(db, Seq::empty(), q3_gkeys(), q3_aggs(), Box::new(q3_filter(ps)), kept, ks, args, gi, 0);
    assert(!fits_query(db, Seq::empty(), q3_group(ps)));
}

} // verus!
