//! The FROM/WHERE rows are the contribution records joined back to table rows (`lemma_where_rows`):
//! `st4(nrows) == contrib(0, n).map(rec_row)`.
//!
//! Proof outline. Every stage distributes over the num rows (`lemma_st4_push`), so the rows are the concatenation
//! over the num rows of the stages of one num row (`lemma_st4_prefix`). For one num row `i` (`lemma_st4_one`): by
//! the sub key at most one sub row `t*` has its adsh, by the tag key at most one tag row `k*` its tag and version;
//! the rows of `i` are the pre rows `l` with its adsh, tag and version for which the WHERE holds on
//! `(i, t*, k*, l)`, in pre row order. Those are exactly the pre rows of the entries matching `i`, in entry order
//! (`lemma_positions`), and each matching entry's sub and tag rows are `t*` and `k*`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::link::join::*;
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::ents::*;
use crate::agent::scan::*;
use crate::agent::fold::Rec;
use crate::agent::sem::*;
use crate::agent::join::*;

verus! {

/// The joined row of a record: its num row with its entry's sub, tag and pre rows.
pub open spec fn rec_row(c: Ctx, ents: Seq<(usize, usize, usize)>, r: Rec) -> Row {
    let (l, j, k) = ents[r.1 as int];
    full_row(c, r.0 as int, j as int, k as int, l as int)
}

pub open spec fn rec_rows(c: Ctx, ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>) -> Seq<Row> {
    recs.map_values(|r: Rec| rec_row(c, ents, r))
}

// ------------------------------------------------------------------------------------------------ distribution

/// The product of one row with a relation.
proof fn lemma_product_one_row(x: Row, b: Seq<Row>)
    ensures product_rows(seq![x], b) == b.map_values(|r: Row| x + r),
{
    let s = seq![x];
    assert(s.drop_last() =~= Seq::<Row>::empty());
    assert(product_rows(Seq::<Row>::empty(), b) == Seq::<Row>::empty());
    assert(Seq::<Row>::empty() + b.map_values(|r: Row| x + r) =~= b.map_values(|r: Row| x + r));
}

/// The product with one more left row.
proof fn lemma_product_push(a: Seq<Row>, x: Row, b: Seq<Row>)
    ensures product_rows(a.push(x), b) == product_rows(a, b) + product_rows(seq![x], b),
{
    assert(a.push(x).drop_last() =~= a);
    lemma_product_one_row(x, b);
}

/// Every stage distributes over one more num row.
pub proof fn lemma_st4_push(db: Database, c: Ctx, ps: Seq<Literal>, a: Seq<Row>, x: Row)
    ensures st4(db, c, ps, a.push(x)) == st4(db, c, ps, a) + st4(db, c, ps, seq![x]),
{
    lemma_product_push(a, x, srows(c));
    lemma_keep_append(product_rows(a, srows(c)), product_rows(seq![x], srows(c)), holds(db, p_ns()));
    lemma_product_append(st1(db, c, a), st1(db, c, seq![x]), trows(c));
    lemma_keep_append(product_rows(st1(db, c, a), trows(c)), product_rows(st1(db, c, seq![x]), trows(c)), holds(db, p_nt()));
    lemma_product_append(st2(db, c, a), st2(db, c, seq![x]), prows(c));
    lemma_keep_append(product_rows(st2(db, c, a), prows(c)), product_rows(st2(db, c, seq![x]), prows(c)), holds(db, p_np()));
    lemma_keep_append(st3(db, c, a), st3(db, c, seq![x]), holds(db, p_where(ps)));
}

// ------------------------------------------------------------------------------------------------ one num row

/// Rows kept by a condition that exactly one position satisfies.
proof fn lemma_keep_one(rows: Seq<Row>, f: spec_fn(Row) -> bool, j: int)
    requires 0 <= j < rows.len(), f(rows[j]), forall|i: int| 0 <= i < rows.len() && i != j ==> !f(#[trigger] rows[i]),
    ensures keep(rows, f) == seq![rows[j]],
{
    let ps = seq![j];
    assert forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) implies exists|t: int| 0 <= t < ps.len() && ps[t] == i by {
        assert(ps[0] == i);
    }
    lemma_keep_positions(rows, f, ps);
    assert(ps.map_values(|p: int| rows[p]) =~= seq![rows[j]]);
}

/// Some sub row has the adsh of num row `i`.
pub open spec fn sub_any(c: Ctx, i: int) -> bool {
    exists|t: int| 0 <= t < c.m && #[trigger] s_adsh(c, t) == n_adsh(c, i)
}

/// Some tag row has the tag and version of num row `i`.
pub open spec fn tag_any(c: Ctx, i: int) -> bool {
    exists|k: int| 0 <= k < c.nt && #[trigger] t_tag(c, k) == n_tag(c, i) && t_ver(c, k) == n_ver(c, i)
}

/// The stage-1 rows of num row `i`: its row joined with the sub row of its adsh, if any.
proof fn lemma_st1_one(db: Database, c: Ctx, i: int)
    requires db_ok(db, c), 0 <= i < c.n,
    ensures
        !sub_any(c, i) ==> st1(db, c, seq![nrow(c, i)]) == Seq::<Row>::empty(),
        sub_any(c, i) ==> ({
            let t = choose|t: int| 0 <= t < c.m && #[trigger] s_adsh(c, t) == n_adsh(c, i);
            st1(db, c, seq![nrow(c, i)]) == seq![ns_row(c, i, t)]
        }),
{
    let n = nrow(c, i);
    let ss = srows(c);
    let m = |r: Row| n + r;
    lemma_product_one_row(n, ss);
    lemma_keep_map(ss, m, holds(db, p_ns()));
    let f = |r: Row| holds(db, p_ns())(m(r));
    assert forall|t: int| 0 <= t < ss.len() implies f(#[trigger] ss[t]) == (s_adsh(c, t) == n_adsh(c, i)) by {
        assert(ss[t] == srow(c, t));
        lemma_eval_ns(db, c, i, t);
    }
    if sub_any(c, i) {
        let t = choose|t: int| 0 <= t < c.m && #[trigger] s_adsh(c, t) == n_adsh(c, i);
        lemma_keys(c);
        assert forall|u: int| 0 <= u < ss.len() && u != t implies !f(#[trigger] ss[u]) by {}
        lemma_keep_one(ss, f, t);
        assert(seq![ss[t]].map_values(m) =~= seq![ns_row(c, i, t)]);
    } else {
        assert forall|u: int| 0 <= u < ss.len() implies !f(#[trigger] ss[u]) by {}
        lemma_keep_none(ss, f);
        assert(Seq::<Row>::empty().map_values(m) =~= Seq::<Row>::empty());
    }
}

/// The stage-2 rows of one stage-1 row `ns_row(i, t)`: joined with the tag row of its tag and version, if any.
proof fn lemma_st2_one(db: Database, c: Ctx, i: int, t: int)
    requires db_ok(db, c), 0 <= i < c.n, 0 <= t < c.m,
    ensures
        !tag_any(c, i) ==> keep(product_rows(seq![ns_row(c, i, t)], trows(c)), holds(db, p_nt())) == Seq::<Row>::empty(),
        tag_any(c, i) ==> ({
            let k = choose|k: int| 0 <= k < c.nt && #[trigger] t_tag(c, k) == n_tag(c, i) && t_ver(c, k) == n_ver(c, i);
            keep(product_rows(seq![ns_row(c, i, t)], trows(c)), holds(db, p_nt())) == seq![nst_row(c, i, t, k)]
        }),
{
    let y = ns_row(c, i, t);
    let ts = trows(c);
    let m = |r: Row| y + r;
    lemma_product_one_row(y, ts);
    lemma_keep_map(ts, m, holds(db, p_nt()));
    let f = |r: Row| holds(db, p_nt())(m(r));
    assert forall|k: int| 0 <= k < ts.len() implies f(#[trigger] ts[k]) == (n_tag(c, i) == t_tag(c, k) && n_ver(c, i) == t_ver(c, k)) by {
        assert(ts[k] == trow(c, k));
        assert(m(ts[k]) == nst_row(c, i, t, k));
        lemma_eval_nt(db, c, i, t, k);
    }
    if tag_any(c, i) {
        let k = choose|k: int| 0 <= k < c.nt && #[trigger] t_tag(c, k) == n_tag(c, i) && t_ver(c, k) == n_ver(c, i);
        lemma_keys(c);
        assert forall|u: int| 0 <= u < ts.len() && u != k implies !f(#[trigger] ts[u]) by {}
        lemma_keep_one(ts, f, k);
        assert(seq![ts[k]].map_values(m) =~= seq![nst_row(c, i, t, k)]);
    } else {
        assert forall|u: int| 0 <= u < ts.len() implies !f(#[trigger] ts[u]) by {}
        lemma_keep_none(ts, f);
        assert(Seq::<Row>::empty().map_values(m) =~= Seq::<Row>::empty());
    }
}

/// The condition on the pre row of a joined row `(i, t, k, l)`: the pre join and the WHERE.
pub open spec fn pre_cond(c: Ctx, i: int, t: int, k: int, l: int) -> bool {
    n_adsh(c, i) == p_adsh(c, l) && n_tag(c, i) == p_tag(c, l) && n_ver(c, i) == p_ver(c, l) && where_ok(c, i, t, k, l)
}

/// The stage-3/4 rows of one stage-2 row `nst_row(i, t, k)`: joined with the pre rows meeting `pre_cond`.
proof fn lemma_st34_one(db: Database, c: Ctx, ps: Seq<Literal>, i: int, t: int, k: int)
    requires db_ok(db, c), lits_ok(c, ps), 0 <= i < c.n, 0 <= t < c.m, 0 <= k < c.nt,
    ensures
        keep(keep(product_rows(seq![nst_row(c, i, t, k)], prows(c)), holds(db, p_np())), holds(db, p_where(ps)))
            == keep(prows(c), |p: Row| pre_cond_row(c, i, t, k, p)).map_values(|p: Row| nst_row(c, i, t, k) + p),
        forall|l: int| 0 <= l < c.npre ==> #[trigger] pre_cond_row(c, i, t, k, prows(c)[l]) == pre_cond(c, i, t, k, l),
{
    let z = nst_row(c, i, t, k);
    let pr = prows(c);
    let m = |r: Row| z + r;
    lemma_product_one_row(z, pr);
    let a3 = pr.map_values(m);
    lemma_keep_keep(a3, holds(db, p_np()), holds(db, p_where(ps)));
    let both = |x: Row| holds(db, p_np())(x) && holds(db, p_where(ps))(x);
    lemma_keep_map(pr, m, both);
    let g = |r: Row| both(m(r));
    assert forall|l: int| 0 <= l < pr.len() implies g(#[trigger] pr[l]) == pre_cond_row(c, i, t, k, pr[l]) by {
        assert(pr[l] == prow(c, l));
        assert(m(pr[l]) == full_row(c, i, t, k, l));
        lemma_eval_np(db, c, i, t, k, l);
        lemma_eval_where(db, c, ps, i, t, k, l);
        lemma_pre_cond_row(c, i, t, k, l);
    }
    lemma_keep_ext(pr, g, |p: Row| pre_cond_row(c, i, t, k, p));
    assert forall|l: int| 0 <= l < c.npre implies #[trigger] pre_cond_row(c, i, t, k, prows(c)[l]) == pre_cond(c, i, t, k, l) by {
        lemma_pre_cond_row(c, i, t, k, l);
    }
}

/// `pre_cond` as a condition on a pre table row (the row's position is recovered from `prow`).
pub open spec fn pre_cond_row(c: Ctx, i: int, t: int, k: int, p: Row) -> bool {
    exists|l: int| 0 <= l < c.npre && p == #[trigger] prow(c, l) && pre_cond(c, i, t, k, l)
}

/// The pre row `l` meets `pre_cond_row` exactly when it meets `pre_cond` (distinct pre rows may be equal rows;
/// equal rows meet `pre_cond` alike, because the condition reads only their cells).
proof fn lemma_pre_cond_row(c: Ctx, i: int, t: int, k: int, l: int)
    requires 0 <= l < c.npre,
    ensures pre_cond_row(c, i, t, k, prow(c, l)) == pre_cond(c, i, t, k, l),
{
    if pre_cond_row(c, i, t, k, prow(c, l)) {
        let l2 = choose|l2: int| 0 <= l2 < c.npre && prow(c, l) == #[trigger] prow(c, l2) && pre_cond(c, i, t, k, l2);
        lemma_cells(c, 0, 0, 0, l);
        lemma_cells(c, 0, 0, 0, l2);
        assert(prow(c, l)[0] == prow(c, l2)[0] && prow(c, l)[3] == prow(c, l2)[3]);
        assert(prow(c, l)[6] == prow(c, l2)[6] && prow(c, l)[7] == prow(c, l2)[7]);
    }
}

// ------------------------------------------------------------------------------------------------ records

/// The records below `x` of num row `i`: matching entries, increasing, each record `(i, e, value)`; and every
/// matching entry below `x` has one.
pub proof fn lemma_recs_mem(c: Ctx, ents: Seq<(usize, usize, usize)>, i: int, x: int)
    requires 0 <= x <= ents.len(), 0 <= i < usize::MAX, ents.len() < usize::MAX,
    ensures
        forall|q: int| 0 <= q < recs(c, ents, i, x).len() ==> {
            let r = #[trigger] recs(c, ents, i, x)[q];
            &&& r.0 as int == i && (r.1 as int) < x && ent_match(c, ents, i, r.1 as int) && r.2 == n_val_s(c)[i]
        },
        forall|q: int, u: int| 0 <= q < u < recs(c, ents, i, x).len() ==>
            (#[trigger] recs(c, ents, i, x)[q]).1 < (#[trigger] recs(c, ents, i, x)[u]).1,
        forall|e: int| 0 <= e < x && #[trigger] ent_match(c, ents, i, e) ==>
            exists|q: int| 0 <= q < recs(c, ents, i, x).len() && recs(c, ents, i, x)[q].1 as int == e,
    decreases x,
{
    if x > 0 {
        lemma_recs_mem(c, ents, i, x - 1);
        let a = recs(c, ents, i, x - 1);
        let b = recs(c, ents, i, x);
        if ent_match(c, ents, i, x - 1) {
            assert(b == a.push((i as usize, (x - 1) as usize, n_val_s(c)[i])));
            assert((i as usize) as int == i && ((x - 1) as usize) as int == x - 1);
            assert forall|q: int| 0 <= q < b.len() implies {
                let r = #[trigger] b[q];
                &&& r.0 as int == i && (r.1 as int) < x && ent_match(c, ents, i, r.1 as int) && r.2 == n_val_s(c)[i]
            } by {
                if q < a.len() {
                    assert(b[q] == a[q]);
                }
            }
            assert forall|q: int, u: int| 0 <= q < u < b.len() implies (#[trigger] b[q]).1 < (#[trigger] b[u]).1 by {
                if u < a.len() {
                    assert(b[q] == a[q] && b[u] == a[u]);
                } else {
                    assert(b[q] == a[q]);
                }
            }
            assert forall|e: int| 0 <= e < x && #[trigger] ent_match(c, ents, i, e) implies
                exists|q: int| 0 <= q < b.len() && b[q].1 as int == e by {
                if e < x - 1 {
                    let q = choose|q: int| 0 <= q < a.len() && a[q].1 as int == e;
                    assert(b[q] == a[q]);
                } else {
                    assert(b[a.len() as int].1 as int == e);
                }
            }
        } else {
            assert(b =~= a);
        }
    }
}

/// The selected pre rows are the entries' pre rows.
pub proof fn lemma_ent_rows(c: Ctx, ents: Seq<(usize, usize, usize)>, e: int)
    requires ents_ok(c, ents), 0 <= e < ents.len(),
    ensures
        pre_sel(c, ents[e].0 as int), 0 <= ents[e].0 < c.npre,
        sub_of(c, ents[e].1 as int, p_adsh(c, ents[e].0 as int)),
        tag_of(c, ents[e].2 as int, p_tag(c, ents[e].0 as int), p_ver(c, ents[e].0 as int)),
        forall|e2: int| 0 <= e2 < e ==> ents[e2].0 < #[trigger] ents[e].0,
{
    let ss = sel_in(c, 0, c.npre);
    assert(ents[e].0 as int == ss[e]);
    lemma_sel_mem(c, 0, c.npre, e);
    assert forall|e2: int| 0 <= e2 < e implies ents[e2].0 < #[trigger] ents[e].0 by {
        assert(ents[e2].0 as int == ss[e2]);
    }
}

/// For num row `i` with the sub row `t` of its adsh and the tag row `k` of its tag and version: the pre rows meeting
/// `pre_cond` are the pre rows of the matching entries, in order, and those entries have sub row `t` and tag row `k`.
#[verifier::spinoff_prover]
proof fn lemma_positions(c: Ctx, ents: Seq<(usize, usize, usize)>, i: int, t: int, k: int)
    requires
        ctx_ok(c), ents_ok(c, ents), 0 <= i < c.n, 0 <= t < c.m, 0 <= k < c.nt, c.n < usize::MAX, ents.len() < usize::MAX,
        s_adsh(c, t) == n_adsh(c, i), t_tag(c, k) == n_tag(c, i), t_ver(c, k) == n_ver(c, i),
    ensures ({
        let ro = row_out(c, ents, i);
        let ls = ro.map_values(|r: Rec| ents[r.1 as int].0 as int);
        &&& keep(prows(c), |p: Row| pre_cond_row(c, i, t, k, p)) == ls.map_values(|l: int| prows(c)[l])
        &&& forall|q: int| 0 <= q < ro.len() ==> ents[(#[trigger] ro[q]).1 as int].1 as int == t && ents[ro[q].1 as int].2 as int == k
    }),
{
    let ro = row_out(c, ents, i);
    let ls = ro.map_values(|r: Rec| ents[r.1 as int].0 as int);
    let pr = prows(c);
    let f = |p: Row| pre_cond_row(c, i, t, k, p);
    lemma_recs_mem(c, ents, i, ents.len() as int);
    lemma_keys(c);
    lemma_views(c);
    // Each matching entry has sub row `t`, tag row `k`, and its pre row meets the condition.
    assert forall|q: int| 0 <= q < ro.len() implies ents[(#[trigger] ro[q]).1 as int].1 as int == t
        && ents[ro[q].1 as int].2 as int == k && pre_cond(c, i, t, k, ents[ro[q].1 as int].0 as int) by {
        let e = ro[q].1 as int;
        lemma_ent_rows(c, ents, e);
        let (l, j, kk) = ents[e];
        assert(ent_match(c, ents, i, e));
        assert(s_adsh(c, j as int) == n_adsh(c, i));
        let s2 = choose|s2: int| #[trigger] sub_of(c, s2, n_adsh(c, i));
        assert(s_adsh(c, s2) == s_adsh(c, t));
        assert(t_tag(c, kk as int) == t_tag(c, k) && t_ver(c, kk as int) == t_ver(c, k));
    }
    assert forall|u: int| 0 <= u < ls.len() implies 0 <= #[trigger] ls[u] < pr.len() && f(pr[ls[u]]) by {
        let e = ro[u].1 as int;
        lemma_ent_rows(c, ents, e);
        assert(pr[ls[u]] == prow(c, ls[u]));
        lemma_pre_cond_row(c, i, t, k, ls[u]);
    }
    assert forall|u: int, w: int| 0 <= u < w < ls.len() implies #[trigger] ls[u] < #[trigger] ls[w] by {
        assert(ro[u].1 < ro[w].1);
        lemma_ent_rows(c, ents, ro[w].1 as int);
    }
    assert forall|l: int| 0 <= l < pr.len() && f(#[trigger] pr[l]) implies exists|u: int| 0 <= u < ls.len() && ls[u] == l by {
        assert(pr[l] == prow(c, l));
        lemma_pre_cond_row(c, i, t, k, l);
        assert(pre_cond(c, i, t, k, l));
        // The pre row is selected: its adsh has the selected sub row `t`, its tag the tag row `k`.
        assert(sub_of(c, t, p_adsh(c, l)));
        assert(tag_of(c, k, p_tag(c, l), p_ver(c, l)));
        assert(pre_sel(c, l));
        lemma_sel_complete(c, 0, c.npre, l);
        let ss = sel_in(c, 0, c.npre);
        let e = choose|e: int| 0 <= e < ss.len() && ss[e] == l;
        assert(ents[e].0 as int == ss[e]);
        assert(sub_of(c, t, n_adsh(c, i)));
        assert(ent_match(c, ents, i, e));
        let u = choose|u: int| 0 <= u < ro.len() && ro[u].1 as int == e;
        assert(ls[u] == l);
    }
    lemma_keep_positions(pr, f, ls);
}

/// The FROM/WHERE rows of one num row are its records' joined rows.
#[verifier::spinoff_prover]
pub proof fn lemma_st4_one(db: Database, c: Ctx, ps: Seq<Literal>, ents: Seq<(usize, usize, usize)>, i: int)
    requires db_ok(db, c), lits_ok(c, ps), ents_ok(c, ents), 0 <= i < c.n, c.n < usize::MAX, ents.len() < usize::MAX,
    ensures st4(db, c, ps, seq![nrow(c, i)]) == rec_rows(c, ents, row_out(c, ents, i)),
{
    let ro = row_out(c, ents, i);
    lemma_recs_mem(c, ents, i, ents.len() as int);
    lemma_st1_one(db, c, i);
    if !sub_any(c, i) {
        // No sub row: no rows, and no entry matches (a match has a selected sub row of this adsh).
        assert(product_rows(Seq::<Row>::empty(), trows(c)) == Seq::<Row>::empty());
        assert(product_rows(Seq::<Row>::empty(), prows(c)) == Seq::<Row>::empty());
        if ro.len() > 0 {
            assert(ent_match(c, ents, i, ro[0].1 as int));
            let s2 = choose|s2: int| #[trigger] sub_of(c, s2, n_adsh(c, i));
            assert(0 <= s2 < c.m && s_adsh(c, s2) == n_adsh(c, i));
        }
        assert(rec_rows(c, ents, ro) =~= Seq::<Row>::empty());
        return;
    }
    let t = choose|t: int| 0 <= t < c.m && #[trigger] s_adsh(c, t) == n_adsh(c, i);
    lemma_st2_one(db, c, i, t);
    if !tag_any(c, i) {
        // No tag row: no rows, and no entry matches (a match's entry has a tag row of this tag and version).
        assert(product_rows(Seq::<Row>::empty(), prows(c)) == Seq::<Row>::empty());
        if ro.len() > 0 {
            let e = ro[0].1 as int;
            assert(ent_match(c, ents, i, e));
            lemma_ent_rows(c, ents, e);
            let kk = ents[e].2 as int;
            assert(0 <= kk < c.nt && t_tag(c, kk) == n_tag(c, i) && t_ver(c, kk) == n_ver(c, i));
        }
        assert(rec_rows(c, ents, ro) =~= Seq::<Row>::empty());
        return;
    }
    let k = choose|k: int| 0 <= k < c.nt && #[trigger] t_tag(c, k) == n_tag(c, i) && t_ver(c, k) == n_ver(c, i);
    lemma_st34_one(db, c, ps, i, t, k);
    lemma_positions(c, ents, i, t, k);
    let z = nst_row(c, i, t, k);
    let ls = ro.map_values(|r: Rec| ents[r.1 as int].0 as int);
    let lhs = ls.map_values(|l: int| prows(c)[l]).map_values(|p: Row| z + p);
    assert forall|q: int| 0 <= q < ro.len() implies #[trigger] lhs[q] == rec_rows(c, ents, ro)[q] by {
        let e = ro[q].1 as int;
        lemma_ent_rows(c, ents, e);
        assert(prows(c)[ls[q]] == prow(c, ls[q]));
        assert(ro[q].0 as int == i);
    }
    assert(lhs =~= rec_rows(c, ents, ro));
}

/// The FROM/WHERE rows of the first `x` num rows are the records of those rows, joined.
proof fn lemma_st4_prefix(db: Database, c: Ctx, ps: Seq<Literal>, ents: Seq<(usize, usize, usize)>, x: int)
    requires db_ok(db, c), lits_ok(c, ps), ents_ok(c, ents), 0 <= x <= c.n, c.n < usize::MAX, ents.len() < usize::MAX,
    ensures st4(db, c, ps, Seq::new(x as nat, |i: int| nrow(c, i))) == rec_rows(c, ents, contrib(c, ents, 0, x)),
    decreases x,
{
    let a = Seq::new(x as nat, |i: int| nrow(c, i));
    if x == 0 {
        assert(a =~= Seq::<Row>::empty());
        assert(product_rows(Seq::<Row>::empty(), srows(c)) == Seq::<Row>::empty());
        assert(product_rows(Seq::<Row>::empty(), trows(c)) == Seq::<Row>::empty());
        assert(product_rows(Seq::<Row>::empty(), prows(c)) == Seq::<Row>::empty());
        assert(rec_rows(c, ents, contrib(c, ents, 0, 0)) =~= Seq::<Row>::empty());
    } else {
        let a0 = Seq::new((x - 1) as nat, |i: int| nrow(c, i));
        assert(a =~= a0.push(nrow(c, x - 1)));
        lemma_st4_prefix(db, c, ps, ents, x - 1);
        lemma_st4_push(db, c, ps, a0, nrow(c, x - 1));
        lemma_st4_one(db, c, ps, ents, x - 1);
        let r0 = contrib(c, ents, 0, x - 1);
        assert(contrib(c, ents, 0, x) == r0 + row_out(c, ents, x - 1));
        assert(rec_rows(c, ents, r0 + row_out(c, ents, x - 1)) =~= rec_rows(c, ents, r0) + rec_rows(c, ents, row_out(c, ents, x - 1)));
    }
}

/// The WHERE node's rows are the joined rows of all records.
pub proof fn lemma_where_rows(db: Database, c: Ctx, ps: Seq<Literal>, ents: Seq<(usize, usize, usize)>)
    requires db_ok(db, c), lits_ok(c, ps), ents_ok(c, ents), c.n < usize::MAX, ents.len() < usize::MAX,
    ensures st4(db, c, ps, nrows(c)) == rec_rows(c, ents, contrib(c, ents, 0, c.n)),
{
    lemma_st4_prefix(db, c, ps, ents, c.n);
    assert(Seq::new(c.n as nat, |i: int| nrow(c, i)) =~= nrows(c));
}

} // verus!
