//! The statement's answers in terms of the stored arrays.
//!
//! Rows (`lemma_answer_rows`): let `L` list (sum, key) pairs with distinct keys that are exactly the groups whose sum
//! exceeds `thr` (`list_ok`: each a whole group, every passing group present), where `thr` is `total * $2 / 10^10`
//! rounded down (`thr_ok`, so `sum > thr` is the HAVING condition); then any permutation `F` of `L` sorted by sum,
//! descending, gives the allowed output `(ps_partkey, value)` rows `F.map(row_of)`.
//!
//! Capacity (`lemma_answer_capacity`): some row qualifies and the total absolute mass or `total * $2` leaves `i128`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::query::query_spec_at;
use crate::exec::relational::domain::fits_query;
use crate::link::expr::{ival, i128_max, lemma_compare_num, lemma_align_same};
use crate::link::query::*;
use crate::link::join::keep;
use crate::gendb_entry::{bound_db, capacity_domain};
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem::*;
use crate::agent::normal::*;
use crate::agent::body::*;
use crate::agent::capacity::*;
use crate::agent::groups::*;
use crate::agent::common::msort::desc;
use crate::agent::common::keep::{lemma_keep_contains, lemma_keep_nodup};

verus! {

/// The output row of a (sum, key) pair.
pub open spec fn row_of(e: (int, int)) -> Row {
    seq![Val::Int(e.1), Val::Num { coeff: e.0, scale: 2 }]
}

/// `thr` is `tc / 10^10` rounded down.
pub open spec fn thr_ok(thr: int, tc: int) -> bool {
    thr * 10_000_000_000 <= tc < (thr + 1) * 10_000_000_000
}

/// Pair `e` is a whole group of all partsupp rows: its sum and a positive count.
pub open spec fn grp_ok(sv: StoresView, p: Seq<u8>, e: (int, int)) -> bool {
    &&& e.0 == rsum(sv, p, t_sum(sv, e.1), 0, ps_n(sv) as int)
    &&& rsum(sv, p, t_cnt(sv, e.1), 0, ps_n(sv) as int) > 0
}

/// `l` lists, with distinct keys, exactly the groups whose sum exceeds `thr`.
pub open spec fn list_ok(sv: StoresView, p: Seq<u8>, thr: int, l: Seq<(int, int)>) -> bool {
    &&& forall|i: int| 0 <= i < l.len() ==> grp_ok(sv, p, #[trigger] l[i]) && l[i].0 > thr
    &&& forall|i: int, j: int| 0 <= i < l.len() && 0 <= j < l.len() && i != j ==> (#[trigger] l[i]).1 != (#[trigger] l[j]).1
    &&& forall|k: int| rsum(sv, p, t_cnt(sv, k), 0, ps_n(sv) as int) > 0
        && #[trigger] rsum(sv, p, t_sum(sv, k), 0, ps_n(sv) as int) > thr
        ==> exists|i: int| 0 <= i < l.len() && l[i].1 == k
}

/// `s > thr` is the HAVING condition `s * 10^10 > tc`.
pub proof fn lemma_thr(thr: int, tc: int, s: int)
    requires thr_ok(thr, tc),
    ensures (s > thr) == (s * 10_000_000_000 > tc),
{
    if s > thr {
        assert(s * 10_000_000_000 >= (thr + 1) * 10_000_000_000) by (nonlinear_arith) requires s >= thr + 1;
    } else {
        assert(s * 10_000_000_000 <= thr * 10_000_000_000) by (nonlinear_arith) requires s <= thr;
    }
}

/// The row of a group key `kr(k)` among the group rows.
proof fn lemma_group_row_of(sv: StoresView, p: Seq<u8>, k: int)
    requires stores_wf(sv), keys_ok(sv), rsum(sv, p, t_cnt(sv, k), 0, ps_n(sv) as int) > 0,
    ensures group_rows_of(sv, p).contains(row_of((rsum(sv, p, t_sum(sv, k), 0, ps_n(sv) as int), k))),
{
    let xs = from_rows(sv);
    lemma_grouped_acc(sv, p, k);
    lemma_gkeys(gq(p), xs);
    let ks = gkeys(gq(p), xs);
    assert(ks.contains(kr(k)));
    let i = choose|i: int| 0 <= i < ks.len() && ks[i] == kr(k);
    lemma_group_row(sv, p, kr(k));
    let f = full_row(gq(p), xs, kr(k));
    assert(f =~= row_of((rsum(sv, p, t_sum(sv, k), 0, ps_n(sv) as int), k)));
    assert(group_rows_of(sv, p)[i] == f);
}

/// Every group row is the row of some key with rows.
proof fn lemma_group_row_from(sv: StoresView, p: Seq<u8>, r: Row)
    requires stores_wf(sv), keys_ok(sv), group_rows_of(sv, p).contains(r),
    ensures exists|k: int| rsum(sv, p, t_cnt(sv, k), 0, ps_n(sv) as int) > 0
        && r == row_of((rsum(sv, p, t_sum(sv, k), 0, ps_n(sv) as int), k)),
{
    let xs = from_rows(sv);
    let ks = gkeys(gq(p), xs);
    let i = choose|i: int| 0 <= i < group_rows_of(sv, p).len() && group_rows_of(sv, p)[i] == r;
    let kk = ks[i];
    assert(ks.contains(kk));
    lemma_group_row(sv, p, kk);
    let k = choose|k: int| kk == kr(k);
    lemma_grouped_acc(sv, p, k);
    lemma_gkeys(gq(p), xs);
    assert(r =~= row_of((rsum(sv, p, t_sum(sv, k), 0, ps_n(sv) as int), k)));
}

/// The group rows are distinct.
proof fn lemma_group_rows_nodup(sv: StoresView, p: Seq<u8>)
    requires stores_wf(sv),
    ensures group_rows_of(sv, p).no_duplicates(),
{
    let xs = from_rows(sv);
    let ks = gkeys(gq(p), xs);
    let g = group_rows_of(sv, p);
    lemma_gkeys(gq(p), xs);
    assert forall|i: int, j: int| 0 <= i < g.len() && 0 <= j < g.len() && i != j implies g[i] != g[j] by {
        assert(ks.contains(ks[i]) && ks.contains(ks[j]));
        lemma_group_row(sv, p, ks[i]);
        lemma_group_row(sv, p, ks[j]);
        let a = choose|a: int| ks[i] == kr(a);
        let b = choose|b: int| ks[j] == kr(b);
        if g[i] == g[j] {
            assert(g[i][0] == g[j][0]);
            assert(ks[i] =~= ks[j]);
        }
    }
}

/// The output rows of a list with distinct keys are distinct.
proof fn lemma_rows_nodup(l: Seq<(int, int)>)
    requires forall|i: int, j: int| 0 <= i < l.len() && 0 <= j < l.len() && i != j ==> (#[trigger] l[i]).1 != (#[trigger] l[j]).1,
    ensures l.map_values(|e: (int, int)| row_of(e)).no_duplicates(),
{
    let o = l.map_values(|e: (int, int)| row_of(e));
    assert forall|i: int, j: int| 0 <= i < o.len() && 0 <= j < o.len() && i != j implies o[i] != o[j] by {
        if o[i] == o[j] {
            assert(o[i][0] == o[j][0]);
        }
    }
}

/// A list sorted by sum (descending) gives rows sorted by `value DESC`.
proof fn lemma_sorted_rows(f: Seq<(int, int)>)
    requires desc(f),
    ensures sorted_by(order_keys(), f.map_values(|e: (int, int)| row_of(e))),
{
    let o = f.map_values(|e: (int, int)| row_of(e));
    assert forall|i: int, j: int| 0 <= i < j < o.len() implies keys_cmp(order_keys(), #[trigger] o[i], #[trigger] o[j]) <= 0 by {
        let (a, b) = (f[i].0, f[j].0);
        assert(a >= b);
        assert(o[i] == row_of(f[i]) && o[j] == row_of(f[j]));
        assert(o[i][1] == Val::Num { coeff: a, scale: 2 } && o[j][1] == Val::Num { coeff: b, scale: 2 });
        lemma_compare_num(a, 2, b, 2);
        lemma_align_same(a, 2);
        lemma_align_same(b, 2);
        assert(max_nat(2, 2) == 2);
        assert(compare(o[i][1], o[j][1]) == Some(sign(a - b)));
        let k = order_keys()[0];
        assert(k.col == 1 && k.desc);
        assert(key_cmp(k, o[i], o[j]) == -sign(a - b));
        assert(order_keys().drop_first() =~= Seq::<OrderKey>::empty());
        assert(keys_cmp(order_keys().drop_first(), o[i], o[j]) == 0);
        assert(keys_cmp(order_keys(), o[i], o[j]) == -sign(a - b));
    }
}

/// The rows answer: any descending permutation of a complete list of passing groups is an allowed output.
pub proof fn lemma_answer_rows(sv: StoresView, p: Seq<u8>, c2: int, thr: int, l: Seq<(int, int)>, f: Seq<(int, int)>)
    requires
        stores_wf(sv), keys_ok(sv), bounds_ok(sv),
        rsum(sv, p, t_absv(sv), 0, ps_n(sv) as int) <= i128_max(),
        -100000000000000000000000000000000000000 < c2 < 100000000000000000000000000000000000000,
        thr_ok(thr, rsum(sv, p, t_val(sv), 0, ps_n(sv) as int) * c2),
        list_ok(sv, p, thr, l),
        f.to_multiset() == l.to_multiset(),
        desc(f),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db)
            ==> ordered_ok(db, query_spec_at(params_of(p, c2)), Ok::<Relation, SqlError>(f.map_values(|e: (int, int)| row_of(e)))),
{
    let ps = params_of(p, c2);
    let n = ps_n(sv) as int;
    let xs = from_rows(sv);
    let t = rsum(sv, p, t_val(sv), 0, n);
    let rf = |e: (int, int)| row_of(e);
    let out = f.map_values(rf);
    let lr = l.map_values(rf);
    lemma_scalar_acc(sv, p);
    lemma_caps(p, xs);
    let g = group_rows_of(sv, p);
    let b = keep(g, hv(t, c2));
    // the body's rows are the rows of `l`
    lemma_group_rows_nodup(sv, p);
    lemma_keep_nodup(g, hv(t, c2));
    lemma_rows_nodup(l);
    assert forall|r: Row| lr.contains(r) <==> b.contains(r) by {
        lemma_keep_contains(g, hv(t, c2), r);
        if lr.contains(r) {
            let i = choose|i: int| 0 <= i < lr.len() && lr[i] == r;
            assert(grp_ok(sv, p, l[i]) && l[i].0 > thr);
            lemma_group_row_of(sv, p, l[i].1);
            assert(r == row_of(l[i]));
            lemma_thr(thr, t * c2, l[i].0);
        }
        if b.contains(r) {
            lemma_group_row_from(sv, p, r);
            let k = choose|k: int| rsum(sv, p, t_cnt(sv, k), 0, n) > 0 && r == row_of((rsum(sv, p, t_sum(sv, k), 0, n), k));
            let s = rsum(sv, p, t_sum(sv, k), 0, n);
            assert(ival(r[1]) == s);
            lemma_thr(thr, t * c2, s);
            let i = choose|i: int| 0 <= i < l.len() && l[i].1 == k;
            assert(grp_ok(sv, p, l[i]));
            assert(l[i] == (s, k));
            assert(lr[i] == r);
        }
    }
    lemma_nodup_same_multiset(lr, b);
    lemma_map_multiset(f, l, rf);
    lemma_sorted_rows(f);
    lemma_slice_all(out);
    assert forall|db: Database| #[trigger] bound_db(sv, db)
        implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)) by {
        lemma_tables(sv, db);
        lemma_bounds(sv, db);
        lemma_query_shape(ps);
        lemma_body_rows(db, sv, p, c2);
        assert(denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(b));
        assert(out.to_multiset() == b.to_multiset());
        assert(sorted_by(query_spec_at(ps).keys, out));
    }
}

/// Every group fits `i128`: the grouped block's `group_caps`.
proof fn lemma_caps_grouped(p: Seq<u8>, xs: Seq<Row>)
    requires forall|k: Row| #[trigger] gabs(gq(p), xs, k, 0) <= i128_max(),
    ensures group_caps(gq(p), xs),
{
    assert forall|k: Row, j: int| 0 <= j < gq(p).aggs.len() && !(gq(p).aggs[j] is Count)
        implies #[trigger] gabs(gq(p), xs, k, j) <= i128_max() by {
        assert(j == 0);
    }
}

/// The capacity answer: some row qualifies and the total absolute mass or `total * $2` leaves `i128`.
pub proof fn lemma_answer_capacity(sv: StoresView, p: Seq<u8>, c2: int)
    requires
        stores_wf(sv), keys_ok(sv), bounds_ok(sv),
        -100000000000000000000000000000000000000 < c2 < 100000000000000000000000000000000000000,
        rsum(sv, p, t_one(), 0, ps_n(sv) as int) > 0,
        rsum(sv, p, t_absv(sv), 0, ps_n(sv) as int) > i128_max()
            || !(i128::MIN as int <= rsum(sv, p, t_val(sv), 0, ps_n(sv) as int) * c2 <= i128::MAX as int),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> !capacity_domain(db, query_spec_at(params_of(p, c2))),
{
    let ps = params_of(p, c2);
    let xs = from_rows(sv);
    let e = Seq::<Val>::empty();
    lemma_scalar_acc(sv, p);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies !capacity_domain(db, query_spec_at(ps)) by {
        lemma_tables(sv, db);
        lemma_bounds(sv, db);
        lemma_query_shape(ps);
        if exists|k: Row| #[trigger] gabs(gq(p), xs, k, 0) > i128_max() {
            let k = choose|k: Row| #[trigger] gabs(gq(p), xs, k, 0) > i128_max();
            lemma_cap_group(db, sv, p, c2, k);
        } else {
            lemma_caps_grouped(p, xs);
            if gabs(sq(p), xs, e, 0) > i128_max() {
                lemma_cap_total(db, sv, p, c2);
            } else {
                lemma_caps(p, xs);
                lemma_cap_scaled(db, sv, p, c2);
            }
        }
    }
}

} // verus!
