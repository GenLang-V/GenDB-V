//! The plan's result and its link to the fixed claim. `res_ok`: the result pairs `(ps_partkey, SUM)` are exactly
//! the groups with a qualifying row whose SUM passes HAVING (`S * 10^10 > T * p`), each with its whole-table SUM,
//! keys distinct. Sorted by SUM descending (`msort::desc`), their rows `out_rows` are an allowed output of the
//! statement for every database bound to the parts (`lemma_final`); `lemma_final_cap` proves the Capacity answer.
//! `thr_of` turns the HAVING comparison into `S > thr` on `i128`; `build_answer` writes the columns.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::numeric::{abs, sign};
use crate::spec::scalar::compare;
use crate::spec::order::{ordered_ok, denote_body, sorted_by, keys_cmp, key_cmp, slice_rows};
use crate::exec::relational::domain::fits_query;
use crate::link::expr::{ival, fits_i128, i128_max};
use crate::link::query::*;
use crate::link::join::{keep, lemma_keep_map, lemma_keep_members};
use crate::gendb_entry::capacity_domain;
use crate::gendb_entry::results::{ResultColumn, ResultColumns, columns_view, columns_wf, column_value, column_wf};
use crate::query::{query_spec_at, param_domain};
use super::common::msort::desc;
use super::nf::*;
use super::sqlrow::*;
use super::sqlq::*;
use super::capq::lemma_capacity;
use super::rows::*;
use super::tables::Tabs;
use super::bind::tabs_of;

verus! {

pub open spec fn n_of(t: Tabs) -> int {
    t.ps.len() as int
}

/// `s * 10^10 > x`: a SUM `s` (scale 2) above `x` (scale 12).
pub open spec fn above(s: int, x: int) -> bool {
    s * 10000000000 > x
}

/// The result pairs: the groups that pass HAVING (`T` = `tsum`, `p` the coefficient of `$2`), keys distinct.
pub open spec fn res_ok(t: Tabs, name: Seq<u8>, res: Seq<(i64, i128)>, pc: int) -> bool {
    let n = n_of(t);
    let tc = tsum(t, name, 0, n);
    &&& forall|i: int| 0 <= i < res.len() ==> {
        &&& kcnt(t, name, #[trigger] res[i].0 as int, 0, n) > 0
        &&& res[i].1 as int == ksum(t, name, res[i].0 as int, 0, n)
        &&& above(res[i].1 as int, tc * pc)
    }
    &&& forall|i: int, j: int| 0 <= i < res.len() && 0 <= j < res.len() && i != j ==> #[trigger] res[i].0 != #[trigger] res[j].0
    &&& forall|k: int| #[trigger] kcnt(t, name, k, 0, n) > 0 && above(ksum(t, name, k, 0, n), tc * pc) ==>
            exists|i: int| 0 <= i < res.len() && res[i].0 as int == k
}

/// One output row: `ps_partkey, value` (scale 2).
pub open spec fn out_row_of(q: (i64, i128)) -> Row {
    seq![Val::Int(q.0 as int), Val::Num { coeff: q.1 as int, scale: 2 }]
}

pub open spec fn out_rows(res: Seq<(i64, i128)>) -> Seq<Row> {
    res.map_values(|q: (i64, i128)| out_row_of(q))
}

/// A kept element of a duplicate-free sequence: membership.
proof fn lemma_keep_contains(s: Seq<Row>, f: spec_fn(Row) -> bool, x: Row)
    requires s.contains(x), f(x),
    ensures keep(s, f).contains(x),
    decreases s.len(),
{
    crate::link::join::lemma_keep_push(s.drop_last(), s.last(), f);
    assert(s.drop_last().push(s.last()) =~= s);
    if s.last() == x {
        assert(keep(s, f).last() == x);
    } else {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
        assert(s.drop_last()[i] == x);
        lemma_keep_contains(s.drop_last(), f, x);
        let j = choose|j: int| 0 <= j < keep(s.drop_last(), f).len() && keep(s.drop_last(), f)[j] == x;
        assert(keep(s, f)[j] == x);
    }
}

/// `keep` of a duplicate-free sequence is duplicate-free.
proof fn lemma_keep_nodup(s: Seq<Row>, f: spec_fn(Row) -> bool)
    requires s.no_duplicates(),
    ensures keep(s, f).no_duplicates(),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        crate::link::join::lemma_keep_push(d, s.last(), f);
        assert(d.push(s.last()) =~= s);
        assert(d.no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < d.len() && 0 <= j < d.len() && i != j implies d[i] != d[j] by {
                assert(d[i] == s[i] && d[j] == s[j]);
            }
        }
        lemma_keep_nodup(d, f);
        if f(s.last()) {
            lemma_keep_members(d, f);
            let k = keep(d, f);
            assert forall|i: int, j: int| 0 <= i < k.len() + 1 && 0 <= j < k.len() + 1 && i != j implies
                k.push(s.last())[i] != k.push(s.last())[j] by {
                if i < k.len() && j < k.len() {
                } else {
                    let a = if i < k.len() { i } else { j };
                    assert(d.contains(k[a]));
                    let m = choose|m: int| 0 <= m < d.len() && d[m] == k[a];
                    assert(s[m] == d[m]);
                    assert(s[s.len() - 1] == s.last());
                }
            }
        }
    }
}

/// A group key of the normal form is `[Int k]` for the key `k` of a qualifying partsupp row.
proof fn lemma_group_key(t: Tabs, name: Seq<u8>, key: Row)
    requires tabs_typed(t), keys_unique(t), gcount(gq(name), xs(t), key) > 0,
    ensures
        key == seq![Val::Int(ival(key[0]))],
        kcnt(t, name, ival(key[0]), 0, n_of(t)) > 0,
{
    let x = xs(t);
    lemma_count_witness(gq(name), x, key);
    let m = choose|m: int| 0 <= m < x.len() && #[trigger] hit(gq(name), x[m], key);
    lemma_xs_typed(t);
    assert(x_typed(x[m]));
    assert(key == seq![x[m][0]]);
    assert(key =~= seq![Val::Int(ival(key[0]))]);
    lemma_bridge(t, name, ival(key[0]));
}

/// The rows of the result keys under the normal form are the output rows.
proof fn lemma_row_of(t: Tabs, name: Seq<u8>, q: (i64, i128))
    requires
        tabs_typed(t), keys_unique(t),
        kcnt(t, name, q.0 as int, 0, n_of(t)) > 0,
        q.1 as int == ksum(t, name, q.0 as int, 0, n_of(t)),
    ensures
        full_row(gq(name), xs(t), seq![Val::Int(q.0 as int)]) == out_row_of(q),
        gcount(gq(name), xs(t), seq![Val::Int(q.0 as int)]) > 0,
{
    lemma_bridge(t, name, q.0 as int);
    lemma_group_row_pub(gq(name), xs(t), seq![Val::Int(q.0 as int)]);
    assert(full_row(gq(name), xs(t), seq![Val::Int(q.0 as int)]) =~= out_row_of(q));
}

/// Descending SUMs are sorted by `value DESC`.
proof fn lemma_sorted_out(res: Seq<(i64, i128)>)
    requires desc(res),
    ensures sorted_by(order_keys(), out_rows(res)),
{
    let o = out_rows(res);
    assert forall|i: int, j: int| 0 <= i < j < o.len() implies keys_cmp(order_keys(), #[trigger] o[i], #[trigger] o[j]) <= 0 by {
        let (a, b) = (res[i].1 as int, res[j].1 as int);
        crate::link::expr::lemma_compare_num(a, 2, b, 2);
        crate::link::expr::lemma_align_same(a, 2);
        crate::link::expr::lemma_align_same(b, 2);
        assert(o[i][1] == Val::Num { coeff: a, scale: 2 });
        assert(o[j][1] == Val::Num { coeff: b, scale: 2 });
        assert(a >= b);
        assert(order_keys().drop_first() =~= Seq::<OrderKey>::empty());
        assert(keys_cmp(Seq::<OrderKey>::empty(), o[i], o[j]) == 0);
        let c = key_cmp(order_keys()[0], o[i], o[j]);
        assert(compare(o[i][1], o[j][1]) == Some(sign(a - b)));
        assert(c == -sign(a - b));
        assert(c <= 0);
        reveal_with_fuel(keys_cmp, 2);
    }
}

/// The parameters: `$1` text, `$2` a numeric coefficient at scale 10 in the declared bounds.
pub proof fn lemma_params(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        ps[0] is Text,
        p_ok(ps[1]),
        ps[1] == (Literal::Num { coeff: p_coeff(ps[1]), scale: 10 }),
{
    assert(crate::spec::numeric::pow10(38) == 100000000000000000000000000000000000000) by (compute);
}

/// The result, sorted by SUM descending, is an allowed output of the statement.
pub proof fn lemma_final(db: Database, ps: Seq<Literal>, res: Seq<(i64, i128)>)
    requires
        db.tables.len() == 8, tabs_typed(tabs_of(db)), keys_unique(tabs_of(db)),
        param_domain(ps),
        tabs(tabs_of(db), ps[0]->Text_0, 0, n_of(tabs_of(db))) <= i128_max(),
        res_ok(tabs_of(db), ps[0]->Text_0, res, p_coeff(ps[1])),
        desc(res),
    ensures ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out_rows(res))),
{
    let t = tabs_of(db);
    let name = ps[0]->Text_0;
    let p = ps[1];
    let pc = p_coeff(p);
    let x = xs(t);
    let g = gq(name);
    let e = Seq::<Val>::empty();
    let n = n_of(t);
    lemma_params(ps);
    lemma_query_shape(ps);
    assert(ps[0] == Literal::Text(name));
    // Capacity of the groups: the scalar mass bounds every group's.
    lemma_bridge(t, name, 0);
    crate::link::join::lemma_acc_sum_of(gs(name), x, e, 0);
    lemma_caps(t, name);
    lemma_body(db, name, p);
    let fr = |k: Row| full_row(g, x, k);
    let pf = |w: Row| passes(name, x, p, w);
    let body = keep(grows(name, x), pf);
    lemma_keep_map(gkeys(g, x), fr, pf);
    let kq = keep(gkeys(g, x), |y: Row| pf(fr(y)));
    assert(body == kq.map_values(fr));
    lemma_gkeys(g, x);
    lemma_keep_nodup(gkeys(g, x), |y: Row| pf(fr(y)));
    lemma_keep_members(gkeys(g, x), |y: Row| pf(fr(y)));
    // The result keys as group keys.
    let ks = res.map_values(|q: (i64, i128)| seq![Val::Int(q.0 as int)]);
    assert(ks.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < ks.len() && 0 <= j < ks.len() && i != j implies ks[i] != ks[j] by {
            assert(res[i].0 != res[j].0);
            if ks[i] == ks[j] {
                assert(ks[i][0] == ks[j][0]);
            }
        }
    }
    assert(gsum(gs(name), x, e, 0) == tsum(t, name, 0, n));
    assert forall|k: Row| ks.contains(k) <==> kq.contains(k) by {
        if ks.contains(k) {
            let i = choose|i: int| 0 <= i < ks.len() && ks[i] == k;
            let q = res[i];
            lemma_row_of(t, name, q);
            assert(gkeys(g, x).contains(k));
            assert(pf(fr(k)));
            lemma_keep_contains(gkeys(g, x), |y: Row| pf(fr(y)), k);
        }
        if kq.contains(k) {
            let i = choose|i: int| 0 <= i < kq.len() && kq[i] == k;
            assert(gkeys(g, x).contains(k) && pf(fr(k)));
            lemma_group_key(t, name, k);
            let kk = ival(k[0]);
            lemma_bridge(t, name, kk);
            lemma_group_row_pub(g, x, k);
            assert(above(ksum(t, name, kk, 0, n), tsum(t, name, 0, n) * pc));
            let j = choose|j: int| 0 <= j < res.len() && res[j].0 as int == kk;
            assert(ks[j] == k);
        }
    }
    lemma_nodup_same_multiset(ks, kq);
    lemma_map_multiset(ks, kq, fr);
    let o = out_rows(res);
    assert(o == ks.map_values(fr)) by {
        assert forall|i: int| 0 <= i < o.len() implies #[trigger] o[i] == ks.map_values(fr)[i] by {
            lemma_row_of(t, name, res[i]);
        }
        assert(o =~= ks.map_values(fr));
    }
    lemma_sorted_out(res);
    lemma_slice_all(o);
    assert(denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(body));
    assert(sorted_by(query_spec_at(ps).keys, o));
}

/// The Capacity answer: the mass of all qualifying rows exceeds `i128`, or `T * $2` does not fit `i128` (`T != 0`).
pub proof fn lemma_final_cap(db: Database, ps: Seq<Literal>)
    requires
        db.tables.len() == 8, tabs_typed(tabs_of(db)), keys_unique(tabs_of(db)),
        param_domain(ps),
        ({
            let t = tabs_of(db);
            let name = ps[0]->Text_0;
            let n = n_of(t);
            tabs(t, name, 0, n) > i128_max()
            || (tabs(t, name, 0, n) <= i128_max() && tsum(t, name, 0, n) != 0
                && !fits_i128(tsum(t, name, 0, n) * p_coeff(ps[1])))
        }),
    ensures !capacity_domain(db, query_spec_at(ps)),
{
    let t = tabs_of(db);
    let name = ps[0]->Text_0;
    let e = Seq::<Val>::empty();
    lemma_params(ps);
    lemma_query_shape(ps);
    assert(ps[0] == Literal::Text(name));
    lemma_bridge(t, name, 0);
    if gcount(gs(name), xs(t), e) == 0 {
        lemma_zero_count(gs(name), xs(t), e, 0);
    }
    lemma_capacity(db, name, ps[1]);
}

/// The result pairs in any order: `res_ok` holds of every permutation.
pub proof fn lemma_res_ok_perm(t: Tabs, name: Seq<u8>, a: Seq<(i64, i128)>, b: Seq<(i64, i128)>, pc: int)
    requires res_ok(t, name, a, pc), a.to_multiset() == b.to_multiset(),
    ensures res_ok(t, name, b, pc),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    let n = n_of(t);
    let tc = tsum(t, name, 0, n);
    // Distinct keys make `a` duplicate-free, so `b` (same multiset) is too.
    assert(a.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j implies a[i] != a[j] by {
            assert(a[i].0 != a[j].0);
        }
    }
    a.lemma_multiset_has_no_duplicates();
    assert forall|x: (i64, i128)| b.to_multiset().contains(x) implies b.to_multiset().count(x) == 1 by {
        assert(a.to_multiset().contains(x));
    }
    b.lemma_multiset_has_no_duplicates_conv();
    // Each element of `b` is an element of `a`, and conversely.
    assert forall|i: int| 0 <= i < b.len() implies exists|p: int| 0 <= p < a.len() && #[trigger] a[p] == #[trigger] b[i] by {
        assert(b.contains(b[i]));
        assert(b.to_multiset().count(b[i]) > 0);
        assert(a.to_multiset().count(b[i]) > 0);
        assert(a.contains(b[i]));
    }
    assert forall|i: int| 0 <= i < b.len() implies {
        &&& kcnt(t, name, #[trigger] b[i].0 as int, 0, n) > 0
        &&& b[i].1 as int == ksum(t, name, b[i].0 as int, 0, n)
        &&& above(b[i].1 as int, tc * pc)
    } by {
        let p = choose|p: int| 0 <= p < a.len() && #[trigger] a[p] == b[i];
        assert(kcnt(t, name, a[p].0 as int, 0, n) > 0);
    }
    assert forall|i: int, j: int| 0 <= i < b.len() && 0 <= j < b.len() && i != j implies #[trigger] b[i].0 != #[trigger] b[j].0 by {
        let p = choose|p: int| 0 <= p < a.len() && #[trigger] a[p] == b[i];
        let q = choose|q: int| 0 <= q < a.len() && #[trigger] a[q] == b[j];
        assert(b[i] != b[j]);
        if p != q {
            assert(a[p].0 != a[q].0);
        }
    }
    assert forall|k: int| #[trigger] kcnt(t, name, k, 0, n) > 0 && above(ksum(t, name, k, 0, n), tc * pc) implies
        exists|i: int| 0 <= i < b.len() && b[i].0 as int == k by {
        let p = choose|p: int| 0 <= p < a.len() && a[p].0 as int == k;
        assert(a.contains(a[p]));
        assert(a.to_multiset().count(a[p]) > 0);
        assert(b.to_multiset().count(a[p]) > 0);
        assert(b.contains(a[p]));
        let i = choose|i: int| 0 <= i < b.len() && b[i] == a[p];
    }
}

// ------------------------------------------------------------------------------------------------ exec pieces

/// `floor(x / 10^10)`: an integer `s` exceeds it exactly when `s * 10^10 > x`.
pub fn thr_of(x: i128) -> (r: i128)
    ensures forall|s: int| #[trigger] above(s, x as int) <==> s > r,
{
    let d: i128 = 10_000_000_000;
    if x >= 0 {
        let q = x / d;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, d as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(x as int, d as int);
            let (qq, rr) = (x as int / d as int, x as int % d as int);
            assert forall|s: int| #[trigger] above(s, x as int) <==> s > q by {
                if s > qq {
                    assert(s * 10000000000 >= qq * 10000000000 + 10000000000) by (nonlinear_arith) requires s > qq;
                } else {
                    assert(s * 10000000000 <= qq * 10000000000) by (nonlinear_arith) requires s <= qq;
                }
            }
        }
        q
    } else {
        let y: i128 = -(x + 1);
        let q = y / d;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(y as int, d as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(y as int, d as int);
            let qq = y as int / d as int;
            assert forall|s: int| #[trigger] above(s, x as int) <==> s > -q - 1 by {
                if s > -qq - 1 {
                    assert(s * 10000000000 >= -qq * 10000000000) by (nonlinear_arith) requires s >= -qq;
                } else {
                    assert(s * 10000000000 <= -qq * 10000000000 - 10000000000) by (nonlinear_arith) requires s <= -qq - 1;
                }
            }
        }
        -q - 1
    }
}

/// The columnar answer of the result rows: `ps_partkey` (bigint) and `value` (numeric, scale 2).
pub fn build_answer(res: &Vec<(i64, i128)>) -> (a: ResultColumns)
    ensures columns_wf(a), columns_view(a) == out_rows(res@),
{
    let m = res.len();
    let mut keys: Vec<i64> = Vec::with_capacity(m);
    let mut vals: Vec<i128> = Vec::with_capacity(m);
    let mut i: usize = 0;
    while i < m
        invariant
            m == res@.len(), i <= m, keys@.len() == i, vals@.len() == i,
            forall|x: int| 0 <= x < i ==> #[trigger] keys@[x] == res@[x].0 && vals@[x] == res@[x].1,
        decreases m - i,
    {
        keys.push(res[i].0);
        vals.push(res[i].1);
        i = i + 1;
    }
    let ghost kv = keys@;
    let ghost vv = vals@;
    let c0 = ResultColumn::Int(keys);
    let c1 = ResultColumn::Num { coeffs: vals, scale: 2 };
    assert(forall|x: int| 0 <= x < m ==> #[trigger] column_value(c0, x) == Val::Int(kv[x] as int));
    assert(forall|x: int| 0 <= x < m ==> #[trigger] column_value(c1, x) == Val::Num { coeff: vv[x] as int, scale: 2 });
    let mut cols: Vec<ResultColumn> = Vec::new();
    cols.push(c0);
    cols.push(c1);
    let a = ResultColumns { rows: m, columns: cols };
    proof {
        assert forall|k: int| 0 <= k < a.columns@.len() implies column_wf(#[trigger] a.columns@[k], a.rows as nat) by {}
        let o = out_rows(res@);
        assert forall|x: int| 0 <= x < o.len() implies #[trigger] o[x].len() == a.columns@.len() by {}
        assert forall|x: int, k: int| 0 <= x < o.len() && 0 <= k < a.columns@.len() implies #[trigger] o[x][k] == column_value(a.columns@[k], x) by {
            assert(a.columns@[0] == c0 && a.columns@[1] == c1);
            assert(column_value(c0, x) == Val::Int(kv[x] as int));
            assert(column_value(c1, x) == Val::Num { coeff: vv[x] as int, scale: 2 });
        }
        crate::gendb_entry::results::lemma_columns_view_eq(a, o);
    }
    a
}

} // verus!
