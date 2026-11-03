//! ORDER BY total_value DESC LIMIT 200 over the group rows.
//!
//! The group rows `ar` (one per group, in any order) are split by a threshold `thr` on the sum: the candidates
//! (`sum >= thr`, `cidx`) and the rest. The candidates are sorted by an insertion sort that computes exactly the
//! spec's stable `sort_rows` (`sort_cands`, `lemma_insert_at`), so `bridge::order::lemma_sort_rows` gives its
//! order and its bag. The witness permutation of all group rows is the sorted candidates followed by the sorted
//! rest: every candidate's sum is at least `thr` and above every other sum. When there are at least 200 candidates
//! (or no other row) its first 200 rows are the first 200 sorted candidates (`lemma_final_rows`).
use vstd::prelude::*;
use vstd::multiset::Multiset;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::order::*;
use crate::bridge::order::*;
use crate::bridge::typing::val_family;
use crate::link::query::*;
use crate::link::expr::lemma_compare_num;
use crate::link::expr::lemma_align_same;
use crate::agent::ctx::*;
use crate::agent::sem::*;
use crate::agent::nf::*;
use crate::agent::sums::*;

verus! {

/// The LIMIT of the statement.
pub const LIMIT: usize = 200;

/// The row of a group: its key, `SUM` at scale 4 and `COUNT(*)`.
pub open spec fn grow(key: Row, sum: int, cnt: int) -> Row {
    key + seq![Val::Num { coeff: sum, scale: 4 }, Val::Int(cnt)]
}

/// The rows at indices `idx`.
pub open spec fn rows_at(ar: Seq<Row>, idx: Seq<usize>) -> Seq<Row> {
    idx.map_values(|i: usize| ar[i as int])
}

/// Rows with a numeric at scale 4 in column 4 (the ORDER BY key).
pub open spec fn sum_at(r: Row) -> int {
    r[4]->Num_coeff
}

pub open spec fn row_shape(r: Row) -> bool {
    r.len() == 6 && r[4] is Num && r[4]->Num_scale == 4
}

/// The order of two group rows: by sum, descending.
pub proof fn lemma_cmp_rows(a: Row, b: Row)
    requires row_shape(a), row_shape(b),
    ensures
        (keys_cmp(order_keys(), a, b) <= 0) == (sum_at(a) >= sum_at(b)),
        (keys_cmp(order_keys(), a, b) > 0) == (sum_at(a) < sum_at(b)),
{
    let k = order_keys();
    let sa = sum_at(a);
    let sb = sum_at(b);
    assert(k.drop_first() =~= Seq::<OrderKey>::empty());
    lemma_compare_num(sa, 4, sb, 4);
    assert(max_nat(4, 4) == 4);
    lemma_align_same(sa, 4);
    lemma_align_same(sb, 4);
    assert(a[4] == (Val::Num { coeff: sa, scale: 4 }));
    assert(b[4] == (Val::Num { coeff: sb, scale: 4 }));
    assert(compare(a[4], b[4]) == Some(sign(sa - sb)));
    let k0 = k[0];
    assert(k0.col == 4 && k0.desc);
    assert(key_cmp(k0, a, b) == -sign(sa - sb));
    reveal_with_fuel(keys_cmp, 2);
    assert(keys_cmp(k.drop_first(), a, b) == 0);
    assert(keys_cmp(k, a, b) == -sign(sa - sb));
}

/// The ORDER BY key families of group rows: one numeric key.
pub open spec fn ofams() -> Seq<int> {
    seq![val_family(Val::Num { coeff: 0, scale: 4 })]
}

pub proof fn lemma_keys_ok(r: Row)
    requires row_shape(r),
    ensures keys_ok(order_keys(), ofams(), r),
{
    assert(key_val(order_keys()[0], r) == r[4]);
    assert(val_family(r[4]) == val_family(Val::Num { coeff: 0, scale: 4 }));
}

/// Insertion of `x` before the rows of `s` from position `j` on (all of them greater than `x`).
pub proof fn lemma_insert_at(s: Seq<Row>, x: Row, j: int)
    requires
        0 <= j <= s.len(),
        forall|i: int| j <= i < s.len() ==> keys_cmp(order_keys(), #[trigger] s[i], x) > 0,
        j == 0 || keys_cmp(order_keys(), s[j - 1], x) <= 0,
    ensures insert_sorted(order_keys(), s, x) == s.take(j) + seq![x] + s.skip(j),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.take(0) + seq![x] + s.skip(0) =~= seq![x]);
    } else if j == s.len() {
        assert(s.take(j) + seq![x] + s.skip(j) =~= s.push(x));
    } else {
        let d = s.drop_last();
        assert forall|i: int| j <= i < d.len() implies keys_cmp(order_keys(), #[trigger] d[i], x) > 0 by {
            assert(d[i] == s[i]);
        }
        if j > 0 {
            assert(d[j - 1] == s[j - 1]);
        }
        lemma_insert_at(d, x, j);
        assert(keys_cmp(order_keys(), s[s.len() - 1], x) > 0);
        assert((d.take(j) + seq![x] + d.skip(j)).push(s.last()) =~= s.take(j) + seq![x] + s.skip(j));
    }
}

/// The candidates among indices `0..n`: values at least `thr`.
pub open spec fn cidx(fv: Seq<i128>, thr: i128, n: int) -> Seq<usize>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else {
        let d = cidx(fv, thr, n - 1);
        if fv[n - 1] >= thr { d.push((n - 1) as usize) } else { d }
    }
}

/// The other indices.
pub open spec fn ridx(fv: Seq<i128>, thr: i128, n: int) -> Seq<usize>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else {
        let d = ridx(fv, thr, n - 1);
        if fv[n - 1] >= thr { d } else { d.push((n - 1) as usize) }
    }
}

/// The candidate and other rows together are all rows.
pub proof fn lemma_split_bag(ar: Seq<Row>, fv: Seq<i128>, thr: i128, n: int)
    requires 0 <= n <= ar.len(), n <= fv.len(), n <= usize::MAX,
    ensures
        rows_at(ar, cidx(fv, thr, n)).to_multiset().add(rows_at(ar, ridx(fv, thr, n)).to_multiset()) == ar.take(n).to_multiset(),
        forall|t: int| 0 <= t < cidx(fv, thr, n).len() ==> (#[trigger] cidx(fv, thr, n)[t] as int) < n && fv[cidx(fv, thr, n)[t] as int] >= thr,
        forall|t: int| 0 <= t < ridx(fv, thr, n).len() ==> (#[trigger] ridx(fv, thr, n)[t] as int) < n && fv[ridx(fv, thr, n)[t] as int] < thr,
        cidx(fv, thr, n).len() + ridx(fv, thr, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_split_bag(ar, fv, thr, n - 1);
        let ci = cidx(fv, thr, n - 1);
        let ri = ridx(fv, thr, n - 1);
        let x = ar[n - 1];
        let a0 = rows_at(ar, ci).to_multiset();
        let b0 = rows_at(ar, ri).to_multiset();
        assert(ar.take(n) =~= ar.take(n - 1).push(x));
        ar.take(n - 1).to_multiset_ensures();
        rows_at(ar, ci).to_multiset_ensures();
        rows_at(ar, ri).to_multiset_ensures();
        assert(ar.take(n).to_multiset() == ar.take(n - 1).to_multiset().insert(x));
        if fv[n - 1] >= thr {
            assert(cidx(fv, thr, n) == ci.push((n - 1) as usize));
            assert(ridx(fv, thr, n) == ri);
            assert(rows_at(ar, ci.push((n - 1) as usize)) =~= rows_at(ar, ci).push(x));
            assert(rows_at(ar, ci).push(x).to_multiset() == a0.insert(x));
            assert(a0.insert(x).add(b0) =~= a0.add(b0).insert(x));
        } else {
            assert(ridx(fv, thr, n) == ri.push((n - 1) as usize));
            assert(cidx(fv, thr, n) == ci);
            assert(rows_at(ar, ri.push((n - 1) as usize)) =~= rows_at(ar, ri).push(x));
            assert(rows_at(ar, ri).push(x).to_multiset() == b0.insert(x));
            assert(a0.add(b0.insert(x)) =~= a0.add(b0).insert(x));
        }
    } else {
        let e = Seq::<Row>::empty();
        assert(ar.take(0) =~= e);
        assert(rows_at(ar, cidx(fv, thr, 0)) =~= e);
        assert(rows_at(ar, ridx(fv, thr, 0)) =~= e);
        e.to_multiset_ensures();
        assert(e.to_multiset().add(e.to_multiset()) =~= e.to_multiset());
    }
}

/// The candidate indices.
pub fn split_cands(fv: &Vec<i128>, n: usize, thr: i128) -> (cand: Vec<usize>)
    requires n <= fv@.len(),
    ensures cand@ == cidx(fv@, thr, n as int),
{
    let mut cand: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant n <= fv@.len(), i <= n, cand@ == cidx(fv@, thr, i as int),
        decreases n - i,
    {
        if fv[i] >= thr {
            cand.push(i);
        }
        i = i + 1;
    }
    cand
}

/// The candidates sorted by the statement's stable insertion sort (sums descending).
pub fn sort_cands(cand: &Vec<usize>, fv: &Vec<i128>, Ghost(ar): Ghost<Seq<Row>>) -> (sv: Vec<usize>)
    requires
        ar.len() == fv@.len(),
        forall|i: int| 0 <= i < ar.len() ==> row_shape(#[trigger] ar[i]) && sum_at(ar[i]) == fv@[i] as int,
        forall|t: int| 0 <= t < cand@.len() ==> (#[trigger] cand@[t] as int) < ar.len(),
    ensures
        rows_at(ar, sv@) == sort_rows(order_keys(), rows_at(ar, cand@)),
        sv@.len() == cand@.len(),
        forall|t: int| 0 <= t < sv@.len() ==> (#[trigger] sv@[t] as int) < ar.len(),
{
    let nc = cand.len();
    let mut sv: Vec<usize> = Vec::new();
    let ghost cr = rows_at(ar, cand@);
    let mut r: usize = 0;
    while r < nc
        invariant
            ar.len() == fv@.len(), nc == cand@.len(), r <= nc, cr == rows_at(ar, cand@),
            forall|i: int| 0 <= i < ar.len() ==> row_shape(#[trigger] ar[i]) && sum_at(ar[i]) == fv@[i] as int,
            forall|t: int| 0 <= t < cand@.len() ==> (#[trigger] cand@[t] as int) < ar.len(),
            sv@.len() == r,
            forall|t: int| 0 <= t < sv@.len() ==> (#[trigger] sv@[t] as int) < ar.len(),
            rows_at(ar, sv@) == sort_rows(order_keys(), cr.take(r as int)),
        decreases nc - r,
    {
        let x = cand[r];
        let fx = fv[x];
        let ghost old_sv = sv@;
        let ghost s = rows_at(ar, old_sv);
        let ghost xr = ar[x as int];
        sv.push(x);
        let mut j: usize = r;
        while j > 0 && fv[sv[j - 1]] < fx
            invariant
                ar.len() == fv@.len(), j <= r, sv@.len() == r + 1, old_sv.len() == r, s == rows_at(ar, old_sv),
                xr == ar[x as int], (x as int) < ar.len(), fx == fv@[x as int],
                forall|i: int| 0 <= i < ar.len() ==> row_shape(#[trigger] ar[i]) && sum_at(ar[i]) == fv@[i] as int,
                forall|t: int| 0 <= t < old_sv.len() ==> (#[trigger] old_sv[t] as int) < ar.len(),
                forall|t: int| 0 <= t < j ==> #[trigger] sv@[t] == old_sv[t],
                forall|t: int| j < t <= r ==> #[trigger] sv@[t] == old_sv[t - 1],
                forall|t: int| j <= t < r ==> fv@[old_sv[t] as int] < fx,
            decreases j,
        {
            let y = sv[j - 1];
            sv[j] = y;
            j = j - 1;
        }
        sv[j] = x;
        proof {
            assert forall|i: int| j <= i < s.len() implies keys_cmp(order_keys(), #[trigger] s[i], xr) > 0 by {
                lemma_cmp_rows(s[i], xr);
            }
            if j > 0 {
                lemma_cmp_rows(s[j - 1], xr);
                assert(sv@[j - 1] == old_sv[j - 1]);
            }
            lemma_insert_at(s, xr, j as int);
            assert(rows_at(ar, sv@) =~= s.take(j as int) + seq![xr] + s.skip(j as int));
            assert(cr.take(r + 1).drop_last() =~= cr.take(r as int));
            assert(cr.take(r + 1).last() == xr);
        }
        r = r + 1;
    }
    proof {
        assert(cr.take(nc as int) =~= cr);
    }
    sv
}

/// Group rows have the shape of the statement's output rows.
pub open spec fn grows_of(gl: Seq<Row>, fv: Seq<i128>, fc: Seq<u64>) -> Seq<Row> {
    Seq::new(gl.len(), |i: int| grow(gl[i], fv[i] as int, fc[i] as int))
}

/// The groups' arithmetic domain: every count fits int8 and every absolute mass `i128`.
pub proof fn lemma_caps(db: Database, c: Ctx)
    requires
        db_ok(db, c),
        forall|k: Row| #[trigger] gacc(c, 0, k, c.q) <= crate::spec::limits::int8_max(),
        forall|k: Row| #[trigger] gacc(c, 2, k, c.q) <= crate::link::expr::i128_max(),
    ensures group_caps(qs(c), jrows(db)),
{
    let g = qs(c);
    let jr = jrows(db);
    assert forall|k: Row, j: int| #![trigger gcount(g, jr, k), g.aggs[j]] 0 <= j < g.aggs.len() && g.aggs[j] is Count implies
        gcount(g, jr, k) <= crate::spec::limits::int8_max() by {
        lemma_gsums(db, c, k);
        assert(gacc(c, 0, k, c.q) <= crate::spec::limits::int8_max());
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies
        #[trigger] gabs(g, jr, k, j) <= crate::link::expr::i128_max() by {
        lemma_gsums(db, c, k);
        assert(j == 0);
        assert(gacc(c, 2, k, c.q) <= crate::link::expr::i128_max());
    }
}

/// The group rows, as a bag, are the statement's result rows.
pub proof fn lemma_rows_bag(db: Database, c: Ctx, gl: Seq<Row>, fv: Seq<i128>, fc: Seq<u64>)
    requires
        db_ok(db, c),
        gl.len() == fv.len(), gl.len() == fc.len(),
        gl.no_duplicates(),
        forall|k: Row| #[trigger] gl.contains(k) <==> gacc(c, 0, k, c.q) > 0,
        forall|i: int| 0 <= i < gl.len() ==> #[trigger] fc[i] as int == gacc(c, 0, gl[i], c.q),
        forall|i: int| 0 <= i < gl.len() ==> #[trigger] fv[i] as int == gacc(c, 1, gl[i], c.q),
        forall|i: int| 0 <= i < gl.len() ==> (#[trigger] gl[i]).len() == 4,
    ensures grows_of(gl, fv, fc).to_multiset() == result_rows(qs(c), jrows(db)).to_multiset(),
{
    let g = qs(c);
    let jr = jrows(db);
    let ar = grows_of(gl, fv, fc);
    lemma_gkeys(g, jr);
    assert forall|k: Row| gl.contains(k) <==> gkeys(g, jr).contains(k) by {
        lemma_gsums(db, c, k);
    }
    lemma_nodup_same_multiset(gl, gkeys(g, jr));
    let f = |k: Row| out_row(g, jr, k);
    lemma_map_multiset(gl, gkeys(g, jr), f);
    assert forall|i: int| 0 <= i < gl.len() implies #[trigger] ar[i] == f(gl[i]) by {
        let k = gl[i];
        lemma_gsums(db, c, k);
        assert(gl.contains(k));
        assert(gcount(g, jr, k) > 0);
        let fr = full_row(g, jr, k);
        assert(agg_outs(g, jr, k) =~= seq![Val::Num { coeff: fv[i] as int, scale: 4 }, Val::Int(fc[i] as int)]);
        lemma_select_identity(fr, g.outs);
        assert(fr =~= ar[i]);
    }
    assert(ar =~= gl.map_values(f));
}

/// Sorted candidates (at least `thr`) followed by the other rows sorted (below `thr`) are sorted.
pub proof fn lemma_witness_sorted(sc: Seq<Row>, sr: Seq<Row>, thr: int)
    requires
        sorted_by(order_keys(), sc), sorted_by(order_keys(), sr),
        forall|i: int| 0 <= i < sc.len() ==> row_shape(#[trigger] sc[i]) && sum_at(sc[i]) >= thr,
        forall|i: int| 0 <= i < sr.len() ==> row_shape(#[trigger] sr[i]) && sum_at(sr[i]) < thr,
    ensures sorted_by(order_keys(), sc + sr),
{
    let p = sc + sr;
    assert forall|i: int, j: int| 0 <= i < j < p.len() implies keys_cmp(order_keys(), #[trigger] p[i], #[trigger] p[j]) <= 0 by {
        if j < sc.len() {
            assert(p[i] == sc[i] && p[j] == sc[j]);
        } else if i >= sc.len() {
            assert(p[i] == sr[i - sc.len()] && p[j] == sr[j - sc.len()]);
        } else {
            assert(p[i] == sc[i] && p[j] == sr[j - sc.len()]);
            lemma_cmp_rows(p[i], p[j]);
        }
    }
}

/// The rows of a sorted bag lie in it.
proof fn lemma_sorted_member(s: Seq<Row>, t: Seq<Row>, i: int)
    requires s.to_multiset() == t.to_multiset(), 0 <= i < s.len(),
    ensures t.contains(s[i]),
{
    s.to_multiset_ensures();
    t.to_multiset_ensures();
    assert(s.to_multiset().count(s[i]) > 0);
}

/// The produced rows are an allowed output of the statement (normal path).
#[verifier::spinoff_prover]
pub proof fn lemma_final_rows(db: Database, c: Ctx, ps: Seq<Literal>, gl: Seq<Row>, fv: Seq<i128>, fc: Seq<u64>,
    thr: i128, cand: Seq<usize>, sv: Seq<usize>, out: Seq<Row>)
    requires
        db_ok(db, c), lits_ok(c, ps),
        gl.len() == fv.len(), gl.len() == fc.len(), gl.len() <= usize::MAX,
        gl.no_duplicates(),
        forall|k: Row| #[trigger] gl.contains(k) <==> gacc(c, 0, k, c.q) > 0,
        forall|i: int| 0 <= i < gl.len() ==> #[trigger] fc[i] as int == gacc(c, 0, gl[i], c.q),
        forall|i: int| 0 <= i < gl.len() ==> #[trigger] fv[i] as int == gacc(c, 1, gl[i], c.q),
        forall|i: int| 0 <= i < gl.len() ==> (#[trigger] gl[i]).len() == 4,
        forall|k: Row| #[trigger] gacc(c, 0, k, c.q) <= crate::spec::limits::int8_max(),
        forall|k: Row| #[trigger] gacc(c, 2, k, c.q) <= crate::link::expr::i128_max(),
        cand == cidx(fv, thr, gl.len() as int),
        rows_at(grows_of(gl, fv, fc), sv) == sort_rows(order_keys(), rows_at(grows_of(gl, fv, fc), cand)),
        cand.len() >= LIMIT || cand.len() == gl.len(),
        out == rows_at(grows_of(gl, fv, fc), sv).take(if sv.len() < LIMIT { sv.len() as int } else { LIMIT as int }),
    ensures ordered_ok(db, crate::query::query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let g = qs(c);
    let jr = jrows(db);
    let oq = crate::query::query_spec_at(ps);
    let ar = grows_of(gl, fv, fc);
    let n = gl.len() as int;
    lemma_query_shape(ps);
    lemma_caps(db, c);
    lemma_body(db, c, ps);
    lemma_rows_bag(db, c, gl, fv, fc);
    let cr = rows_at(ar, cand);
    let ri = ridx(fv, thr, n);
    let rr = rows_at(ar, ri);
    lemma_split_bag(ar, fv, thr, n);
    assert(ar.take(n) =~= ar);
    assert forall|i: int| 0 <= i < cr.len() implies keys_ok(order_keys(), ofams(), #[trigger] cr[i]) by {
        lemma_keys_ok(cr[i]);
    }
    assert forall|i: int| 0 <= i < rr.len() implies keys_ok(order_keys(), ofams(), #[trigger] rr[i]) by {
        lemma_keys_ok(rr[i]);
    }
    lemma_sort_rows(order_keys(), ofams(), cr);
    lemma_sort_rows(order_keys(), ofams(), rr);
    let sc = sort_rows(order_keys(), cr);
    let sr = sort_rows(order_keys(), rr);
    assert forall|i: int| 0 <= i < sc.len() implies row_shape(#[trigger] sc[i]) && sum_at(sc[i]) >= thr as int by {
        lemma_sorted_member(sc, cr, i);
        let t = choose|t: int| 0 <= t < cr.len() && cr[t] == sc[i];
        assert(cr[t] == ar[cand[t] as int]);
    }
    assert forall|i: int| 0 <= i < sr.len() implies row_shape(#[trigger] sr[i]) && sum_at(sr[i]) < thr as int by {
        lemma_sorted_member(sr, rr, i);
        let t = choose|t: int| 0 <= t < rr.len() && rr[t] == sr[i];
        assert(rr[t] == ar[ri[t] as int]);
    }
    let p = sc + sr;
    lemma_witness_sorted(sc, sr, thr as int);
    vstd::seq_lib::lemma_multiset_commutative(sc, sr);
    assert(p.to_multiset() == result_rows(g, jr).to_multiset());
    lemma_result_ok_from(g, order_keys(), 0, Some(200nat), jr, p);
    if cand.len() < LIMIT {
        assert(rr.len() == 0);
        assert(sr.len() == 0);
        assert(p =~= sc);
    }
    assert(sv.len() == cand.len()) by {
        cr.to_multiset_ensures();
        sc.to_multiset_ensures();
        assert(rows_at(ar, sv).len() == sv.len());
        assert(rows_at(ar, sv).len() == sc.len());
        assert(cr.len() == cand.len());
    }
    assert(slice_rows(p, 0, Some(200nat)) =~= out);
    lemma_ordered_link(db, oq, g, jr, out);
}

} // verus!
