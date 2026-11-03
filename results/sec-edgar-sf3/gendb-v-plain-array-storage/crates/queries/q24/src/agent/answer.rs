//! The answer from the groups (calling thread): the groups with COUNT(*) > 10 (`having_idx`, the HAVING in group
//! order), sorted by COUNT(*) descending with a stable insertion sort that is exactly the specification's
//! `sort_rows` (`sort_idx`), and the first 100 of them as result rows (`out_rows`). `lemma_answer` states that these
//! rows are an allowed output of the statement on every database bound to the parts.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::relation::keep_true;
use crate::spec::scalar::*;
use crate::spec::limits::int8_max;
use crate::exec::value::{EVal, view_row};
use crate::link::query::*;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::link::expr::i128_max;
use crate::agent::spec::*;
use crate::agent::sem::*;
use crate::agent::txt::*;
use crate::agent::group::*;
use crate::agent::scan::{kept, lemma_keep_range_len};

verus! {

/// The result row of a group: `[tag, version, COUNT(*), SUM(value)]`.
pub open spec fn grow(c: Ctx, rep: int, cnt: int, sum: int) -> Row {
    seq![Val::Text(ntag(c, rep)), Val::Text(nver(c, rep)), Val::Int(cnt), Val::Num { coeff: sum, scale: 4 }]
}

pub open spec fn grows(c: Ctx, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>) -> Seq<Row> {
    Seq::new(reps.len(), |t: int| grow(c, reps[t] as int, cnts[t] as int, sums[t] as int))
}

/// The GROUP BY rows are the groups' rows.
pub proof fn lemma_grows(c: Ctx, xs: Seq<Row>, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>, masses: Seq<u128>)
    requires groups_ok(c, xs, reps, cnts, sums, masses),
    ensures grp_rows(c, xs) == grows(c, reps, cnts, sums),
{
    let g = nf(c);
    let ks = gkeys(g, xs);
    lemma_groups_reps(c, xs, reps, cnts, sums, masses);
    lemma_gkeys(g, xs);
    assert forall|t: int| 0 <= t < ks.len() implies #[trigger] grp_rows(c, xs)[t] == grows(c, reps, cnts, sums)[t] by {
        lemma_groups_at(c, xs, reps, cnts, sums, masses, t);
        assert((reps[t] as int) < c.n && ks[t] == nf_key(xrow(c, reps[t] as int)));
        lemma_xrow_key(c, reps[t] as int);
        assert(ks.contains(ks[t]));
        assert(gcount(g, xs, ks[t]) > 0);
        assert(agg_outs(g, xs, ks[t]) =~= seq![Val::Int(cnts[t] as int), Val::Num { coeff: sums[t] as int, scale: 4 }]);
        assert(full_row(g, xs, ks[t]) =~= grow(c, reps[t] as int, cnts[t] as int, sums[t] as int));
    }
    assert(grp_rows(c, xs) =~= grows(c, reps, cnts, sums));
}

// ------------------------------------------------------------------------------------------------ HAVING

/// The groups among `0..t` with COUNT(*) > 10, in order.
pub open spec fn hsel(cnts: Seq<u64>, t: int) -> Seq<usize>
    decreases t,
{
    if t <= 0 {
        Seq::empty()
    } else if cnts[t - 1] > 10 {
        hsel(cnts, t - 1).push((t - 1) as usize)
    } else {
        hsel(cnts, t - 1)
    }
}

pub fn having_idx(cnts: &Vec<u64>) -> (h: Vec<usize>)
    ensures h@ == hsel(cnts@, cnts@.len() as int),
{
    let mut h: Vec<usize> = Vec::new();
    let n = cnts.len();
    let mut t: usize = 0;
    while t < n
        invariant t <= n, n == cnts@.len(), h@ == hsel(cnts@, t as int),
        decreases n - t,
    {
        if cnts[t] > 10 {
            h.push(t);
        }
        t = t + 1;
    }
    h
}

/// The HAVING keeps the rows of the selected groups.
pub proof fn lemma_having_rows(rows: Seq<Row>, cnts: Seq<u64>, t: int)
    requires
        rows.len() == cnts.len(), 0 <= t <= rows.len(), rows.len() <= usize::MAX,
        forall|q: int| 0 <= q < rows.len() ==> #[trigger] row_cnt(rows[q]) == cnts[q] as int,
    ensures
        keep_true(rows.take(t), having_truths(rows).take(t)) == hsel(cnts, t).map_values(|q: usize| rows[q as int]),
        forall|q: int| 0 <= q < hsel(cnts, t).len() ==> (#[trigger] hsel(cnts, t)[q] as int) < t,
    decreases t,
{
    let f = |q: usize| rows[q as int];
    if t == 0 {
        assert(rows.take(0).len() == 0);
        assert(hsel(cnts, 0).map_values(f) =~= Seq::<Row>::empty());
    } else {
        lemma_having_rows(rows, cnts, t - 1);
        let rt = rows.take(t);
        let tt = having_truths(rows).take(t);
        assert(rt.drop_last() =~= rows.take(t - 1));
        assert(tt.drop_last() =~= having_truths(rows).take(t - 1));
        assert(rt.last() == rows[t - 1]);
        assert(tt.last() == truth_of(cnts[t - 1] > 10));
        if cnts[t - 1] > 10 {
            assert(((t - 1) as usize) as int == t - 1);
            assert(hsel(cnts, t) == hsel(cnts, t - 1).push((t - 1) as usize));
            assert(hsel(cnts, t).map_values(f) =~= hsel(cnts, t - 1).map_values(f).push(rows[t - 1]));
        }
    }
}

// ------------------------------------------------------------------------------------------------ ORDER BY

/// On rows whose third column is an integer count, the ORDER BY key compares the counts, larger first.
pub proof fn lemma_keys_cmp(a: Row, b: Row)
    requires a.len() == 4, b.len() == 4, a[2] is Int, b[2] is Int,
    ensures
        keys_cmp(order_keys(), a, b) <= 0 <==> row_cnt(a) >= row_cnt(b),
        keys_cmp(order_keys(), a, b) == 0 <==> row_cnt(a) == row_cnt(b),
{
    let k = order_keys();
    assert(k.drop_first() =~= Seq::<OrderKey>::empty());
    assert(keys_cmp(k.drop_first(), a, b) == 0);
}

/// Stable insertion at `pos`: after every row that is not below `r`, before the rows below it.
pub proof fn lemma_insert_pos(s: Seq<Row>, r: Row, pos: int)
    requires
        0 <= pos <= s.len(),
        forall|q: int| pos <= q < s.len() ==> keys_cmp(order_keys(), #[trigger] s[q], r) > 0,
        pos == 0 || keys_cmp(order_keys(), s[pos - 1], r) <= 0,
    ensures insert_sorted(order_keys(), s, r) == s.insert(pos, r),
    decreases s.len(),
{
    let k = order_keys();
    if s.len() == 0 {
        assert(s.insert(0, r) =~= seq![r]);
    } else if keys_cmp(k, s.last(), r) <= 0 {
        if pos < s.len() {
            assert(keys_cmp(k, s[s.len() - 1], r) > 0);
        }
        assert(s.insert(pos, r) =~= s.push(r));
    } else {
        let d = s.drop_last();
        assert(pos < s.len()) by {
            if pos == s.len() {
                assert(keys_cmp(k, s[pos - 1], r) <= 0);
            }
        }
        assert forall|q: int| pos <= q < d.len() implies keys_cmp(k, #[trigger] d[q], r) > 0 by {
            assert(d[q] == s[q]);
        }
        if pos > 0 {
            assert(d[pos - 1] == s[pos - 1]);
        }
        lemma_insert_pos(d, r, pos);
        assert(d.insert(pos, r).push(s.last()) =~= s.insert(pos, r));
    }
}

/// The rows of a sequence of group indices.
pub open spec fn rows_of(rows: Seq<Row>, ix: Seq<usize>) -> Seq<Row> {
    ix.map_values(|t: usize| rows[t as int])
}

/// Group rows whose third column is the count.
pub open spec fn counted(rows: Seq<Row>, cnts: Seq<u64>) -> bool {
    &&& rows.len() == cnts.len()
    &&& forall|t: int| 0 <= t < rows.len() ==> (#[trigger] rows[t]).len() == 4 && rows[t][2] == Val::Int(cnts[t] as int)
}

/// Sort the selected groups `h` by COUNT(*) descending: exactly `sort_rows` of their rows.
pub fn sort_idx(h: &Vec<usize>, cnts: &Vec<u64>, Ghost(rows): Ghost<Seq<Row>>) -> (o: Vec<usize>)
    requires
        counted(rows, cnts@),
        forall|q: int| 0 <= q < h@.len() ==> (#[trigger] h@[q] as int) < cnts@.len(),
    ensures
        rows_of(rows, o@) == sort_rows(order_keys(), rows_of(rows, h@)),
        forall|q: int| 0 <= q < o@.len() ==> (#[trigger] o@[q] as int) < cnts@.len(),
        o@.len() == h@.len(),
{
    let mut o: Vec<usize> = Vec::new();
    let n = h.len();
    let mut i: usize = 0;
    proof {
        assert(rows_of(rows, h@.take(0)) =~= Seq::<Row>::empty());
        assert(rows_of(rows, o@) =~= Seq::<Row>::empty());
    }
    while i < n
        invariant
            i <= n, n == h@.len(), counted(rows, cnts@),
            forall|q: int| 0 <= q < h@.len() ==> (#[trigger] h@[q] as int) < cnts@.len(),
            forall|q: int| 0 <= q < o@.len() ==> (#[trigger] o@[q] as int) < cnts@.len(),
            o@.len() == i,
            rows_of(rows, o@) == sort_rows(order_keys(), rows_of(rows, h@.take(i as int))),
        decreases n - i,
    {
        let t = h[i];
        let ct = cnts[t];
        let ghost s = rows_of(rows, o@);
        let ghost r = rows[t as int];
        let mut pos = o.len();
        while pos > 0 && cnts[o[pos - 1]] < ct
            invariant
                pos <= o@.len(), counted(rows, cnts@), (t as int) < cnts@.len(), ct == cnts@[t as int],
                forall|q: int| 0 <= q < o@.len() ==> (#[trigger] o@[q] as int) < cnts@.len(),
                s == rows_of(rows, o@), r == rows[t as int],
                forall|q: int| pos <= q < o@.len() ==> keys_cmp(order_keys(), #[trigger] s[q], r) > 0,
            decreases pos,
        {
            proof {
                let q = pos - 1;
                assert(s[q] == rows[o@[q] as int]);
                lemma_keys_cmp(s[q], r);
            }
            pos = pos - 1;
        }
        proof {
            if pos > 0 {
                let q = pos - 1;
                assert(s[q] == rows[o@[q] as int]);
                lemma_keys_cmp(s[q], r);
            }
            lemma_insert_pos(s, r, pos as int);
            let hp = rows_of(rows, h@.take(i as int));
            assert(rows_of(rows, h@.take(i + 1)) =~= hp.push(r));
            assert(hp.push(r).drop_last() =~= hp);
        }
        let ghost o0 = o@;
        o.insert(pos, t);
        proof {
            assert(rows_of(rows, o@) =~= s.insert(pos as int, r));
            assert forall|q: int| 0 <= q < o@.len() implies (#[trigger] o@[q] as int) < cnts@.len() by {
                if q < pos as int {
                    assert(o@[q] == o0[q]);
                } else if q > pos as int {
                    assert(o@[q] == o0[q - 1]);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert(h@.take(n as int) =~= h@);
    }
    o
}

// ------------------------------------------------------------------------------------------------ result rows

/// A copy of the bytes `b` (`n` of them).
fn copy_bytes(b: &[u8], n: usize) -> (v: Vec<u8>)
    requires n == b@.len(),
    ensures v@ == b@,
{
    let mut v: Vec<u8> = Vec::with_capacity(n);
    let mut k: usize = 0;
    while k < n
        invariant k <= n, n == b@.len(), v@ == b@.subrange(0, k as int),
        decreases n - k,
    {
        v.push(b[k]);
        k = k + 1;
        proof {
            assert(v@ =~= b@.subrange(0, k as int));
        }
    }
    v
}

/// The result row of one group.
fn make_row(rep: usize, cnt: u64, sum: i128, tag_col: &TextCol, ver_col: &TextCol, Ghost(c): Ghost<Ctx>) -> (row: Vec<EVal>)
    requires
        ctx_ok(c), (rep as int) < c.n, cnt <= i64::MAX,
        tag_col@ == ntag_v(c), ver_col@ == nver_v(c), text_wf(tag_col@, c.n), text_wf(ver_col@, c.n),
    ensures view_row(row@) == grow(c, rep as int, cnt as int, sum as int),
{
    let (tb, tl) = text_get(tag_col, rep, Ghost(c.n));
    let (vb, vl) = text_get(ver_col, rep, Ghost(c.n));
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Text(copy_bytes(tb, tl)));
    row.push(EVal::Text(copy_bytes(vb, vl)));
    row.push(EVal::Int(cnt as i64));
    row.push(EVal::Num { coeff: sum, scale: 4 });
    proof {
        assert(view_row(row@) =~= grow(c, rep as int, cnt as int, sum as int));
    }
    row
}

/// The result rows of the first `lim` sorted groups.
#[verifier::spinoff_prover]
pub fn out_rows(o: &Vec<usize>, lim: usize, reps: &Vec<usize>, cnts: &Vec<u64>, sums: &Vec<i128>, tag_col: &TextCol,
    ver_col: &TextCol, Ghost(c): Ghost<Ctx>) -> (out: Vec<Vec<EVal>>)
    requires
        ctx_ok(c), lim <= o@.len(),
        tag_col@ == ntag_v(c), ver_col@ == nver_v(c),
        reps@.len() == cnts@.len() && reps@.len() == sums@.len(),
        forall|q: int| 0 <= q < o@.len() ==> (#[trigger] o@[q] as int) < reps@.len(),
        forall|t: int| 0 <= t < reps@.len() ==> (#[trigger] reps@[t] as int) < c.n && cnts@[t] <= i64::MAX,
    ensures view_rows(out@) == rows_of(grows(c, reps@, cnts@, sums@), o@).take(lim as int),
{
    proof {
        lemma_text_cols_wf(c);
    }
    let ghost gr = grows(c, reps@, cnts@, sums@);
    let mut out: Vec<Vec<EVal>> = Vec::new();
    let mut q: usize = 0;
    proof {
        assert(view_rows(out@) =~= rows_of(gr, o@).take(0));
    }
    while q < lim
        invariant
            q <= lim, lim <= o@.len(), ctx_ok(c),
            tag_col@ == ntag_v(c), ver_col@ == nver_v(c), text_wf(tag_col@, c.n), text_wf(ver_col@, c.n),
            reps@.len() == cnts@.len() && reps@.len() == sums@.len(),
            forall|q2: int| 0 <= q2 < o@.len() ==> (#[trigger] o@[q2] as int) < reps@.len(),
            forall|t: int| 0 <= t < reps@.len() ==> (#[trigger] reps@[t] as int) < c.n && cnts@[t] <= i64::MAX,
            gr == grows(c, reps@, cnts@, sums@),
            view_rows(out@) == rows_of(gr, o@).take(q as int),
        decreases lim - q,
    {
        let t = o[q];
        proof {
            assert((o@[q as int] as int) < reps@.len());
            assert((reps@[t as int] as int) < c.n && cnts@[t as int] <= i64::MAX);
        }
        let row = make_row(reps[t], cnts[t], sums[t], tag_col, ver_col, Ghost(c));
        proof {
            crate::link::outcome::lemma_view_rows_push(out@, row);
            assert(view_row(row@) == gr[t as int]);
            assert(rows_of(gr, o@).take(q + 1) =~= rows_of(gr, o@).take(q as int).push(gr[o@[q as int] as int]));
        }
        out.push(row);
        q = q + 1;
    }
    out
}

// ------------------------------------------------------------------------------------------------ the claim

/// The ORDER BY key families of the group rows: every count is an integer.
pub proof fn lemma_keys_ok(rows: Seq<Row>, cnts: Seq<u64>)
    requires counted(rows, cnts),
    ensures crate::bridge::order::all_keys_ok(order_keys(), seq![1int], rows),
{
    assert forall|i: int| 0 <= i < rows.len() implies crate::bridge::order::keys_ok(order_keys(), seq![1int], #[trigger] rows[i]) by {
        assert forall|k: int| 0 <= k < order_keys().len() implies #[trigger] crate::bridge::order::key_ok(order_keys()[k], seq![1int][k], rows[i]) by {
            assert(k == 0);
        }
    }
}

/// The groups' counts and absolute sums are inside the arithmetic domain.
pub proof fn lemma_caps_groups(c: Ctx, u: Seq<usize>, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>, masses: Seq<u128>)
    requires
        ctx_ok(c), c.n <= int8_max(), u == kept(c, 0, c.n),
        groups_ok(c, xr(c, u), reps, cnts, sums, masses),
    ensures caps_ok(c, xr(c, u)),
{
    let g = nf(c);
    let xs = xr(c, u);
    lemma_gkeys(g, xs);
    lemma_groups_reps(c, xs, reps, cnts, sums, masses);
    lemma_keep_range_len(c, 0, c.n);
    assert forall|k: Row| #[trigger] gcount(g, xs, k) <= int8_max() by {
        lemma_gcount_le(g, xs, k);
    }
    assert forall|k: Row| #[trigger] gabs(g, xs, k, 1) <= i128_max() by {
        let ks = gkeys(g, xs);
        if ks.contains(k) {
            let t = choose|t: int| 0 <= t < ks.len() && ks[t] == k;
            lemma_groups_ok_cap(c, xs, reps, cnts, sums, masses, t);
        } else {
            lemma_zero_count(g, xs, k, 1);
        }
    }
}

/// The HAVING rows are the rows of the selected groups.
pub proof fn lemma_having_groups(c: Ctx, xs: Seq<Row>, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>, masses: Seq<u128>)
    requires groups_ok(c, xs, reps, cnts, sums, masses), reps.len() <= usize::MAX,
    ensures
        having(grp_rows(c, xs)) == rows_of(grows(c, reps, cnts, sums), hsel(cnts, cnts.len() as int)),
        counted(grows(c, reps, cnts, sums), cnts),
{
    lemma_grows(c, xs, reps, cnts, sums, masses);
    lemma_groups_reps(c, xs, reps, cnts, sums, masses);
    let gr = grows(c, reps, cnts, sums);
    assert(counted(gr, cnts));
    lemma_having_rows(gr, cnts, gr.len() as int);
    assert(gr.take(gr.len() as int) =~= gr);
    assert(having_truths(gr).take(gr.len() as int) =~= having_truths(gr));
}

/// The rows of selected groups are counted rows.
pub proof fn lemma_sel_counted(gr: Seq<Row>, cnts: Seq<u64>, h: Seq<usize>)
    requires counted(gr, cnts), forall|q: int| 0 <= q < h.len() ==> (#[trigger] h[q] as int) < cnts.len(),
    ensures counted(rows_of(gr, h), h.map_values(|t: usize| cnts[t as int])),
{
    let hr = rows_of(gr, h);
    let hc = h.map_values(|t: usize| cnts[t as int]);
    assert forall|q: int| 0 <= q < hr.len() implies (#[trigger] hr[q]).len() == 4 && hr[q][2] == Val::Int(hc[q] as int) by {
        assert((h[q] as int) < cnts.len());
    }
}

/// Every database bound to the parts: the produced rows are an allowed output of the statement.
#[verifier::spinoff_prover]
pub proof fn lemma_answer(db: Database, c: Ctx, ps: Seq<Literal>, u: Seq<usize>, reps: Seq<usize>, cnts: Seq<u64>,
    sums: Seq<i128>, masses: Seq<u128>, h: Seq<usize>, o: Seq<usize>, out: Seq<Row>)
    requires
        db_ok(db, c), lits_ok(c, ps), c.n <= usize::MAX, c.n <= int8_max(),
        u == kept(c, 0, c.n),
        groups_ok(c, xr(c, u), reps, cnts, sums, masses),
        reps.len() <= usize::MAX,
        h == hsel(cnts, cnts.len() as int),
        forall|q: int| 0 <= q < h.len() ==> (#[trigger] h[q] as int) < cnts.len(),
        rows_of(grows(c, reps, cnts, sums), o) == sort_rows(order_keys(), rows_of(grows(c, reps, cnts, sums), h)),
        out == rows_of(grows(c, reps, cnts, sums), o).take(if o.len() < 100 { o.len() as int } else { 100 }),
    ensures
        ordered_ok(db, crate::query::query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let xs = xr(c, u);
    lemma_keep_range_elems(c, 0, c.n);
    assert(xs =~= xrows(c, keep_range(c, 0, c.n)));
    lemma_caps_groups(c, u, reps, cnts, sums, masses);
    lemma_having(db, c, ps);
    lemma_having_groups(c, xs, reps, cnts, sums, masses);
    let gr = grows(c, reps, cnts, sums);
    let hr = rows_of(gr, h);
    let p = sort_rows(order_keys(), hr);
    lemma_sel_counted(gr, cnts, h);
    lemma_keys_ok(hr, h.map_values(|t: usize| cnts[t as int]));
    crate::bridge::order::lemma_sort_rows(order_keys(), seq![1int], hr);
    lemma_query_shape(ps);
    crate::link::outcome::lemma_outcome_sorted(db, crate::query::query_spec_at(ps), hr, p);
    assert(slice_rows(p, 0, Some(100nat)) =~= out);
}

/// The absolute sum of a group fits `i128` (part of `groups_ok`).
pub proof fn lemma_groups_ok_cap(c: Ctx, xs: Seq<Row>, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>, masses: Seq<u128>, t: int)
    requires groups_ok(c, xs, reps, cnts, sums, masses), 0 <= t < reps.len(),
    ensures gabs(nf(c), xs, gkeys(nf(c), xs)[t], 1) <= i128_max(),
{
    reveal(groups_ok);
    let r = reps[t];
    assert((r as int) < c.n);
}

} // verus!
