//! From the candidates above a threshold to the answer rows: the `sub` match of each candidate (`fy = $2`), the
//! group-maximum test inside that set, the ORDER BY sort (stable insertion, as the spec's `sort_rows`) and the
//! LIMIT.
use vstd::prelude::*;
use crate::gendb_entry::work::{text_bytes, text_eq};
use crate::link::query::{text_at, text_wf, view_rows, TextCol};
use crate::link::outcome::lemma_view_rows_push;
use crate::exec::value::{view_row, EVal};
use crate::spec::value::Row;
use crate::spec::text::lex_cmp;
use crate::spec::order::{keys_cmp, sort_rows, insert_sorted};
use crate::agent::spec::*;
use crate::agent::subtable::*;
use crate::agent::order::*;
use crate::agent::sem::order_keys;

verus! {

/// The text columns the ranking reads: `num.tag` (`n` rows) and `sub.name` (`m` rows).
pub struct RankCols {
    pub tag: TextCol,
    pub name: TextCol,
}

/// Bytes of value `i` of a well-formed text column of `n` rows.
pub fn text_of(c: &TextCol, i: usize, Ghost(n): Ghost<int>) -> (r: &'static [u8])
    requires text_wf(c@, n), i < n,
    ensures r@ == text_at(c@, i as int),
{
    proof {
        assert(0 <= c@.offsets[i as int] <= c@.offsets[i + 1] <= c@.bytes.len());
    }
    text_bytes(c, i)
}

/// Byte-wise three-way comparison (C collation), the spec's `lex_cmp`.
pub fn lex(a: &[u8], b: &[u8]) -> (r: i8)
    ensures r as int == lex_cmp(a@, b@),
{
    let na = a.len();
    let nb = b.len();
    let mut k: usize = 0;
    proof {
        assert(a@.skip(0) =~= a@);
        assert(b@.skip(0) =~= b@);
    }
    while k < na && k < nb
        invariant
            na == a@.len(), nb == b@.len(),
            k <= na, k <= nb,
            lex_cmp(a@, b@) == lex_cmp(a@.skip(k as int), b@.skip(k as int)),
        decreases na - k,
    {
        proof {
            let (x, y) = (a@.skip(k as int), b@.skip(k as int));
            assert(x[0] == a@[k as int] && y[0] == b@[k as int]);
            assert(x.drop_first() =~= a@.skip(k + 1));
            assert(y.drop_first() =~= b@.skip(k + 1));
        }
        if a[k] < b[k] {
            return -1;
        }
        if a[k] > b[k] {
            return 1;
        }
        k = k + 1;
    }
    proof {
        assert(a@.skip(k as int).len() == na - k);
        assert(b@.skip(k as int).len() == nb - k);
    }
    if na == k && nb == k {
        0
    } else if na == k {
        -1
    } else {
        1
    }
}

/// ORDER BY n.value DESC, s.name, n.tag between two answer rows given as (num row, sub row, coefficient).
pub fn row_cmp(c: &RankCols, ra: usize, sa: usize, ca: i128, rb: usize, sb: usize, cb: i128,
    Ghost(n): Ghost<int>, Ghost(m): Ghost<int>, Ghost(cx): Ghost<Ctx>) -> (r: i8)
    requires
        text_wf(c.tag@, n), text_wf(c.name@, m),
        c.tag@ == tag_view(cx.np),
        c.name@ == sname_view(cx.sp),
        ra < n, rb < n, sa < m, sb < m,
    ensures
        r as int == keys_cmp(order_keys(), ans_row(cx, ra as int, sa as int, ca as int), ans_row(cx, rb as int, sb as int, cb as int)),
{
    proof {
        lemma_keys_cmp_ans(cx, ra as int, sa as int, ca as int, rb as int, sb as int, cb as int);
    }
    if ca > cb {
        -1
    } else if ca < cb {
        1
    } else {
        let x = lex(text_of(&c.name, sa, Ghost(m)), text_of(&c.name, sb, Ghost(m)));
        if x != 0 {
            x
        } else {
            lex(text_of(&c.tag, ra, Ghost(n)), text_of(&c.tag, rb, Ghost(n)))
        }
    }
}

/// Answer rows at threshold `t2`: among the candidates at `t2` (computed from those at `thr <= t2`), the rows
/// with a matching `sub` row (`fy = $2`) that are the maximum of their group. A larger member of a group is a
/// candidate at `t2` as well and has the same `sub` row (the `sub` key), so the test runs inside that set.
/// Returned as (num rows, sub rows, coefficients), in row order.
pub fn body_rows(rows: &Vec<usize>, coeffs: &Vec<i128>, thr: i128, t2: i128, table: &SubTable, adsh: &TextCol,
    cols: &RankCols, Ghost(c): Ghost<Ctx>) -> (r: (Vec<usize>, Vec<usize>, Vec<i128>))
    requires
        ctx_ok(c),
        sub_key(c),
        table_wf(*table, c),
        adsh@ == adsh_view(c.np),
        cols.tag@ == tag_view(c.np),
        rows@.len() == coeffs@.len(),
        lists(c, rows@, coeffs@, rows@.len() as int, cands(c, 0, c.n, thr as int)),
        thr <= t2,
    ensures
        entries(c, r.0@, r.1@, r.2@, cands(c, 0, c.n, t2 as int).filter(body_p(c))),
{
    let ghost src = cands(c, 0, c.n, thr as int);
    let ghost f1 = ge_thr(c, t2 as int);
    let ghost f2 = has_sub_p(c);
    let ghost fb = body_p(c);
    proof {
        lemma_num_text_wf(c);
        assert(src.subrange(0, 0) =~= Seq::<int>::empty());
        reveal(Seq::filter);
    }
    // The adsh hash of every candidate, first: the iterations are independent, so their cache misses into
    // `num.adsh` overlap (the probes below reuse the loaded lines).
    let len = rows.len();
    let mut hs: Vec<u64> = Vec::with_capacity(len);
    let mut k: usize = 0;
    while k < len
        invariant
            len == rows@.len(), k <= len,
            ctx_ok(c),
            adsh@ == adsh_view(c.np),
            text_wf(adsh@, c.n),
            lists(c, rows@, coeffs@, len as int, src),
            src == cands(c, 0, c.n, thr as int),
            hs@.len() == k,
            forall|q: int| 0 <= q < k ==> #[trigger] hs@[q] == hash_spec(adsh_text(c, rows@[q] as int)),
        decreases len - k,
    {
        let row = rows[k];
        proof {
            lemma_cands_range(c, 0, c.n, thr as int, k as int);
            assert(0 <= adsh@.offsets[row as int] <= adsh@.offsets[row + 1] <= adsh@.bytes.len());
        }
        let key = text_bytes(adsh, row);
        hs.push(hash_key(key, key.len()));
        k = k + 1;
    }
    // D: the candidates at t2 with their matching sub row.
    let mut drows: Vec<usize> = Vec::new();
    let mut dsubs: Vec<usize> = Vec::new();
    let mut dcoeffs: Vec<i128> = Vec::new();
    let mut k: usize = 0;
    while k < len
        invariant
            len == rows@.len(), len == coeffs@.len(), k <= len,
            hs@.len() == len,
            forall|q: int| 0 <= q < len ==> #[trigger] hs@[q] == hash_spec(adsh_text(c, rows@[q] as int)),
            ctx_ok(c),
            table_wf(*table, c),
            adsh@ == adsh_view(c.np),
            text_wf(adsh@, c.n),
            lists(c, rows@, coeffs@, len as int, src),
            src == cands(c, 0, c.n, thr as int),
            f1 == ge_thr(c, t2 as int),
            f2 == has_sub_p(c),
            entries(c, drows@, dsubs@, dcoeffs@, src.subrange(0, k as int).filter(f1).filter(f2)),
        decreases len - k,
    {
        let ghost x = src[k as int];
        proof {
            lemma_cands_range(c, 0, c.n, thr as int, k as int);
            lemma_filter_push(src.subrange(0, k as int), x, f1);
            lemma_filter_push(src.subrange(0, k as int).filter(f1), x, f2);
            assert(src.subrange(0, k as int + 1) =~= src.subrange(0, k as int).push(x));
        }
        if coeffs[k] >= t2 {
            let row = rows[k];
            proof {
                assert(0 <= adsh@.offsets[row as int] <= adsh@.offsets[row + 1] <= adsh@.bytes.len());
            }
            let key = text_bytes(adsh, row);
            match lookup(table, key, hs[k], Ghost(c)) {
                Some(s) => {
                    proof {
                        assert(sub_match(c, x, s as int));
                    }
                    drows.push(row);
                    dsubs.push(s);
                    dcoeffs.push(coeffs[k]);
                },
                None => {
                    proof {
                        assert(!has_sub(c, x)) by {
                            if has_sub(c, x) {
                                let s = choose|s: int| #[trigger] sub_match(c, x, s);
                                assert(member(c, s) && sadsh_text(c, s) == key@);
                            }
                        }
                    }
                },
            }
        }
        k = k + 1;
    }
    let ghost d = cands(c, 0, c.n, t2 as int).filter(f2);
    proof {
        assert(src.subrange(0, len as int) =~= src);
        lemma_cands_raise(c, 0, c.n, thr as int, t2 as int);
        assert(d.subrange(0, 0) =~= Seq::<int>::empty());
    }
    // B: the members of D that are the maximum of their group.
    let mut brows: Vec<usize> = Vec::new();
    let mut bsubs: Vec<usize> = Vec::new();
    let mut bcoeffs: Vec<i128> = Vec::new();
    let dn = drows.len();
    let mut a: usize = 0;
    while a < dn
        invariant
            dn == drows@.len(), dn == dsubs@.len(), dn == dcoeffs@.len(), a <= dn,
            ctx_ok(c),
            sub_key(c),
            cols.tag@ == tag_view(c.np),
            text_wf(cols.tag@, c.n),
            entries(c, drows@, dsubs@, dcoeffs@, d),
            d == cands(c, 0, c.n, t2 as int).filter(f2),
            f2 == has_sub_p(c),
            fb == body_p(c),
            entries(c, brows@, bsubs@, bcoeffs@, d.subrange(0, a as int).filter(fb)),
        decreases dn - a,
    {
        proof {
            lemma_d_member(c, t2 as int, d, a as int);
        }
        let mut best = true;
        let mut b: usize = 0;
        while b < dn && best
            invariant
                dn == drows@.len(), dn == dsubs@.len(), dn == dcoeffs@.len(), a < dn, b <= dn,
                ctx_ok(c),
                text_wf(cols.tag@, c.n),
                cols.tag@ == tag_view(c.np),
                entries(c, drows@, dsubs@, dcoeffs@, d),
                d == cands(c, 0, c.n, t2 as int).filter(f2),
                f2 == has_sub_p(c),
                0 <= d[a as int] < c.n,
                drows@[a as int] as int == d[a as int],
                best ==> forall|q: int| 0 <= q < b ==> !#[trigger] beats(c, d, dsubs@, q, a as int),
                !best ==> b > 0 && beats(c, d, dsubs@, b - 1, a as int),
            decreases dn - b,
        {
            proof {
                lemma_d_member(c, t2 as int, d, b as int);
            }
            let mut hit = false;
            if dsubs[b] == dsubs[a] && dcoeffs[b] > dcoeffs[a] {
                proof {
                    assert(0 <= cols.tag@.offsets[drows@[b as int] as int] <= cols.tag@.offsets[drows@[b as int] + 1] <= cols.tag@.bytes.len());
                    assert(0 <= cols.tag@.offsets[drows@[a as int] as int] <= cols.tag@.offsets[drows@[a as int] + 1] <= cols.tag@.bytes.len());
                }
                hit = text_eq(&cols.tag, drows[b], &cols.tag, drows[a]);
            }
            proof {
                assert(hit == beats(c, d, dsubs@, b as int, a as int));
            }
            if hit {
                best = false;
            }
            b = b + 1;
        }
        proof {
            lemma_group_check(c, t2 as int, d, dsubs@, a as int);
            if best {
                assert(b == dn);
                assert(!exists|q: int| 0 <= q < d.len() && #[trigger] beats(c, d, dsubs@, q, a as int));
            } else {
                assert(beats(c, d, dsubs@, b - 1, a as int));
            }
            lemma_filter_push(d.subrange(0, a as int), d[a as int], fb);
            assert(d.subrange(0, a as int + 1) =~= d.subrange(0, a as int).push(d[a as int]));
        }
        if best {
            brows.push(drows[a]);
            bsubs.push(dsubs[a]);
            bcoeffs.push(dcoeffs[a]);
        }
        a = a + 1;
    }
    proof {
        assert(d.subrange(0, dn as int) =~= d);
        lemma_filter_implied(cands(c, 0, c.n, t2 as int), f2, fb);
    }
    (brows, bsubs, bcoeffs)
}

/// Entry `q` of D beats entry `a`: same `sub` row (so the same adsh), same tag, larger coefficient.
pub open spec fn beats(c: Ctx, d: Seq<int>, dsubs: Seq<usize>, q: int, a: int) -> bool {
    dsubs[q] == dsubs[a] && coeff(c, d[q]) > coeff(c, d[a]) && tag_text(c, d[q]) == tag_text(c, d[a])
}

/// A member of D (the candidates at `t2` with a sub match) is such a candidate.
pub proof fn lemma_d_member(c: Ctx, t2: int, d: Seq<int>, k: int)
    requires d == cands(c, 0, c.n, t2).filter(has_sub_p(c)), 0 <= k < d.len(),
    ensures 0 <= d[k] < c.n, cand(c, d[k], t2), has_sub(c, d[k]),
{
    let s = cands(c, 0, c.n, t2);
    lemma_filter_source(s, has_sub_p(c), k);
    let j = choose|j: int| 0 <= j < s.len() && s[j] == d[k];
    lemma_cands_range(c, 0, c.n, t2, j);
    s.lemma_filter_pred(has_sub_p(c), k);
}

/// The group test inside D: some member beats entry `a` exactly when `a` is not an answer row.
pub proof fn lemma_group_check(c: Ctx, t2: int, d: Seq<int>, dsubs: Seq<usize>, a: int)
    requires
        ctx_ok(c),
        sub_key(c),
        d == cands(c, 0, c.n, t2).filter(has_sub_p(c)),
        dsubs.len() == d.len(),
        forall|k: int| 0 <= k < d.len() ==> #[trigger] sub_match(c, d[k], dsubs[k] as int),
        0 <= a < d.len(),
    ensures
        (exists|q: int| 0 <= q < d.len() && #[trigger] beats(c, d, dsubs, q, a)) <==> !body_ok(c, d[a]),
{
    let i = d[a];
    lemma_d_member(c, t2, d, a);
    assert(sub_match(c, i, dsubs[a] as int));
    if exists|q: int| 0 <= q < d.len() && #[trigger] beats(c, d, dsubs, q, a) {
        let q = choose|q: int| 0 <= q < d.len() && #[trigger] beats(c, d, dsubs, q, a);
        let j = d[q];
        lemma_d_member(c, t2, d, q);
        assert(sub_match(c, j, dsubs[q] as int));
        assert(mate(c, i, j));
        assert(!gmax(c, i));
    }
    if !body_ok(c, i) {
        assert(!gmax(c, i));
        let j = choose|j: int| 0 <= j < c.n && #[trigger] mate(c, i, j) && !(coeff(c, j) <= coeff(c, i));
        // j is a candidate at t2 with a sub match, so it is in D.
        assert(sub_match(c, j, dsubs[a] as int));
        assert(has_sub(c, j));
        assert(cand(c, j, t2));
        lemma_cands_contains(c, 0, c.n, t2, j);
        let s = cands(c, 0, c.n, t2);
        let p = choose|p: int| 0 <= p < s.len() && s[p] == j;
        s.lemma_filter_contains(has_sub_p(c), p);
        let q = choose|q: int| 0 <= q < d.len() && d[q] == j;
        assert(sub_match(c, j, dsubs[q] as int));
        lemma_d_member(c, t2, d, q);
        assert(dsubs[q] == dsubs[a]) by {
            assert(sadsh_text(c, dsubs[q] as int) == sadsh_text(c, dsubs[a] as int));
        }
        assert(beats(c, d, dsubs, q, a));
    }
}

/// ORDER BY sort: stable insertion of each answer row after every row that is not greater (the spec's
/// `sort_rows`), as positions into `brows`/`bsubs`/`bcoeffs`.
#[verifier::spinoff_prover]
pub fn sort_positions(brows: &Vec<usize>, bsubs: &Vec<usize>, bcoeffs: &Vec<i128>, c: &RankCols,
    Ghost(n): Ghost<int>, Ghost(m): Ghost<int>, Ghost(cx): Ghost<Ctx>) -> (r: Vec<usize>)
    requires
        text_wf(c.tag@, n), text_wf(c.name@, m),
        c.tag@ == tag_view(cx.np),
        c.name@ == sname_view(cx.sp),
        brows@.len() == bsubs@.len(), brows@.len() == bcoeffs@.len(),
        forall|q: int| 0 <= q < brows@.len() ==> #[trigger] brows@[q] < n,
        forall|q: int| 0 <= q < bsubs@.len() ==> #[trigger] bsubs@[q] < m,
    ensures
        r@.len() == brows@.len(),
        forall|q: int| 0 <= q < r@.len() ==> #[trigger] r@[q] < brows@.len(),
        ordered_view(ans_rows(cx, brows@, bsubs@, bcoeffs@), r@) == sort_rows(order_keys(), ans_rows(cx, brows@, bsubs@, bcoeffs@)),
{
    hide(keys_cmp);
    hide(sort_rows);
    hide(insert_sorted);
    let ghost v = ans_rows(cx, brows@, bsubs@, bcoeffs@);
    let ghost keys = order_keys();
    let len = brows.len();
    let mut out: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    proof {
        lemma_sort_empty(keys, v);
        reveal(ordered_view);
        assert(ordered_view(v, out@) =~= Seq::<Row>::empty());
    }
    while k < len
        invariant
            len == brows@.len(), len == bsubs@.len(), len == bcoeffs@.len(), k <= len,
            v == ans_rows(cx, brows@, bsubs@, bcoeffs@),
            keys == order_keys(),
            text_wf(c.tag@, n), text_wf(c.name@, m),
            c.tag@ == tag_view(cx.np),
            c.name@ == sname_view(cx.sp),
            forall|q: int| 0 <= q < brows@.len() ==> #[trigger] brows@[q] < n,
        forall|q: int| 0 <= q < bsubs@.len() ==> #[trigger] bsubs@[q] < m,
            out@.len() == k,
            forall|q: int| 0 <= q < out@.len() ==> #[trigger] out@[q] < len,
            ordered_view(v, out@) == sort_rows(keys, v.take(k as int)),
        decreases len - k,
    {
        let ghost s = ordered_view(v, out@);
        proof {
            lemma_ordered_len(v, out@);
        }
        let mut j: usize = out.len();
        let mut done = false;
        while j > 0 && !done
            invariant
                done ==> j > 0 && keys_cmp(keys, s[j - 1], v[k as int]) <= 0,
                j <= out@.len(), k < len,
                len == brows@.len(), len == bsubs@.len(), len == bcoeffs@.len(),
                v == ans_rows(cx, brows@, bsubs@, bcoeffs@),
                keys == order_keys(),
                s == ordered_view(v, out@),
                text_wf(c.tag@, n), text_wf(c.name@, m),
                c.tag@ == tag_view(cx.np),
                c.name@ == sname_view(cx.sp),
                forall|q: int| 0 <= q < brows@.len() ==> #[trigger] brows@[q] < n,
        forall|q: int| 0 <= q < bsubs@.len() ==> #[trigger] bsubs@[q] < m,
                forall|q: int| 0 <= q < out@.len() ==> #[trigger] out@[q] < len,
                forall|q: int| j <= q < s.len() ==> keys_cmp(keys, #[trigger] s[q], v[k as int]) > 0,
            decreases j + (if done { 0int } else { 1int }),
        {
            let p = out[j - 1];
            let x = row_cmp(c, brows[p], bsubs[p], bcoeffs[p], brows[k], bsubs[k], bcoeffs[k], Ghost(n), Ghost(m), Ghost(cx));
            proof {
                lemma_ordered_at(v, out@, j - 1);
                lemma_ans_rows_at(cx, brows@, bsubs@, bcoeffs@, p as int);
                lemma_ans_rows_at(cx, brows@, bsubs@, bcoeffs@, k as int);
            }
            if x <= 0 {
                done = true;
            } else {
                j = j - 1;
            }
        }
        proof {
            lemma_insert_at(keys, s, v[k as int], j as int);
            lemma_sort_step(keys, v, k as int);
        }
        let ghost before = out@;
        out.insert(j, k);
        proof {
            lemma_ordered_insert(v, before, j as int, k as int);
        }
        k = k + 1;
    }
    proof {
        assert(v.take(len as int) =~= v);
    }
    out
}

/// Row `q` of an ordered view.
pub proof fn lemma_ordered_at(v: Seq<Row>, order: Seq<usize>, q: int)
    requires 0 <= q < order.len(),
    ensures ordered_view(v, order)[q] == v[order[q] as int], ordered_view(v, order).len() == order.len(),
{
    reveal(ordered_view);
}

/// The ordered view after inserting position `k` at `j`.
pub proof fn lemma_ordered_insert(v: Seq<Row>, order: Seq<usize>, j: int, k: int)
    requires 0 <= j <= order.len(), 0 <= k < v.len(), k <= usize::MAX,
    ensures ({
        let s = ordered_view(v, order);
        ordered_view(v, order.insert(j, k as usize)) == s.take(j) + seq![v[k]] + s.skip(j)
    }),
{
    reveal(ordered_view);
    let s = ordered_view(v, order);
    let o2 = order.insert(j, k as usize);
    let t = s.take(j) + seq![v[k]] + s.skip(j);
    assert(o2.len() == order.len() + 1);
    assert forall|q: int| 0 <= q < o2.len() implies #[trigger] ordered_view(v, o2)[q] == t[q] by {
        if q < j {
            assert(o2[q] == order[q]);
        } else if q == j {
            assert(o2[q] == k as usize);
        } else {
            assert(o2[q] == order[q - 1]);
        }
    }
    assert(ordered_view(v, o2) =~= t);
}

/// The length of an ordered view.
pub proof fn lemma_ordered_len(v: Seq<Row>, order: Seq<usize>)
    ensures ordered_view(v, order).len() == order.len(),
{
    reveal(ordered_view);
}

/// Row `k` of the answer rows.
pub proof fn lemma_ans_rows_at(c: Ctx, rows: Seq<usize>, subs: Seq<usize>, coeffs: Seq<i128>, k: int)
    requires 0 <= k < rows.len(),
    ensures
        ans_rows(c, rows, subs, coeffs)[k] == ans_row(c, rows[k] as int, subs[k] as int, coeffs[k] as int),
        ans_rows(c, rows, subs, coeffs).len() == rows.len(),
{
}

/// The rows at positions `order` of `v`.
#[verifier::opaque]
pub open spec fn ordered_view(v: Seq<Row>, order: Seq<usize>) -> Seq<Row> {
    Seq::new(order.len(), |q: int| v[order[q] as int])
}

/// A copy of a byte slice.
pub fn copy_bytes(x: &[u8]) -> (v: Vec<u8>)
    ensures v@ == x@,
{
    let mut v: Vec<u8> = Vec::new();
    let n = x.len();
    let mut k: usize = 0;
    while k < n
        invariant n == x@.len(), k <= n, v@ == x@.subrange(0, k as int),
        decreases n - k,
    {
        v.push(x[k]);
        proof {
            assert(v@ =~= x@.subrange(0, k as int + 1));
        }
        k = k + 1;
    }
    proof {
        assert(x@.subrange(0, n as int) =~= x@);
    }
    v
}

/// LIMIT: the first `limit` sorted answer rows as result rows (name, tag, value at scale 4).
#[verifier::spinoff_prover]
pub fn answer_rows(order: &Vec<usize>, brows: &Vec<usize>, bsubs: &Vec<usize>, bcoeffs: &Vec<i128>, c: &RankCols,
    limit: usize, Ghost(n): Ghost<int>, Ghost(m): Ghost<int>, Ghost(cx): Ghost<Ctx>) -> (r: Vec<Vec<EVal>>)
    requires
        text_wf(c.tag@, n), text_wf(c.name@, m),
        c.tag@ == tag_view(cx.np),
        c.name@ == sname_view(cx.sp),
        brows@.len() == bsubs@.len(), brows@.len() == bcoeffs@.len(),
        forall|q: int| 0 <= q < brows@.len() ==> #[trigger] brows@[q] < n,
        forall|q: int| 0 <= q < bsubs@.len() ==> #[trigger] bsubs@[q] < m,
        forall|q: int| 0 <= q < order@.len() ==> #[trigger] order@[q] < brows@.len(),
    ensures
        view_rows(r@) == ordered_view(ans_rows(cx, brows@, bsubs@, bcoeffs@), order@).take(
            if order@.len() < limit { order@.len() as int } else { limit as int }),
{
    hide(view_rows);
    let ghost v = ans_rows(cx, brows@, bsubs@, bcoeffs@);
    let ghost w = ordered_view(v, order@);
    let total = order.len();
    let count = if total < limit { total } else { limit };
    let mut out: Vec<Vec<EVal>> = Vec::new();
    let mut k: usize = 0;
    proof {
        reveal(view_rows);
        assert(view_rows(out@) =~= w.take(0));
    }
    while k < count
        invariant
            count <= total, total == order@.len(), k <= count,
            v == ans_rows(cx, brows@, bsubs@, bcoeffs@),
            w == ordered_view(v, order@),
            text_wf(c.tag@, n), text_wf(c.name@, m),
            c.tag@ == tag_view(cx.np),
            c.name@ == sname_view(cx.sp),
            brows@.len() == bsubs@.len(), brows@.len() == bcoeffs@.len(),
            forall|q: int| 0 <= q < brows@.len() ==> #[trigger] brows@[q] < n,
        forall|q: int| 0 <= q < bsubs@.len() ==> #[trigger] bsubs@[q] < m,
            forall|q: int| 0 <= q < order@.len() ==> #[trigger] order@[q] < brows@.len(),
            view_rows(out@) == w.take(k as int),
        decreases count - k,
    {
        let p = order[k];
        let name = copy_bytes(text_of(&c.name, bsubs[p], Ghost(m)));
        let tag = copy_bytes(text_of(&c.tag, brows[p], Ghost(n)));
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Text(name));
        row.push(EVal::Text(tag));
        row.push(EVal::Num { coeff: bcoeffs[p], scale: 4 });
        proof {
            lemma_ans_row(cx, brows@[p as int] as int, bsubs@[p as int] as int, bcoeffs@[p as int] as int);
            assert(view_row(row@) =~= ans_row(cx, brows@[p as int] as int, bsubs@[p as int] as int, bcoeffs@[p as int] as int));
            lemma_ordered_at(v, order@, k as int);
            lemma_ans_rows_at(cx, brows@, bsubs@, bcoeffs@, p as int);
            lemma_view_rows_push(out@, row);
            assert(w.take(k as int).push(w[k as int]) =~= w.take(k + 1));
        }
        out.push(row);
        k = k + 1;
    }
    out
}

} // verus!
