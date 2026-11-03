//! From the hits to the answer rows: the candidates are the hits whose supply cost is least for their part key
//! (`least_per_key`), each candidate's output row is that of its unique kept FROM row (`sem_plan::cand_row`), and
//! the answer is the first 100 of those rows in ORDER BY order (`topk`), built as executable values.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::order::*;
use crate::exec::value::*;
use crate::link::query::{select, view_rows, text_at};
use crate::gendb_entry::stores::StoresView;
use crate::agent::model::*;
use crate::agent::sem_ast::{out_cols, order_keys};
use crate::agent::sem_outer::*;
use crate::agent::sem_plan::*;
use crate::agent::columns::*;
use crate::agent::pipeline::{HitVecs, to_vec};
use crate::agent::scan_part::{text_row, keys_unique};
use crate::agent::topk::*;
use crate::agent::common::least_per_key::{least_per_key, least_list, least_at};
use crate::agent::common::key_lookup::find_key;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;

verus! {

/// The hits are exactly the model's hits, in increasing row order, with consistent fields.
pub open spec fn hits_ok(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, h: HitVecs) -> bool {
    &&& h.b@.len() == h.c@.len() && h.pk@.len() == h.c@.len() && h.cost@.len() == h.c@.len() && h.acct@.len() == h.c@.len()
    &&& forall|i: int| 0 <= i < h.c@.len() ==> {
        let c = #[trigger] h.c@[i] as int;
        let b = h.b@[i] as int;
        &&& 0 <= c < ps_n(sv)
        &&& hit(sv, v, pat, rp, c)
        &&& 0 <= b < supp_n(sv)
        &&& s_keys(sv)[b] == ps_skeys(sv)[c]
        &&& h.pk@[i] == ps_pkeys(sv)[c]
        &&& h.cost@[i] == ps_costs(sv)[c]
        &&& h.acct@[i] == s_accts(sv)[b]
    }
    &&& forall|i: int, j: int| 0 <= i < j < h.c@.len() ==> h.c@[i] < h.c@[j]
    &&& forall|c: int| 0 <= c < ps_n(sv) && #[trigger] hit(sv, v, pat, rp, c) ==> exists|i: int| 0 <= i < h.c@.len() && h.c@[i] == c
}

/// The output rows of candidates `cs`.
pub open spec fn cand_out(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, cs: Seq<int>) -> Seq<Row> {
    cs.map_values(|c: int| out_row(cand_row(sv, v, pat, rp, c)))
}

/// `out` is an allowed `ORDER BY .. LIMIT 100` output of the candidates' rows.
pub open spec fn answer_ok(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, out: Seq<Row>) -> bool {
    exists|cs: Seq<int>, p: Seq<Row>| #![trigger lists_cands(sv, v, pat, rp, cs), sorted_by(order_keys(), p)]
        lists_cands(sv, v, pat, rp, cs)
        && p.to_multiset() == cand_out(sv, v, pat, rp, cs).to_multiset()
        && sorted_by(order_keys(), p)
        && out == slice_rows(p, 0, Some(100))
}

/// The output row of a FROM row, column by column.
pub proof fn lemma_out_row(sv: StoresView, a: int, b: int, c: int, d: int, e: int)
    requires stores_wf(sv), in5(sv, a, b, c, d, e),
    ensures
        out_row(row5(sv, a, b, c, d, e)) == seq![
            Val::Num { coeff: s_accts(sv)[b] as int, scale: 2 },
            Val::Text(text_at(si::text_view(sv.flat_supplier, si::S_NAME_OFFSETS as int, si::S_NAME_BYTES as int), b)),
            Val::Text(text_at(ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int), d)),
            Val::Int(p_keys(sv)[a] as int),
            Val::Text(text_at(pi::text_view(sv.flat_part, pi::P_MFGR_OFFSETS as int, pi::P_MFGR_BYTES as int), a)),
            Val::Text(text_at(si::text_view(sv.flat_supplier, si::S_ADDRESS_OFFSETS as int, si::S_ADDRESS_BYTES as int), b)),
            Val::Text(text_at(si::text_view(sv.flat_supplier, si::S_PHONE_OFFSETS as int, si::S_PHONE_BYTES as int), b)),
            Val::Text(text_at(si::text_view(sv.flat_supplier, si::S_COMMENT_OFFSETS as int, si::S_COMMENT_BYTES as int), b)),
        ],
{
    lemma_row5(sv, a, b, c, d, e);
    let x = row5(sv, a, b, c, d, e);
    assert(supp_rows(sv)[b] == si::row_at(sv.flat_supplier, b));
    assert(nat_rows(sv)[d] == ni::row_at(sv.flat_nation, d));
    assert(part_rows(sv)[a] == pi::row_at(sv.flat_part, a));
    let cols = out_cols();
    assert(cols[0] == 14 && cols[1] == 10 && cols[2] == 22 && cols[3] == 0 && cols[4] == 2 && cols[5] == 11 && cols[6] == 13 && cols[7] == 15);
    let r = out_row(x);
    assert(r.len() == 8);
    assert(r =~= seq![x[14], x[10], x[22], x[0], x[2], x[11], x[13], x[15]]);
}

/// The candidates' rows from the hits and the least-cost positions.
proof fn lemma_cands(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, h: HitVecs, f: Seq<usize>)
    requires
        stores_wf(sv),
        hits_ok(sv, v, pat, rp, h),
        least_list(h.pk@, h.cost@, f),
    ensures lists_cands(sv, v, pat, rp, f.map_values(|i: usize| h.c@[i as int] as int)),
{
    let cs = f.map_values(|i: usize| h.c@[i as int] as int);
    // A hit is a candidate exactly when its cost is least among the hits of its part key.
    assert forall|i: int| 0 <= i < h.c@.len() implies (#[trigger] least_at(h.pk@, h.cost@, i)) == cand(sv, v, pat, rp, h.c@[i] as int) by {
        let c = h.c@[i] as int;
        lemma_cand_iff(sv, v, pat, rp, c);
        if least_at(h.pk@, h.cost@, i) {
            assert forall|c2: int| 0 <= c2 < ps_n(sv) && #[trigger] hit(sv, v, pat, rp, c2) && ps_pkeys(sv)[c2] == ps_pkeys(sv)[c]
                implies ps_costs(sv)[c] <= ps_costs(sv)[c2] by {
                let i2 = choose|i2: int| 0 <= i2 < h.c@.len() && h.c@[i2] == c2;
                assert(h.pk@[i2] == h.pk@[i]);
            }
        }
        if cand(sv, v, pat, rp, c) {
            assert forall|j: int| 0 <= j < h.pk@.len() && #[trigger] h.pk@[j] == h.pk@[i] implies h.cost@[i] <= h.cost@[j] by {
                let c2 = h.c@[j] as int;
                assert(hit(sv, v, pat, rp, c2));
            }
        }
    }
    assert forall|q: int| 0 <= q < cs.len() implies 0 <= #[trigger] cs[q] < ps_n(sv) && cand(sv, v, pat, rp, cs[q]) by {
        assert(least_at(h.pk@, h.cost@, f[q] as int));
    }
    assert forall|q: int, r: int| 0 <= q < r < cs.len() implies cs[q] < cs[r] by {
        assert(f[q] < f[r]);
    }
    assert forall|c: int| 0 <= c < ps_n(sv) && #[trigger] cand(sv, v, pat, rp, c) implies exists|q: int| 0 <= q < cs.len() && cs[q] == c by {
        lemma_cand_iff(sv, v, pat, rp, c);
        let i = choose|i: int| 0 <= i < h.c@.len() && h.c@[i] == c;
        assert(least_at(h.pk@, h.cost@, i));
        let q = choose|q: int| 0 <= q < f.len() && f[q] == i;
        assert(cs[q] == c);
    }
}

/// The executable output row of FROM row `row5(a, b, c, d, e)` (part `a` found by key `k`, nation `d` by the
/// supplier's nation key).
fn build_row(cl: &Cols, Ghost(sv): Ghost<StoresView>, acct: i128, b: usize, k: i64,
    Ghost(a0): Ghost<int>, Ghost(c): Ghost<int>, Ghost(d0): Ghost<int>, Ghost(e): Ghost<int>) -> (row: Vec<EVal>)
    requires
        cols_ok(*cl, sv), stores_wf(sv), keys_ok(sv),
        in5(sv, a0, b as int, c, d0, e),
        p_keys(sv)[a0] == k,
        n_keys(sv)[d0] == s_nks(sv)[b as int],
        acct == s_accts(sv)[b as int],
    ensures view_row(row@) == out_row(row5(sv, a0, b as int, c, d0, e)),
{
    let a = match find_key(cl.p_keys, cl.np, k) {
        Some(a) => a,
        None => { proof { assert(cl.p_keys@[a0] == k); } vstd::pervasive::unreached() },
    };
    let d = match find_key(cl.n_keys, cl.nn, cl.s_nks[b]) {
        Some(d) => d,
        None => { proof { assert(cl.n_keys@[d0] == cl.s_nks@[b as int]); } vstd::pervasive::unreached() },
    };
    proof {
        assert(p_keys(sv)[a as int] == p_keys(sv)[a0]);
        assert(a as int == a0);
        assert(n_keys(sv)[d as int] == n_keys(sv)[d0]);
        assert(d as int == d0);
        lemma_out_row(sv, a0, b as int, c, d0, e);
    }
    let sname = to_vec(text_slice(cl.s_name.off, cl.s_name.bytes, cl.s_name.n, cl.s_name.blen, b));
    let nname = to_vec(text_slice(cl.n_name.off, cl.n_name.bytes, cl.n_name.n, cl.n_name.blen, d));
    let mfgr = to_vec(text_slice(cl.p_mfgr.off, cl.p_mfgr.bytes, cl.p_mfgr.n, cl.p_mfgr.blen, a));
    let addr = to_vec(text_slice(cl.s_address.off, cl.s_address.bytes, cl.s_address.n, cl.s_address.blen, b));
    let phone = to_vec(text_slice(cl.s_phone.off, cl.s_phone.bytes, cl.s_phone.n, cl.s_phone.blen, b));
    let comm = to_vec(text_slice(cl.s_comment.off, cl.s_comment.bytes, cl.s_comment.n, cl.s_comment.blen, b));
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Num { coeff: acct, scale: 2 });
    row.push(EVal::Text(sname));
    row.push(EVal::Text(nname));
    row.push(EVal::Int(k));
    row.push(EVal::Text(mfgr));
    row.push(EVal::Text(addr));
    row.push(EVal::Text(phone));
    row.push(EVal::Text(comm));
    proof {
        assert(view_row(row@) =~= out_row(row5(sv, a0, b as int, c, d0, e)));
    }
    row
}

/// What `build_row` needs for candidate `q` (its kept FROM row's tuple and key data).
proof fn lemma_row_inputs(sv: StoresView, v: int, pat: Seq<u8>, rp: Seq<u8>, h: HitVecs, f: Seq<usize>, cs: Seq<int>,
    acct: Seq<i128>, pk: Seq<i64>, bb: Seq<usize>, q: int)
    requires
        stores_wf(sv), keys_ok(sv),
        hits_ok(sv, v, pat, rp, h),
        least_list(h.pk@, h.cost@, f),
        cs == f.map_values(|i: usize| h.c@[i as int] as int),
        lists_cands(sv, v, pat, rp, cs),
        forall|y: int| 0 <= y < f.len() ==> acct[y] == h.acct@[f[y] as int] && pk[y] == h.pk@[f[y] as int] && bb[y] == h.b@[f[y] as int],
        0 <= q < f.len(),
    ensures ({
        let t = cand_tuple(sv, v, pat, rp, cs[q]);
        &&& in5(sv, t.0, bb[q] as int, cs[q], t.2, t.3)
        &&& t.1 == bb[q] as int
        &&& p_keys(sv)[t.0] == pk[q]
        &&& n_keys(sv)[t.2] == s_nks(sv)[bb[q] as int]
        &&& acct[q] == s_accts(sv)[bb[q] as int]
        &&& cand_out(sv, v, pat, rp, cs)[q] == out_row(row5(sv, t.0, bb[q] as int, cs[q], t.2, t.3))
    }),
{
    let cx = cs[q];
    let i = f[q] as int;
    assert(0 <= cx < ps_n(sv) && cand(sv, v, pat, rp, cx));
    lemma_cand_row(sv, v, pat, rp, cx);
    let t = cand_tuple(sv, v, pat, rp, cx);
    lemma_keep_row5(sv, v, pat, rp, t.0, t.1, cx, t.2, t.3);
    assert(h.c@[i] as int == cx);
    assert(s_keys(sv)[t.1] == s_keys(sv)[h.b@[i] as int]);
    assert(t.1 == bb[q] as int);
}

/// The answer rows (see the module comment).
pub fn answer_rows(c: &Cols, Ghost(sv): Ghost<StoresView>, h: &HitVecs, Ghost(v): Ghost<int>, Ghost(pat): Ghost<Seq<u8>>,
    Ghost(rp): Ghost<Seq<u8>>) -> (rows: Vec<Vec<EVal>>)
    requires
        cols_ok(*c, sv),
        stores_wf(sv),
        keys_ok(sv),
        hits_ok(sv, v, pat, rp, *h),
    ensures answer_ok(sv, v, pat, rp, view_rows(rows@)),
{
    hide(hits_ok);
    hide(lists_cands);
    hide(topk_inv);
    hide(cand_keys_ok);
    proof {
        reveal(hits_ok);
        assert(h.b@.len() == h.c@.len() && h.pk@.len() == h.c@.len() && h.cost@.len() == h.c@.len() && h.acct@.len() == h.c@.len());
    }
    let f = least_per_key(&h.pk, &h.cost);
    let ghost cs = f@.map_values(|i: usize| h.c@[i as int] as int);
    proof { reveal(hits_ok); reveal(lists_cands); lemma_cands(sv, v, pat, rp, *h, f@); }
    let ghost rows_g = cand_out(sv, v, pat, rp, cs);
    // The candidates' key data.
    let mut acct: Vec<i128> = Vec::with_capacity(f.len());
    let mut pk: Vec<i64> = Vec::with_capacity(f.len());
    let mut bb: Vec<usize> = Vec::with_capacity(f.len());
    let nc = NameCols {
        soff: c.s_name.off, sbytes: c.s_name.bytes, ns: c.ns, sblen: c.s_name.blen,
        noff: c.n_name.off, nbytes: c.n_name.bytes, nn: c.nn, nblen: c.n_name.blen,
        supp_nk: c.s_nks, nat_keys: c.n_keys,
    };
    let mut q: usize = 0;
    while q < f.len()
        invariant
            cols_ok(*c, sv), stores_wf(sv), keys_ok(sv),
            hits_ok(sv, v, pat, rp, *h),
            least_list(h.pk@, h.cost@, f@),
            cs == f@.map_values(|i: usize| h.c@[i as int] as int),
            lists_cands(sv, v, pat, rp, cs),
            rows_g == cand_out(sv, v, pat, rp, cs),
            nc.wf(),
            nc.soff == c.s_name.off && nc.sbytes == c.s_name.bytes && nc.noff == c.n_name.off && nc.nbytes == c.n_name.bytes,
            nc.supp_nk == c.s_nks && nc.nat_keys == c.n_keys && nc.ns == c.ns && nc.nn == c.nn,
            q <= f@.len(),
            h.b@.len() == h.c@.len() && h.pk@.len() == h.c@.len() && h.cost@.len() == h.c@.len() && h.acct@.len() == h.c@.len(),
            acct@.len() == q, pk@.len() == q, bb@.len() == q,
            forall|x: int| 0 <= x < q ==> acct@[x] == h.acct@[f@[x] as int] && pk@[x] == h.pk@[f@[x] as int] && bb@[x] == h.b@[f@[x] as int],
        decreases f@.len() - q,
    {
        let i = f[q];
        acct.push(h.acct[i]);
        pk.push(h.pk[i]);
        bb.push(h.b[i]);
        q = q + 1;
    }
    proof {
        reveal(hits_ok);
        reveal(lists_cands);
        reveal(cand_keys_ok);
        assert forall|x: int| 0 <= x < rows_g.len() implies nc.keys_of(#[trigger] rows_g[x], acct@[x] as int, bb@[x] as int, pk@[x] as int) by {
            let i = f@[x] as int;
            let cx = cs[x];
            assert(cx == h.c@[i] as int);
            lemma_cand_row(sv, v, pat, rp, cx);
            let t = cand_tuple(sv, v, pat, rp, cx);
            lemma_keep_row5(sv, v, pat, rp, t.0, t.1, cx, t.2, t.3);
            lemma_out_row(sv, t.0, t.1, cx, t.2, t.3);
            assert(s_keys(sv)[t.1] == s_keys(sv)[h.b@[i] as int]);
            assert(t.1 == h.b@[i] as int);
            assert(text_row(nc.soff@, nc.sbytes@, t.1) == text_at(si::text_view(sv.flat_supplier, si::S_NAME_OFFSETS as int, si::S_NAME_BYTES as int), t.1));
            assert(text_row(nc.noff@, nc.nbytes@, t.2) == text_at(ni::text_view(sv.flat_nation, ni::N_NAME_OFFSETS as int, ni::N_NAME_BYTES as int), t.2));
            assert(nc.nat_keys@[t.2] == nc.supp_nk@[t.1]);
            assert(rows_g[x] == out_row(cand_row(sv, v, pat, rp, cx)));
        }
        assert(cand_keys_ok(nc, acct@, pk@, bb@, rows_g));
    }
    let (top, Ghost(rest)) = top_k(&nc, &acct, &pk, &bb, Ghost(rows_g), 100);
    proof {
        reveal(topk_inv);
        assert(forall|y: int| 0 <= y < top@.len() ==> (#[trigger] top@[y]) < rows_g.len());
        assert(rows_g.len() == f@.len() && acct@.len() == f@.len() && pk@.len() == f@.len() && bb@.len() == f@.len());
    }
    // The answer rows of the kept candidates.
    let mut out: Vec<Vec<EVal>> = Vec::new();
    let mut x: usize = 0;
    while x < top.len()
        invariant
            cols_ok(*c, sv), stores_wf(sv), keys_ok(sv),
            hits_ok(sv, v, pat, rp, *h),
            nc.wf(),
            nc.soff == c.s_name.off && nc.sbytes == c.s_name.bytes && nc.noff == c.n_name.off && nc.nbytes == c.n_name.bytes,
            nc.supp_nk == c.s_nks && nc.nat_keys == c.n_keys && nc.ns == c.ns && nc.nn == c.nn,
            cs == f@.map_values(|i: usize| h.c@[i as int] as int),
            lists_cands(sv, v, pat, rp, cs),
            rows_g == cand_out(sv, v, pat, rp, cs),
            cand_keys_ok(nc, acct@, pk@, bb@, rows_g),
            forall|y: int| 0 <= y < f@.len() ==> acct@[y] == h.acct@[f@[y] as int] && pk@[y] == h.pk@[f@[y] as int] && bb@[y] == h.b@[f@[y] as int],
            forall|y: int| 0 <= y < top@.len() ==> (#[trigger] top@[y]) < rows_g.len(),
            rows_g.len() == f@.len() && acct@.len() == f@.len() && pk@.len() == f@.len() && bb@.len() == f@.len(),
            least_list(h.pk@, h.cost@, f@),
            x <= top@.len(),
            view_rows(out@) == rows_of(rows_g, top@).subrange(0, x as int),
            topk_inv(rows_g, top@, rest, rows_g.len() as int, 100),
        decreases top@.len() - x,
    {
        let qq = top[x];
        let b = bb[qq];
        let k = pk[qq];
        let ghost cx = cs[qq as int];
        let ghost t = cand_tuple(sv, v, pat, rp, cx);
        proof {
            reveal(hits_ok);
            reveal(lists_cands);
            lemma_row_inputs(sv, v, pat, rp, *h, f@, cs, acct@, pk@, bb@, qq as int);
        }
        let row = build_row(c, Ghost(sv), acct[qq], b, k, Ghost(t.0), Ghost(cx), Ghost(t.2), Ghost(t.3));
        let ghost out0 = out@;
        out.push(row);
        proof {
            let rq = rows_g[qq as int];
            crate::link::outcome::lemma_view_rows_push(out0, row);
            assert(rows_of(rows_g, top@).subrange(0, x + 1) =~= rows_of(rows_g, top@).subrange(0, x as int).push(rq));
        }
        x = x + 1;
    }
    proof {
        reveal(topk_inv);
        reveal(lists_cands);
        reveal(cand_keys_ok);
        let t = rows_of(rows_g, top@);
        assert(t.subrange(0, x as int) =~= t);
        assert(rows_g.subrange(0, rows_g.len() as int) =~= rows_g);
        lemma_rows_keys_ok(nc, acct@, pk@, bb@, rows_g);
        lemma_kept_keys_ok(rows_g, top@, rows_g.len() as int);
        lemma_topk_perm(rows_g, t, rest, 100);
        let p = t + sort_rows(order_keys(), rest);
        assert(lists_cands(sv, v, pat, rp, cs) && sorted_by(order_keys(), p));
    }
    out
}

} // verus!
