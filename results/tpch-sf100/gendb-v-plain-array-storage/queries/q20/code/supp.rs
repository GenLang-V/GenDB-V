//! The qualifying supplier keys (`in_supp`) as a set (`SuppSet`): the list of the supplier keys of the qualifying
//! partsupp rows, with their bitmap when every key lies in the bitmap's range (else membership is a linear search).
//!
//! From the decisions of the decide tasks (`supp_from_decisions`): the supplier keys of the decided slots of every
//! group, in group order. The general path (`supp_naive`) decides every partsupp row from the definitions (a scan of
//! lineitem per row whose part matches); it is only taken for data outside the fast path's layout facts.
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::keys::*;
use crate::agent::pspass::*;
use crate::agent::scan::*;
use crate::agent::decide::*;
use crate::agent::bucket::*;
use crate::agent::common::buckets::*;
use crate::agent::den_li::{sizes_ok, lemma_ltotals_bounds};
use crate::agent::common::selection::*;
use crate::agent::common::split::*;

verus! {

/// The qualifying supplier keys: their list and, when built, their bitmap.
pub struct SuppSet {
    pub keys: Vec<i64>,
    pub kb: Option<KeyBits>,
}

/// `ss` holds exactly the keys of `in_supp`.
pub open spec fn supp_ok(ss: SuppSet, sv: StoresView, ps: Seq<Literal>, dlo: int, dhi: int) -> bool {
    &&& forall|v: int| #[trigger] ints(ss.keys@).contains(v) == in_supp(sv, ps, dlo, dhi, v)
    &&& ss.kb matches Some(kb) ==> kb_ok(kb, ints(ss.keys@))
}

/// The set of a key list (with its bitmap when the keys fit one).
fn set_of(keys: Vec<i64>) -> (ss: SuppSet)
    ensures ss.keys@ == keys@, ss.kb matches Some(kb) ==> kb_ok(kb, ints(ss.keys@)),
{
    let kb = build_keybits(&keys);
    SuppSet { keys, kb }
}

/// Whether `v` is a qualifying supplier key.
pub fn supp_has(ss: &SuppSet, v: i64, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(dlo): Ghost<int>,
    Ghost(dhi): Ghost<int>) -> (r: bool)
    requires supp_ok(*ss, sv, ps, dlo, dhi),
    ensures r == in_supp(sv, ps, dlo, dhi, v as int),
{
    match &ss.kb {
        Some(kb) => kb_has(kb, v, Ghost(ints(ss.keys@))),
        None => contains_key(&ss.keys, v),
    }
}

/// The qualifying supplier keys from the decisions of the `nb` buckets (every matching part key lies in one).
pub fn supp_from_decisions(res: &Vec<DecideOut>, nb: usize, bm: u64, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>,
    Ghost(dlo): Ghost<int>, Ghost(dhi): Ghost<int>) -> (ss: SuppSet)
    requires
        1 <= nb, res@.len() == nb,
        forall|u: int| 0 <= u < nb ==> #[trigger] res@[u].done && decide_ok(res@[u], sv, ps, bm, u, dlo, dhi),
        forall|v: int| #[trigger] in_part(sv, ps, v) ==> bk(v as i64, bm) < nb,
    ensures supp_ok(ss, sv, ps, dlo, dhi),
{
    let ghost nps = n_ps(sv) as int;
    let mut keys: Vec<i64> = Vec::new();
    let mut u: usize = 0;
    proof {
        assert forall|q: int| #[trigger] bk(pspk(sv)[q], bm) >= 0 by { lemma_bk_nonneg(pspk(sv)[q], bm); }
    }
    while u < nb
        invariant
            1 <= nb, res@.len() == nb, u <= nb, nps == n_ps(sv) as int,
            forall|u2: int| 0 <= u2 < nb ==> #[trigger] res@[u2].done && decide_ok(res@[u2], sv, ps, bm, u2, dlo, dhi),
            forall|v: int| #[trigger] ints(keys@).contains(v) == exists|q: int| 0 <= q < nps
                && #[trigger] ps_ok(sv, ps, dlo, dhi, q) && pssk(sv)[q] as int == v && bk(pspk(sv)[q], bm) < u,
        decreases nb - u,
    {
        let ghost p = and_pred(inp(sv, ps), kbucket(pspk(sv), bm, u as int));
        let ghost qs = bucket_rows(sv, ps, bm, u as int);
        proof {
            lemma_range_filter_members(0, nps, p);
        }
        let o = &res[u];
        let n = o.n;
        let ghost before = ints(keys@);
        let mut s: usize = 0;
        while s < n
            invariant
                s <= n, n == o.n, o.done, decide_ok(*o, sv, ps, bm, u as int, dlo, dhi), qs == bucket_rows(sv, ps, bm, u as int),
                forall|v: int| #[trigger] ints(keys@).contains(v) == (before.contains(v)
                    || exists|s2: int| 0 <= s2 < s && #[trigger] o.ok@[s2] && o.ssk@[s2] as int == v),
            decreases n - s,
        {
            let ghost k0 = ints(keys@);
            if o.ok[s] {
                keys.push(o.ssk[s]);
            }
            proof {
                let k1 = ints(keys@);
                assert forall|v: int| #[trigger] k1.contains(v) == (before.contains(v)
                    || exists|s2: int| 0 <= s2 < s + 1 && #[trigger] o.ok@[s2] && o.ssk@[s2] as int == v) by {
                    if o.ok@[s as int] {
                        assert(k1 =~= k0.push(o.ssk@[s as int] as int));
                        if k0.contains(v) {
                            let t = choose|t: int| 0 <= t < k0.len() && k0[t] == v;
                            assert(k1[t] == v);
                        }
                        if k1.contains(v) && v != o.ssk@[s as int] as int {
                            let t = choose|t: int| 0 <= t < k1.len() && k1[t] == v;
                            assert(t < k0.len() && k0[t] == v);
                        }
                        if v == o.ssk@[s as int] as int {
                            assert(k1[k0.len() as int] == v);
                        }
                    } else {
                        assert(k1 =~= k0);
                    }
                    if exists|s2: int| 0 <= s2 < s + 1 && #[trigger] o.ok@[s2] && o.ssk@[s2] as int == v {
                        let s2 = choose|s2: int| 0 <= s2 < s + 1 && #[trigger] o.ok@[s2] && o.ssk@[s2] as int == v;
                        if s2 < s {
                            assert(exists|s3: int| 0 <= s3 < s && #[trigger] o.ok@[s3] && o.ssk@[s3] as int == v);
                        }
                    }
                }
            }
            s = s + 1;
        }
        proof {
            // the bucket adds the qualifying rows whose key lies in bucket u
            assert forall|v: int| #[trigger] ints(keys@).contains(v) == exists|q: int| 0 <= q < nps
                && #[trigger] ps_ok(sv, ps, dlo, dhi, q) && pssk(sv)[q] as int == v && bk(pspk(sv)[q], bm) < u + 1 by {
                if exists|s2: int| 0 <= s2 < n && #[trigger] o.ok@[s2] && o.ssk@[s2] as int == v {
                    let s2 = choose|s2: int| 0 <= s2 < n && #[trigger] o.ok@[s2] && o.ssk@[s2] as int == v;
                    let q = qs[s2];
                    assert(p(q));
                    assert(ps_ok(sv, ps, dlo, dhi, q) && pssk(sv)[q] as int == v && bk(pspk(sv)[q], bm) == u);
                }
                if exists|q: int| 0 <= q < nps && #[trigger] ps_ok(sv, ps, dlo, dhi, q) && pssk(sv)[q] as int == v && bk(pspk(sv)[q], bm) < u + 1 {
                    let q = choose|q: int| 0 <= q < nps && #[trigger] ps_ok(sv, ps, dlo, dhi, q) && pssk(sv)[q] as int == v
                        && bk(pspk(sv)[q], bm) < u + 1;
                    if bk(pspk(sv)[q], bm) == u {
                        assert(inp(sv, ps)(q));
                        assert(p(q));
                        assert(exists|s3: int| 0 <= s3 < qs.len() && #[trigger] qs[s3] == q);
                        let s2 = choose|s2: int| 0 <= s2 < qs.len() && #[trigger] qs[s2] == q;
                        assert(o.n == qs.len());
                        assert(o.ok@[s2] == ps_ok(sv, ps, dlo, dhi, qs[s2]));
                        assert(o.ssk@[s2] == pssk(sv)[qs[s2]]);
                        assert(o.ok@[s2] && o.ssk@[s2] as int == v);
                    } else {
                        assert(before.contains(v));
                    }
                }
            }
        }
        u = u + 1;
    }
    proof {
        assert forall|v: int| #[trigger] ints(keys@).contains(v) == in_supp(sv, ps, dlo, dhi, v) by {
            if in_supp(sv, ps, dlo, dhi, v) {
                let q = choose|q: int| 0 <= q < n_ps(sv) && #[trigger] ps_ok(sv, ps, dlo, dhi, q) && pssk(sv)[q] as int == v;
                assert(in_part(sv, ps, pspk(sv)[q] as int));
                assert(((pspk(sv)[q] as int) as i64) == pspk(sv)[q]);
            }
        }
    }
    set_of(keys)
}

/// Whether `v` is among `keys[0..n]` (linear search).
fn contains_key(keys: &Vec<i64>, v: i64) -> (r: bool)
    ensures r == ints(keys@).contains(v as int),
{
    let ghost ks = ints(keys@);
    let n = keys.len();
    let mut i: usize = 0;
    while i < n
        invariant n == keys@.len(), i <= n, ks == ints(keys@),
            forall|t: int| 0 <= t < i ==> keys@[t] != v,
        decreases n - i,
    {
        if keys[i] == v {
            proof { assert(ks[i as int] == v as int); }
            return true;
        }
        i = i + 1;
    }
    proof {
        if ks.contains(v as int) {
            let t = choose|t: int| 0 <= t < ks.len() && ks[t] == v as int;
            assert(keys@[t] == v);
        }
    }
    false
}

// ------------------------------------------------------------------------------------------------ the general path

/// `lcnt(a, b)` and `lsum(a, b)` by a scan of lineitem.
fn scan_pair(c: &Cols, a: i64, b: i64, dlo: i32, dhi: i32, Ghost(sv): Ghost<StoresView>) -> (r: (u64, i128))
    requires cols_ok(*c, sv), model_ok(sv), sizes_ok(sv),
    ensures
        r.0 as int == lcnt(sv, dlo as int, dhi as int, a as int, b as int),
        r.1 as int == lsum(sv, dlo as int, dhi as int, a as int, b as int),
{
    let nl = c.nl;
    let mut cnt: u64 = 0;
    let mut sum: i128 = 0;
    let mut l: usize = 0;
    while l < nl
        invariant
            cols_ok(*c, sv), model_ok(sv), sizes_ok(sv), nl == c.nl, l <= nl,
            cnt as int == range_sum(0, l as int, lcnt_term(sv, dlo as int, dhi as int, a as int, b as int)),
            sum as int == range_sum(0, l as int, lsum_term(sv, dlo as int, dhi as int, a as int, b as int)),
        decreases nl - l,
    {
        proof {
            crate::agent::den_li::lemma_lterm_bounds(sv, dlo as int, dhi as int, a as int, b as int, 0, l as int + 1);
            assert(num15(lqt(sv)[l as int]));
            let k = range_sum(0, l as int + 1, lcnt_term(sv, dlo as int, dhi as int, a as int, b as int));
            assert(999_999_999_999_999 * k <= 999_999_999_999_999 * 0xffff_ffff_ffff_ffff) by (nonlinear_arith)
                requires 0 <= k <= 0xffff_ffff_ffff_ffff;
        }
        if c.lpk[l] == a && c.lsk[l] == b && dlo <= c.lsd[l] && c.lsd[l] < dhi {
            cnt = cnt + 1;
            sum = sum + c.lqt[l];
        }
        l = l + 1;
    }
    (cnt, sum)
}

/// The qualifying supplier keys from the definitions (general path): `keys` are the matching part keys.
pub fn supp_naive(c: &Cols, keys: &Vec<i64>, dlo: i32, dhi: i32, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (ss: SuppSet)
    requires
        cols_ok(*c, sv), model_ok(sv), sizes_ok(sv),
        forall|v: int| #[trigger] ints(keys@).contains(v) == in_part(sv, ps, v),
    ensures supp_ok(ss, sv, ps, dlo as int, dhi as int),
{
    let nps = c.nps;
    let mut out: Vec<i64> = Vec::new();
    let mut q: usize = 0;
    while q < nps
        invariant
            cols_ok(*c, sv), model_ok(sv), sizes_ok(sv), nps == c.nps, q <= nps,
            forall|v: int| #[trigger] ints(keys@).contains(v) == in_part(sv, ps, v),
            forall|v: int| #[trigger] ints(out@).contains(v) == exists|q2: int| 0 <= q2 < q
                && #[trigger] ps_ok(sv, ps, dlo as int, dhi as int, q2) && pssk(sv)[q2] as int == v,
        decreases nps - q,
    {
        let a = c.pspk[q];
        let b = c.pssk[q];
        let aq = c.psaq[q];
        let d = if contains_key(keys, a) {
            let (k, s) = scan_pair(c, a, b, dlo, dhi, Ghost(sv));
            proof { lemma_ltotals_bounds(sv, dlo as int, dhi as int, a as int, b as int); }
            k > 0 && (aq as i128) * 200 > s
        } else {
            false
        };
        let ghost k0 = ints(out@);
        if d {
            out.push(b);
        }
        proof {
            let k1 = ints(out@);
            assert(d == ps_ok(sv, ps, dlo as int, dhi as int, q as int));
            assert forall|v: int| #[trigger] k1.contains(v) == exists|q2: int| 0 <= q2 < q + 1
                && #[trigger] ps_ok(sv, ps, dlo as int, dhi as int, q2) && pssk(sv)[q2] as int == v by {
                if d {
                    assert(k1 =~= k0.push(b as int));
                    if k0.contains(v) {
                        let t = choose|t: int| 0 <= t < k0.len() && k0[t] == v;
                        assert(k1[t] == v);
                    }
                    if k1.contains(v) && v != b as int {
                        let t = choose|t: int| 0 <= t < k1.len() && k1[t] == v;
                        assert(t < k0.len() && k0[t] == v);
                    }
                    if v == b as int {
                        assert(k1[k0.len() as int] == v);
                    }
                } else {
                    assert(k1 =~= k0);
                }
            }
        }
        q = q + 1;
    }
    set_of(out)
}

} // verus!
