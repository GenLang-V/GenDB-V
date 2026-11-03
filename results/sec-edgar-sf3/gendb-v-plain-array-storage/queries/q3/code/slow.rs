//! The fallback for inputs beyond the fast path's bounds (at least `0xffff_fff0` sub rows, or very many qualifying
//! subs): per rank, its total by a direct pass over all num rows, and the groups by linear search. Quadratic, so
//! only correct, not fast; never taken on inputs of realistic size.
use vstd::prelude::*;
use crate::spec::numeric::*;
use crate::spec::value::*;
use crate::link::query::{text_wf, text_at, TextView};
use crate::agent::common::bytes::*;
use crate::agent::common::wide::*;
use crate::agent::scan::*;
use crate::agent::keys::{SubCols, rank_key, lemma_qlist};
use crate::agent::run::{totals_ok, lemma_tot_in_range};
use crate::agent::groups::*;

verus! {

/// The sub columns the fallback reads: the adsh text.
pub open spec fn sub_text_ok(sub: &SubCols) -> bool {
    &&& text_wf(sub.text(), sub.n as int)
    &&& sub.bytes_len == sub.adsh_bytes@.len()
}

/// The total and whether some row counted, over all num rows, for the adsh `key`.
fn rank_total(num: &NumCols, p0: &[u8], p0_len: usize, key: &[u8], kn: usize) -> (r: (Wide, bool))
    requires num.wf(), p0_len == p0@.len(), kn == key@.len(),
    ensures
        wval(r.0) == rsum(num, p0@, key@, 0, num.n as int),
        r.1 == (rcnt(num, p0@, key@, 0, num.n as int) > 0),
{
    let n = num.n;
    let mut acc = wide_zero();
    let mut cnt = false;
    let mut i: usize = 0;
    while i < n
        invariant
            num.wf(), p0_len == p0@.len(), kn == key@.len(), n == num.n, i <= n,
            wval(acc) == rsum(num, p0@, key@, 0, i as int),
            cnt == (rcnt(num, p0@, key@, 0, i as int) > 0),
        decreases n - i,
    {
        proof {
            assert(text_wf(num.uom_text(), num.n as int));
            assert(text_wf(num.adsh_text(), num.n as int));
            assert(0 <= num.uom_text().offsets[i as int] <= num.uom_text().offsets[i + 1] <= num.uom_text().bytes.len());
            assert(0 <= num.adsh_text().offsets[i as int] <= num.adsh_text().offsets[i + 1] <= num.adsh_text().bytes.len());
            lemma_tot_in_range(num, p0@, key@, i as int);
            lemma_rcnt_nonneg(num, p0@, key@, 0, i as int);
            assert(abs(num.val(i as int)) < pow10(28));
            assert(pow10(28) == 10000000000000000000000000000) by (compute);
        }
        let ua = num.uom_off[i] as usize;
        let ub = num.uom_off[i + 1] as usize;
        let aa = num.adsh_off[i] as usize;
        let ab = num.adsh_off[i + 1] as usize;
        if ub - ua == p0_len && eq_n(sub_bytes(num.uom_bytes, ua, ub), p0, p0_len)
            && ab - aa == kn && eq_n(sub_bytes(num.adsh_bytes, aa, ab), key, kn) {
            acc = wide_add_i128(acc, num.value[i]);
            cnt = true;
        }
        i = i + 1;
    }
    (acc, cnt)
}

/// The totals of every rank by direct passes.
pub fn slow_totals(num: &NumCols, sub: &SubCols, p0: &[u8], p0_len: usize, qr: &Vec<usize>) -> (r: (Vec<Wide>, Vec<bool>))
    requires
        num.wf(), sub_text_ok(sub), p0_len == p0@.len(),
        qr@.len() == sub.qlist(sub.n as int).len(),
        forall|t: int| 0 <= t < qr@.len() ==> #[trigger] qr@[t] as int == sub.qlist(sub.n as int)[t],
    ensures totals_ok(num, sub, p0@, r.0@, r.1@, num.n as int),
{
    let nq = qr.len();
    let mut tot: Vec<Wide> = Vec::with_capacity(nq);
    let mut seen: Vec<bool> = Vec::with_capacity(nq);
    let mut id: usize = 0;
    proof {
        lemma_qlist(sub, sub.n as int);
    }
    while id < nq
        invariant
            num.wf(), sub_text_ok(sub), p0_len == p0@.len(), nq == qr@.len(),
            qr@.len() == sub.qlist(sub.n as int).len(),
            forall|t: int| 0 <= t < qr@.len() ==> #[trigger] qr@[t] as int == sub.qlist(sub.n as int)[t],
            forall|a: int| 0 <= a < sub.qlist(sub.n as int).len() ==> 0 <= #[trigger] sub.qlist(sub.n as int)[a] < sub.n,
            id <= nq, tot@.len() == id, seen@.len() == id,
            forall|t: int| 0 <= t < id ==> #[trigger] wval(tot@[t]) == rsum(num, p0@, rank_key(sub, t), 0, num.n as int),
            forall|t: int| 0 <= t < id ==> #[trigger] seen@[t] == (rcnt(num, p0@, rank_key(sub, t), 0, num.n as int) > 0),
        decreases nq - id,
    {
        let j = qr[id];
        proof {
            assert(qr@[id as int] as int == sub.qlist(sub.n as int)[id as int]);
            assert(0 <= sub.text().offsets[j as int] <= sub.text().offsets[j + 1] <= sub.text().bytes.len());
        }
        let ka = sub.adsh_off[j] as usize;
        let kb = sub.adsh_off[j + 1] as usize;
        let key = sub_bytes(sub.adsh_bytes, ka, kb);
        let (w, c) = rank_total(num, p0, p0_len, key, kb - ka);
        proof {
            assert(key@ == rank_key(sub, id as int));
        }
        tot.push(w);
        seen.push(c);
        id = id + 1;
    }
    (tot, seen)
}

/// The groups of every rank by linear search.
pub fn slow_groups(kc: &KeyCols, qr: &Vec<usize>, tot: &Vec<Wide>, seen: &Vec<bool>) -> (g: Groups)
    requires kc.wf(), ranks_wf(kc, qr@, tot@, seen@),
    ensures
        groups_ok(&g, kc, qr@, tot@, seen@, qr@.len() as int),
        groups_cols(&g, kc),
        g.sum@.len() == g.rep@.len(),
{
    let nq = qr.len();
    let mut g = Groups {
        bits: 1,
        nslots: 0,
        slots: Vec::new(),
        cik: Vec::new(),
        rep: Vec::new(),
        sum: Vec::new(),
        ncik: 0,
        total: wide_zero(),
    };
    proof {
        assert(gks(kc, qr@, seen@, 0) =~= Seq::<Row>::empty());
        reveal(groups_ok);
    }
    let mut id: usize = 0;
    while id < nq
        invariant
            kc.wf(), ranks_wf(kc, qr@, tot@, seen@), nq == qr@.len(), id <= nq,
            groups_cols(&g, kc), g.ncik <= g.rep@.len(),
            g.cik@.len() == g.rep@.len(), g.sum@.len() == g.rep@.len(),
            groups_ok(&g, kc, qr@, tot@, seen@, id as int),
        decreases nq - id,
    {
        let ghost g0 = g;
        let ghost ks = gks(kc, qr@, seen@, id as int);
        proof {
            lemma_gks(kc, qr@, seen@, id as int);
            lemma_sums_in_range(kc, qr@, tot@, seen@, Seq::empty(), id as int);
            lemma_groups_facts(&g, kc, qr@, tot@, seen@, id as int);
        }
        if seen[id] {
            let j = qr[id];
            proof {
                lemma_kc_row(kc, j as int);
            }
            let c = kc.cik[j];
            let a = kc.name_off[j] as usize;
            let b = kc.name_off[j + 1] as usize;
            let x = sub_bytes(kc.name_bytes, a, b);
            let ghost k = kc.okey(j as int);
            // search the groups
            let ng = g.rep.len();
            let mut found: usize = ng;
            let mut cik_seen = false;
            let mut i: usize = 0;
            while i < ng
                invariant
                    kc.wf(), groups_cols(&g, kc), g == g0, ng == g.rep@.len(), i <= ng, found <= ng,
                    g.cik@.len() == g.rep@.len(),
                    j < kc.n, c as int == kc.cik(j as int), x@ == kc.name(j as int), k == kc.okey(j as int),
                    a <= b, x@.len() == b - a,
                    found < ng ==> group_key(&g, kc, found as int) == k,
                    found == ng ==> forall|i2: int| 0 <= i2 < i ==> #[trigger] group_key(&g, kc, i2) != k,
                    found == ng ==> (cik_seen == exists|i2: int| 0 <= i2 < i && #[trigger] g.cik@[i2] == c),
                decreases ng - i,
            {
                if found == ng {
                    if g.cik[i] == c {
                        let rj = g.rep[i];
                        proof {
                            lemma_kc_row(kc, rj as int);
                        }
                        let ra = kc.name_off[rj] as usize;
                        let rb = kc.name_off[rj + 1] as usize;
                        if rb - ra == b - a && eq_n(sub_bytes(kc.name_bytes, ra, rb), x, b - a) {
                            proof {
                                assert(kc.okey(rj as int) =~= kc.okey(j as int));
                            }
                            found = i;
                        } else {
                            proof {
                                assert(kc.okey(rj as int)[0] != kc.okey(j as int)[0]);
                            }
                        }
                        cik_seen = true;
                    } else {
                        proof {
                            assert(kc.okey(g.rep@[i as int] as int)[1] != kc.okey(j as int)[1]);
                        }
                    }
                }
                i = i + 1;
            }
            proof {
                lemma_cik_in_groups(&g0, kc, qr@, tot@, seen@, id as int, c);
            }
            if found < ng {
                proof {
                    lemma_sums_in_range(kc, qr@, tot@, seen@, ks[found as int], id as int);
                    assert(ks[found as int] == k);
                    assert(g0.cik@[found as int] == c);
                }
                let s = wide_add(g.sum[found], tot[id]);
                g.sum.set(found, s);
                g.total = wide_add(g.total, tot[id]);
                proof {
                    lemma_found_step(&g0, &g, kc, qr@, tot@, seen@, id as int, found as int);
                }
            } else {
                proof {
                    assert(!ks.contains(k)) by {
                        if ks.contains(k) {
                            let i2 = choose|i2: int| 0 <= i2 < ks.len() && ks[i2] == k;
                            assert(group_key(&g0, kc, i2) == k);
                        }
                    }
                }
                if !cik_seen {
                    g.ncik = g.ncik + 1;
                }
                g.rep.push(j);
                g.cik.push(c);
                g.sum.push(tot[id]);
                g.total = wide_add(g.total, tot[id]);
                proof {
                    lemma_new_step(&g0, &g, kc, qr@, tot@, seen@, id as int, cik_seen);
                }
            }
        } else {
            proof {
                lemma_skip_step(&g, kc, qr@, tot@, seen@, id as int);
            }
        }
        id = id + 1;
    }
    g
}

} // verus!
