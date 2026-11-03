//! The lineitem pass: the lineitem rows whose shipdate lies in the window and whose part key is a matching part's
//! (`lrecs`), each recorded as the triple (part key, supplier key, quantity coefficient) in the region of its part-key
//! bucket (`bucket`): region `u` holds the records for the bucket's keys `bkeys(keys, bm, u)` (`line_range`).
//!
//! Kernel, per chunk of `CH` rows: first the candidates (`chunk_cands`): per block of 64 rows a mask of the rows in
//! the date window (`block_mask`, the 4-byte shipdate column read in order), then only for the mask's rows, lowest
//! first, the coarse key bitmap, the passing rows' offsets compacted into a buffer without a branch on the outcome.
//! Then the candidates together (`chunk_recs`): the exact key bitmap, and the record of each row that passes.
//! Testing the exact bitmap for a whole chunk's candidates at once lets its cache misses overlap instead of each
//! stalling the mask work. Nothing here looks up partsupp: the records are matched to partsupp rows later, per
//! part-key range (`decide`).
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::keys::*;
use crate::agent::common::bitset::*;
use crate::agent::common::selection::*;
use crate::agent::common::tz::tz64;
use crate::agent::common::buckets::*;
use crate::agent::bucket::*;

verus! {

/// Lineitem row `l`'s shipdate lies in `[dlo, dhi)`.
pub open spec fn in_win(sv: StoresView, dlo: int, dhi: int, l: int) -> bool { dlo <= lsd(sv)[l] && lsd(sv)[l] < dhi }

/// Lineitem row `l` is in the window and its part key is one of `keys`.
pub open spec fn lrec(sv: StoresView, dlo: int, dhi: int, keys: Seq<int>) -> spec_fn(int) -> bool {
    |l: int| in_win(sv, dlo, dhi, l) && keys.contains(lpk(sv)[l] as int)
}

/// The recorded rows of `[lo, hi)`, ascending.
pub open spec fn lrecs(sv: StoresView, dlo: int, dhi: int, keys: Seq<int>, lo: int, hi: int) -> Seq<int> {
    range_filter(lo, hi, lrec(sv, dlo, dhi, keys))
}

/// `rec[0 .. 3 n]` records the rows `rs`: record `t` is `rec[3 t]` (part key), `rec[3 t + 1]` (supplier key) and
/// `rec[3 t + 2]` (quantity coefficient) of row `rs[t]`.
pub open spec fn recs_ok(rec: Seq<i64>, n: int, sv: StoresView, rs: Seq<int>) -> bool {
    &&& n == rs.len() && 3 * n <= rec.len()
    &&& forall|t: int| 0 <= t < n ==> rec[3 * t] == lpk(sv)[#[trigger] rs[t]] && rec[3 * t + 1] == lsk(sv)[rs[t]]
            && rec[3 * t + 2] as int == lqt(sv)[rs[t]] as int
}

/// No row of `[a, b)` satisfies `f`: the filter is unchanged.
pub proof fn lemma_range_filter_skip(lo: int, a: int, b: int, f: spec_fn(int) -> bool)
    requires lo <= a <= b, forall|l: int| a <= l < b ==> !#[trigger] f(l),
    ensures range_filter(lo, b, f) == range_filter(lo, a, f),
    decreases b - a,
{
    if b > a {
        lemma_range_filter_skip(lo, a, b - 1, f);
        assert(!f(b - 1));
    }
}

/// The window mask of rows `i .. bend` (at most 64): bit `u` is set exactly for row `i + u` in the window.
pub fn block_mask(lsd: &[i32], nl: usize, i: usize, bend: usize, dlo: i32, dhi: i32, Ghost(sv): Ghost<StoresView>) -> (m: u64)
    requires lsd@ == crate::agent::tables::lsd(sv), lsd@.len() == nl, i <= bend <= nl, bend - i <= 64,
    ensures forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == ((u as int) < bend - i && in_win(sv, dlo as int, dhi as int, i + u)),
    no_unwind
{
    let mut m: u64 = 0;
    let mut j = i;
    proof {
        assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == ((u as int) < j - i && in_win(sv, dlo as int, dhi as int, i + u)) by {
            lemma_bit_zero(u);
        }
    }
    while j < bend
        invariant
            lsd@ == crate::agent::tables::lsd(sv), lsd@.len() == nl, i <= j <= bend <= nl, bend - i <= 64,
            forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == ((u as int) < j - i && in_win(sv, dlo as int, dhi as int, i + u)),
        decreases bend - j,
    {
        let d = lsd[j];
        let ghost m0 = m;
        if dlo <= d && d < dhi {
            let t = (j - i) as u64;
            m = m | (1u64 << t);
            proof {
                assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == ((u as int) < j + 1 - i && in_win(sv, dlo as int, dhi as int, i + u)) by {
                    lemma_bit_or(m0, t, u);
                }
            }
        } else {
            proof {
                assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == ((u as int) < j + 1 - i && in_win(sv, dlo as int, dhi as int, i + u)) by {
                    if u as int == j - i {
                        assert(!in_win(sv, dlo as int, dhi as int, j as int));
                    }
                }
            }
        }
        j = j + 1;
    }
    m
}

/// Rows per chunk of a lineitem task: the candidates of a chunk are collected first, then tested together.
pub const CH: usize = 65536;

/// Row `l` is in the window and its part key passes the coarse bitmap.
pub open spec fn cpred(sv: StoresView, dlo: int, dhi: int, kb: KeyBits) -> spec_fn(int) -> bool {
    |l: int| in_win(sv, dlo, dhi, l) && coarse_hit(kb, lpk(sv)[l] as int)
}

/// The candidates of the rows `[i, e)` (`cpred`) as offsets from `i` in `cand[0..nc]` (`no_unwind`): per block of
/// 64 rows the window mask, then for its rows the coarse test, written without a branch on its outcome.
fn chunk_cands(lsd: &[i32], lpk: &[i64], nl: usize, kb: &KeyBits, i: usize, e: usize, dlo: i32, dhi: i32,
    cand: &mut Vec<u32>, Ghost(sv): Ghost<StoresView>) -> (nc: usize)
    requires
        lsd@ == crate::agent::tables::lsd(sv), lpk@ == crate::agent::tables::lpk(sv), lsd@.len() == nl, lpk@.len() == nl,
        i <= e <= nl, e - i <= CH, old(cand)@.len() >= CH, kb.coarse@.len() == kb.ncw, kb.kmax <= 0x1_0000_0000,
    ensures
        final(cand)@.len() == old(cand)@.len(),
        sel_matches(final(cand)@, nc as int, i as int, range_filter(i as int, e as int, cpred(sv, dlo as int, dhi as int, *kb))),
    no_unwind
{
    let ghost p = cpred(sv, dlo as int, dhi as int, *kb);
    let mut nc: usize = 0;
    let mut j = i;
    while j < e
        invariant
            lsd@ == crate::agent::tables::lsd(sv), lpk@ == crate::agent::tables::lpk(sv), lsd@.len() == nl, lpk@.len() == nl,
            i <= j <= e <= nl, e - i <= CH, cand@.len() == old(cand)@.len(), cand@.len() >= CH,
            kb.coarse@.len() == kb.ncw, kb.kmax <= 0x1_0000_0000, p == cpred(sv, dlo as int, dhi as int, *kb),
            nc <= j - i,
            sel_matches(cand@, nc as int, i as int, range_filter(i as int, j as int, p)),
        decreases e - j,
    {
        let bend = if e - j >= 64 { j + 64 } else { e };
        let mut m = block_mask(lsd, nl, j, bend, dlo, dhi, Ghost(sv));
        let ghost mut pos: int = 0;
        while m != 0
            invariant
                lsd@ == crate::agent::tables::lsd(sv), lpk@ == crate::agent::tables::lpk(sv), lsd@.len() == nl, lpk@.len() == nl,
                i <= j < bend <= e <= nl, e - i <= CH, bend - j <= 64, cand@.len() == old(cand)@.len(), cand@.len() >= CH,
                kb.coarse@.len() == kb.ncw, kb.kmax <= 0x1_0000_0000, p == cpred(sv, dlo as int, dhi as int, *kb),
                0 <= pos <= bend - j, nc <= j + pos - i,
                forall|u: u64| u < 64 ==> #[trigger] bit(m, u) == (pos <= u && (u as int) < bend - j && in_win(sv, dlo as int, dhi as int, j + u)),
                sel_matches(cand@, nc as int, i as int, range_filter(i as int, j + pos, p)),
            decreases bend - j - pos,
        {
            proof { lemma_first_bit(m); }
            let t = tz64(m);
            let r = j + t as usize;
            proof {
                // the rows from `pos` to `t` are outside the window
                assert forall|l: int| j + pos <= l < r implies !#[trigger] p(l) by {
                    let u = (l - j) as u64;
                    assert(u < t);
                    assert(!bit(m, u));
                }
                lemma_range_filter_skip(i as int, j + pos, r as int, p);
                assert(bit(m, t as u64));
                assert(in_win(sv, dlo as int, dhi as int, r as int));
            }
            let v = lpk[r];
            let keep = kb_coarse(kb, v);
            let off = (r - i) as u32;
            proof {
                lemma_sel_write(cand@, nc as int, i as int, range_filter(i as int, r as int, p), off, keep);
                assert(p(r as int) == keep);
                assert(range_filter(i as int, r as int + 1, p)
                    == if keep { range_filter(i as int, r as int, p).push(r as int) } else { range_filter(i as int, r as int, p) });
            }
            cand[nc] = off;
            nc = nc + if keep { 1usize } else { 0usize };
            let ghost m0 = m;
            m = m & (m - 1);
            proof {
                pos = t as int + 1;
                assert forall|u: u64| u < 64 implies #[trigger] bit(m, u) == (pos <= u && (u as int) < bend - j && in_win(sv, dlo as int, dhi as int, j + u)) by {
                    lemma_clear_lowest(m0, t as u64, u);
                }
            }
        }
        proof {
            assert forall|l: int| j + pos <= l < bend implies !#[trigger] p(l) by {
                let u = (l - j) as u64;
                lemma_bit_zero(u);
            }
            lemma_range_filter_skip(i as int, j + pos, bend as int, p);
        }
        j = bend;
    }
    nc
}

/// The records of `[lo, i)` of every bucket, with the candidates `cs[..q]` of `[i, e)` that pass the exact test.
pub open spec fn recs_upto(sv: StoresView, dlo: int, dhi: int, keys: Seq<int>, bm: u64, lo: int, i: int, cs: Seq<int>, q: int)
    -> spec_fn(int) -> Seq<int> {
    |u: int| lrecs(sv, dlo, dhi, bkeys(keys, bm, u), lo, i) + seq_filter(cs.take(q), lrec(sv, dlo, dhi, bkeys(keys, bm, u)))
}

/// The bucketed records of `[lo, i)`.
pub open spec fn brecs(sv: StoresView, dlo: int, dhi: int, keys: Seq<int>, bm: u64, lo: int, i: int) -> spec_fn(int) -> Seq<int> {
    |u: int| lrecs(sv, dlo, dhi, bkeys(keys, bm, u), lo, i)
}

/// The records of the candidates `cand[0..nc]` of the rows `[i, e)` appended to their buckets after the records of
/// `[lo, i)` (`no_unwind`): the exact key test, then the record. False when a bucket outgrows `cap`.
#[inline(always)]
fn chunk_recs(lpk: &[i64], lsk: &[i64], lqt: &[i128], nl: usize, kb: &KeyBits, cand: &Vec<u32>, nc: usize,
    i: usize, e: usize, out: &mut Vec<i64>, cnt: &mut Vec<usize>, olen: usize, nb: usize, bm: u64, cap: usize, lo: usize,
    Ghost(sv): Ghost<StoresView>, Ghost(keys): Ghost<Seq<int>>, Ghost(dlo): Ghost<int>, Ghost(dhi): Ghost<int>) -> (fit: bool)
    requires
        lpk@ == crate::agent::tables::lpk(sv), lsk@ == crate::agent::tables::lsk(sv), lqt@ == crate::agent::tables::lqt(sv),
        nl as int == n_l(sv), lpk@.len() == n_l(sv), lsk@.len() == n_l(sv), lqt@.len() == n_l(sv), domains_ok(sv),
        kb_ok(*kb, keys), lo <= i <= e <= nl, 1 <= nb <= 64, olen == old(out)@.len(),
        sel_matches(cand@, nc as int, i as int, range_filter(i as int, e as int, cpred(sv, dlo, dhi, *kb))),
        regions_ok(old(out)@, old(cnt)@, nb as int, cap as int, crate::agent::tables::lpk(sv), crate::agent::tables::lsk(sv), lq_c(sv),
            brecs(sv, dlo, dhi, keys, bm, lo as int, i as int)),
    ensures
        final(out)@.len() == old(out)@.len(), final(cnt)@.len() == old(cnt)@.len(),
        fit ==> regions_ok(final(out)@, final(cnt)@, nb as int, cap as int, crate::agent::tables::lpk(sv), crate::agent::tables::lsk(sv),
            lq_c(sv), brecs(sv, dlo, dhi, keys, bm, lo as int, e as int)),
    no_unwind
{
    let ghost f = lrec(sv, dlo, dhi, keys);
    let ghost p = cpred(sv, dlo, dhi, *kb);
    let ghost cs = range_filter(i as int, e as int, p);
    let ghost (ka, kb2, kc) = (crate::agent::tables::lpk(sv), crate::agent::tables::lsk(sv), lq_c(sv));
    proof {
        lemma_range_filter_members(i as int, e as int, p);
        lemma_range_filter_len(i as int, e as int, p);
        assert forall|u: int| 0 <= u < nb implies #[trigger] cnt@[u] <= cap
            && trip_at(out@, 3 * cap * u, cnt@[u] as int, ka, kb2, kc, recs_upto(sv, dlo, dhi, keys, bm, lo as int, i as int, cs, 0)(u)) by {
            assert(cs.take(0) =~= Seq::<int>::empty());
            let bu = lrecs(sv, dlo, dhi, bkeys(keys, bm, u), lo as int, i as int);
            assert(bu + Seq::<int>::empty() =~= bu);
        }
    }
    let mut q: usize = 0;
    while q < nc
        invariant
            lpk@ == crate::agent::tables::lpk(sv), lsk@ == crate::agent::tables::lsk(sv), lqt@ == crate::agent::tables::lqt(sv),
            nl as int == n_l(sv), lpk@.len() == n_l(sv), lsk@.len() == n_l(sv), lqt@.len() == n_l(sv), domains_ok(sv),
            kb_ok(*kb, keys), f == lrec(sv, dlo, dhi, keys),
            p == cpred(sv, dlo, dhi, *kb), cs == range_filter(i as int, e as int, p),
            lo <= i <= e <= nl, q <= nc, nc == cs.len(), nc <= e - i, 1 <= nb <= 64,
            sel_matches(cand@, nc as int, i as int, cs),
            forall|t: int| 0 <= t < cs.len() ==> i <= #[trigger] cs[t] < e && p(cs[t]),
            olen == out@.len(), out@.len() == old(out)@.len(), cnt@.len() == old(cnt)@.len(),
            ka == crate::agent::tables::lpk(sv), kb2 == crate::agent::tables::lsk(sv), kc == lq_c(sv),
            regions_ok(out@, cnt@, nb as int, cap as int, ka, kb2, kc, recs_upto(sv, dlo, dhi, keys, bm, lo as int, i as int, cs, q as int)),
        decreases nc - q,
    {
        let r = i + cand[q] as usize;
        let v = lpk[r];
        let ghost s1 = recs_upto(sv, dlo, dhi, keys, bm, lo as int, i as int, cs, q as int);
        let ghost s2 = recs_upto(sv, dlo, dhi, keys, bm, lo as int, i as int, cs, q as int + 1);
        let hit = v >= 0 && kb_exact(kb, v, Ghost(keys));
        proof {
            assert(r as int == cs[q as int]);
            assert(p(r as int));
            lemma_take_step(cs, q as int);
            if v < 0 { assert(!wbit(kb.bits@, v as int)); }
            assert(hit == f(r as int));
            lemma_bkeys(keys, bm, 0);
            assert forall|u: int| 0 <= u < nb implies #[trigger] s2(u)
                == if hit && bk(v, bm) == u { s1(u).push(r as int) } else { s1(u) } by {
                let fu = lrec(sv, dlo, dhi, bkeys(keys, bm, u));
                lemma_seq_filter_push(cs.take(q as int), r as int, fu);
                lemma_bkeys(keys, bm, u);
                assert(((v as int) as i64) == v);
                assert(fu(r as int) == (hit && bk(v, bm) == u));
                let bu = lrecs(sv, dlo, dhi, bkeys(keys, bm, u), lo as int, i as int);
                let sf = seq_filter(cs.take(q as int), fu);
                assert((bu + sf).push(r as int) =~= bu + sf.push(r as int));
            }
        }
        if hit {
            proof { assert(num15(lqt@[r as int])); }
            let ok = bucket_push(out, cnt, olen, nb, bm, cap, v, lsk[r], lqt[r] as i64, Ghost(ka), Ghost(kb2), Ghost(kc),
                Ghost(s1), Ghost(s2), Ghost(r as int));
            if !ok {
                return false;
            }
        } else {
            proof {
                assert forall|u: int| 0 <= u < nb implies #[trigger] cnt@[u] <= cap
                    && trip_at(out@, 3 * cap * u, cnt@[u] as int, ka, kb2, kc, s2(u)) by {
                    assert(s2(u) == s1(u));
                }
            }
        }
        q = q + 1;
    }
    proof {
        assert(cs.take(nc as int) =~= cs);
        assert forall|u: int| 0 <= u < nb implies #[trigger] cnt@[u] <= cap
            && trip_at(out@, 3 * cap * u, cnt@[u] as int, ka, kb2, kc, brecs(sv, dlo, dhi, keys, bm, lo as int, e as int)(u)) by {
            let fu = lrec(sv, dlo, dhi, bkeys(keys, bm, u));
            lemma_bkeys(keys, bm, u);
            lemma_filter_range_filter(i as int, e as int, p, fu);
            assert forall|l: int| i <= l < e implies #[trigger] and_pred(p, fu)(l) == fu(l) by {
                if fu(l) {
                    lemma_key_coarse(*kb, keys, crate::agent::tables::lpk(sv)[l] as int);
                }
            }
            lemma_range_filter_ext(i as int, e as int, and_pred(p, fu), fu);
            lemma_range_filter_concat(lo as int, i as int, e as int, fu);
            assert(recs_upto(sv, dlo, dhi, keys, bm, lo as int, i as int, cs, nc as int)(u)
                == brecs(sv, dlo, dhi, keys, bm, lo as int, e as int)(u));
        }
    }
    true
}

/// The lineitem columns and the window a lineitem range is scanned with.
pub open spec fn line_cols_ok(lpk: &[i64], lsk: &[i64], lsd: &[i32], lqt: &[i128], nl: usize, sv: StoresView) -> bool {
    &&& lpk@ == crate::agent::tables::lpk(sv) && lsk@ == crate::agent::tables::lsk(sv)
    &&& lsd@ == crate::agent::tables::lsd(sv) && lqt@ == crate::agent::tables::lqt(sv)
    &&& nl as int == n_l(sv) && lpk@.len() == n_l(sv) && lsk@.len() == n_l(sv) && lsd@.len() == n_l(sv) && lqt@.len() == n_l(sv)
    &&& domains_ok(sv)
}

/// The records of the lineitem rows `lo..hi` into the bucket regions of `out` (`no_unwind`), chunk by chunk
/// (`chunk_cands`, then `chunk_recs`), the bucket sizes in `cnt`; false when a bucket outgrows `cap` triples.
pub fn line_range(lpk: &[i64], lsk: &[i64], lsd: &[i32], lqt: &[i128], nl: usize, kb: &KeyBits, dlo: i32, dhi: i32,
    lo: usize, hi: usize, nb: usize, bm: u64, cap: usize, out: &mut Vec<i64>, cnt: &mut Vec<usize>, cand: &mut Vec<u32>,
    Ghost(sv): Ghost<StoresView>, Ghost(keys): Ghost<Seq<int>>) -> (fit: bool)
    requires
        line_cols_ok(lpk, lsk, lsd, lqt, nl, sv), kb_ok(*kb, keys), lo <= hi <= nl,
        1 <= nb <= 64, old(out)@.len() >= 3 * cap * nb, old(cnt)@.len() >= nb, old(cand)@.len() >= CH,
    ensures
        final(out)@.len() == old(out)@.len(), final(cnt)@.len() == old(cnt)@.len(), final(cand)@.len() == old(cand)@.len(),
        fit ==> brec_ok(final(out)@, final(cnt)@, cap as int, nb as int, sv, dlo as int, dhi as int, keys, bm, lo as int, hi as int),
    no_unwind
{
    let olen = out.len();
    let ghost (ka, kb2, kc) = (crate::agent::tables::lpk(sv), crate::agent::tables::lsk(sv), lq_c(sv));
    bucket_init(cnt, nb, Ghost(out@), cap, Ghost(ka), Ghost(kb2), Ghost(kc), Ghost(brecs(sv, dlo as int, dhi as int, keys, bm, lo as int, lo as int)));
    let mut i = lo;
    while i < hi
        invariant
            line_cols_ok(lpk, lsk, lsd, lqt, nl, sv), kb_ok(*kb, keys), lo <= i <= hi <= nl, 1 <= nb <= 64,
            olen == out@.len(), out@.len() == old(out)@.len(), cnt@.len() == old(cnt)@.len(),
            cand@.len() == old(cand)@.len(), cand@.len() >= CH,
            ka == crate::agent::tables::lpk(sv), kb2 == crate::agent::tables::lsk(sv), kc == lq_c(sv),
            regions_ok(out@, cnt@, nb as int, cap as int, ka, kb2, kc, brecs(sv, dlo as int, dhi as int, keys, bm, lo as int, i as int)),
        decreases hi - i,
    {
        let e = if hi - i >= CH { i + CH } else { hi };
        let nc = chunk_cands(lsd, lpk, nl, kb, i, e, dlo, dhi, cand, Ghost(sv));
        let ok = chunk_recs(lpk, lsk, lqt, nl, kb, cand, nc, i, e, out, cnt, olen, nb, bm, cap, lo,
            Ghost(sv), Ghost(keys), Ghost(dlo as int), Ghost(dhi as int));
        if !ok {
            return false;
        }
        i = e;
    }
    proof {
        assert forall|u: int| 0 <= u < nb implies #[trigger] cnt@[u] <= cap
            && trip_at(out@, 3 * cap * u, cnt@[u] as int, ka, kb2, kc,
                lrecs(sv, dlo as int, dhi as int, bkeys(keys, bm, u), lo as int, hi as int)) by {}
    }
    true
}

} // verus!
