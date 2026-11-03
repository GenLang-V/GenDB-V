//! The partsupp pass: the partsupp rows whose part key is a matching part's (`qrows`), each written as the triple
//! (part key, supplier key, availability) into the region of its part-key bucket (`bucket`) of a preallocated output
//! (`ps_range`).
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::keys::*;
use crate::agent::common::selection::*;
use crate::agent::common::buckets::*;
use crate::agent::bucket::*;

verus! {

/// Partsupp row `q`'s part matches.
pub open spec fn inp(sv: StoresView, ps: Seq<Literal>) -> spec_fn(int) -> bool { |q: int| in_part(sv, ps, pspk(sv)[q] as int) }

/// The partsupp rows of `[lo, hi)` whose part matches, ascending.
pub open spec fn qrows(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> Seq<int> { range_filter(lo, hi, inp(sv, ps)) }

/// `out[0 .. 3 n]` holds the key pairs and availabilities of the partsupp rows `qs`, one triple per row.
pub open spec fn ps_out_ok(out: Seq<i64>, n: int, sv: StoresView, qs: Seq<int>) -> bool {
    &&& n == qs.len() && 3 * n <= out.len()
    &&& forall|t: int| 0 <= t < n ==> out[3 * t] == pspk(sv)[#[trigger] qs[t]] && out[3 * t + 1] == pssk(sv)[qs[t]]
            && out[3 * t + 2] == psaq(sv)[qs[t]]
}

/// The key set of the part pass decides `in_part`.
pub open spec fn keys_decide(keys: Seq<int>, sv: StoresView, ps: Seq<Literal>) -> bool {
    forall|v: int| #[trigger] keys.contains(v) == in_part(sv, ps, v)
}

/// The partsupp columns a partsupp range is scanned with.
pub open spec fn ps_cols_ok(pspk: &[i64], pssk: &[i64], psaq: &[i64], nps: usize, sv: StoresView) -> bool {
    &&& pspk@ == crate::agent::tables::pspk(sv) && pssk@ == crate::agent::tables::pssk(sv) && psaq@ == crate::agent::tables::psaq(sv)
    &&& nps as int == n_ps(sv) && pssk@.len() == n_ps(sv) && psaq@.len() == n_ps(sv)
}

/// The partsupp rows `lo..hi` whose part matches into the bucket regions of `out` (`no_unwind`), the bucket sizes in
/// `cnt`; false when a bucket outgrows `cap` triples.
pub fn ps_range(pspk: &[i64], pssk: &[i64], psaq: &[i64], nps: usize, kb: &KeyBits, lo: usize, hi: usize,
    nb: usize, bm: u64, cap: usize, out: &mut Vec<i64>, cnt: &mut Vec<usize>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(keys): Ghost<Seq<int>>) -> (fit: bool)
    requires
        ps_cols_ok(pspk, pssk, psaq, nps, sv), kb_ok(*kb, keys), keys_decide(keys, sv, ps),
        lo <= hi <= nps, 1 <= nb <= 64, old(out)@.len() >= 3 * cap * nb, old(cnt)@.len() >= nb,
    ensures
        final(out)@.len() == old(out)@.len(), final(cnt)@.len() == old(cnt)@.len(),
        fit ==> bps_ok(final(out)@, final(cnt)@, cap as int, nb as int, sv, ps, bm, lo as int, hi as int),
    no_unwind
{
    let olen = out.len();
    let ghost (ka, kb2, kc) = (crate::agent::tables::pspk(sv), crate::agent::tables::pssk(sv), ps_c(sv));
    bucket_init(cnt, nb, Ghost(out@), cap, Ghost(ka), Ghost(kb2), Ghost(kc),
        Ghost(|u: int| bqrows(sv, ps, bm, u, lo as int, lo as int)));
    let mut q = lo;
    while q < hi
        invariant
            olen == out@.len(), out@.len() == old(out)@.len(), cnt@.len() == old(cnt)@.len(),
            ps_cols_ok(pspk, pssk, psaq, nps, sv), kb_ok(*kb, keys), keys_decide(keys, sv, ps),
            lo <= q <= hi <= nps, 1 <= nb <= 64,
            ka == crate::agent::tables::pspk(sv), kb2 == crate::agent::tables::pssk(sv), kc == ps_c(sv),
            regions_ok(out@, cnt@, nb as int, cap as int, ka, kb2, kc, |u: int| bqrows(sv, ps, bm, u, lo as int, q as int)),
        decreases hi - q,
    {
        let v = pspk[q];
        let hit = if v < 0 { false } else { kb_exact(kb, v, Ghost(keys)) };
        let ghost s1 = |u: int| bqrows(sv, ps, bm, u, lo as int, q as int);
        let ghost s2 = |u: int| bqrows(sv, ps, bm, u, lo as int, q as int + 1);
        proof {
            if v < 0 { assert(!crate::agent::common::bitset::wbit(kb.bits@, v as int)); }
            assert(hit == inp(sv, ps)(q as int));
            assert forall|u: int| 0 <= u < nb implies #[trigger] s2(u)
                == if hit && bk(v, bm) == u { s1(u).push(q as int) } else { s1(u) } by {
                let p = and_pred(inp(sv, ps), kbucket(ka, bm, u));
                assert(p(q as int) == (hit && bk(v, bm) == u));
            }
        }
        if hit {
            let ok = bucket_push(out, cnt, olen, nb, bm, cap, v, pssk[q], psaq[q], Ghost(ka), Ghost(kb2), Ghost(kc),
                Ghost(s1), Ghost(s2), Ghost(q as int));
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
        assert forall|u: int| 0 <= u < nb implies #[trigger] cnt@[u] <= cap
            && trip_at(out@, 3 * cap * u, cnt@[u] as int, ka, kb2, kc, bqrows(sv, ps, bm, u, lo as int, hi as int)) by {}
    }
    true
}

} // verus!
