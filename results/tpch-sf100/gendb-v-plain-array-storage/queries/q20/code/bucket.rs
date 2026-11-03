//! The scan outputs by part-key bucket (`common::buckets`): bucket `u` holds the part keys `v` with `bk(v, bm) == u`.
//! A scan task writes its matching partsupp triples (`pspass::ps_range`) and its lineitem records
//! (`linepass::line_range`) into `nb` regions of `cap` triples each; a decide task then reads one bucket of every scan
//! task.
//!
//! Region `u` of the partsupp triples of rows `[lo, hi)` is `bqrows(u, lo, hi)`: the rows of a matching part whose
//! key lies in bucket `u` (`bps_ok`). Region `u` of the lineitem records of `[lo, hi)` are the records for the key set
//! `bkeys(keys, bm, u)`, the matching keys of bucket `u` (`brec_ok`), so the per-slot totals of `agg` apply to one
//! bucket with that key set unchanged.
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::agent::tables::*;
use crate::agent::pspass::*;
use crate::agent::linepass::*;
use crate::agent::common::selection::*;
use crate::agent::common::buckets::*;

verus! {

/// Key `v` lies in bucket `u`.
pub open spec fn in_bk(bm: u64, u: int) -> spec_fn(int) -> bool { |v: int| bk(v as i64, bm) == u }

/// The keys of `keys` in bucket `u`.
pub open spec fn bkeys(keys: Seq<int>, bm: u64, u: int) -> Seq<int> { keys.filter(in_bk(bm, u)) }

/// A key is in bucket `u`'s key set exactly when it is a key in bucket `u`.
pub proof fn lemma_bkeys(keys: Seq<int>, bm: u64, u: int)
    ensures forall|v: int| #[trigger] bkeys(keys, bm, u).contains(v) == (keys.contains(v) && bk(v as i64, bm) == u),
{
    let p = in_bk(bm, u);
    assert forall|v: int| #[trigger] bkeys(keys, bm, u).contains(v) == (keys.contains(v) && bk(v as i64, bm) == u) by {
        let f = keys.filter(p);
        if f.contains(v) {
            let i = choose|i: int| 0 <= i < f.len() && f[i] == v;
            keys.lemma_filter_pred(p, i);
            keys.lemma_filter_contains_rev(p, v);
        }
        if keys.contains(v) && bk(v as i64, bm) == u {
            let i = choose|i: int| 0 <= i < keys.len() && keys[i] == v;
            keys.lemma_filter_contains(p, i);
        }
    }
}

/// The availability of partsupp row `q` and the quantity coefficient of lineitem row `l`, as the third value of a
/// triple.
pub open spec fn ps_c(sv: StoresView) -> spec_fn(int) -> int { |q: int| psaq(sv)[q] as int }
pub open spec fn lq_c(sv: StoresView) -> spec_fn(int) -> int { |l: int| lqt(sv)[l] as int }

/// The partsupp rows of `[lo, hi)` of a matching part whose key lies in bucket `u`, ascending.
pub open spec fn bqrows(sv: StoresView, ps: Seq<Literal>, bm: u64, u: int, lo: int, hi: int) -> Seq<int> {
    range_filter(lo, hi, and_pred(inp(sv, ps), kbucket(pspk(sv), bm, u)))
}

/// Region `u < nb` of `buf` holds the triples of `bqrows(u, lo, hi)`, `cnt[u] <= cap` of them.
pub open spec fn bps_ok(buf: Seq<i64>, cnt: Seq<usize>, cap: int, nb: int, sv: StoresView, ps: Seq<Literal>, bm: u64,
    lo: int, hi: int) -> bool {
    &&& cnt.len() >= nb && 3 * cap * nb <= buf.len()
    &&& forall|u: int| 0 <= u < nb ==> #[trigger] cnt[u] <= cap
            && trip_at(buf, 3 * cap * u, cnt[u] as int, pspk(sv), pssk(sv), ps_c(sv), bqrows(sv, ps, bm, u, lo, hi))
}

/// Region `u < nb` of `buf` holds the records of `[lo, hi)` for the keys of bucket `u`, `cnt[u] <= cap` of them.
pub open spec fn brec_ok(buf: Seq<i64>, cnt: Seq<usize>, cap: int, nb: int, sv: StoresView, dlo: int, dhi: int,
    keys: Seq<int>, bm: u64, lo: int, hi: int) -> bool {
    &&& cnt.len() >= nb && 3 * cap * nb <= buf.len()
    &&& forall|u: int| 0 <= u < nb ==> #[trigger] cnt[u] <= cap
            && trip_at(buf, 3 * cap * u, cnt[u] as int, lpk(sv), lsk(sv), lq_c(sv), lrecs(sv, dlo, dhi, bkeys(keys, bm, u), lo, hi))
}

} // verus!
