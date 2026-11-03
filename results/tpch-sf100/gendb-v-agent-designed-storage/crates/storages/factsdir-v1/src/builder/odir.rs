//! The o_orderkey directory of the inherited orders rows: one pass finds the key range `[kmin, kmax]`, a second
//! writes each stored row `p` into the entry of its key (`odir_build`). Entries start as `ODIR_NONE`; a row only
//! ever writes its own position into its own key's entry, so every entry stays `ODIR_NONE` or names a row of its key
//! (sound), and every written key's entry stays named (complete). A key span wider than `8 n + SPAN_SLACK`, more
//! than U32 entries, or `n >= ODIR_NONE` rows give no directory.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::work::filled;
use crate::stores::factsdir::interface::{ORDERS_FIRST, OR_ORDERKEY_CODES, OR_ORDERKEY_BASE};
use crate::stores::factsdir::interface::common::colfmt::{u32s, i64s};
use crate::stores::factsdir::interface::dirs::*;
use super::pdir::{lemma_div_lt, SPAN_SLACK};

verus! {

/// What the build uses of the source parts `fp`: the o_orderkey column over `n` rows.
pub open spec fn okey_src_ok(fp: Seq<PartView>, n: int) -> bool {
    let bs = or_bs(fp);
    &&& fp.len() > ORDERS_FIRST + OR_ORDERKEY_BASE
    &&& bs >= 1
    &&& u32s(fp[(ORDERS_FIRST + OR_ORDERKEY_CODES) as int]).len() == n
    &&& i64s(fp[(ORDERS_FIRST + OR_ORDERKEY_BASE) as int]).len() * bs >= n
}

/// The directory `(kmin, rows)` over the `n` stored orders rows: sound and complete.
pub open spec fn odir_spec(fp: Seq<PartView>, n: int, kmin: int, rows: Seq<u32>) -> bool {
    &&& n < ODIR_NONE
    &&& forall|e: int| 0 <= e < rows.len() ==> #[trigger] odir_entry_ok(fp, n, kmin, rows, e)
    &&& forall|p: int| 0 <= p < n ==> #[trigger] odir_found(fp, kmin, rows, p)
}

/// Entry `e` is `ODIR_NONE` or a stored row (of `n`) with key `kmin + e`.
pub open spec fn odir_entry_ok(fp: Seq<PartView>, n: int, kmin: int, rows: Seq<u32>, e: int) -> bool {
    rows[e] == ODIR_NONE || (rows[e] < n && or_key(fp, rows[e] as int) == kmin + e)
}

/// The key of stored row `p` has an entry that is not `ODIR_NONE`.
pub open spec fn odir_found(fp: Seq<PartView>, kmin: int, rows: Seq<u32>, p: int) -> bool {
    let e = or_key(fp, p) - kmin;
    &&& 0 <= e < rows.len()
    &&& rows[e] != ODIR_NONE
}

/// The key of stored row `p` (in `i128`).
fn okey_exec(oc: &[u32], ob: &[i64], bs: usize, n: usize, p: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (k: i128)
    requires
        okey_src_ok(fp, n as int),
        bs as int == or_bs(fp),
        oc@ == u32s(fp[(ORDERS_FIRST + OR_ORDERKEY_CODES) as int]),
        ob@ == i64s(fp[(ORDERS_FIRST + OR_ORDERKEY_BASE) as int]),
        p < n,
    ensures
        k as int == or_key(fp, p as int),
        i64::MIN <= k <= i64::MAX + u32::MAX,
{
    proof {
        lemma_div_lt(p as int, bs as int, ob@.len() as int);
    }
    ob[p / bs] as i128 + oc[p] as i128
}

/// The o_orderkey directory: `Some((kmin, rows))` with `odir_spec`, or `None`.
pub fn odir_build(oc: &[u32], ob: &[i64], bs: usize, n: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (r: Option<(i64, Vec<u32>)>)
    requires
        okey_src_ok(fp, n as int),
        bs as int == or_bs(fp),
        oc@ == u32s(fp[(ORDERS_FIRST + OR_ORDERKEY_CODES) as int]),
        ob@ == i64s(fp[(ORDERS_FIRST + OR_ORDERKEY_BASE) as int]),
    ensures
        r matches Some((kmin, rows)) ==> odir_spec(fp, n as int, kmin as int, rows@),
{
    if n == 0 || n >= ODIR_NONE as usize {
        return None;
    }
    // The key range.
    let mut kmin = okey_exec(oc, ob, bs, n, 0, Ghost(fp));
    let mut kmax = kmin;
    let mut p: usize = 1;
    while p < n
        invariant
            okey_src_ok(fp, n as int),
            bs as int == or_bs(fp),
            oc@ == u32s(fp[(ORDERS_FIRST + OR_ORDERKEY_CODES) as int]),
            ob@ == i64s(fp[(ORDERS_FIRST + OR_ORDERKEY_BASE) as int]),
            1 <= p <= n,
            kmin <= kmax,
            i64::MIN <= kmin, kmax <= i64::MAX + u32::MAX,
            forall|q: int| 0 <= q < p ==> kmin <= #[trigger] or_key(fp, q) <= kmax,
        decreases n - p,
    {
        let k = okey_exec(oc, ob, bs, n, p, Ghost(fp));
        if k < kmin {
            kmin = k;
        }
        if k > kmax {
            kmax = k;
        }
        p = p + 1;
    }
    if kmin < i64::MIN as i128 || kmin > i64::MAX as i128 {
        return None;
    }
    let span: i128 = kmax - kmin + 1;
    if span > 8 * (n as i128) + SPAN_SLACK as i128 || span > 0xffff_fffe {
        return None;
    }
    let nk = span as usize;
    let mut rows: Vec<u32> = filled(nk, ODIR_NONE);
    let mut p: usize = 0;
    while p < n
        invariant
            okey_src_ok(fp, n as int),
            bs as int == or_bs(fp),
            oc@ == u32s(fp[(ORDERS_FIRST + OR_ORDERKEY_CODES) as int]),
            ob@ == i64s(fp[(ORDERS_FIRST + OR_ORDERKEY_BASE) as int]),
            n < ODIR_NONE,
            p <= n,
            rows@.len() == nk,
            nk as int == kmax - kmin + 1,
            forall|q: int| 0 <= q < n ==> kmin <= #[trigger] or_key(fp, q) <= kmax,
            forall|e: int| 0 <= e < nk ==> #[trigger] odir_entry_ok(fp, n as int, kmin as int, rows@, e),
            forall|q: int| 0 <= q < p ==> #[trigger] odir_found(fp, kmin as int, rows@, q),
        decreases n - p,
    {
        let k = okey_exec(oc, ob, bs, n, p, Ghost(fp));
        let e = (k - kmin) as usize;
        let ghost old_rows = rows@;
        rows[e] = p as u32;
        proof {
            assert(rows@ == old_rows.update(e as int, p as u32));
            assert forall|f: int| 0 <= f < nk implies #[trigger] odir_entry_ok(fp, n as int, kmin as int, rows@, f) by {
                if f != e as int {
                    assert(odir_entry_ok(fp, n as int, kmin as int, old_rows, f));
                }
            }
            assert forall|q: int| 0 <= q < p + 1 implies #[trigger] odir_found(fp, kmin as int, rows@, q) by {
                if q < p {
                    assert(odir_found(fp, kmin as int, old_rows, q));
                }
            }
        }
        p = p + 1;
    }
    Some((kmin as i64, rows))
}

} // verus!
