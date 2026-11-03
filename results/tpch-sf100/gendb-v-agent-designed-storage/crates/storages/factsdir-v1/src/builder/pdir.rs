//! The l_partkey directory over the inherited l_partkey key index (kind 2: index positions list the stored lineitem
//! rows in nondecreasing key order). One scan along the index positions `p` reads each key `li_key(pdir_irow(p))`
//! and appends, for every entry not yet started, the position `p` (`dir_scan`): entry `e` starts at the first
//! position whose key is at least `kmin + e`; the last entry ends at `n`. A key span wider than `2 n + SPAN_SLACK`
//! or than U32 offsets allow gives no directory.
//!
//! Proof: the scan's invariant (`scan_inv`) places every scanned position in the entry of its key (adapted from the
//! admitted builder of storage `li_partdir`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::stores::factsdir::interface::{LI_LAYOUT, LI_PARTKEY_CODES, LI_PARTKEY_BASE, LI_KEYIDX_CODES, LI_KEYIDX_BASE};
use crate::stores::factsdir::interface::common::colfmt::{u32s, u64s, i64s};
use crate::stores::factsdir::interface::dirs::*;

verus! {

/// Largest key span (number of directory entries) the builder accepts beyond `2 n`.
pub const SPAN_SLACK: usize = 1_000_000;

/// `j < m * b` implies `j / b < m`.
pub proof fn lemma_div_lt(j: int, b: int, m: int)
    requires
        0 <= j < m * b,
        b >= 1,
    ensures
        0 <= j / b < m,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, b);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, b);
    assert(b * (j / b) == (j / b) * b) by (nonlinear_arith);
    assert(j / b < m) by (nonlinear_arith) requires (j / b) * b <= j, j < m * b, b >= 1;
}

/// What the scan uses of the source parts `fp`: the key and index columns over `n` rows, index positions naming
/// stored rows, keys nondecreasing along the index.
pub open spec fn idx_src_ok(fp: Seq<PartView>, n: int) -> bool {
    let bs = li_bs(fp);
    &&& fp.len() > LI_KEYIDX_BASE
    &&& bs >= 1
    &&& u32s(fp[LI_PARTKEY_CODES as int]).len() == n && i64s(fp[LI_PARTKEY_BASE as int]).len() * bs >= n
    &&& u32s(fp[LI_KEYIDX_CODES as int]).len() == n && u64s(fp[LI_KEYIDX_BASE as int]).len() * bs >= n
    &&& forall|p: int| 0 <= p < n ==> 0 <= #[trigger] pdir_irow(fp, p) < n
    &&& forall|p: int| 0 <= p < n - 1 ==> #[trigger] idx_sorted_at(fp, p)
}

/// Keys do not decrease from index position `p` to `p + 1`.
pub open spec fn idx_sorted_at(fp: Seq<PartView>, p: int) -> bool {
    li_key(fp, pdir_irow(fp, p)) <= li_key(fp, pdir_irow(fp, p + 1))
}

/// Keys are nondecreasing along the index between any two positions.
proof fn lemma_sorted_le(fp: Seq<PartView>, n: int, a: int, b: int)
    requires
        idx_src_ok(fp, n),
        0 <= a <= b < n,
    ensures
        li_key(fp, pdir_irow(fp, a)) <= li_key(fp, pdir_irow(fp, b)),
    decreases b - a,
{
    if a < b {
        lemma_sorted_le(fp, n, a, b - 1);
        assert(idx_sorted_at(fp, b - 1));
    }
}

/// The slices of the scan are the source's index and key parts.
pub open spec fn slices_ok(fp: Seq<PartView>, n: int, bs: int, ic: Seq<u32>, ib: Seq<u64>, kc: Seq<u32>, kb: Seq<i64>) -> bool {
    &&& idx_src_ok(fp, n)
    &&& bs == li_bs(fp)
    &&& ic == u32s(fp[LI_KEYIDX_CODES as int])
    &&& ib == u64s(fp[LI_KEYIDX_BASE as int])
    &&& kc == u32s(fp[LI_PARTKEY_CODES as int])
    &&& kb == i64s(fp[LI_PARTKEY_BASE as int])
}

/// The stored row at index position `p`.
fn irow_exec(ic: &[u32], ib: &[u64], kc: &[u32], kb: &[i64], bs: usize, n: usize, p: usize, Ghost(fp): Ghost<Seq<PartView>>)
    -> (s: usize)
    requires
        slices_ok(fp, n as int, bs as int, ic@, ib@, kc@, kb@),
        p < n,
    ensures
        s as int == pdir_irow(fp, p as int),
        s < n,
{
    proof {
        lemma_div_lt(p as int, bs as int, ib@.len() as int);
        assert(0 <= pdir_irow(fp, p as int) < n);
    }
    (ib[p / bs] as u128 + ic[p] as u128) as usize
}

/// The key of stored row `s` (in `i128`: no bound on the keys is needed).
fn key_exec(ic: &[u32], ib: &[u64], kc: &[u32], kb: &[i64], bs: usize, n: usize, s: usize, Ghost(fp): Ghost<Seq<PartView>>)
    -> (k: i128)
    requires
        slices_ok(fp, n as int, bs as int, ic@, ib@, kc@, kb@),
        s < n,
    ensures
        k as int == li_key(fp, s as int),
{
    proof {
        lemma_div_lt(s as int, bs as int, kb@.len() as int);
    }
    kb[s / bs] as i128 + kc[s] as i128
}

/// A directory over the `n` index positions (`kmin`, offsets `offs`): nondecreasing offsets from 0 to `n`, every
/// position inside the entry of its key.
pub open spec fn dir_spec(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>) -> bool {
    &&& offs.len() >= 1
    &&& offs[0] == 0
    &&& offs[offs.len() - 1] == n
    &&& forall|e: int| 0 <= e < offs.len() - 1 ==> #[trigger] offs[e] <= offs[e + 1]
    &&& forall|p: int| 0 <= p < n ==> {
        let e = #[trigger] li_key(fp, pdir_irow(fp, p)) - kmin;
        &&& 0 <= e < offs.len() - 1
        &&& offs[e] <= p < offs[e + 1]
    }
}

/// The scan's invariant after positions `0 .. p` with `cur` entries started.
pub open spec fn scan_inv(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, p: int, cur: int) -> bool {
    &&& offs.len() == cur
    &&& cur >= 1 ==> offs[0] == 0
    &&& forall|e: int| 0 <= e < cur ==> #[trigger] offs[e] <= p
    &&& forall|e: int| 0 <= e < cur - 1 ==> #[trigger] offs[e] <= offs[e + 1]
    &&& forall|q: int| 0 <= q < p ==> {
        let e = #[trigger] li_key(fp, pdir_irow(fp, q)) - kmin;
        &&& 0 <= e < cur
        &&& offs[e] <= q
        &&& e + 1 < cur ==> q < offs[e + 1]
    }
}

/// The directory of the key index: `Some((kmin, offs))` with `dir_spec`, or `None` when the key span is too wide.
pub fn dir_scan(ic: &[u32], ib: &[u64], kc: &[u32], kb: &[i64], bs: usize, n: usize, Ghost(fp): Ghost<Seq<PartView>>)
    -> (r: Option<(i64, Vec<u32>)>)
    requires
        slices_ok(fp, n as int, bs as int, ic@, ib@, kc@, kb@),
        1 <= n <= u32::MAX,
    ensures
        r matches Some((kmin, offs)) ==> dir_spec(fp, n as int, kmin as int, offs@),
{
    let ghost ni = n as int;
    let s0 = irow_exec(ic, ib, kc, kb, bs, n, 0, Ghost(fp));
    let kmin_w = key_exec(ic, ib, kc, kb, bs, n, s0, Ghost(fp));
    let sl = irow_exec(ic, ib, kc, kb, bs, n, n - 1, Ghost(fp));
    let kmax = key_exec(ic, ib, kc, kb, bs, n, sl, Ghost(fp));
    proof {
        lemma_sorted_le(fp, ni, 0, ni - 1);
    }
    if kmin_w < i64::MIN as i128 || kmin_w > i64::MAX as i128 {
        return None;
    }
    let kmin = kmin_w as i64;
    let span: i128 = kmax - kmin_w + 1;
    if span > 2 * (n as i128) + SPAN_SLACK as i128 || span > 0xffff_fffe {
        return None;
    }
    let nk = span as usize;
    let mut offs: Vec<u32> = Vec::new();
    let mut cur: usize = 0;
    let mut p: usize = 0;
    while p < n
        invariant
            slices_ok(fp, ni, bs as int, ic@, ib@, kc@, kb@),
            ni == n as int,
            1 <= n <= u32::MAX,
            kmin as int == li_key(fp, pdir_irow(fp, 0)),
            nk as int == li_key(fp, pdir_irow(fp, ni - 1)) - kmin + 1,
            p <= n,
            cur <= nk,
            p == 0 ==> cur == 0,
            p > 0 ==> cur as int == li_key(fp, pdir_irow(fp, p - 1)) - kmin + 1,
            scan_inv(fp, ni, kmin as int, offs@, p as int, cur as int),
        decreases n - p,
    {
        let s = irow_exec(ic, ib, kc, kb, bs, n, p, Ghost(fp));
        let k = key_exec(ic, ib, kc, kb, bs, n, s, Ghost(fp));
        proof {
            lemma_sorted_le(fp, ni, 0, p as int);
            lemma_sorted_le(fp, ni, p as int, ni - 1);
            if p > 0 {
                lemma_sorted_le(fp, ni, p - 1, p as int);
                lemma_sorted_le(fp, ni, 0, p - 1);
            }
        }
        let e = (k - kmin as i128) as usize;
        while cur <= e
            invariant
                slices_ok(fp, ni, bs as int, ic@, ib@, kc@, kb@),
                ni == n as int,
                1 <= n <= u32::MAX,
                p < n,
                e < nk,
                e as int == li_key(fp, pdir_irow(fp, p as int)) - kmin,
                cur <= e + 1,
                scan_inv(fp, ni, kmin as int, offs@, p as int, cur as int),
                p == 0 ==> (cur == 0 || offs@[0] == 0),
                cur == 0 ==> p == 0,
            decreases e + 1 - cur,
        {
            proof {
                let ghost o = offs@;
                lemma_push_entry_any(fp, ni, kmin as int, o, p as int, cur as int);
            }
            offs.push(p as u32);
            cur = cur + 1;
        }
        proof {
            let ghost o = offs@;
            lemma_step(fp, ni, kmin as int, o, p as int, cur as int);
        }
        p = p + 1;
    }
    while cur <= nk
        invariant
            ni == n as int,
            1 <= n <= u32::MAX,
            nk <= cur <= nk + 1,
            nk <= 0xffff_fffe,
            nk >= 1,
            cur == nk + 1 ==> offs@[nk as int] == n,
            scan_inv(fp, ni, kmin as int, offs@, ni, cur as int),
        decreases nk + 1 - cur,
    {
        proof {
            let ghost o = offs@;
            lemma_push_entry_any(fp, ni, kmin as int, o, ni, cur as int);
        }
        offs.push(n as u32);
        cur = cur + 1;
    }
    proof {
        assert(offs@.len() == nk + 1);
        assert(offs@[nk as int] == ni);
        assert forall|q: int| 0 <= q < ni implies {
            let e = #[trigger] li_key(fp, pdir_irow(fp, q)) - kmin;
            &&& 0 <= e < offs@.len() - 1
            &&& offs@[e] <= q < offs@[e + 1]
        } by {
            let e = li_key(fp, pdir_irow(fp, q)) - kmin;
            lemma_sorted_le(fp, ni, q, ni - 1);
            assert(scan_inv(fp, ni, kmin as int, offs@, ni, cur as int));
            assert(e + 1 < cur);
        }
    }
    Some((kmin, offs))
}

/// One more entry starting at `p` keeps the invariant (inner loop step).
proof fn lemma_push_entry_any(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, p: int, cur: int)
    requires
        scan_inv(fp, n, kmin, offs, p, cur),
        0 <= p <= u32::MAX,
        cur == 0 ==> p == 0,
    ensures
        scan_inv(fp, n, kmin, offs.push(p as u32), p, cur + 1),
{
    let o2 = offs.push(p as u32);
    assert forall|e: int| 0 <= e < cur + 1 implies #[trigger] o2[e] <= p by {
        if e < cur {
            assert(o2[e] == offs[e]);
        }
    }
    assert forall|e: int| 0 <= e < cur implies #[trigger] o2[e] <= o2[e + 1] by {
        if e < cur - 1 {
            assert(offs[e] <= offs[e + 1]);
        } else {
            assert(offs[e] <= p);
        }
    }
    assert forall|q: int| 0 <= q < p implies {
        let e = #[trigger] li_key(fp, pdir_irow(fp, q)) - kmin;
        &&& 0 <= e < cur + 1
        &&& o2[e] <= q
        &&& e + 1 < cur + 1 ==> q < o2[e + 1]
    } by {
        let e = li_key(fp, pdir_irow(fp, q)) - kmin;
        assert(0 <= e < cur && offs[e] <= q);
        assert(o2[e] == offs[e]);
        if e + 1 < cur {
            assert(o2[e + 1] == offs[e + 1]);
        } else {
            assert(o2[e + 1] == p);
            assert(q < p);
        }
    }
    if cur >= 1 {
        assert(o2[0] == offs[0]);
    }
}

/// After the entries up to the key of position `p` are started, position `p` is placed.
proof fn lemma_step(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, p: int, cur: int)
    requires
        scan_inv(fp, n, kmin, offs, p, cur),
        0 <= p < n,
        cur == li_key(fp, pdir_irow(fp, p)) - kmin + 1,
        li_key(fp, pdir_irow(fp, p)) - kmin >= 0,
    ensures
        scan_inv(fp, n, kmin, offs, p + 1, cur),
{
    assert forall|e: int| 0 <= e < cur implies #[trigger] offs[e] <= p + 1 by {
        assert(offs[e] <= p);
    }
    assert forall|q: int| 0 <= q < p + 1 implies {
        let e = #[trigger] li_key(fp, pdir_irow(fp, q)) - kmin;
        &&& 0 <= e < cur
        &&& offs[e] <= q
        &&& e + 1 < cur ==> q < offs[e + 1]
    } by {
        if q == p {
            let e = li_key(fp, pdir_irow(fp, q)) - kmin;
            assert(e == cur - 1);
            assert(offs[e] <= p);
        }
    }
}

} // verus!
