//! The directory scan over facts' l_partkey key index (kind 2: a bijection of the stored rows in nondecreasing key
//! order): one pass along the index positions `p` reads each key `key_at(kirow(p))` and appends, for every key entry
//! not yet started, the position `p` (`dir_scan`); entry `e` starts at the first position whose key is at least
//! `kmin + e`; the entries after the last key end at `n`. Adapted from the admitted builder of `li_partdir`.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::stores::li_pkqty::interface::*;
use super::src::*;

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

/// Keys are nondecreasing along the index between any two positions.
pub proof fn lemma_sorted_le(fp: Seq<PartView>, n: int, a: int, b: int)
    requires
        index_ok(fp, n),
        0 <= a <= b < n,
    ensures
        key_at(fp, kirow(fp, a)) <= key_at(fp, kirow(fp, b)),
    decreases b - a,
{
    if a < b {
        lemma_sorted_le(fp, n, a, b - 1);
        assert(ksorted_at(fp, b - 1));
    }
}

/// The slices of the scan are the source's index and key parts.
pub open spec fn slices_ok(fp: Seq<PartView>, n: int, bs: int, ic: Seq<u32>, ib: Seq<u64>, kc: Seq<u32>, kb: Seq<i64>) -> bool {
    &&& base_ok(fp, n)
    &&& index_ok(fp, n)
    &&& bs == bsize(fp)
    &&& ic == u32s(fp[LI_KEYIDX_CODES as int])
    &&& ib == u64s(fp[LI_KEYIDX_BASE as int])
    &&& kc == u32s(fp[LI_PARTKEY_CODES as int])
    &&& kb == i64s(fp[LI_PARTKEY_BASE as int])
}

/// The stored row at index position `p`.
pub fn irow_exec(ic: &[u32], ib: &[u64], bs: usize, n: usize, p: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (s: usize)
    requires
        slices_ok(fp, n as int, bs as int, ic@, ib@, u32s(fp[LI_PARTKEY_CODES as int]), i64s(fp[LI_PARTKEY_BASE as int])),
        p < n,
    ensures
        s as int == kirow(fp, p as int),
        s < n,
{
    proof {
        lemma_div_lt(p as int, bs as int, ib@.len() as int);
        assert(0 <= kirow(fp, p as int) < n);
    }
    (ib[p / bs] + ic[p] as u64) as usize
}

/// The key of stored row `s`.
pub fn key_exec(kc: &[u32], kb: &[i64], bs: usize, n: usize, s: usize, Ghost(fp): Ghost<Seq<PartView>>) -> (k: i64)
    requires
        base_ok(fp, n as int),
        bs as int == bsize(fp),
        kc@ == u32s(fp[LI_PARTKEY_CODES as int]),
        kb@ == i64s(fp[LI_PARTKEY_BASE as int]),
        s < n,
    ensures
        k as int == key_at(fp, s as int),
{
    proof {
        lemma_div_lt(s as int, bs as int, kb@.len() as int);
        assert(i64::MIN <= key_at(fp, s as int) <= i64::MAX);
    }
    kb[s / bs] + kc[s] as i64
}

/// A directory over the `n` index positions (`kmin`, offsets `offs`): nondecreasing offsets at most `n`, every
/// position inside the entry of its key.
#[verifier::opaque]
pub open spec fn dir_spec(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>) -> bool {
    &&& offs.len() >= 1
    &&& offs[offs.len() - 1] <= n
    &&& forall|e: int| 0 <= e < offs.len() - 1 ==> #[trigger] offs[e] <= offs[e + 1]
    &&& forall|p: int| 0 <= p < n ==> {
        let e = #[trigger] key_at(fp, kirow(fp, p)) - kmin;
        &&& 0 <= e < offs.len() - 1
        &&& offs[e] <= p < offs[e + 1]
    }
}

/// The scan's invariant after positions `0 .. p` with `cur` entries started.
pub open spec fn scan_inv(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, p: int, cur: int) -> bool {
    &&& offs.len() == cur
    &&& forall|e: int| 0 <= e < cur ==> #[trigger] offs[e] <= p
    &&& forall|e: int| 0 <= e < cur - 1 ==> #[trigger] offs[e] <= offs[e + 1]
    &&& forall|q: int| 0 <= q < p ==> {
        let e = #[trigger] key_at(fp, kirow(fp, q)) - kmin;
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
    reveal(dir_spec);
    let ghost ni = n as int;
    let s0 = irow_exec(ic, ib, bs, n, 0, Ghost(fp));
    let kmin = key_exec(kc, kb, bs, n, s0, Ghost(fp));
    let sl = irow_exec(ic, ib, bs, n, n - 1, Ghost(fp));
    let kmax = key_exec(kc, kb, bs, n, sl, Ghost(fp));
    proof {
        lemma_sorted_le(fp, ni, 0, ni - 1);
    }
    let span: i128 = kmax as i128 - kmin as i128 + 1;
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
            kmin as int == key_at(fp, kirow(fp, 0)),
            nk as int == key_at(fp, kirow(fp, ni - 1)) - kmin + 1,
            p <= n,
            cur <= nk,
            p == 0 ==> cur == 0,
            p > 0 ==> cur as int == key_at(fp, kirow(fp, p - 1)) - kmin + 1,
            scan_inv(fp, ni, kmin as int, offs@, p as int, cur as int),
        decreases n - p,
    {
        let s = irow_exec(ic, ib, bs, n, p, Ghost(fp));
        let k = key_exec(kc, kb, bs, n, s, Ghost(fp));
        proof {
            lemma_sorted_le(fp, ni, 0, p as int);
            lemma_sorted_le(fp, ni, p as int, ni - 1);
            if p > 0 {
                lemma_sorted_le(fp, ni, p - 1, p as int);
            }
        }
        let e = (k as i128 - kmin as i128) as usize;
        while cur <= e
            invariant
                slices_ok(fp, ni, bs as int, ic@, ib@, kc@, kb@),
                ni == n as int,
                1 <= n <= u32::MAX,
                p < n,
                e < nk,
                e as int == key_at(fp, kirow(fp, p as int)) - kmin,
                cur <= e + 1,
                scan_inv(fp, ni, kmin as int, offs@, p as int, cur as int),
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
            scan_inv(fp, ni, kmin as int, offs@, ni, cur as int),
        decreases nk + 1 - cur,
    {
        proof {
            let ghost o = offs@;
            lemma_push_end(fp, ni, kmin as int, o, cur as int);
        }
        offs.push(n as u32);
        cur = cur + 1;
    }
    proof {
        assert(offs@.len() == nk + 1);
        assert(offs@[nk as int] <= ni);
        assert forall|q: int| 0 <= q < ni implies {
            let e = #[trigger] key_at(fp, kirow(fp, q)) - kmin;
            &&& 0 <= e < offs@.len() - 1
            &&& offs@[e] <= q < offs@[e + 1]
        } by {
            let e = key_at(fp, kirow(fp, q)) - kmin;
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
        let e = #[trigger] key_at(fp, kirow(fp, q)) - kmin;
        &&& 0 <= e < cur + 1
        &&& o2[e] <= q
        &&& e + 1 < cur + 1 ==> q < o2[e + 1]
    } by {
        let e = key_at(fp, kirow(fp, q)) - kmin;
        assert(0 <= e < cur && offs[e] <= q);
        assert(o2[e] == offs[e]);
        if e + 1 < cur {
            assert(o2[e + 1] == offs[e + 1]);
        } else {
            assert(o2[e + 1] == p);
            assert(q < p);
        }
    }
}

/// After the entries up to the key of position `p` are started, position `p` is placed.
proof fn lemma_step(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, p: int, cur: int)
    requires
        scan_inv(fp, n, kmin, offs, p, cur),
        0 <= p < n,
        cur == key_at(fp, kirow(fp, p)) - kmin + 1,
        key_at(fp, kirow(fp, p)) - kmin >= 0,
    ensures
        scan_inv(fp, n, kmin, offs, p + 1, cur),
{
    assert forall|e: int| 0 <= e < cur implies #[trigger] offs[e] <= p + 1 by {
        assert(offs[e] <= p);
    }
    assert forall|q: int| 0 <= q < p + 1 implies {
        let e = #[trigger] key_at(fp, kirow(fp, q)) - kmin;
        &&& 0 <= e < cur
        &&& offs[e] <= q
        &&& e + 1 < cur ==> q < offs[e + 1]
    } by {
        if q == p {
            let e = key_at(fp, kirow(fp, q)) - kmin;
            assert(e == cur - 1);
            assert(offs[e] <= p);
        }
    }
}

/// The entries after the last key end at `n`.
proof fn lemma_push_end(fp: Seq<PartView>, n: int, kmin: int, offs: Seq<u32>, cur: int)
    requires
        scan_inv(fp, n, kmin, offs, n, cur),
        0 <= n <= u32::MAX,
    ensures
        scan_inv(fp, n, kmin, offs.push(n as u32), n, cur + 1),
{
    lemma_push_entry_any(fp, n, kmin, offs, n, cur);
}

} // verus!
