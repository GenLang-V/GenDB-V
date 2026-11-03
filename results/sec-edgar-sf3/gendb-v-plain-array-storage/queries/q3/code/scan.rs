//! The parallel scan of `num`: one task per contiguous row range. A task shares the key structure of the
//! qualifying subs (`keys`, built once by the caller) and, block by block, selects the rows with `uom = $1`, then
//! looks up each selected row's adsh and adds its value to the accumulator of that sub's rank. Its output: per rank, the exact sum (`rsum`) and whether some row was added
//! (`rcnt > 0`). Ranges hold at most 2^33 rows, so every partial sum of values below 10^28 fits `i128`.
use vstd::prelude::*;
use crate::spec::numeric::*;
use crate::link::query::{text_wf, text_at, TextView};
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::bytes::*;
use crate::agent::common::wordeq::*;
use crate::agent::keys::*;

verus! {

/// Largest row range of one task.
pub const MAX_RANGE: u64 = 0x2_0000_0000;

/// The num columns a task reads (whole parts).
#[derive(Clone, Copy)]
pub struct NumCols {
    pub uom_off: &'static [i64],
    pub uom_bytes: &'static [u8],
    pub adsh_off: &'static [i64],
    pub adsh_bytes: &'static [u8],
    pub value: &'static [i128],
    /// Number of num rows.
    pub n: usize,
    /// Number of uom and adsh bytes.
    pub uom_len: usize,
    pub adsh_len: usize,
}

impl NumCols {
    pub open spec fn uom_text(&self) -> TextView {
        TextView { offsets: self.uom_off@, bytes: self.uom_bytes@ }
    }

    pub open spec fn adsh_text(&self) -> TextView {
        TextView { offsets: self.adsh_off@, bytes: self.adsh_bytes@ }
    }

    pub open spec fn uom(&self, i: int) -> Seq<u8> {
        text_at(self.uom_text(), i)
    }

    pub open spec fn adsh(&self, i: int) -> Seq<u8> {
        text_at(self.adsh_text(), i)
    }

    pub open spec fn val(&self, i: int) -> int {
        self.value@[i] as int
    }

    pub open spec fn wf(&self) -> bool {
        &&& text_wf(self.uom_text(), self.n as int)
        &&& text_wf(self.adsh_text(), self.n as int)
        &&& self.value@.len() == self.n
        &&& self.n < usize::MAX
        &&& self.uom_len == self.uom_bytes@.len()
        &&& self.adsh_len == self.adsh_bytes@.len()
        &&& forall|i: int| 0 <= i < self.n ==> #[trigger] abs(self.val(i)) < pow10(28)
    }
}

/// The sum of the values of the rows `lo..i` with `uom = p0` and adsh `key`.
pub open spec fn rsum(nc: &NumCols, p0: Seq<u8>, key: Seq<u8>, lo: int, i: int) -> int
    decreases i - lo,
{
    if i <= lo {
        0
    } else {
        rsum(nc, p0, key, lo, i - 1) + if nc.uom(i - 1) == p0 && nc.adsh(i - 1) == key { nc.val(i - 1) } else { 0 }
    }
}

/// The number of those rows.
pub open spec fn rcnt(nc: &NumCols, p0: Seq<u8>, key: Seq<u8>, lo: int, i: int) -> int
    decreases i - lo,
{
    if i <= lo {
        0
    } else {
        rcnt(nc, p0, key, lo, i - 1) + if nc.uom(i - 1) == p0 && nc.adsh(i - 1) == key { 1int } else { 0int }
    }
}

/// `|rsum| <= (i - lo) * (10^28 - 1)` and `rcnt >= 0`.
pub proof fn lemma_rsum_bound(nc: &NumCols, p0: Seq<u8>, key: Seq<u8>, lo: int, i: int)
    requires nc.wf(), 0 <= lo <= i <= nc.n,
    ensures
        abs(rsum(nc, p0, key, lo, i)) <= (i - lo) * (pow10(28) - 1),
        rcnt(nc, p0, key, lo, i) >= 0,
    decreases i - lo,
{
    if i > lo {
        lemma_rsum_bound(nc, p0, key, lo, i - 1);
        assert(abs(nc.val(i - 1)) < pow10(28));
        assert((i - lo) * (pow10(28) - 1) == (i - 1 - lo) * (pow10(28) - 1) + (pow10(28) - 1)) by (nonlinear_arith);
    }
}

/// Adjacent ranges add.
pub proof fn lemma_rsum_split(nc: &NumCols, p0: Seq<u8>, key: Seq<u8>, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        rsum(nc, p0, key, lo, hi) == rsum(nc, p0, key, lo, mid) + rsum(nc, p0, key, mid, hi),
        rcnt(nc, p0, key, lo, hi) == rcnt(nc, p0, key, lo, mid) + rcnt(nc, p0, key, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_rsum_split(nc, p0, key, lo, mid, hi - 1);
    }
}

/// Different ranks have different keys (sub adsh is a key; ranks are different sub rows).
pub proof fn lemma_rank_keys_distinct(sc: &SubCols, a: int, b: int)
    requires sc.wf(), 0 <= a < sc.qlist(sc.n as int).len(), 0 <= b < sc.qlist(sc.n as int).len(), a != b,
    ensures rank_key(sc, a) != rank_key(sc, b),
{
    lemma_qlist(sc, sc.n as int);
    let ql = sc.qlist(sc.n as int);
    if a < b {
        assert(ql[a] < ql[b]);
    } else {
        assert(ql[b] < ql[a]);
    }
}

/// Rows per block of the scan.
pub const BLK: usize = 1024;

/// A task's output (and scratch): per rank the sum and whether some row counted (dense, indexed by rank), and
/// the block buffer.
pub struct ScanOut {
    pub acc: Vec<i128>,
    pub seen: Vec<u8>,
    pub sel: Vec<usize>,
}

pub struct ScanTask {
    pub num: NumCols,
    pub sub: SubCols,
    pub p0: &'static [u8],
    pub p0_len: usize,
    pub lo: usize,
    pub hi: usize,
    pub keys: std::sync::Arc<Keys>,
    pub out: ScanOut,
}

impl ScanTask {
    /// The number of qualifying subs.
    pub open spec fn nq(&self) -> int {
        self.sub.qlist(self.sub.n as int).len() as int
    }

    /// The accumulators of the rows `lo..i`.
    pub open spec fn acc_ok(&self, acc: Seq<i128>, seen: Seq<u8>, i: int) -> bool {
        &&& acc.len() >= self.nq()
        &&& seen.len() >= self.nq()
        &&& forall|id: int| 0 <= id < self.nq() ==> #[trigger] acc[id] as int
            == rsum(&self.num, self.p0@, rank_key(&self.sub, id), self.lo as int, i)
        &&& forall|id: int| 0 <= id < self.nq() ==> (#[trigger] seen[id] != 0)
            == (rcnt(&self.num, self.p0@, rank_key(&self.sub, id), self.lo as int, i) > 0)
    }
}

/// The rows `lo..i` with `uom = p0`, in order.
pub open spec fn matches(nc: &NumCols, p0: Seq<u8>, lo: int, i: int) -> Seq<usize>
    decreases i - lo,
{
    if i <= lo {
        Seq::empty()
    } else if nc.uom(i - 1) == p0 {
        matches(nc, p0, lo, i - 1).push((i - 1) as usize)
    } else {
        matches(nc, p0, lo, i - 1)
    }
}

/// `matches`: increasing rows of `lo..i` with `uom = p0`, and every such row is listed.
proof fn lemma_matches(nc: &NumCols, p0: Seq<u8>, lo: int, i: int)
    requires 0 <= lo <= i < usize::MAX,
    ensures ({
        let m = matches(nc, p0, lo, i);
        &&& m.len() <= i - lo
        &&& forall|t: int| 0 <= t < m.len() ==> lo <= #[trigger] m[t] < i && nc.uom(m[t] as int) == p0
        &&& forall|t1: int, t2: int| 0 <= t1 < t2 < m.len() ==> #[trigger] m[t1] < #[trigger] m[t2]
        &&& forall|r: int| lo <= r < i && #[trigger] nc.uom(r) == p0 ==> exists|t: int| 0 <= t < m.len() && m[t] == r
    }),
    decreases i - lo,
{
    if i > lo {
        lemma_matches(nc, p0, lo, i - 1);
        let m0 = matches(nc, p0, lo, i - 1);
        let m = matches(nc, p0, lo, i);
        if nc.uom(i - 1) == p0 {
            assert forall|r: int| lo <= r < i && #[trigger] nc.uom(r) == p0 implies exists|t: int| 0 <= t < m.len() && m[t] == r by {
                if r < i - 1 {
                    let t = choose|t: int| 0 <= t < m0.len() && m0[t] == r;
                    assert(m[t] == r);
                } else {
                    assert(m[m0.len() as int] == (i - 1) as usize);
                    assert(m[m0.len() as int] as int == r);
                }
            }
        }
    }
}

/// The rows strictly between consecutive matches have another uom.
proof fn lemma_matches_gap(nc: &NumCols, p0: Seq<u8>, lo: int, i: int, t: int, r: int)
    requires
        0 <= lo <= i < usize::MAX, 0 <= t <= matches(nc, p0, lo, i).len(),
        (if t == 0 { lo } else { matches(nc, p0, lo, i)[t - 1] + 1 }) <= r,
        r < (if t == matches(nc, p0, lo, i).len() { i } else { matches(nc, p0, lo, i)[t] as int }),
    ensures nc.uom(r) != p0,
{
    lemma_matches(nc, p0, lo, i);
    let m = matches(nc, p0, lo, i);
    if nc.uom(r) == p0 {
        assert(lo <= r < i);
        let u = choose|u: int| 0 <= u < m.len() && m[u] == r;
        if u < t {
            if u < t - 1 {
                assert(m[u] < m[t - 1]);
            }
        } else {
            if u > t {
                assert(m[t] < m[u]);
            }
        }
    }
}

/// One row: the accumulators of `lo..i+1` from those of `lo..i`, given the rank (or none) the row adds to.
proof fn lemma_scan_step(t: &ScanTask, acc: Seq<i128>, seen: Seq<u8>, acc2: Seq<i128>, seen2: Seq<u8>, i: int, hit: Option<int>)
    requires
        t.acc_ok(acc, seen, i),
        t.sub.wf(), t.lo <= i,
        match hit {
            Some(id) => {
                &&& 0 <= id < t.nq()
                &&& t.num.uom(i) == t.p0@ && t.num.adsh(i) == rank_key(&t.sub, id)
                &&& acc2 == acc.update(id, (acc[id] + t.num.val(i)) as i128)
                &&& acc[id] + t.num.val(i) == (acc[id] + t.num.val(i)) as i128
                &&& seen2.len() == seen.len() && seen2[id] != 0
                &&& forall|j: int| 0 <= j < seen.len() && j != id ==> #[trigger] seen2[j] == seen[j]
            },
            None => {
                &&& forall|id: int| 0 <= id < t.nq() ==> !(t.num.uom(i) == t.p0@ && t.num.adsh(i) == #[trigger] rank_key(&t.sub, id))
                &&& acc2 == acc && seen2 == seen
            },
        },
    ensures t.acc_ok(acc2, seen2, i + 1),
{
    let (p0, lo) = (t.p0@, t.lo as int);
    assert forall|id: int| #![trigger acc2[id]] #![trigger seen2[id]] 0 <= id < t.nq() implies
        acc2[id] as int == rsum(&t.num, p0, rank_key(&t.sub, id), lo, i + 1)
        && (seen2[id] != 0) == (rcnt(&t.num, p0, rank_key(&t.sub, id), lo, i + 1) > 0) by {
        let key = rank_key(&t.sub, id);
        let hits = t.num.uom(i) == p0 && t.num.adsh(i) == key;
        assert(rsum(&t.num, p0, key, lo, i + 1) == rsum(&t.num, p0, key, lo, i) + if hits { t.num.val(i) } else { 0 });
        assert(rcnt(&t.num, p0, key, lo, i + 1) == rcnt(&t.num, p0, key, lo, i) + if hits { 1int } else { 0int });
        lemma_rcnt_nonneg(&t.num, p0, key, lo, i);
        assert(acc[id] as int == rsum(&t.num, p0, key, lo, i));
        assert((seen[id] != 0) == (rcnt(&t.num, p0, key, lo, i) > 0));
        match hit {
            Some(h) => {
                if id != h {
                    lemma_rank_keys_distinct(&t.sub, id, h);
                    assert(!hits);
                    assert(acc2[id] == acc[id]);
                    assert(seen2[id] == seen[id]);
                } else {
                    assert(hits);
                    assert(acc2[id] as int == acc[id] + t.num.val(i));
                }
            },
            None => {
                assert(!hits);
            },
        }
    }
}

pub proof fn lemma_rcnt_nonneg(nc: &NumCols, p0: Seq<u8>, key: Seq<u8>, lo: int, i: int)
    ensures rcnt(nc, p0, key, lo, i) >= 0,
    decreases i - lo,
{
    if i > lo {
        lemma_rcnt_nonneg(nc, p0, key, lo, i - 1);
    }
}

/// Rows without `uom = p0` change nothing.
proof fn lemma_skip_rows(t: &ScanTask, acc: Seq<i128>, seen: Seq<u8>, a: int, b: int)
    requires
        t.acc_ok(acc, seen, a), t.sub.wf(), t.lo <= a <= b,
        forall|r: int| a <= r < b ==> #[trigger] t.num.uom(r) != t.p0@,
    ensures t.acc_ok(acc, seen, b),
    decreases b - a,
{
    if a < b {
        assert(t.num.uom(a) != t.p0@);
        lemma_scan_step(t, acc, seen, acc, seen, a, None);
        lemma_skip_rows(t, acc, seen, a + 1, b);
    }
}

/// The word and mask of `p0` when it has at most 8 bytes (else zero).
fn p0_word(p0: &[u8], p0_len: usize) -> (r: (u64, u64))
    requires p0_len == p0@.len(),
    ensures p0_len <= 8 ==> r.0 == pword(p0@, p0_len as int) && r.1 == bmask(p0_len as int),
    no_unwind
{
    if p0_len > 8 {
        return (0, 0);
    }
    let mut w: u64 = 0;
    let mut q: usize = 0;
    while q < p0_len
        invariant q <= p0_len <= 8, p0_len == p0@.len(), w == pword(p0@, q as int),
        decreases p0_len - q,
    {
        w = w | ((p0[q] as u64) << ((8 * q) as u64));
        q = q + 1;
    }
    proof {
        lemma_bmask_values();
    }
    let mask: u64 = if p0_len == 8 { 0xffff_ffff_ffff_ffff } else if p0_len == 7 { 0xff_ffff_ffff_ffff }
        else if p0_len == 6 { 0xffff_ffff_ffff } else if p0_len == 5 { 0xff_ffff_ffff } else if p0_len == 4 { 0xffff_ffff }
        else if p0_len == 3 { 0xff_ffff } else if p0_len == 2 { 0xffff } else if p0_len == 1 { 0xff } else { 0 };
    (w, mask)
}

/// One row with `uom = p0`: look up its adsh among the ranks and add its value.
#[inline(always)]
fn add_row(Ghost(t): Ghost<ScanTask>, num: &NumCols, sub: &SubCols, keys: &Keys, i: usize, acc: &mut Vec<i128>,
    seen: &mut Vec<u8>)
    requires
        t.num == *num, t.sub == *sub, num.wf(), sub.wf(), t.lo <= i < num.n, i - t.lo < 0x2_0000_0000int,
        keys_inv(keys.view(), sub, t.nq()),
        num.uom(i as int) == t.p0@,
        t.acc_ok(old(acc)@, old(seen)@, i as int),
    ensures
        t.acc_ok(final(acc)@, final(seen)@, i + 1),
        final(acc)@.len() == old(acc)@.len(), final(seen)@.len() == old(seen)@.len(),
    no_unwind
{
    let ghost acc0 = acc@;
    let ghost seen0 = seen@;
    let ghost nq = t.nq();
    let ghost p0 = t.p0@;
    let ghost lo = t.lo as int;
    proof {
        assert(0 <= num.adsh_text().offsets[i as int] <= num.adsh_text().offsets[i + 1] <= num.adsh_text().bytes.len());
    }
    let aa = num.adsh_off[i] as usize;
    let ab = num.adsh_off[i + 1] as usize;
    let x = sub_bytes(num.adsh_bytes, aa, ab);
    let n = ab - aa;
    let w = key_words(x, n);
    let h = key_hash(n, w);
    let id = probe(keys, sub, x, n, w, h);
    if id != usize::MAX {
        proof {
            lemma_rsum_bound(num, p0, rank_key(sub, id as int), lo, i as int);
            lemma_pow10_i128_boundary();
            assert(pow10(28) == 10000000000000000000000000000) by (compute);
            let ghost m = i - lo;
            assert(m * (pow10(28) - 1) <= 0x2_0000_0000int * 9999999999999999999999999999int) by (nonlinear_arith)
                requires 0 <= m <= 0x2_0000_0000int, pow10(28) == 10000000000000000000000000000int;
            assert(0x2_0000_0000int * 9999999999999999999999999999int + 10000000000000000000000000000int
                < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffint);
        }
        let v = num.value[i];
        let a = acc[id];
        proof {
            let key = rank_key(sub, id as int);
            assert(a as int == rsum(num, p0, key, lo, i as int));
            assert(abs(num.val(i as int)) < pow10(28));
            assert(v as int == num.val(i as int));
            let b = 0x2_0000_0000int * 9999999999999999999999999999int;
            assert(-b <= a as int <= b);
            assert(-10000000000000000000000000000int < (v as int) && (v as int) < 10000000000000000000000000000int);
        }
        acc[id] = a + v;
        seen[id] = 1;
        proof {
            lemma_scan_step(&t, acc0, seen0, acc@, seen@, i as int, Some(id as int));
        }
    } else {
        proof {
            lemma_scan_step(&t, acc0, seen0, acc@, seen@, i as int, None);
        }
    }
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        &&& self.num.wf()
        &&& self.sub.wf()
        &&& self.p0_len == self.p0@.len()
        &&& self.lo <= self.hi <= self.num.n
        &&& self.hi - self.lo <= 0x2_0000_0000int
        &&& keys_inv((*self.keys).view(), &self.sub, self.nq())
        &&& self.out.acc@.len() >= self.nq()
        &&& self.out.seen@.len() >= self.nq()
        &&& self.out.sel@.len() == BLK
        &&& forall|id: int| 0 <= id < self.out.acc@.len() ==> #[trigger] self.out.acc@[id] == 0
        &&& forall|id: int| 0 <= id < self.out.seen@.len() ==> #[trigger] self.out.seen@[id] == 0
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        &&& self.acc_ok(out.acc@, out.seen@, self.hi as int)
        &&& out.acc@.len() == self.out.acc@.len() && out.seen@.len() == self.out.seen@.len()
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let ghost t = self;
        let ScanTask { num, sub, p0, p0_len, lo, hi, keys, out } = self;
        let keys: &Keys = &*keys;
        let ScanOut { acc, seen, sel } = out;
        let mut acc = acc;
        let mut seen = seen;
        let mut sel = sel;
        let ghost nq = t.nq();
        proof {
            assert(t.acc_ok(acc@, seen@, lo as int));
            lemma_inv_shape(keys.view(), &sub, nq);
            lemma_qlist(&sub, sub.n as int);
        }
        let ulen = num.uom_len;
        let (p0w, mask) = p0_word(p0, p0_len);
        let small = p0_len <= 8;
        let mut b0 = lo;
        while b0 < hi
            invariant
                t.num == num, t.sub == sub, t.p0 == p0, t.lo == lo, t.hi == hi, nq == t.nq(),
                num.wf(), sub.wf(), p0_len == p0@.len(), lo <= b0 <= hi, hi <= num.n, hi - lo <= 0x2_0000_0000int,
                keys_inv(keys.view(), &sub, nq), ulen == num.uom_bytes@.len(), sel@.len() == BLK,
                small == (p0_len <= 8), small ==> p0w == pword(p0@, p0_len as int) && mask == bmask(p0_len as int),
                t.acc_ok(acc@, seen@, b0 as int),
                acc@.len() == t.out.acc@.len(), seen@.len() == t.out.seen@.len(),
            decreases hi - b0,
        {
            let b1 = if hi - b0 > BLK { b0 + BLK } else { hi };
            // Phase 1: the rows of the block with `uom = p0` (no branch on the data).
            let mut k: usize = 0;
            let mut i = b0;
            while i < b1
                invariant
                    num.wf(), p0_len == p0@.len(), b0 <= i <= b1, b1 <= num.n, b1 - b0 <= BLK, sel@.len() == BLK,
                    ulen == num.uom_bytes@.len(), k <= i - b0,
                    small == (p0_len <= 8), small ==> p0w == pword(p0@, p0_len as int) && mask == bmask(p0_len as int),
                    sel@.subrange(0, k as int) == matches(&num, p0@, b0 as int, i as int),
                decreases b1 - i,
            {
                proof {
                    assert(0 <= num.uom_text().offsets[i as int] <= num.uom_text().offsets[i + 1] <= num.uom_text().bytes.len());
                }
                let ua = num.uom_off[i] as usize;
                let ub = num.uom_off[i + 1] as usize;
                let m: usize = if small && 8 <= ulen - ua {
                    let w = word8(sub_bytes(num.uom_bytes, ua, ua + 8));
                    proof {
                        lemma_word_shift(num.uom_bytes@, ua as int);
                        lemma_word_eq(num.uom_bytes@, ua as int, p0@, p0_len as int);
                    }
                    let c1 = ub - ua == p0_len;
                    let c2 = ((w ^ p0w) & mask) == 0;
                    if c1 && c2 { 1 } else { 0 }
                } else if ub - ua == p0_len && eq_n(sub_bytes(num.uom_bytes, ua, ub), p0, p0_len) {
                    1
                } else {
                    0
                };
                proof {
                    let u = num.uom(i as int);
                    assert(u == num.uom_bytes@.subrange(ua as int, ub as int));
                    if ub - ua == p0_len {
                        assert(num.uom_bytes@.subrange(ua as int, ua + p0_len) == u);
                    } else {
                        assert(u.len() != p0@.len());
                    }
                    assert((m == 1) == (u == p0@));
                    assert(m <= 1);
                }
                let ghost s0 = sel@;
                sel[k] = i;
                proof {
                    let mi = matches(&num, p0@, b0 as int, i + 1);
                    if m == 1 {
                        assert(sel@.subrange(0, k + 1) =~= s0.subrange(0, k as int).push(i));
                    } else {
                        assert(sel@.subrange(0, k as int) =~= s0.subrange(0, k as int));
                    }
                }
                k = k + m;
                i = i + 1;
            }
            let ghost ms = matches(&num, p0@, b0 as int, b1 as int);
            proof {
                lemma_matches(&num, p0@, b0 as int, b1 as int);
                assert(ms.len() == k);
                assert forall|u: int| 0 <= u < k implies #[trigger] sel@[u] == ms[u] by {
                    assert(sel@.subrange(0, k as int)[u] == sel@[u]);
                }
            }
            // Phase 2: look up the adsh of every selected row and add its value.
            let mut u: usize = 0;
            let ghost mut cur: int = b0 as int;
            while u < k
                invariant
                    t.num == num, t.sub == sub, t.p0 == p0, t.lo == lo, t.hi == hi, nq == t.nq(),
                    num.wf(), sub.wf(), p0_len == p0@.len(), lo <= b0 < b1 <= hi, hi <= num.n, hi - lo <= 0x2_0000_0000int,
                    keys_inv(keys.view(), &sub, nq), sel@.len() == BLK, k <= BLK,
                    ms == matches(&num, p0@, b0 as int, b1 as int), ms.len() == k, u <= k,
                    forall|w: int| 0 <= w < k ==> #[trigger] sel@[w] == ms[w],
                    cur == (if u == 0 { b0 as int } else { ms[u - 1] + 1 }),
                    b0 <= cur <= b1,
                    t.acc_ok(acc@, seen@, cur),
                    acc@.len() == t.out.acc@.len(), seen@.len() == t.out.seen@.len(),
                decreases k - u,
            {
                let i = sel[u];
                proof {
                    lemma_matches(&num, p0@, b0 as int, b1 as int);
                    assert(cur <= i);
                    assert forall|r: int| cur <= r < i implies #[trigger] num.uom(r) != p0@ by {
                        lemma_matches_gap(&num, p0@, b0 as int, b1 as int, u as int, r);
                    }
                    lemma_skip_rows(&t, acc@, seen@, cur, i as int);
                    assert(num.uom(i as int) == p0@);
                    assert(0 <= num.adsh_text().offsets[i as int] <= num.adsh_text().offsets[i + 1] <= num.adsh_text().bytes.len());
                }
                add_row(Ghost(t), &num, &sub, keys, i, &mut acc, &mut seen);
                proof {
                    cur = i + 1;
                }
                u = u + 1;
            }
            proof {
                lemma_matches(&num, p0@, b0 as int, b1 as int);
                assert forall|r: int| cur <= r < b1 implies #[trigger] num.uom(r) != p0@ by {
                    lemma_matches_gap(&num, p0@, b0 as int, b1 as int, k as int, r);
                }
                lemma_skip_rows(&t, acc@, seen@, cur, b1 as int);
            }
            b0 = b1;
        }
        ScanOut { acc, seen, sel }
    }
}

} // verus!
