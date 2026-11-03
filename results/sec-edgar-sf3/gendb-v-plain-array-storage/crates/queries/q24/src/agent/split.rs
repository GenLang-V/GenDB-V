//! Phase 1 worker: partition the `pre` rows `plo..phi` by the top bits of `ad_hash` (items `(ad_hash, tv_hash)` of
//! their keys, `partition_pre`: a counting pass hashes `adsh` only, the scatter pass hashes both keys and writes the
//! items in place, so no per-row scratch is allocated), and the `tag` rows `tlo..thi` by the top bits of `tv_hash`
//! (items `(tv_hash, row)`, `common::partition`). Every `pre` row of one `adsh` lands in one partition, and so does
//! every `tag` row of one value, so phase 2 can build the `pre` key sets and check the hash separation of `tag`
//! partition by partition. `adsh` partitions are about equal in size (no popular value dominates one).
use vstd::prelude::*;
use crate::link::query::{text_wf, TextCol};
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::spec::*;
use crate::agent::txt::*;
use crate::agent::common::partition::*;
use crate::agent::common::pairset::zeroed;

verus! {

/// The `pre` partition keys of rows `lo..hi`: `ad_hash` (item `q` is row `lo + q`).
pub open spec fn pre_ks(c: Ctx, lo: int, hi: int) -> Seq<u64> {
    Seq::new((hi - lo) as nat, |q: int| pre_ad(c, lo + q))
}

/// The `pre` item auxiliaries of rows `lo..hi`: `tv_hash`.
pub open spec fn pre_xs(c: Ctx, lo: int, hi: int) -> Seq<u64> {
    Seq::new((hi - lo) as nat, |q: int| pre_tv(c, lo + q))
}

/// The `tag` value hashes of rows `lo..hi`, with the row numbers.
pub open spec fn tag_ks(c: Ctx, lo: int, hi: int) -> Seq<u64> {
    Seq::new((hi - lo) as nat, |q: int| tag_tv(c, lo + q))
}

pub open spec fn tag_xs(c: Ctx, lo: int, hi: int) -> Seq<u64> {
    Seq::new((hi - lo) as nat, |q: int| (lo + q) as u64)
}

/// Buffers for partitioning `len` items (allocated on the calling thread).
pub struct PartBufs {
    pub sk: Vec<u64>,
    pub sx: Vec<u64>,
    pub keys: Vec<u64>,
    pub auxs: Vec<u64>,
    pub starts: Vec<usize>,
    pub ends: Vec<usize>,
}

pub open spec fn bufs_ok(b: PartBufs, len: int) -> bool {
    &&& b.sk@.len() >= len && b.sx@.len() >= len
    &&& b.keys@.len() >= len && b.auxs@.len() == b.keys@.len()
    &&& b.starts@.len() == PARTS && b.ends@.len() == PARTS
    &&& forall|p: int| 0 <= p < PARTS ==> #[trigger] b.ends@[p] == 0
}

/// Buffers without the per-row scratch `sk`/`sx` (for `partition_pre`).
pub open spec fn direct_bufs_ok(b: PartBufs, len: int) -> bool {
    &&& b.keys@.len() >= len && b.auxs@.len() == b.keys@.len()
    &&& b.starts@.len() == PARTS && b.ends@.len() == PARTS
    &&& forall|p: int| 0 <= p < PARTS ==> #[trigger] b.ends@[p] == 0
}

pub fn new_direct_bufs(len: usize) -> (b: PartBufs)
    ensures direct_bufs_ok(b, len as int),
{
    PartBufs {
        sk: Vec::new(),
        sx: Vec::new(),
        keys: zeroed(len),
        auxs: zeroed(len),
        starts: vec![0usize; PARTS],
        ends: vec![0usize; PARTS],
    }
}

pub fn new_bufs(len: usize) -> (b: PartBufs)
    ensures bufs_ok(b, len as int),
{
    PartBufs {
        sk: zeroed(len),
        sx: zeroed(len),
        keys: zeroed(len),
        auxs: zeroed(len),
        starts: vec![0usize; PARTS],
        ends: vec![0usize; PARTS],
    }
}

pub struct SplitTask {
    pub c: Ghost<Ctx>,
    pub ptag: TextCol,
    pub pver: TextCol,
    pub padsh: TextCol,
    pub plo: usize,
    pub phi: usize,
    pub pb: PartBufs,
    pub ttag: TextCol,
    pub tver: TextCol,
    pub tlo: usize,
    pub thi: usize,
    pub tb: PartBufs,
}

pub struct SplitOut {
    pub pre: Option<Parted>,
    pub tag: Option<Parted>,
}

pub open spec fn split_pre(t: SplitTask) -> bool {
    let c = t.c@;
    &&& ctx_ok(c)
    &&& t.ptag@ == ptag_v(c) && t.pver@ == pver_v(c) && t.padsh@ == padsh_v(c)
    &&& t.ttag@ == ttag_v(c) && t.tver@ == tver_v(c)
    &&& t.plo <= t.phi <= c.m && t.tlo <= t.thi <= c.nt
    &&& direct_bufs_ok(t.pb, t.phi - t.plo) && bufs_ok(t.tb, t.thi - t.tlo)
}

impl WorkerTask for SplitTask {
    type Output = SplitOut;

    open spec fn pre(&self) -> bool {
        split_pre(*self)
    }

    open spec fn post(&self, out: SplitOut) -> bool {
        let c = self.c@;
        &&& (out.pre matches Some(o) ==> parted_ok(o, pre_ks(c, self.plo as int, self.phi as int), pre_xs(c, self.plo as int, self.phi as int)))
        &&& (out.tag matches Some(o) ==> parted_ok(o, tag_ks(c, self.tlo as int, self.thi as int), tag_xs(c, self.tlo as int, self.thi as int)))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.plo as u64, self.phi as u64)
    }

    fn run(self) -> (out: SplitOut) {
        let SplitTask { c, ptag, pver, padsh, plo, phi, pb, ttag, tver, tlo, thi, tb } = self;
        let PartBufs { sk: _, sx: _, keys, auxs, starts, ends } = pb;
        let pre = partition_pre(&ptag, &pver, &padsh, plo, phi, keys, auxs, starts, ends, c);
        let PartBufs { sk, sx, keys, auxs, starts, ends } = tb;
        let (sk, sx) = hash_tag_rows(&ttag, &tver, tlo, thi, sk, sx, c);
        let tag = partition(&sk, &sx, thi - tlo, keys, auxs, starts, ends);
        SplitOut { pre, tag }
    }
}

/// Partition the `pre` rows `plo..phi` by the top bits of `ad_hash` into `keys`/`auxs` (at least `phi - plo` slots
/// each): item `q` is `(ad_hash, tv_hash)` of row `plo + q` (`pre_ks`, `pre_xs`). As `common::partition`, but the
/// items are computed from the key texts in both passes instead of read from scratch vectors: the counting pass
/// hashes `adsh` only, the scatter pass both keys. `starts`/`ends`: `PARTS` zeros each.
#[verifier::spinoff_prover]
fn partition_pre(ptag: &TextCol, pver: &TextCol, padsh: &TextCol, plo: usize, phi: usize, keys: Vec<u64>,
    auxs: Vec<u64>, starts: Vec<usize>, ends: Vec<usize>, c: Ghost<Ctx>) -> (r: Option<Parted>)
    requires
        ctx_ok(c@), ptag@ == ptag_v(c@), pver@ == pver_v(c@), padsh@ == padsh_v(c@), plo <= phi <= c@.m,
        starts@.len() == PARTS, ends@.len() == PARTS,
        forall|p: int| 0 <= p < PARTS ==> #[trigger] ends@[p] == 0,
        keys@.len() >= phi - plo, auxs@.len() == keys@.len(),
    ensures
        r matches Some(o) ==> parted_ok(o, pre_ks(c@, plo as int, phi as int), pre_xs(c@, plo as int, phi as int)),
    no_unwind
{
    let ghost cc = c@;
    proof {
        lemma_text_cols_wf(cc);
    }
    let len = phi - plo;
    let ghost kss = pre_ks(cc, plo as int, phi as int);
    let ghost xss = pre_xs(cc, plo as int, phi as int);
    let mut keys = keys;
    let mut auxs = auxs;
    let mut starts = starts;
    let mut cursor = ends;
    let cap = keys.len();
    // Count the rows of every partition (in `cursor`).
    let mut q: usize = 0;
    while q < len
        invariant
            q <= len, len == phi - plo, phi <= cc.m, text_wf(padsh@, cc.m), cursor@.len() == PARTS,
            forall|p: int| 0 <= p < PARTS ==> #[trigger] cursor@[p] <= q,
        decreases len - q,
    {
        let p = part_exec(ad_hash_at(padsh, plo + q, Ghost(cc.m)));
        let ghost before = cursor@;
        cursor[p] = cursor[p] + 1;
        proof {
            assert forall|p2: int| 0 <= p2 < PARTS implies #[trigger] cursor@[p2] <= q + 1 by {
                if p2 != p as int {
                    assert(cursor@[p2] == before[p2]);
                }
            }
        }
        q = q + 1;
    }
    // Segment starts: `b[p]` is the sum of the counts below `p` (`b[PARTS]` the total); cursors restart at them.
    let ghost mut b: Seq<usize> = seq![0usize];
    let mut acc: usize = 0;
    let mut p: usize = 0;
    while p < PARTS
        invariant
            p <= PARTS, acc <= cap, cursor@.len() == PARTS, starts@.len() == PARTS,
            b.len() == p + 1, b[p as int] == acc,
            forall|a: int, c2: int| #![trigger b[a], b[c2]] 0 <= a <= c2 <= p ==> b[a] <= b[c2],
            forall|a: int| 0 <= a < p ==> #[trigger] starts@[a] == b[a] && cursor@[a] == b[a],
        decreases PARTS - p,
    {
        let count = cursor[p];
        if count > cap - acc {
            return None;
        }
        starts[p] = acc;
        cursor[p] = acc;
        acc = acc + count;
        proof {
            b = b.push(acc);
        }
        p = p + 1;
    }
    proof {
        assert forall|a: int| 0 <= a < PARTS implies b[a] <= #[trigger] cursor@[a] && cursor@[a] <= b[a + 1] by {
            assert(starts@[a] == b[a]);
            assert(cursor@[a] == b[a]);
            assert(b[a] <= b[a + 1]);
        }
        assert forall|a: int, e: int| #[trigger] filled(b, cursor@, a, e) implies
            part_of(keys@[e]) == a && src_item(kss, xss, keys@[e], auxs@[e]) by {
            assert(starts@[a] == b[a]);
            assert(cursor@[a] == b[a]);
        }
    }
    // Scatter: row `plo + q` goes to the cursor of its partition.
    let mut q: usize = 0;
    while q < len
        invariant
            q <= len, len == phi - plo, phi <= cc.m,
            text_wf(ptag@, cc.m), text_wf(pver@, cc.m), text_wf(padsh@, cc.m),
            ptag@ == ptag_v(cc), pver@ == pver_v(cc), padsh@ == padsh_v(cc),
            kss == pre_ks(cc, plo as int, phi as int), xss == pre_xs(cc, plo as int, phi as int),
            cursor@.len() == PARTS, starts@.len() == PARTS,
            keys@.len() == cap, auxs@.len() == cap,
            b.len() == PARTS + 1, b[PARTS as int] <= cap, b[PARTS as int] == acc,
            forall|a: int, c2: int| #![trigger b[a], b[c2]] 0 <= a <= c2 <= PARTS ==> b[a] <= b[c2],
            forall|a: int| 0 <= a < PARTS ==> #[trigger] starts@[a] == b[a],
            forall|a: int| 0 <= a < PARTS ==> b[a] <= #[trigger] cursor@[a] && cursor@[a] <= b[a + 1],
            forall|a: int, e: int| #[trigger] filled(b, cursor@, a, e) ==>
                part_of(keys@[e]) == a && src_item(kss, xss, keys@[e], auxs@[e]),
            forall|t: int| 0 <= t < q ==> #[trigger] placed(b, cursor@, keys@, auxs@, kss[t], xss[t]),
        decreases len - q,
    {
        let j = plo + q;
        let k = ad_hash_at(padsh, j, Ghost(cc.m));
        let x = tv_hash_at(ptag, pver, j, Ghost(cc.m));
        let p = part_exec(k);
        let pos = cursor[p];
        let end = if p + 1 < PARTS { starts[p + 1] } else { acc };
        proof {
            assert(end == b[p + 1]);
        }
        if pos >= end {
            return None;
        }
        let ghost keys0 = keys@;
        let ghost auxs0 = auxs@;
        let ghost cur0 = cursor@;
        keys[pos] = k;
        auxs[pos] = x;
        cursor[p] = pos + 1;
        proof {
            assert(kss[q as int] == k && xss[q as int] == x);
            // `pos` is outside the filled part of every other segment.
            assert forall|a: int, e: int| #[trigger] filled(b, cur0, a, e) && a != p as int implies e != pos as int by {
                if a < p as int {
                    assert(b[a + 1] <= b[p as int]);
                } else {
                    assert(b[p as int + 1] <= b[a]);
                }
            }
            assert forall|a: int, e: int| #[trigger] filled(b, cursor@, a, e) implies
                part_of(keys@[e]) == a && src_item(kss, xss, keys@[e], auxs@[e]) by {
                if e == pos as int {
                    if a != p as int {
                        assert(cursor@[a] == cur0[a]);
                        assert(filled(b, cur0, a, e));
                    }
                    assert(src_item(kss, xss, k, x));
                } else {
                    if a == p as int {
                        assert(filled(b, cur0, a, e));
                    } else {
                        assert(cursor@[a] == cur0[a]);
                        assert(filled(b, cur0, a, e));
                    }
                }
            }
            assert forall|t: int| 0 <= t < q + 1 implies #[trigger] placed(b, cursor@, keys@, auxs@, kss[t], xss[t]) by {
                if t == q as int {
                    let a = part_of(kss[t]);
                    assert(a == p as int);
                    assert(keys@[pos as int] == kss[t]);
                    assert(auxs@[pos as int] == xss[t]);
                    assert(filled(b, cursor@, a, pos as int));
                } else {
                    let a = part_of(kss[t]);
                    assert(placed(b, cur0, keys0, auxs0, kss[t], xss[t]));
                    let e = choose|e: int| #[trigger] filled(b, cur0, a, e) && keys0[e] == kss[t] && auxs0[e] == xss[t];
                    if a != p as int {
                        assert(e != pos as int);
                        assert(cursor@[a] == cur0[a]);
                    } else {
                        assert(e < pos as int);
                    }
                    assert(keys@[e] == keys0[e]);
                    assert(auxs@[e] == auxs0[e]);
                    assert(filled(b, cursor@, a, e));
                }
            }
        }
        q = q + 1;
    }
    let o = Parted { keys, auxs, starts, ends: cursor };
    proof {
        assert forall|a: int| 0 <= a < PARTS implies #[trigger] o.starts@[a] <= o.ends@[a] && o.ends@[a] <= o.keys@.len() by {
            assert(b[a + 1] <= b[PARTS as int]);
        }
        assert forall|a: int, e: int| #[trigger] in_seg(o, a, e) implies
            part_of(o.keys@[e]) == a && src_item(kss, xss, o.keys@[e], o.auxs@[e]) by {
            assert(filled(b, cursor@, a, e));
        }
        assert forall|t: int| 0 <= t < kss.len() implies #[trigger] seg_has(o, part_of(kss[t]), kss[t], xss[t]) by {
            let a = part_of(kss[t]);
            assert(placed(b, cursor@, keys@, auxs@, kss[t], xss[t]));
            let e = choose|e: int| #[trigger] filled(b, cursor@, a, e) && keys@[e] == kss[t] && auxs@[e] == xss[t];
            assert(in_seg(o, a, e));
        }
    }
    Some(o)
}

/// `sk[q], sx[q]` = the value hash and the row number of `tag` row `tlo + q`.
fn hash_tag_rows(ttag: &TextCol, tver: &TextCol, tlo: usize, thi: usize, sk: Vec<u64>, sx: Vec<u64>,
    c: Ghost<Ctx>) -> (r: (Vec<u64>, Vec<u64>))
    requires
        ctx_ok(c@), ttag@ == ttag_v(c@), tver@ == tver_v(c@),
        tlo <= thi <= c@.nt, sk@.len() >= thi - tlo, sx@.len() >= thi - tlo,
    ensures
        r.0@.len() == sk@.len(), r.1@.len() == sx@.len(),
        r.0@.subrange(0, thi - tlo) == tag_ks(c@, tlo as int, thi as int),
        r.1@.subrange(0, thi - tlo) == tag_xs(c@, tlo as int, thi as int),
    no_unwind
{
    let ghost cc = c@;
    proof {
        lemma_text_cols_wf(cc);
    }
    let ghost sk_len = sk@.len();
    let ghost sx_len = sx@.len();
    let mut sk = sk;
    let mut sx = sx;
    let len = thi - tlo;
    let mut q: usize = 0;
    while q < len
        invariant
            q <= len, len == thi - tlo, thi <= cc.nt,
            text_wf(ttag@, cc.nt), text_wf(tver@, cc.nt),
            ttag@ == ttag_v(cc), tver@ == tver_v(cc),
            sk@.len() == sk_len, sx@.len() == sx_len, sk@.len() >= len, sx@.len() >= len,
            forall|t: int| 0 <= t < q ==> #[trigger] sk@[t] == tag_tv(cc, tlo + t),
            forall|t: int| 0 <= t < q ==> #[trigger] sx@[t] == (tlo + t) as u64,
        decreases len - q,
    {
        let a = tlo + q;
        let h = tv_hash_at(ttag, tver, a, Ghost(cc.nt));
        sk[q] = h;
        sx[q] = a as u64;
        q = q + 1;
    }
    proof {
        assert(sk@.subrange(0, len as int) =~= tag_ks(cc, tlo as int, thi as int));
        assert(sx@.subrange(0, len as int) =~= tag_xs(cc, tlo as int, thi as int));
    }
    (sk, sx)
}

} // verus!
