//! Which rows of a text column hold given segments in order (`match_from`), for a run of rows `lo..hi`, in one pass
//! over their contiguous bytes. The scan looks for a filter literal `g` that every matching row contains
//! (`gram_ok`; a part of one segment, chosen per call as the rarest in a sample, `choose_gram`): windows of 64
//! positions (`find::window_any`, then `find::window_first`) test `g`'s first (up to) four bytes; at a hit the row
//! holding it is evaluated exactly by the greedy matcher (`segments::match_segments`) from its start, and the scan
//! resumes at the row's end.
//!
//! Layout: `offs` are the column's `n + 1` offsets into `bytes` (`offs_wf`), row `x` is `val(offs, bytes, x)`;
//! `flags[x - lo]` is 1 exactly for the matching rows (`flags` zero on entry).
//! Invariant (`scan_inv`, opaque): a set flag is a match; every matching row with an occurrence of `g` that
//! starts before the scan position `p` has its flag set.
use vstd::prelude::*;
use crate::agent::common::find::*;
use crate::agent::common::segments::*;

verus! {

/// Offsets of `n` values in `blen` bytes: non-decreasing, inside the bytes.
pub open spec fn offs_wf(offs: Seq<i64>, n: int, blen: int) -> bool {
    &&& offs.len() == n + 1
    &&& forall|i: int| 0 <= i < n ==> 0 <= #[trigger] offs[i] <= offs[i + 1] <= blen
}

/// The bytes of row `x`.
pub open spec fn val(offs: Seq<i64>, bytes: Seq<u8>, x: int) -> Seq<u8> {
    bytes.subrange(offs[x] as int, offs[x + 1] as int)
}

/// Row `x` holds the segments in order.
pub open spec fn row_match(offs: Seq<i64>, bytes: Seq<u8>, ss: Seq<Seq<u8>>, x: int) -> bool {
    match_from(val(offs, bytes, x), ss, 0)
}

/// The offsets do not decrease.
pub proof fn lemma_offs_mono(offs: Seq<i64>, n: int, blen: int, a: int, b: int)
    requires offs_wf(offs, n, blen), 0 <= a <= b <= n, n >= 1,
    ensures 0 <= offs[a] <= offs[b] <= blen,
    decreases b - a,
{
    if a < b {
        lemma_offs_mono(offs, n, blen, a, b - 1);
        assert(offs[b - 1] <= offs[b]);
    } else if a < n {
        assert(0 <= offs[a] <= offs[a + 1] <= blen);
    } else if n > 0 {
        assert(0 <= offs[n - 1] <= offs[n] <= blen);
    }
}

/// A byte lies in at most one row.
proof fn lemma_row_unique(offs: Seq<i64>, n: int, blen: int, x: int, r: int, t: int)
    requires offs_wf(offs, n, blen), 0 <= x < n, 0 <= r < n, offs[x] <= t < offs[x + 1], offs[r] <= t < offs[r + 1],
    ensures x == r,
{
    if x < r { lemma_offs_mono(offs, n, blen, x + 1, r); }
    if r < x { lemma_offs_mono(offs, n, blen, r + 1, x); }
}

/// An occurrence inside row `x` is an occurrence in the bytes, ending inside the row.
proof fn lemma_occ_in_row(offs: Seq<i64>, bytes: Seq<u8>, n: int, x: int, lit: Seq<u8>, j: int)
    requires offs_wf(offs, n, bytes.len() as int), 0 <= x < n, sub_at(val(offs, bytes, x), lit, j),
    ensures
        occ(bytes, lit, offs[x] + j, offs[x + 1] as int),
        offs[x] <= offs[x] + j < offs[x + 1] || lit.len() == 0,
{
    assert(0 <= offs[x] <= offs[x + 1] <= bytes.len());
    lemma_occ_row(bytes, lit, offs[x] as int, offs[x + 1] as int, offs[x] + j);
}

// ------------------------------------------------------------------------------------------------ the filter literal

/// Every text holding the segments in order holds `g` (the scan's filter literal).
pub open spec fn gram_ok(ss: Seq<Seq<u8>>, g: Seq<u8>) -> bool {
    &&& g.len() >= 1
    &&& forall|t: Seq<u8>| #[trigger] match_from(t, ss, 0) ==> exists|j: int| sub_at(t, g, j)
}

/// A text holding the segments in order from `i` holds each of them at or after `i`.
proof fn lemma_match_holds(t: Seq<u8>, ss: Seq<Seq<u8>>, i: int, k: int)
    requires match_from(t, ss, i), 0 <= k < ss.len(),
    ensures exists|q: int| i <= q && #[trigger] sub_at(t, ss[k], q),
    decreases k,
{
    let q0 = choose|q0: int| i <= q0 && #[trigger] sub_at(t, ss[0], q0) && match_from(t, ss.drop_first(), q0 + ss[0].len());
    if k == 0 {
        assert(i <= q0 && sub_at(t, ss[0], q0));
    } else {
        lemma_match_holds(t, ss.drop_first(), q0 + ss[0].len(), k - 1);
        assert(ss.drop_first()[k - 1] == ss[k]);
        let q = choose|q: int| q0 + ss[0].len() <= q && #[trigger] sub_at(t, ss.drop_first()[k - 1], q);
        assert(i <= q && sub_at(t, ss[k], q));
    }
}

/// A part `ss[k][o .. o + m]` of a segment is a filter literal.
pub proof fn lemma_gram_part(ss: Seq<Seq<u8>>, k: int, o: int, m: int)
    requires 0 <= k < ss.len(), 0 <= o, 1 <= m, o + m <= ss[k].len(),
    ensures gram_ok(ss, ss[k].subrange(o, o + m)),
{
    let g = ss[k].subrange(o, o + m);
    assert forall|t: Seq<u8>| #[trigger] match_from(t, ss, 0) implies exists|j: int| sub_at(t, g, j) by {
        lemma_match_holds(t, ss, 0, k);
        let q = choose|q: int| 0 <= q && #[trigger] sub_at(t, ss[k], q);
        assert(t.subrange(q, q + ss[k].len()) == ss[k]);
        assert(t.subrange(q + o, q + o + m) =~= g) by {
            assert forall|i: int| 0 <= i < m implies #[trigger] t.subrange(q + o, q + o + m)[i] == g[i] by {
                assert(t.subrange(q, q + ss[k].len())[o + i] == ss[k][o + i]);
            }
        }
        assert(sub_at(t, g, q + o));
    }
}

/// Positions `[0, s)` of the sample where `pf`'s bytes occur (`pf` masks: bytes past a short literal match).
fn sample_hits(bytes: &[u8], nbytes: usize, s: usize, pf: &Prefix) -> (cnt: usize)
    requires nbytes == bytes@.len(), s + 3 <= nbytes,
    no_unwind
{
    let mut cnt: usize = 0;
    let mut q: usize = 0;
    while q < s
        invariant s + 3 <= nbytes, nbytes == bytes@.len(), q <= s, cnt <= q,
        decreases s - q,
    {
        if bytes[q] == pf.c0 && (bytes[q + 1] & pf.k1) == pf.c1 && (bytes[q + 2] & pf.k2) == pf.c2
            && (bytes[q + 3] & pf.k3) == pf.c3 {
            cnt = cnt + 1;
        }
        q = q + 1;
    }
    cnt
}

/// Bytes of the column sampled to choose the filter literal.
pub const SAMPLE: usize = 65536;

/// The scan's filter literal: its comparison pattern, and whether it is the part of the first segment at byte
/// `off` (then a hit at `q` starts the greedy match at `q - off`; otherwise at the row's start).
#[derive(Clone, Copy)]
pub struct Gram {
    pub pf: Prefix,
    pub first: bool,
    pub off: usize,
}

/// `gr` is the filter literal `g` of the segments `ss`.
pub open spec fn gram_view_ok(gr: Gram, ss: Seq<Seq<u8>>, g: Seq<u8>) -> bool {
    &&& gram_ok(ss, g) && prefix_ok(gr.pf, g)
    &&& ss.len() >= 1
    &&& gr.first ==> gr.off + g.len() <= ss[0].len() && g == ss[0].subrange(gr.off as int, gr.off + g.len())
}

/// The bytes `lit[o .. o + m]`.
fn part_of(lit: &Vec<u8>, o: usize, m: usize) -> (part: Vec<u8>)
    requires o + m <= lit@.len(),
    ensures part@ == lit@.subrange(o as int, (o + m) as int),
{
    let n = lit.len();
    let mut part: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant i <= m, o + m <= lit@.len(), n == lit@.len(), part@ == lit@.subrange(o as int, (o + i) as int),
        decreases m - i,
    {
        part.push(lit[o + i]);
        i = i + 1;
        proof { assert(part@ =~= lit@.subrange(o as int, (o + i) as int)); }
    }
    part
}

/// The fewest sample hits of a part `lit[o .. o + m]` (`m = min(4, |lit|)`), and its offset.
fn rarest_part(bytes: &[u8], nbytes: usize, smp: usize, lit: &Vec<u8>) -> (r: (usize, usize))
    requires nbytes == bytes@.len(), smp == 0 || smp + 3 <= nbytes, lit@.len() >= 1,
    ensures r.1 + (if lit@.len() < 4 { lit@.len() } else { 4 }) <= lit@.len(),
{
    let len = lit.len();
    let m = if len < 4 { len } else { 4 };
    let mut best: usize = usize::MAX;
    let mut bo: usize = 0;
    let mut o: usize = 0;
    while m <= len - o
        invariant
            nbytes == bytes@.len(), smp == 0 || smp + 3 <= nbytes, len == lit@.len(), 1 <= m <= 4, m <= len,
            m == (if len < 4 { len } else { 4 }), bo + m <= len, o <= len,
        decreases len - o,
    {
        let part = part_of(lit, o, m);
        let pf = prefix_of(&part, m);
        let h = if smp > 0 { sample_hits(bytes, nbytes, smp, &pf) } else { 0 };
        if h < best {
            best = h;
            bo = o;
        }
        o = o + 1;
    }
    (best, bo)
}

/// The filter literal of the scan: the part (`min(4, |s|)` bytes) of a segment `s` that occurs least often in
/// the first `SAMPLE` bytes of the column. A part of the first segment is preferred (a hit then starts the
/// greedy match inside the row, not at its start) unless a later segment's part has under a quarter of its hits.
pub fn choose_gram(bytes: &[u8], nbytes: usize, s: &Segs, Ghost(ss): Ghost<Seq<Seq<u8>>>) -> (r: (Gram, Ghost<Seq<u8>>))
    requires nbytes == bytes@.len(), segs_view_ok(s, ss),
    ensures gram_view_ok(r.0, ss, r.1@),
{
    let ns = s.bytes.len();
    let smp = if nbytes >= SAMPLE + 3 { SAMPLE } else { 0 };
    proof {
        assert forall|k: int| 0 <= k < ns implies #[trigger] s.bytes@[k]@.len() >= 1 by {
            assert(seg_ok(ss[k]));
        }
    }
    let (h0, o0) = rarest_part(bytes, nbytes, smp, &s.bytes[0]);
    // the rarest part of a later segment: segment `bk`, offset `bo`, `best` hits
    let mut best: usize = usize::MAX;
    let mut bk: usize = 0;
    let mut bo: usize = 0;
    let mut k: usize = 1;
    while k < ns
        invariant
            segs_view_ok(s, ss), ns == ss.len(), 1 <= k <= ns, nbytes == bytes@.len(), smp == 0 || smp + 3 <= nbytes,
            forall|k2: int| 0 <= k2 < ns ==> #[trigger] s.bytes@[k2]@.len() >= 1,
            best < usize::MAX ==> 1 <= bk < ns
                && bo + (if ss[bk as int].len() < 4 { ss[bk as int].len() } else { 4 }) <= ss[bk as int].len(),
        decreases ns - k,
    {
        let (h, o) = rarest_part(bytes, nbytes, smp, &s.bytes[k]);
        proof { assert(s.bytes@[k as int]@ == ss[k as int]); }
        if h < best {
            best = h;
            bk = k;
            bo = o;
        }
        k = k + 1;
    }
    let later = best < usize::MAX && (best as u128) * 4 < (h0 as u128);
    let (k, o) = if later { (bk, bo) } else { (0usize, o0) };
    let lit = &s.bytes[k];
    proof { assert(lit@ == ss[k as int]); }
    let len = s.lens[k];
    let m = if len < 4 { len } else { 4 };
    let part = part_of(lit, o, m);
    let pf = prefix_of(&part, m);
    proof { lemma_gram_part(ss, k as int, o as int, m as int); }
    (Gram { pf, first: !later, off: o }, Ghost(part@))
}

// ------------------------------------------------------------------------------------------------ the scan

/// The scan invariant at position `p` (see the module header).
#[verifier::opaque]
pub open spec fn scan_inv(offs: Seq<i64>, bytes: Seq<u8>, lo: int, hi: int, g: Seq<u8>, ss: Seq<Seq<u8>>, flags: Seq<u8>,
    p: int) -> bool
{
    &&& forall|x: int| lo <= x < hi && #[trigger] flags[x - lo] != 0u8 ==> row_match(offs, bytes, ss, x)
    &&& forall|x: int, j: int| lo <= x < hi && #[trigger] sub_at(val(offs, bytes, x), g, j) && offs[x] + j < p
            && row_match(offs, bytes, ss, x) ==> flags[x - lo] != 0u8
}

/// No occurrence of the filter literal starts in `[p, p2)`: the invariant moves to `p2`.
proof fn lemma_skip(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, g: Seq<u8>, ss: Seq<Seq<u8>>,
    flags: Seq<u8>, p: int, p2: int)
    requires
        offs_wf(offs, n, bytes.len() as int), 0 <= lo <= hi <= n, g.len() >= 1, p <= p2,
        scan_inv(offs, bytes, lo, hi, g, ss, flags, p),
        forall|q: int| p <= q < p2 ==> !#[trigger] pre4(bytes, q, g),
    ensures scan_inv(offs, bytes, lo, hi, g, ss, flags, p2),
{
    reveal(scan_inv);
    assert forall|x: int, j: int| lo <= x < hi && #[trigger] sub_at(val(offs, bytes, x), g, j) && offs[x] + j < p2
        && row_match(offs, bytes, ss, x) implies flags[x - lo] != 0u8 by {
        if offs[x] + j >= p {
            lemma_occ_in_row(offs, bytes, n, x, g, j);
            lemma_occ_pre4(bytes, g, offs[x] + j, offs[x + 1] as int);
        }
    }
}

/// A hit at `q` in row `r` (no occurrence of the filter literal in `[p, q)`): with row `r`'s flag set when `mm`
/// (which implies the row matches, and holds when it matches and its flag is not set yet), the invariant moves to
/// the row's end.
proof fn lemma_hit(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, g: Seq<u8>, ss: Seq<Seq<u8>>,
    f0: Seq<u8>, f1: Seq<u8>, p: int, q: int, r: int, mm: bool)
    requires
        offs_wf(offs, n, bytes.len() as int), 0 <= lo <= r < hi <= n, g.len() >= 1, p <= q,
        offs[r] <= q < offs[r + 1],
        scan_inv(offs, bytes, lo, hi, g, ss, f0, p),
        forall|t: int| p <= t < q ==> !#[trigger] pre4(bytes, t, g),
        mm ==> row_match(offs, bytes, ss, r),
        row_match(offs, bytes, ss, r) ==> mm || f0[r - lo] != 0u8,
        f1.len() == f0.len(), hi - lo <= f0.len(),
        f1[r - lo] == (if mm { 1u8 } else { f0[r - lo] }),
        forall|x: int| lo <= x < hi && x != r ==> #[trigger] f1[x - lo] == f0[x - lo],
    ensures scan_inv(offs, bytes, lo, hi, g, ss, f1, offs[r + 1] as int),
{
    reveal(scan_inv);
    assert forall|x: int| lo <= x < hi && #[trigger] f1[x - lo] != 0u8 implies row_match(offs, bytes, ss, x) by {
        if x != r { assert(f1[x - lo] == f0[x - lo]); }
    }
    assert forall|x: int, j: int| lo <= x < hi && #[trigger] sub_at(val(offs, bytes, x), g, j)
        && offs[x] + j < offs[r + 1] && row_match(offs, bytes, ss, x) implies f1[x - lo] != 0u8 by {
        lemma_occ_in_row(offs, bytes, n, x, g, j);
        if offs[x] + j < p {
            assert(f0[x - lo] != 0u8);
            if x != r { assert(f1[x - lo] == f0[x - lo]); }
        } else {
            lemma_occ_pre4(bytes, g, offs[x] + j, offs[x + 1] as int);
            assert(offs[x] + j >= q);
            lemma_row_unique(offs, n, bytes.len() as int, x, r, offs[x] + j);
        }
    }
}

/// An occurrence of a segment holds an occurrence of each of its parts.
proof fn lemma_sub_part(v: Seq<u8>, s: Seq<u8>, t: int, o: int, m: int)
    requires sub_at(v, s, t), 0 <= o, o + m <= s.len(), m >= 0,
    ensures sub_at(v, s.subrange(o, o + m), t + o),
{
    assert(v.subrange(t + o, t + o + m) =~= s.subrange(o, o + m)) by {
        assert forall|i: int| 0 <= i < m implies #[trigger] v.subrange(t + o, t + o + m)[i] == s.subrange(o, o + m)[i] by {
            assert(v.subrange(t, t + s.len())[o + i] == s[o + i]);
        }
    }
}

/// A hit at `q` in row `r` for the part of the first segment at byte `off`: the greedy match from `q - off`
/// (inside the row) decides the row unless its flag is set already (an occurrence of the first segment before
/// `q - off` would put an occurrence of the filter literal before `q`: before `p`, where the invariant set the
/// flag of a matching row, or in `[p, q)`, where there is none).
proof fn lemma_first_seg(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, g: Seq<u8>, ss: Seq<Seq<u8>>,
    f0: Seq<u8>, p: int, q: int, r: int, off: int)
    requires
        offs_wf(offs, n, bytes.len() as int), 0 <= lo <= r < hi <= n, g.len() >= 1, p <= q, ss.len() >= 1,
        offs[r] <= q - off, q < offs[r + 1], 0 <= off, off + g.len() <= ss[0].len(),
        g == ss[0].subrange(off, off + g.len()),
        scan_inv(offs, bytes, lo, hi, g, ss, f0, p),
        forall|t: int| p <= t < q ==> !#[trigger] pre4(bytes, t, g),
    ensures
        match_from(val(offs, bytes, r), ss, q - off - offs[r]) ==> row_match(offs, bytes, ss, r),
        row_match(offs, bytes, ss, r) ==> match_from(val(offs, bytes, r), ss, q - off - offs[r]) || f0[r - lo] != 0u8,
{
    reveal(scan_inv);
    let v = val(offs, bytes, r);
    let i0 = q - off - offs[r];
    if match_from(v, ss, i0) {
        lemma_match_mono(v, ss, 0, i0);
    }
    if row_match(offs, bytes, ss, r) && f0[r - lo] == 0u8 {
        assert forall|t: int| 0 <= t < i0 implies !#[trigger] sub_at(v, ss[0], t) by {
            if sub_at(v, ss[0], t) {
                lemma_sub_part(v, ss[0], t, off, g.len() as int);
                lemma_occ_in_row(offs, bytes, n, r, g, t + off);
                if offs[r] + t + off >= p {
                    lemma_occ_pre4(bytes, g, offs[r] + t + off, offs[r + 1] as int);
                }
            }
        }
        lemma_match_skip(v, ss, 0, i0);
    }
}

/// The row holding byte `q`: the first row from the cursor `r` whose end is past `q`.
fn row_of(offs: &[i64], hi: usize, r: usize, q: usize, Ghost(n): Ghost<int>, Ghost(blen): Ghost<int>) -> (r2: usize)
    requires offs_wf(offs@, n, blen), r < hi <= n, offs@[r as int] <= q < offs@[hi as int],
    ensures r <= r2 < hi, offs@[r2 as int] <= q < offs@[r2 + 1],
    no_unwind
{
    let ghost offv = offs@;
    let mut x = r;
    loop
        invariant offs_wf(offv, n, blen), offv == offs@, r <= x < hi <= n, offv[x as int] <= q < offv[hi as int],
        decreases hi - x,
    {
        proof {
            assert(0 <= offv[x as int] <= offv[x + 1] <= blen);
        }
        let nx = offs[x + 1];
        if (q as i64) < nx {
            return x;
        }
        proof {
            if x + 1 == hi { assert(false); }
        }
        x = x + 1;
    }
}

/// OR of the bytes `a..b` (branch-free over a sub-slice, so it vectorizes): ASCII exactly when every byte is.
pub fn or_range(bytes: &[u8], a: usize, b: usize) -> (r: u8)
    requires a <= b <= bytes@.len(),
    ensures (r < 0x80u8) == (forall|q: int| a <= q < b ==> #[trigger] bytes@[q] < 0x80u8),
    no_unwind
{
    let (_, tail) = bytes.split_at(a);
    let (run, _) = tail.split_at(b - a);
    assert(run@ =~= bytes@.subrange(a as int, b as int));
    let n = b - a;
    let mut acc: u8 = 0;
    let mut q: usize = 0;
    while q < n
        invariant
            q <= n, n == run@.len(), run@ == bytes@.subrange(a as int, b as int), a <= b <= bytes@.len(),
            (acc < 0x80u8) == (forall|t: int| a <= t < a + q ==> #[trigger] bytes@[t] < 0x80u8),
        decreases n - q,
    {
        proof { lemma_or_ascii(acc, run@[q as int]); }
        acc = acc | run[q];
        q = q + 1;
    }
    acc
}

/// The scan state at byte `p`: the cursor row `r` starts at or before `p`, and the invariant holds at `p`.
pub open spec fn state_ok(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, g: Seq<u8>, ss: Seq<Seq<u8>>,
    flags: Seq<u8>, p: int, r: int) -> bool
{
    &&& offs_wf(offs, n, bytes.len() as int) && lo < hi <= n && ss.len() >= 1 && segs_ok(ss) && g.len() >= 1
    &&& hi - lo <= flags.len()
    &&& offs[lo] <= p && offs[hi] <= bytes.len()
    &&& lo <= r < hi && offs[r] <= p
    &&& scan_inv(offs, bytes, lo, hi, g, ss, flags, p)
}

/// One step of the scan from `p < offs[hi]`: a window of 64 positions (or one byte near the end of the buffer),
/// then at a hit the row holding it, evaluated from its start. Returns the new position and cursor.
fn scan_step(offs: &[i64], bytes: &[u8], nbytes: usize, n: usize, lo: usize, hi: usize, s: &Segs, gr: &Gram,
    flags: &mut Vec<u8>, p: usize, r: usize, Ghost(g): Ghost<Seq<u8>>, Ghost(ss): Ghost<Seq<Seq<u8>>>)
    -> (out: (usize, usize))
    requires
        nbytes == bytes@.len(), segs_view_ok(s, ss), gram_view_ok(*gr, ss, g),
        state_ok(offs@, bytes@, n as int, lo as int, hi as int, g, ss, old(flags)@, p as int, r as int),
        p < offs@[hi as int],
    ensures
        final(flags)@.len() == old(flags)@.len(),
        p < out.0 <= nbytes,
        state_ok(offs@, bytes@, n as int, lo as int, hi as int, g, ss, final(flags)@, out.0 as int, out.1 as int),
    no_unwind
{
    let ghost offv = offs@;
    let ghost bv = bytes@;
    let pf = &gr.pf;
    let e = offs[hi] as usize;
    let c0 = pf.c0;
    // `j`: no occurrence starts in `[p, p + j)`; `j == w` when the window `[p, p + w)` holds none
    let (j, w) = if nbytes - p >= 67 {
        if window_any(bytes, p, pf, Ghost(g)) {
            (window_first(bytes, p, pf, Ghost(g)), 64usize)
        } else {
            (64usize, 64usize)
        }
    } else {
        let b = bytes[p];
        proof {
            if b != c0 {
                assert forall|t: int| p <= t < p + 1 implies !#[trigger] pre4(bv, t, g) by {
                    if pre4(bv, t, g) { assert(bv[t + 0] == g[0]); }
                }
            }
        }
        (if b == c0 { 0usize } else { 1usize }, 1usize)
    };
    proof {
        assert(j <= w);
        assert(forall|t: int| p <= t < p + j ==> !#[trigger] pre4(bv, t, g));
    }
    if j >= w {
        proof { lemma_skip(offv, bv, n as int, lo as int, hi as int, g, ss, flags@, p as int, (p + w) as int); }
        return (p + w, r);
    }
    let q = p + j;
    if q >= e {
        proof { lemma_skip(offv, bv, n as int, lo as int, hi as int, g, ss, flags@, p as int, q as int); }
        return (q, r);
    }
    let r2 = row_of(offs, hi, r, q, Ghost(n as int), Ghost(nbytes as int));
    proof { assert(0 <= offv[r2 as int] <= offv[r2 + 1] <= nbytes); }
    let b = offs[r2 + 1] as usize;
    let rs = offs[r2] as usize;
    // the greedy match starts where the filter literal's segment would start, or at the row's start
    let from = if gr.first && q - rs >= gr.off { q - gr.off } else { rs };
    let mm = match_segments(bytes, nbytes, from, b, s, Ghost(rs as int), Ghost(ss));
    proof {
        if gr.first && q - rs >= gr.off {
            lemma_first_seg(offv, bv, n as int, lo as int, hi as int, g, ss, flags@, p as int, q as int, r2 as int,
                gr.off as int);
        }
    }
    let ghost f0 = flags@;
    if mm {
        flags[r2 - lo] = 1u8;
    }
    proof {
        lemma_hit(offv, bv, n as int, lo as int, hi as int, g, ss, f0, flags@, p as int, q as int, r2 as int, mm);
    }
    (b, r2)
}

/// The invariant at the run's first byte (no flag set yet).
proof fn lemma_start(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, g: Seq<u8>, ss: Seq<Seq<u8>>,
    flags: Seq<u8>)
    requires
        offs_wf(offs, n, bytes.len() as int), 0 <= lo < hi <= n, g.len() >= 1, hi - lo <= flags.len(),
        forall|i: int| 0 <= i < flags.len() ==> #[trigger] flags[i] == 0u8,
    ensures scan_inv(offs, bytes, lo, hi, g, ss, flags, offs[lo] as int),
{
    reveal(scan_inv);
    assert forall|x: int, j: int| lo <= x < hi && #[trigger] sub_at(val(offs, bytes, x), g, j) && offs[x] + j < offs[lo]
        && row_match(offs, bytes, ss, x) implies flags[x - lo] != 0u8 by {
        lemma_occ_in_row(offs, bytes, n, x, g, j);
        lemma_offs_mono(offs, n, bytes.len() as int, lo, x);
    }
    assert forall|x: int| lo <= x < hi && #[trigger] flags[x - lo] != 0u8 implies row_match(offs, bytes, ss, x) by {
        assert(flags[x - lo] == 0u8);
    }
}

/// The invariant at the run's end: the flags are exactly the matching rows (a matching row holds the filter
/// literal, `gram_ok`).
proof fn lemma_end(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int, g: Seq<u8>, ss: Seq<Seq<u8>>,
    flags: Seq<u8>, p: int)
    requires
        offs_wf(offs, n, bytes.len() as int), 0 <= lo < hi <= n, gram_ok(ss, g), offs[hi] <= p,
        scan_inv(offs, bytes, lo, hi, g, ss, flags, p),
    ensures forall|x: int| lo <= x < hi ==> (#[trigger] flags[x - lo] != 0u8) == row_match(offs, bytes, ss, x),
{
    reveal(scan_inv);
    assert forall|x: int| lo <= x < hi implies (#[trigger] flags[x - lo] != 0u8) == row_match(offs, bytes, ss, x) by {
        if row_match(offs, bytes, ss, x) {
            let v = val(offs, bytes, x);
            assert(match_from(v, ss, 0));
            let jj = choose|jj: int| sub_at(v, g, jj);
            lemma_occ_in_row(offs, bytes, n, x, g, jj);
            lemma_offs_mono(offs, n, bytes.len() as int, x + 1, hi);
        }
    }
}

/// ASCII bytes over the run's bytes make every row of the run ASCII.
pub proof fn lemma_rows_ascii(offs: Seq<i64>, bytes: Seq<u8>, n: int, lo: int, hi: int)
    requires
        offs_wf(offs, n, bytes.len() as int), 0 <= lo < hi <= n,
        forall|t: int| offs[lo] <= t < offs[hi] ==> #[trigger] bytes[t] < 0x80u8,
    ensures forall|x: int| lo <= x < hi ==> #[trigger] ascii(val(offs, bytes, x)),
{
    assert forall|x: int| lo <= x < hi implies #[trigger] ascii(val(offs, bytes, x)) by {
        lemma_offs_mono(offs, n, bytes.len() as int, lo, x);
        lemma_offs_mono(offs, n, bytes.len() as int, x + 1, hi);
        assert(offs[x] <= offs[x + 1]);
        let v = val(offs, bytes, x);
        assert forall|i: int| 0 <= i < v.len() implies #[trigger] v[i] < 0x80u8 by {
            assert(v[i] == bytes[offs[x] + i]);
        }
    }
}

/// Flags of the rows `lo..hi` holding the segments in order: `flags[x - lo]` is 1 exactly for those rows (zero
/// flags on entry). `gr` is the filter literal `g`.
pub fn match_flags(offs: &[i64], bytes: &[u8], nbytes: usize, n: usize, lo: usize, hi: usize, s: &Segs, gr: &Gram,
    flags: &mut Vec<u8>, Ghost(g): Ghost<Seq<u8>>, Ghost(ss): Ghost<Seq<Seq<u8>>>)
    requires
        offs_wf(offs@, n as int, nbytes as int), nbytes == bytes@.len(), lo < hi <= n, segs_view_ok(s, ss),
        gram_view_ok(*gr, ss, g),
        hi - lo <= old(flags)@.len(),
        forall|i: int| 0 <= i < old(flags)@.len() ==> #[trigger] old(flags)@[i] == 0u8,
    ensures
        final(flags)@.len() == old(flags)@.len(),
        forall|x: int| lo <= x < hi ==> (#[trigger] final(flags)@[x - lo] != 0u8) == row_match(offs@, bytes@, ss, x),
    no_unwind
{
    let ghost offv = offs@;
    let ghost bv = bytes@;
    let ghost nf = flags@.len();
    proof {
        lemma_offs_mono(offv, n as int, nbytes as int, lo as int, hi as int);
        lemma_start(offv, bv, n as int, lo as int, hi as int, g, ss, flags@);
    }
    let s0 = offs[lo] as usize;
    let e = offs[hi] as usize;
    let mut p = s0;
    let mut r = lo;
    while p < e
        invariant
            offv == offs@, bv == bytes@, nbytes == bv.len(), segs_view_ok(s, ss), gram_view_ok(*gr, ss, g),
            flags@.len() == nf, e == offv[hi as int], p <= nbytes,
            state_ok(offv, bv, n as int, lo as int, hi as int, g, ss, flags@, p as int, r as int),
        decreases nbytes - p,
    {
        let (p2, r2) = scan_step(offs, bytes, nbytes, n, lo, hi, s, gr, flags, p, r, Ghost(g), Ghost(ss));
        p = p2;
        r = r2;
    }
    proof {
        lemma_end(offv, bv, n as int, lo as int, hi as int, g, ss, flags@, p as int);
    }
}

} // verus!
