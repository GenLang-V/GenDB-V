//! The distinct-count pass: one task per group bucket `b` (group ids `glo .. glo + ng`).
//!
//! 1. gather: the entries of bucket `b` from every part task's region (`gathered`), into `ent`;
//! 2. group them by group id (`common::key_group`): segment `γ` of `rows` lists the part rows of group `glo + γ`;
//! 3. per group, the supplier keys of the partsupp rows `l * a .. l * a + l` of its parts, as offsets
//!    `ps_suppkey - smin` (`seg_vals`), are counted once each unless excluded (`tset`): the bit set `bits` starts as
//!    the excluded offsets (`ebits`), a key is counted when its bit was clear, and afterwards every touched word is
//!    copied back from `ebits`. Keys are loaded in batches of up to 256 (several parts at a time), so the loads of
//!    different parts overlap.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::model::*;
use crate::agent::cols::*;
use crate::agent::parts::PartOut;
use crate::agent::common::key_group::*;
use crate::agent::common::bitset::*;
use vstd::set_lib::set_int_range;

verus! {

/// The offsets of the supplier keys of the partsupp rows of part row `a`.
pub open spec fn row_vals(sk: Seq<i64>, l: int, smin: int, a: int) -> Seq<int> {
    Seq::new(l as nat, |i: int| sk[l * a + i] as int - smin)
}

/// The offsets of the supplier keys of the partsupp rows of the part rows `rows`, in order.
pub open spec fn seg_vals(sk: Seq<i64>, l: int, smin: int, rows: Seq<u32>) -> Seq<int>
    decreases rows.len(),
{
    if rows.len() == 0 { Seq::empty() } else { seg_vals(sk, l, smin, rows.drop_last()) + row_vals(sk, l, smin, rows.last() as int) }
}

/// The distinct offsets of `rows` that are not excluded.
pub open spec fn tset(sk: Seq<i64>, l: int, smin: int, rows: Seq<u32>, eb: Seq<u64>) -> Set<int> {
    seg_vals(sk, l, smin, rows).to_set().filter(|d: int| !bit_at(eb, d))
}

/// The region of bucket `b` of a part task's output.
pub open spec fn region_seq(o: PartOut, b: int) -> Seq<u64> {
    o.buf@.subrange(b * o.cap, b * o.cap + o.boff@[b])
}

/// The entries of bucket `b` of the first `w` part tasks.
pub open spec fn gathered(outs: Seq<PartOut>, b: int, w: int) -> Seq<u64>
    decreases w,
{
    if w <= 0 { Seq::empty() } else { gathered(outs, b, w - 1) + region_seq(outs[w - 1], b) }
}

/// Gathering more part tasks never shortens the entries.
pub proof fn lemma_gathered_mono(outs: Seq<PartOut>, b: int, w1: int, w2: int)
    requires 0 <= w1 <= w2,
    ensures gathered(outs, b, w1).len() <= gathered(outs, b, w2).len(),
    decreases w2 - w1,
{
    if w1 < w2 {
        lemma_gathered_mono(outs, b, w1, w2 - 1);
    }
}

/// The region of bucket `b` fits in the buffer of a part task's output.
pub open spec fn region_fits(o: PartOut, b: int) -> bool {
    &&& 0 <= b < o.boff@.len()
    &&& o.boff@[b] <= o.cap
    &&& b * o.cap + o.cap <= o.buf@.len()
}

/// One group bucket.
pub struct CntTask {
    pub b: usize,
    pub glo: u64,
    pub ng: usize,
    pub m: usize,
    pub c: Cols,
    pub l: usize,
    pub smin: i64,
    pub ins: Arc<Vec<PartOut>>,
    pub ebits: Arc<Vec<u64>>,
    pub ent: Vec<u64>,
    pub ends: Vec<usize>,
    pub rows: Vec<u32>,
    pub bits: Vec<u64>,
    pub scratch: Vec<i64>,
    pub out: Vec<u64>,
    pub sv: Ghost<StoresView>,
}

/// What a task needs.
pub open spec fn cnt_pre(t: CntTask) -> bool {
    let sv = t.sv@;
    let g = gathered(t.ins@, t.b as int, t.ins@.len() as int);
    &&& cols_ok(t.c, sv)
    &&& 1 <= t.l <= 64 && t.c.nq == t.l * t.c.np
    &&& forall|w: int| 0 <= w < t.ins@.len() ==> #[trigger] region_fits(t.ins@[w], t.b as int)
    &&& t.m == g.len()
    &&& t.ng <= 0x400_0000 && t.glo <= 0x400_0000
    &&& t.ebits@.len() < 0x100_0000_0000_0000
    &&& keys_in(g, t.glo as int, t.ng as int)
    &&& forall|i: int| 0 <= i < g.len() ==> #[trigger] evalue(g[i]) < t.c.np
    &&& forall|c: int| 0 <= c < t.c.nq ==> 0 <= #[trigger] t.c.ps_sk@[c] - t.smin && in_bits(t.ebits@, t.c.ps_sk@[c] - t.smin)
    &&& t.ent@.len() >= t.m && t.rows@.len() >= t.m
    &&& t.ends@.len() == t.ng + 1 && forall|k: int| 0 <= k <= t.ng ==> #[trigger] t.ends@[k] == 0
    &&& t.bits@.len() == t.ebits@.len()
    &&& t.scratch@.len() == 256
    &&& t.out@.len() == t.ng
}

/// What a task guarantees: the count of every group of the bucket.
pub open spec fn cnt_post(t: CntTask, out: Vec<u64>) -> bool {
    let g = gathered(t.ins@, t.b as int, t.ins@.len() as int);
    &&& out@.len() == t.ng
    &&& forall|k: int| 0 <= k < t.ng ==> #[trigger] out@[k] == tset(t.c.ps_sk@, t.l as int, t.smin as int,
        kvals(g, t.glo as int, k), t.ebits@).len()
}

/// Gather the entries of bucket `b` of every part task into `ent`.
fn gather(ins: &Vec<PartOut>, b: usize, ent: &mut Vec<u64>, m: usize)
    requires
        forall|w: int| 0 <= w < ins@.len() ==> #[trigger] region_fits(ins@[w], b as int),
        m == gathered(ins@, b as int, ins@.len() as int).len(),
        old(ent)@.len() >= m,
    ensures
        final(ent)@.len() == old(ent)@.len(),
        final(ent)@.take(m as int) == gathered(ins@, b as int, ins@.len() as int),
    no_unwind
{
    let nw = ins.len();
    let mut k: usize = 0;
    let mut w: usize = 0;
    proof { assert(ent@.take(0) =~= gathered(ins@, b as int, 0)); }
    while w < nw
        invariant
            nw == ins@.len(), w <= nw, ent@.len() == old(ent)@.len(), old(ent)@.len() >= m,
            forall|x: int| 0 <= x < ins@.len() ==> #[trigger] region_fits(ins@[x], b as int),
            m == gathered(ins@, b as int, nw as int).len(),
            k == gathered(ins@, b as int, w as int).len(),
            ent@.take(k as int) == gathered(ins@, b as int, w as int),
        decreases nw - w,
    {
        let o = &ins[w];
        proof {
            assert(region_fits(ins@[w as int], b as int));
            assert(gathered(ins@, b as int, w + 1) == gathered(ins@, b as int, w as int) + region_seq(*o, b as int));
            lemma_gathered_mono(ins@, b as int, w + 1, nw as int);
        }
        let blen = o.buf.len();
        let cnt = o.boff[b];
        proof { assert(b * o.cap + o.cap <= blen); }
        let start = b * o.cap;
        let mut x: usize = 0;
        while x < cnt
            invariant
                cnt == o.boff@[b as int], start == b * o.cap, region_fits(*o, b as int), x <= cnt, blen == o.buf@.len(),
                ent@.len() == old(ent)@.len(), k + cnt <= m, m <= ent@.len(),
                ent@.take(k + x) == gathered(ins@, b as int, w as int) + region_seq(*o, b as int).take(x as int),
            decreases cnt - x,
        {
            let e = o.buf[start + x];
            let ghost before = ent@.take(k + x);
            ent[k + x] = e;
            proof {
                assert(ent@.take(k + x + 1) =~= before.push(e));
                assert(region_seq(*o, b as int).take(x + 1) =~= region_seq(*o, b as int).take(x as int).push(e));
            }
            x = x + 1;
        }
        proof {
            assert(region_seq(*o, b as int).take(cnt as int) =~= region_seq(*o, b as int));
        }
        k = k + cnt;
        w = w + 1;
    }
}

/// Copy `src` into `dst` (same length).
fn copy_words(src: &Vec<u64>, dst: &mut Vec<u64>)
    requires old(dst)@.len() == src@.len(),
    ensures final(dst)@ == src@,
    no_unwind
{
    let n = src.len();
    let mut i: usize = 0;
    while i < n
        invariant n == src@.len(), dst@.len() == n, i <= n, forall|j: int| 0 <= j < i ==> dst@[j] == src@[j],
        decreases n - i,
    {
        dst[i] = src[i];
        i = i + 1;
    }
    proof { assert(dst@ =~= src@); }
}

/// `seg_vals` of one more row.
proof fn lemma_seg_push(sk: Seq<i64>, l: int, smin: int, rows: Seq<u32>, a: u32)
    ensures seg_vals(sk, l, smin, rows.push(a)) == seg_vals(sk, l, smin, rows) + row_vals(sk, l, smin, a as int),
{
    assert(rows.push(a).drop_last() =~= rows);
}

/// The length of `seg_vals`.
proof fn lemma_seg_len(sk: Seq<i64>, l: int, smin: int, rows: Seq<u32>)
    requires l >= 0,
    ensures seg_vals(sk, l, smin, rows).len() == rows.len() * l,
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_seg_len(sk, l, smin, rows.drop_last());
        assert(rows.len() * l == (rows.len() - 1) * l + l) by (nonlinear_arith);
    }
}

/// Every offset is a supplier key of some partsupp row, minus `smin`.
pub proof fn lemma_seg_vals_in(sk: Seq<i64>, l: int, smin: int, rows: Seq<u32>, np: int, x: int)
    requires l >= 1, sk.len() == l * np, forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]) < np,
        0 <= x < seg_vals(sk, l, smin, rows).len(),
    ensures exists|c: int| 0 <= c < sk.len() && #[trigger] sk[c] as int - smin == seg_vals(sk, l, smin, rows)[x],
    decreases rows.len(),
{
    let d = rows.drop_last();
    assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i]) < np by { assert(d[i] == rows[i]); }
    lemma_seg_len(sk, l, smin, d);
    if x < seg_vals(sk, l, smin, d).len() {
        lemma_seg_vals_in(sk, l, smin, d, np, x);
        let c = choose|c: int| 0 <= c < sk.len() && #[trigger] sk[c] as int - smin == seg_vals(sk, l, smin, d)[x];
        assert(seg_vals(sk, l, smin, rows)[x] == seg_vals(sk, l, smin, d)[x]);
    } else {
        let i = x - seg_vals(sk, l, smin, d).len();
        let a = rows.last() as int;
        assert(a < np) by { assert(rows.last() == rows[rows.len() - 1]); }
        assert(l * a + i < l * np) by (nonlinear_arith) requires 0 <= i < l, 0 <= a < np, l >= 1;
        assert(0 <= l * a + i) by (nonlinear_arith) requires 0 <= i, 0 <= a, l >= 1;
        assert(seg_vals(sk, l, smin, rows)[x] == row_vals(sk, l, smin, a)[i]);
        assert(sk[l * a + i] as int - smin == seg_vals(sk, l, smin, rows)[x]);
    }
}

/// The offsets of in-range rows all lie in the bit set.
pub proof fn lemma_seg_vals_ok(sk: Seq<i64>, l: int, smin: int, rows: Seq<u32>, np: int, eb: Seq<u64>)
    requires l >= 1, sk.len() == l * np, forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]) < np,
        forall|c: int| 0 <= c < sk.len() ==> 0 <= #[trigger] sk[c] - smin && in_bits(eb, sk[c] - smin),
    ensures forall|x: int| 0 <= x < seg_vals(sk, l, smin, rows).len() ==> 0 <= #[trigger] seg_vals(sk, l, smin, rows)[x]
        && in_bits(eb, seg_vals(sk, l, smin, rows)[x]),
{
    assert forall|x: int| 0 <= x < seg_vals(sk, l, smin, rows).len() implies 0 <= #[trigger] seg_vals(sk, l, smin, rows)[x]
        && in_bits(eb, seg_vals(sk, l, smin, rows)[x]) by {
        lemma_seg_vals_in(sk, l, smin, rows, np, x);
    }
}

/// The distinct non-excluded offsets of a sequence of in-range offsets lie in `0 .. 64 * eb.len()`.
pub proof fn lemma_fresh_bound(vals: Seq<int>, eb: Seq<u64>)
    requires forall|x: int| 0 <= x < vals.len() ==> 0 <= #[trigger] vals[x] && in_bits(eb, vals[x]),
    ensures fresh(vals, eb).len() <= 64 * eb.len(),
{
    let r = set_int_range(0, (64 * eb.len()) as int);
    vstd::set_lib::lemma_int_range(0, (64 * eb.len()) as int);
    assert(fresh(vals, eb).subset_of(r)) by {
        assert forall|d: int| fresh(vals, eb).contains(d) implies r.contains(d) by {
            let x = choose|x: int| 0 <= x < vals.len() && vals[x] == d;
            assert(0 <= vals[x] && in_bits(eb, vals[x]));
        }
    }
    vstd::set_lib::lemma_len_subset(fresh(vals, eb), r);
}

/// The distinct non-excluded offsets of a sequence.
pub open spec fn fresh(vals: Seq<int>, eb: Seq<u64>) -> Set<int> {
    vals.to_set().filter(|d: int| !bit_at(eb, d))
}

/// `fresh` of one more value.
proof fn lemma_fresh_push(vals: Seq<int>, d: int, eb: Seq<u64>)
    ensures fresh(vals.push(d), eb) == if bit_at(eb, d) { fresh(vals, eb) } else { fresh(vals, eb).insert(d) },
{
    assert forall|x: int| fresh(vals.push(d), eb).contains(x) <==>
        (if bit_at(eb, d) { fresh(vals, eb) } else { fresh(vals, eb).insert(d) }).contains(x) by {
        if vals.push(d).contains(x) {
            let j = choose|j: int| 0 <= j < vals.push(d).len() && vals.push(d)[j] == x;
            if j < vals.len() { assert(vals[j] == x); }
        }
        if vals.contains(x) {
            let j = choose|j: int| 0 <= j < vals.len() && vals[j] == x;
            assert(vals.push(d)[j] == x);
        }
        if x == d { assert(vals.push(d)[vals.len() as int] == x); }
    }
    assert(fresh(vals.push(d), eb) =~= if bit_at(eb, d) { fresh(vals, eb) } else { fresh(vals, eb).insert(d) });
}

/// The bits are the excluded offsets plus `seen`.
pub open spec fn bits_seen(bits: Seq<u64>, eb: Seq<u64>, seen: Set<int>) -> bool {
    &&& bits.len() == eb.len()
    &&& forall|p: int| #[trigger] in_bits(eb, p) ==> bit_at(bits, p) == (bit_at(eb, p) || seen.contains(p))
}

/// Count one offset `d`: when its bit is clear (not excluded, not seen), set it and count it.
fn count_one(bits: &mut Vec<u64>, d: u64, cnt: &mut u64, Ghost(eb): Ghost<Seq<u64>>, Ghost(vals): Ghost<Seq<int>>)
    requires
        in_bits(eb, d as int), bits_seen(old(bits)@, eb, fresh(vals, eb)), *old(cnt) == fresh(vals, eb).len(),
        fresh(vals, eb).len() < u64::MAX,
    ensures
        bits_seen(final(bits)@, eb, fresh(vals.push(d as int), eb)), *final(cnt) == fresh(vals.push(d as int), eb).len(),
    no_unwind
{
    let ghost bits0 = bits@;
    let ghost seen = fresh(vals, eb);
    proof { lemma_fresh_push(vals, d as int, eb); }
    let was_clear = test_set(bits, d);
    if was_clear {
        *cnt = *cnt + 1;
        proof {
            assert(!bit_at(eb, d as int) && !seen.contains(d as int));
            assert(seen.insert(d as int).len() == seen.len() + 1);
        }
    }
    proof {
        let seen2 = fresh(vals.push(d as int), eb);
        assert forall|p: int| #[trigger] in_bits(eb, p) implies bit_at(bits@, p) == (bit_at(eb, p) || seen2.contains(p)) by {
            if p != d as int {
                assert(bit_at(bits@, p) == bit_at(bits0, p));
            }
        }
    }
}

/// Copy back the words touched by the values of `row_vals` of rows `rows`, restoring the excluded bits there.
fn restore_rows(c: &Cols, l: usize, smin: i64, rows: &Vec<u32>, s: usize, e: usize, ebits: &Vec<u64>, bits: &mut Vec<u64>,
    Ghost(sv): Ghost<StoresView>, Ghost(seen): Ghost<Set<int>>)
    requires
        cols_ok(*c, sv), 1 <= l <= 64, c.nq == l * c.np, s <= e <= rows@.len(),
        forall|i: int| s <= i < e ==> (#[trigger] rows@[i]) < c.np,
        forall|x: int| 0 <= x < c.nq ==> 0 <= #[trigger] c.ps_sk@[x] - smin && in_bits(ebits@, c.ps_sk@[x] - smin),
        bits_seen(old(bits)@, ebits@, seen),
        seen.subset_of(seg_vals(c.ps_sk@, l as int, smin as int, rows@.subrange(s as int, e as int)).to_set()),
        ebits@.len() < 0x100_0000_0000_0000,
    ensures bits_seen(final(bits)@, ebits@, Set::<int>::empty()),
    no_unwind
{
    let ghost eb = ebits@;
    let ghost sk = c.ps_sk@;
    let ghost all = seg_vals(sk, l as int, smin as int, rows@.subrange(s as int, e as int));
    let mut j = s;
    while j < e
        invariant
            cols_ok(*c, sv), 1 <= l <= 64, c.nq == l * c.np, s <= j <= e <= rows@.len(), eb == ebits@, sk == c.ps_sk@,
            forall|i: int| s <= i < e ==> (#[trigger] rows@[i]) < c.np,
            forall|x: int| 0 <= x < c.nq ==> 0 <= #[trigger] c.ps_sk@[x] - smin && in_bits(ebits@, c.ps_sk@[x] - smin),
            eb.len() < 0x100_0000_0000_0000,
            all == seg_vals(sk, l as int, smin as int, rows@.subrange(s as int, e as int)),
            seen.subset_of(all.to_set()),
            bits@.len() == eb.len(),
            forall|p: int| #[trigger] in_bits(eb, p) ==> bit_at(bits@, p) == (bit_at(eb, p) || (seen.contains(p)
                && !seg_vals(sk, l as int, smin as int, rows@.subrange(s as int, j as int)).to_set().contains(p)
                && forall|q: int| #[trigger] seg_vals(sk, l as int, smin as int, rows@.subrange(s as int, j as int)).to_set().contains(q)
                    ==> q / 64 != p / 64)),
        decreases e - j,
    {
        let a = rows[j] as usize;
        proof { assert(l * a + l <= l * c.np) by (nonlinear_arith) requires a < c.np, l >= 1; }
        let ghost done = seg_vals(sk, l as int, smin as int, rows@.subrange(s as int, j as int));
        let mut i: usize = 0;
        while i < l
            invariant
                cols_ok(*c, sv), 1 <= l <= 64, c.nq == l * c.np, a < c.np, l * a + l <= c.nq, i <= l, eb == ebits@, sk == c.ps_sk@,
                forall|x: int| 0 <= x < c.nq ==> 0 <= #[trigger] c.ps_sk@[x] - smin && in_bits(ebits@, c.ps_sk@[x] - smin),
                eb.len() < 0x100_0000_0000_0000,
                bits@.len() == eb.len(),
                forall|p: int| #[trigger] in_bits(eb, p) ==> bit_at(bits@, p) == (bit_at(eb, p) || (seen.contains(p)
                    && !(done + row_vals(sk, l as int, smin as int, a as int).take(i as int)).to_set().contains(p)
                    && forall|q: int| #[trigger] (done + row_vals(sk, l as int, smin as int, a as int).take(i as int)).to_set().contains(q)
                        ==> q / 64 != p / 64)),
            decreases l - i,
        {
            let v = c.ps_sk[l * a + i];
            let d = (v - smin) as u64;
            let ghost bits0 = bits@;
            let ghost pre = done + row_vals(sk, l as int, smin as int, a as int).take(i as int);
            let ghost post = done + row_vals(sk, l as int, smin as int, a as int).take(i + 1);
            proof {
                assert(post =~= pre.push(d as int));
                assert(in_bits(eb, d as int));
            }
            copy_word(bits, ebits, d);
            proof {
                assert forall|q: int| #[trigger] post.to_set().contains(q) <==> (pre.to_set().contains(q) || q == d as int) by {
                    if post.to_set().contains(q) {
                        let x = choose|x: int| 0 <= x < post.len() && post[x] == q;
                        if x < pre.len() { assert(pre[x] == q); }
                    }
                    if pre.to_set().contains(q) {
                        let x = choose|x: int| 0 <= x < pre.len() && pre[x] == q;
                        assert(post[x] == q);
                    }
                    if q == d as int { assert(post[post.len() - 1] == q); }
                }
                assert forall|p: int| #[trigger] in_bits(eb, p) implies bit_at(bits@, p) == (bit_at(eb, p) || (seen.contains(p)
                    && !post.to_set().contains(p) && forall|q: int| #[trigger] post.to_set().contains(q) ==> q / 64 != p / 64)) by {
                    if p / 64 == d as int / 64 {
                        assert(post.to_set().contains(d as int));
                    } else {
                        assert(bit_at(bits@, p) == bit_at(bits0, p));
                        assert(p != d as int);
                        if forall|q: int| #[trigger] post.to_set().contains(q) ==> q / 64 != p / 64 {
                            assert forall|q: int| #[trigger] pre.to_set().contains(q) implies q / 64 != p / 64 by {
                                assert(post.to_set().contains(q));
                            }
                        }
                        if forall|q: int| #[trigger] pre.to_set().contains(q) ==> q / 64 != p / 64 {
                            assert forall|q: int| #[trigger] post.to_set().contains(q) implies q / 64 != p / 64 by {
                                if q != d as int { assert(pre.to_set().contains(q)); }
                            }
                        }
                    }
                }
            }
            i = i + 1;
        }
        proof {
            assert(row_vals(sk, l as int, smin as int, a as int).take(l as int) =~= row_vals(sk, l as int, smin as int, a as int));
            assert(rows@.subrange(s as int, j + 1) =~= rows@.subrange(s as int, j as int).push(rows@[j as int]));
            lemma_seg_push(sk, l as int, smin as int, rows@.subrange(s as int, j as int), rows@[j as int]);
        }
        j = j + 1;
    }
    proof {
        assert forall|p: int| #[trigger] in_bits(eb, p) implies bit_at(bits@, p) == (bit_at(eb, p) || Set::<int>::empty().contains(p)) by {
            if seen.contains(p) {
                assert(all.to_set().contains(p));
            }
        }
    }
}

/// Count the distinct non-excluded offsets of the part rows `rows[s..e]` (`bits` holds exactly the excluded ones
/// before and after).
fn count_rows(c: &Cols, l: usize, smin: i64, rows: &Vec<u32>, s: usize, e: usize, ebits: &Vec<u64>, bits: &mut Vec<u64>,
    scratch: &mut Vec<i64>, Ghost(sv): Ghost<StoresView>) -> (cnt: u64)
    requires
        cols_ok(*c, sv), 1 <= l <= 64, c.nq == l * c.np, s <= e <= rows@.len(),
        forall|i: int| s <= i < e ==> (#[trigger] rows@[i]) < c.np,
        forall|x: int| 0 <= x < c.nq ==> 0 <= #[trigger] c.ps_sk@[x] - smin && in_bits(ebits@, c.ps_sk@[x] - smin),
        bits_seen(old(bits)@, ebits@, Set::<int>::empty()),
        old(scratch)@.len() == 256,
        ebits@.len() < 0x100_0000_0000_0000,
    ensures
        bits_seen(final(bits)@, ebits@, Set::<int>::empty()),
        final(scratch)@.len() == 256,
        cnt == tset(c.ps_sk@, l as int, smin as int, rows@.subrange(s as int, e as int), ebits@).len(),
    no_unwind
{
    let ghost eb = ebits@;
    let ghost sk = c.ps_sk@;
    let mut cnt: u64 = 0;
    let mut j = s;
    proof {
        assert(rows@.subrange(s as int, s as int) =~= Seq::<u32>::empty());
        assert(seg_vals(sk, l as int, smin as int, Seq::<u32>::empty()).to_set() =~= Set::<int>::empty());
        assert(fresh(seg_vals(sk, l as int, smin as int, rows@.subrange(s as int, s as int)), eb) =~= Set::<int>::empty());
    }
    while j < e
        invariant
            cols_ok(*c, sv), 1 <= l <= 64, c.nq == l * c.np, s <= j <= e <= rows@.len(), eb == ebits@, sk == c.ps_sk@,
            forall|i: int| s <= i < e ==> (#[trigger] rows@[i]) < c.np,
            forall|x: int| 0 <= x < c.nq ==> 0 <= #[trigger] c.ps_sk@[x] - smin && in_bits(ebits@, c.ps_sk@[x] - smin),
            eb.len() < 0x100_0000_0000_0000,
            scratch@.len() == 256,
            bits_seen(bits@, eb, fresh(seg_vals(sk, l as int, smin as int, rows@.subrange(s as int, j as int)), eb)),
            cnt == fresh(seg_vals(sk, l as int, smin as int, rows@.subrange(s as int, j as int)), eb).len(),
        decreases e - j,
    {
        // Fill a batch with the supplier keys of the next parts.
        let j0 = j;
        let mut k: usize = 0;
        while j < e && k + l <= 256
            invariant
                cols_ok(*c, sv), 1 <= l <= 64, c.nq == l * c.np, j0 <= j <= e <= rows@.len(), sk == c.ps_sk@, scratch@.len() == 256,
                forall|i: int| s <= i < e ==> (#[trigger] rows@[i]) < c.np, s <= j0,
                k == (j - j0) * l, k <= 256,
                forall|t: int| 0 <= t < k ==> scratch@[t] as int - smin == #[trigger] seg_vals(sk, l as int, smin as int, rows@.subrange(j0 as int, j as int))[t],
            decreases e - j,
        {
            let a = rows[j] as usize;
            proof { assert(l * a + l <= l * c.np) by (nonlinear_arith) requires a < c.np, l >= 1; }
            let ghost sv0 = seg_vals(sk, l as int, smin as int, rows@.subrange(j0 as int, j as int));
            if l == 4 {
                // The TPC-H layout: the four keys of the part from an exact four-element subslice (no per-key
                // bounds checks, so the loads of the batch's parts issue back to back).
                let (_, tail) = c.ps_sk.split_at(4 * a);
                let (q, _) = tail.split_at(4);
                let ghost s0 = scratch@;
                scratch[k] = q[0];
                scratch[k + 1] = q[1];
                scratch[k + 2] = q[2];
                scratch[k + 3] = q[3];
                proof {
                    assert forall|t: int| 0 <= t < 4 implies #[trigger] q@[t] == sk[4 * a + t] by {
                        assert(q@[t] == tail@[t]);
                    }
                    assert forall|t: int| 0 <= t < k implies scratch@[t] as int - smin == #[trigger] sv0[t] by {
                        assert(scratch@[t] == s0[t]);
                    }
                    assert forall|t: int| 0 <= t < l implies scratch@[k + t] as int - smin
                        == #[trigger] row_vals(sk, l as int, smin as int, a as int)[t] by {
                        assert(q@[t] == sk[4 * a + t]);
                        if t == 0 {} else if t == 1 {} else if t == 2 {} else {}
                    }
                }
            } else {
                let mut i: usize = 0;
                while i < l
                    invariant
                        cols_ok(*c, sv), 1 <= l <= 64, a < c.np, l * a + l <= c.nq, i <= l, k + l <= 256, scratch@.len() == 256, sk == c.ps_sk@,
                        forall|t: int| 0 <= t < k ==> scratch@[t] as int - smin == #[trigger] sv0[t],
                        forall|t: int| 0 <= t < i ==> scratch@[k + t] as int - smin == #[trigger] row_vals(sk, l as int, smin as int, a as int)[t],
                    decreases l - i,
                {
                    scratch[k + i] = c.ps_sk[l * a + i];
                    i = i + 1;
                }
            }
            proof {
                assert(rows@.subrange(j0 as int, j + 1) =~= rows@.subrange(j0 as int, j as int).push(rows@[j as int]));
                lemma_seg_push(sk, l as int, smin as int, rows@.subrange(j0 as int, j as int), rows@[j as int]);
                lemma_seg_len(sk, l as int, smin as int, rows@.subrange(j0 as int, j as int));
                assert((j + 1 - j0) * l == (j - j0) * l + l) by (nonlinear_arith);
            }
            k = k + l;
            j = j + 1;
        }
        proof {
            lemma_seg_len(sk, l as int, smin as int, rows@.subrange(j0 as int, j as int));
            assert(j > j0) by {
                if j == j0 { assert(k == 0); assert(k + l <= 256); }
            }
        }
        // Count the batch.
        let ghost before = seg_vals(sk, l as int, smin as int, rows@.subrange(s as int, j0 as int));
        let ghost batch = seg_vals(sk, l as int, smin as int, rows@.subrange(j0 as int, j as int));
        proof {
            assert forall|i: int| 0 <= i < rows@.subrange(j0 as int, j as int).len() implies (#[trigger] rows@.subrange(j0 as int, j as int)[i]) < c.np by {
                assert(rows@.subrange(j0 as int, j as int)[i] == rows@[j0 + i]);
            }
            assert forall|i: int| 0 <= i < rows@.subrange(s as int, j0 as int).len() implies (#[trigger] rows@.subrange(s as int, j0 as int)[i]) < c.np by {
                assert(rows@.subrange(s as int, j0 as int)[i] == rows@[s + i]);
            }
            lemma_seg_vals_ok(sk, l as int, smin as int, rows@.subrange(j0 as int, j as int), c.np as int, eb);
            lemma_seg_vals_ok(sk, l as int, smin as int, rows@.subrange(s as int, j0 as int), c.np as int, eb);
        }
        let mut t: usize = 0;
        while t < k
            invariant
                t <= k, k == batch.len(), k <= 256, scratch@.len() == 256, eb == ebits@, eb.len() < 0x100_0000_0000_0000,
                forall|x: int| 0 <= x < k ==> scratch@[x] as int - smin == #[trigger] batch[x],
                forall|x: int| 0 <= x < k ==> 0 <= #[trigger] batch[x] && in_bits(eb, batch[x]),
                forall|x: int| 0 <= x < before.len() ==> 0 <= #[trigger] before[x] && in_bits(eb, before[x]),
                bits_seen(bits@, eb, fresh(before + batch.take(t as int), eb)),
                cnt == fresh(before + batch.take(t as int), eb).len(),
            decreases k - t,
        {
            proof {
                let cur = before + batch.take(t as int);
                assert forall|x: int| 0 <= x < cur.len() implies 0 <= #[trigger] cur[x] && in_bits(eb, cur[x]) by {
                    if x < before.len() { assert(cur[x] == before[x]); } else { assert(cur[x] == batch[x - before.len()]); }
                }
                lemma_fresh_bound(cur, eb);
                assert(scratch@[t as int] as int - smin == batch[t as int]);
                assert((before + batch.take(t + 1)) =~= cur.push(batch[t as int]));
            }
            let d = (scratch[t] - smin) as u64;
            count_one(bits, d, &mut cnt, Ghost(eb), Ghost(before + batch.take(t as int)));
            t = t + 1;
        }
        proof {
            assert(batch.take(k as int) =~= batch);
            assert(rows@.subrange(s as int, j as int) =~= rows@.subrange(s as int, j0 as int) + rows@.subrange(j0 as int, j as int));
            lemma_seg_concat(sk, l as int, smin as int, rows@.subrange(s as int, j0 as int), rows@.subrange(j0 as int, j as int));
        }
    }
    let ghost seen = fresh(seg_vals(sk, l as int, smin as int, rows@.subrange(s as int, e as int)), eb);
    proof {
        assert(seen.subset_of(seg_vals(sk, l as int, smin as int, rows@.subrange(s as int, e as int)).to_set()));
    }
    restore_rows(c, l, smin, rows, s, e, ebits, bits, Ghost(sv), Ghost(seen));
    cnt
}

/// `seg_vals` of a concatenation.
proof fn lemma_seg_concat(sk: Seq<i64>, l: int, smin: int, r1: Seq<u32>, r2: Seq<u32>)
    ensures seg_vals(sk, l, smin, r1 + r2) == seg_vals(sk, l, smin, r1) + seg_vals(sk, l, smin, r2),
    decreases r2.len(),
{
    if r2.len() == 0 {
        assert(r1 + r2 =~= r1);
        assert(seg_vals(sk, l, smin, r2) =~= Seq::<int>::empty());
        assert(seg_vals(sk, l, smin, r1) + seg_vals(sk, l, smin, r2) =~= seg_vals(sk, l, smin, r1));
    } else {
        lemma_seg_concat(sk, l, smin, r1, r2.drop_last());
        assert((r1 + r2).drop_last() =~= r1 + r2.drop_last());
        assert((r1 + r2).last() == r2.last());
    }
}

/// Every value of `kvals` is the value of some entry.
pub proof fn lemma_kvals_from(es: Seq<u64>, base: int, k: int, x: int)
    requires 0 <= x < kvals(es, base, k).len(),
    ensures exists|i: int| 0 <= i < es.len() && #[trigger] evalue(es[i]) == kvals(es, base, k)[x],
    decreases es.len(),
{
    let d = es.drop_last();
    lemma_kvals_len(d, base, k);
    if x < kvals(d, base, k).len() {
        lemma_kvals_from(d, base, k, x);
        let i = choose|i: int| 0 <= i < d.len() && #[trigger] evalue(d[i]) == kvals(d, base, k)[x];
        assert(es[i] == d[i]);
    } else {
        assert(evalue(es[es.len() - 1]) == kvals(es, base, k)[x]);
    }
}

impl WorkerTask for CntTask {
    type Output = Vec<u64>;

    open spec fn pre(&self) -> bool {
        cnt_pre(*self)
    }

    open spec fn post(&self, out: Vec<u64>) -> bool {
        cnt_post(*self, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        let hi = if self.ng as u64 <= u64::MAX - self.glo { self.glo + self.ng as u64 } else { u64::MAX };
        (self.glo, hi)
    }

    fn run(self) -> (out: Vec<u64>) {
        let ghost t0 = self;
        let CntTask { b, glo, ng, m, c, l, smin, ins, ebits, mut ent, mut ends, mut rows, mut bits, mut scratch, mut out, sv } = self;
        let ghost sv = sv@;
        let ghost g = gathered(ins@, b as int, ins@.len() as int);
        gather(&ins, b, &mut ent, m);
        copy_words(&ebits, &mut bits);
        group_by_key(&ent, m, glo, ng, &mut ends, &mut rows);
        let ghost es = ent@.take(m as int);
        proof {
            assert(es == g);
            assert(bits_seen(bits@, ebits@, Set::<int>::empty()));
        }
        let mut start: usize = 0;
        let mut k: usize = 0;
        while k < ng
            invariant
                cnt_pre(t0), t0.b == b && t0.glo == glo && t0.ng == ng && t0.m == m && t0.c == c && t0.l == l && t0.smin == smin
                    && t0.ins == ins && t0.ebits == ebits && t0.sv@ == sv,
                g == gathered(ins@, b as int, ins@.len() as int), es == g,
                ends@.len() == ng + 1, rows@.len() >= m, scratch@.len() == 256, out@.len() == ng,
                kstart(es, glo as int, ng as int) == m,
                forall|j: int| 0 <= j < ng ==> #[trigger] ends@[j] == kstart(es, glo as int, j + 1),
                forall|j: int| 0 <= j < ng ==> #[trigger] rows@.subrange(kstart(es, glo as int, j) as int,
                    kstart(es, glo as int, j + 1) as int) == kvals(es, glo as int, j),
                k <= ng, start == kstart(es, glo as int, k as int),
                bits_seen(bits@, ebits@, Set::<int>::empty()), ebits@.len() < 0x100_0000_0000_0000,
                forall|j: int| 0 <= j < k ==> #[trigger] out@[j] == tset(c.ps_sk@, l as int, smin as int, kvals(es, glo as int, j), ebits@).len(),
            decreases ng - k,
        {
            let end = ends[k];
            proof {
                lemma_segment_end(es, glo as int, k as int, ng as int);
                assert(start <= end <= m);
                let seg = rows@.subrange(start as int, end as int);
                assert(seg == kvals(es, glo as int, k as int));
                assert forall|i: int| start <= i < end implies (#[trigger] rows@[i]) < c.np by {
                    assert(rows@[i] == seg[i - start]);
                    lemma_kvals_len(es, glo as int, k as int);
                    lemma_kvals_from(es, glo as int, k as int, i - start);
                    let x = choose|x: int| 0 <= x < es.len() && #[trigger] evalue(es[x]) == kvals(es, glo as int, k as int)[i - start];
                }
            }
            let cnt = count_rows(&c, l, smin, &rows, start, end, &ebits, &mut bits, &mut scratch, Ghost(sv));
            out[k] = cnt;
            start = end;
            k = k + 1;
        }
        out
    }
}

} // verus!
