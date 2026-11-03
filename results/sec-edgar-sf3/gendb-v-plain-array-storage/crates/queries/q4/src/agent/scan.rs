//! P4: the contributions of num rows `lo..hi` (`contrib`): for each num row in row order with `uom = $1` and an
//! adsh with a selected sub row, one record `(num row, entry, value)` per pre entry with the same adsh, tag and
//! version, in entry order (= pre row order).
//!
//! Per row (`num_row`): the cheap filter first (the adsh hash against the sub bitmap, or `uom`, whichever the
//! caller sampled as more selective), then the sub row, then the entry bitmap and the walk of the entry chain of
//! `mix((tag, version) hash, sub row)`; entries compare their sub row, hash, tag and version. A task stops before a
//! row whose records do not fit (`stopped`); the calling thread finishes the range (`scan_serial`).
//!
//! Tasks run in blocks of `BLK` rows (`scan_block`), one tight loop per stage; before each stage that reads
//! scattered rows, a gather loop loads only the text offsets (adsh for B, tag and version for C, uom for D) or the
//! chain heads and values (D) of the surviving rows into scratch lists (`gather_offs`, `gather_c`, `gather_d`), so
//! that the cache misses of many rows are in flight at once; the stage then slices the bytes from those offsets
//! (`col_offs`, `offs_ok`, `heads_ok` state what the lists hold).
use vstd::prelude::*;
use std::sync::Arc;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::hash::*;
use crate::agent::common::chains::*;
use crate::agent::common::text::*;
use crate::agent::common::buf::Buf;
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::pre::pre_tv_hash;
use crate::agent::sub::*;
use crate::agent::ents::*;

verus! {

/// Num row `i` takes part: `uom = $1` and its adsh has a selected sub row.
pub open spec fn num_sel(c: Ctx, i: int) -> bool {
    n_uom(c, i) == c.uom && has_sub(c, n_adsh(c, i))
}

/// Entry `e` matches num row `i`: same adsh, tag and version, and the num row takes part.
pub open spec fn ent_match(c: Ctx, ents: Seq<(usize, usize, usize)>, i: int, e: int) -> bool {
    let l = ents[e].0 as int;
    &&& num_sel(c, i)
    &&& p_adsh(c, l) == n_adsh(c, i) && p_tag(c, l) == n_tag(c, i) && p_ver(c, l) == n_ver(c, i)
}

/// The records `(i, e, value)` of the entries `e < x` matching num row `i`, in entry order.
pub open spec fn recs(c: Ctx, ents: Seq<(usize, usize, usize)>, i: int, x: int) -> Seq<(usize, usize, i128)>
    decreases x,
{
    if x <= 0 {
        Seq::empty()
    } else {
        recs(c, ents, i, x - 1) + if ent_match(c, ents, i, x - 1) {
            seq![(i as usize, (x - 1) as usize, n_val_s(c)[i])]
        } else {
            Seq::<(usize, usize, i128)>::empty()
        }
    }
}

/// The records of num row `i`.
pub open spec fn row_out(c: Ctx, ents: Seq<(usize, usize, usize)>, i: int) -> Seq<(usize, usize, i128)> {
    recs(c, ents, i, ents.len() as int)
}

/// The records of num rows `lo..hi`, in row order.
pub open spec fn contrib(c: Ctx, ents: Seq<(usize, usize, usize)>, lo: int, hi: int) -> Seq<(usize, usize, i128)>
    decreases hi - lo,
{
    if hi <= lo { Seq::empty() } else { contrib(c, ents, lo, hi - 1) + row_out(c, ents, hi - 1) }
}

pub proof fn lemma_contrib_split(c: Ctx, ents: Seq<(usize, usize, usize)>, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures contrib(c, ents, lo, hi) == contrib(c, ents, lo, mid) + contrib(c, ents, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_contrib_split(c, ents, lo, mid, hi - 1);
        assert(contrib(c, ents, lo, hi) =~= contrib(c, ents, lo, mid) + contrib(c, ents, mid, hi));
    } else {
        assert(contrib(c, ents, mid, hi) =~= Seq::<(usize, usize, i128)>::empty());
        assert(contrib(c, ents, lo, hi) =~= contrib(c, ents, lo, mid) + contrib(c, ents, mid, hi));
    }
}

/// No entry in `x..y` matches: the records below `y` are those below `x`.
proof fn lemma_recs_skip(c: Ctx, ents: Seq<(usize, usize, usize)>, i: int, x: int, y: int)
    requires 0 <= x <= y, forall|e: int| x <= e < y ==> !#[trigger] ent_match(c, ents, i, e),
    ensures recs(c, ents, i, y) == recs(c, ents, i, x),
    decreases y - x,
{
    if y > x {
        lemma_recs_skip(c, ents, i, x, y - 1);
        assert(recs(c, ents, i, y) =~= recs(c, ents, i, y - 1));
    }
}

/// At most `x` records below `x`.
proof fn lemma_recs_len(c: Ctx, ents: Seq<(usize, usize, usize)>, i: int, x: int)
    ensures recs(c, ents, i, x).len() <= if x < 0 { 0 } else { x },
    decreases x,
{
    if x > 0 {
        lemma_recs_len(c, ents, i, x - 1);
    }
}

/// One entry more.
proof fn lemma_recs_step(c: Ctx, ents: Seq<(usize, usize, usize)>, i: int, x: int)
    requires 0 <= x,
    ensures recs(c, ents, i, x + 1) == if ent_match(c, ents, i, x) {
        recs(c, ents, i, x).push((i as usize, x as usize, n_val_s(c)[i]))
    } else {
        recs(c, ents, i, x)
    },
{
    assert(recs(c, ents, i, x + 1) =~= if ent_match(c, ents, i, x) {
        recs(c, ents, i, x).push((i as usize, x as usize, n_val_s(c)[i]))
    } else {
        recs(c, ents, i, x)
    });
}

/// The columns and indexes the num scan reads; `adsh_first` picks the filter order (performance only).
pub struct NumScan {
    pub n_uom: TextCol,
    pub n_adsh: TextCol,
    pub n_tag: TextCol,
    pub n_ver: TextCol,
    pub n_val: &'static [i128],
    pub uom: &'static [u8],
    pub uom_len: usize,
    pub sx: Arc<SubIndex>,
    pub ex: Arc<Entries>,
    pub adsh_first: bool,
}

#[verifier::opaque]
pub open spec fn num_scan_ok(s: &NumScan, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& s.n_uom@ == n_uom_v(c) && s.n_adsh@ == n_adsh_v(c) && s.n_tag@ == n_tag_v(c) && s.n_ver@ == n_ver_v(c)
    &&& s.n_val@ == n_val_s(c)
    &&& text_wf(s.n_uom@, c.n) && text_wf(s.n_adsh@, c.n) && text_wf(s.n_tag@, c.n) && text_wf(s.n_ver@, c.n)
    &&& s.n_val@.len() == c.n
    &&& s.uom@ == c.uom && s.uom_len == c.uom.len()
    &&& sub_index_ok(&*s.sx, c)
    &&& ents_index_ok(&*s.ex, c)
}

/// The records of row `i` after `old` give `new` when `done`; otherwise nothing was added.
pub open spec fn row_done(c: Ctx, ents: Seq<(usize, usize, usize)>, i: int, old: Seq<(usize, usize, i128)>,
    new: Seq<(usize, usize, i128)>, done: bool) -> bool
{
    if done { new == old + row_out(c, ents, i) } else { new == old }
}

/// No entry has the probe hash of row `i` (with sub row `j`): the row has no records.
proof fn lemma_no_entry(s: &NumScan, c: Ctx, i: int, j: usize, h: u64)
    requires
        num_scan_ok(s, c), 0 <= i < c.n, sub_of(c, j as int, n_adsh(c, i)),
        h == key_hash(pair_hash_spec(1, n_tag(c, i), n_ver(c, i)), j),
        forall|e: int| 0 <= e < s.ex.chains.hashes@.len() ==> #[trigger] s.ex.chains.hashes@[e] != h,
    ensures recs(c, s.ex.list@, i, s.ex.list@.len() as int) == Seq::<(usize, usize, i128)>::empty(),
{
    reveal(num_scan_ok);
    let ents = s.ex.list@;
    assert forall|e: int| 0 <= e < ents.len() implies !#[trigger] ent_match(c, ents, i, e) by {
        if ent_match(c, ents, i, e) {
            lemma_match_key(s, c, i, j, e);
        }
    }
    lemma_recs_skip(c, ents, i, 0, ents.len() as int);
    assert(recs(c, ents, i, 0) =~= Seq::<(usize, usize, i128)>::empty());
}

/// A matching entry has the sub row of the num row and its probe hash; an entry with that sub row, tag and
/// version matches (when the num row takes part).
proof fn lemma_match_key(s: &NumScan, c: Ctx, i: int, j: usize, e: int)
    requires num_scan_ok(s, c), 0 <= i < c.n, sub_of(c, j as int, n_adsh(c, i)), 0 <= e < s.ex.list@.len(),
    ensures
        ent_match(c, s.ex.list@, i, e) ==> s.ex.list@[e].1 == j
            && s.ex.chains.hashes@[e] == key_hash(pair_hash_spec(1, n_tag(c, i), n_ver(c, i)), j),
        (num_sel(c, i) && s.ex.list@[e].1 == j && p_tag(c, s.ex.list@[e].0 as int) == n_tag(c, i)
            && p_ver(c, s.ex.list@[e].0 as int) == n_ver(c, i)) ==> ent_match(c, s.ex.list@, i, e),
{
    reveal(num_scan_ok);
    let ents = s.ex.list@;
    let ss = sel_in(c, 0, c.npre);
    let (l, je, k) = ents[e];
    assert(l as int == ss[e]);
    assert(sub_of(c, je as int, p_adsh(c, l as int)));
    if ent_match(c, ents, i, e) {
        lemma_sub_unique(c, je as int, j as int, n_adsh(c, i));
    }
}

/// Entry `e` matches num row `i` (whose sub row is `j`, tag `t`, version `v`, probe hash `h`).
fn entry_hit(s: &NumScan, i: usize, j: usize, t: &[u8], tl: usize, v: &[u8], vl: usize, h: u64, e: usize,
    Ghost(c): Ghost<Ctx>) -> (hit: bool)
    requires
        num_scan_ok(s, c), (i as int) < c.n, num_sel(c, i as int), sub_of(c, j as int, n_adsh(c, i as int)),
        t@ == n_tag(c, i as int), v@ == n_ver(c, i as int), tl == t@.len(), vl == v@.len(),
        h == key_hash(pair_hash_spec(1, t@, v@), j), (e as int) < s.ex.list@.len(),
    ensures hit == ent_match(c, s.ex.list@, i as int, e as int),
    no_unwind
{
    proof { reveal(num_scan_ok); }
    let x: &Entries = &*s.ex;
    let (l, ej, k) = x.list[e];
    let mut hit = false;
    proof {
        lemma_match_key(s, c, i as int, j, e as int);
    }
    if x.chains.hashes[e] == h && ej == j {
        // The entry's tag row has its pre row's tag and version (`ents_ok`); the tag table's copies of the few
        // distinct tag rows stay in cache, unlike one copy per pre row.
        proof {
            let ss = sel_in(c, 0, c.npre);
            assert(l as int == ss[e as int]);
            lemma_sel_mem(c, 0, c.npre, e as int);
            lemma_views(c);
            assert(tag_of(c, k as int, p_tag(c, l as int), p_ver(c, l as int)));
        }
        let (pt, ptl) = text_val(&x.t_tag, k, Ghost(c.nt));
        let (pv, pvl) = text_val(&x.t_ver, k, Ghost(c.nt));
        hit = bytes_eq(pt, ptl, t, tl) && bytes_eq(pv, pvl, v, vl);
    }
    hit
}

/// The walk of the entry chain of `h` for num row `i` (sub row `j`): every matching entry's record onto `out`,
/// in entry order, when they fit (`true`); otherwise `out` is unchanged (`false`).
fn walk_entries(s: &NumScan, i: usize, j: usize, t: &[u8], tl: usize, v: &[u8], vl: usize, h: u64,
    e_start: usize, val: i128, out: &mut Buf<(usize, usize, i128)>, Ghost(c): Ghost<Ctx>) -> (done: bool)
    requires
        num_scan_ok(s, c), (i as int) < c.n, num_sel(c, i as int), sub_of(c, j as int, n_adsh(c, i as int)),
        t@ == n_tag(c, i as int), v@ == n_ver(c, i as int), tl == t@.len(), vl == v@.len(),
        h == key_hash(pair_hash_spec(1, t@, v@), j), old(out).wf(),
        e_start == enc(first_of(s.ex.chains.hashes@, s.ex.chains.shift, bucket_of(h, s.ex.chains.shift), 0)),
        val == n_val_s(c)[i as int],
    ensures
        final(out).wf(), final(out).capacity() == old(out).capacity(),
        row_done(c, s.ex.list@, i as int, old(out).view(), final(out).view(), done),
        old(out).view().len() + s.ex.list@.len() < old(out).capacity() ==> done,
    no_unwind
{
    proof { reveal(num_scan_ok); }
    let x: &Entries = &*s.ex;
    let ghost ents = x.list@;
    let ghost iv = i as int;
    let ghost o0 = out.view();
    let len0 = out.len();
    let cap = out.cap();
    let ghost hs = x.chains.hashes@;
    let ghost n = hs.len() as int;
    let ghost b = bucket_of(h, x.chains.shift);
    let mut e = e_start;
    let ghost mut pos: int = 0;
    proof {
        assert(o0 + recs(c, ents, iv, 0) =~= o0);
    }
    while e != NONE
        invariant
            num_scan_ok(s, c), x == &*s.ex, ents == x.list@, hs == x.chains.hashes@, n == hs.len(), n == ents.len(),
            chains_wf(&x.chains),
            (i as int) < c.n, iv == i as int, num_sel(c, iv), sub_of(c, j as int, n_adsh(c, iv)),
            t@ == n_tag(c, iv), v@ == n_ver(c, iv), tl == t@.len(), vl == v@.len(), val == n_val_s(c)[iv],
            h == key_hash(pair_hash_spec(1, t@, v@), j), b == bucket_of(h, x.chains.shift),
            0 <= pos <= n, e == enc(first_of(hs, x.chains.shift, b, pos)),
            out.wf(), cap == out.capacity(), out.capacity() == old(out).capacity(), o0 == old(out).view(),
            len0 == o0.len(),
            out.view() == o0 + recs(c, ents, iv, pos),
        decreases n - pos,
    {
        proof {
            lemma_first_of(hs, x.chains.shift, b, pos);
            assert forall|e2: int| pos <= e2 < e as int implies !#[trigger] ent_match(c, ents, iv, e2) by {
                lemma_match_key(s, c, iv, j, e2);
            }
            lemma_recs_skip(c, ents, iv, pos, e as int);
            lemma_recs_step(c, ents, iv, e as int);
        }
        let ghost e0 = e as int;
        let hit = entry_hit(s, i, j, t, tl, v, vl, h, e, Ghost(c));
        if hit {
            if out.len() >= cap {
                out.truncate_to(len0);
                proof {
                    assert(out.view() =~= o0);
                    lemma_recs_len(c, ents, iv, e0);
                }
                return false;
            }
            out.push((i, e, val));
            proof {
                assert(out.view() =~= o0 + recs(c, ents, iv, e0 + 1));
            }
        }
        e = chain_next(&x.chains, e);
        proof {
            pos = e0 + 1;
        }
    }
    proof {
        lemma_first_of(hs, x.chains.shift, b, pos);
        assert forall|e2: int| pos <= e2 < n implies !#[trigger] ent_match(c, ents, iv, e2) by {
            lemma_match_key(s, c, iv, j, e2);
        }
        lemma_recs_skip(c, ents, iv, pos, n);
    }
    true
}

/// A row that does not take part has no records.
proof fn lemma_row_empty(s: &NumScan, c: Ctx, i: int)
    requires num_scan_ok(s, c), !num_sel(c, i),
    ensures recs(c, s.ex.list@, i, s.ex.list@.len() as int) == Seq::<(usize, usize, i128)>::empty(),
{
    reveal(num_scan_ok);
    let ents = s.ex.list@;
    assert forall|e: int| 0 <= e < ents.len() implies !#[trigger] ent_match(c, ents, i, e) by {}
    lemma_recs_skip(c, ents, i, 0, ents.len() as int);
    assert(recs(c, ents, i, 0) =~= Seq::<(usize, usize, i128)>::empty());
}

/// A row whose adsh hash is absent from the sub bitmap has no records.
proof fn lemma_row_empty_nosub(s: &NumScan, c: Ctx, i: int, a: Seq<u8>, ha: u64)
    requires
        num_scan_ok(s, c), a == n_adsh(c, i), ha == text_hash_spec(0, a),
        forall|e: int| 0 <= e < s.sx.chains.hashes@.len() ==> #[trigger] s.sx.chains.hashes@[e] != ha,
    ensures recs(c, s.ex.list@, i, s.ex.list@.len() as int) == Seq::<(usize, usize, i128)>::empty(),
{
    reveal(num_scan_ok);
    reveal(sub_rows_ok);
    if has_sub(c, a) {
        let sr = choose|sr: int| #[trigger] sub_of(c, sr, a);
        assert(sub_sel(c, sr));
        let q = choose|q: int| 0 <= q < s.sx.rows@.len() && s.sx.rows@[q] == sr;
        assert(s.sx.chains.hashes@[q] == ha);
    }
    lemma_row_empty(s, c, i);
}

// ------------------------------------------------------------------------------------------------ blocks
//
// A task scans its rows in blocks of `BLK` rows, each in four tight loops so that the cache misses of different
// rows overlap: (A) the cheap first filter over the block, (B) the sub row and `uom` of the rows kept by A,
// (C) the probe hash and the entry bitmap of the rows kept by B, (D) the entry walk of the rows kept by C, pushing
// their records. Each filter keeps, in increasing order, every row of the block that has records (`rows_in`,
// `keeps`), so the records of the block are those of the rows kept by C (`lemma_block`).

/// Rows per block.
pub const BLK: usize = 512;

/// The records of the rows `l`, in order.
pub open spec fn cat_rows(c: Ctx, ents: Seq<(usize, usize, usize)>, l: Seq<usize>) -> Seq<(usize, usize, i128)>
    decreases l.len(),
{
    if l.len() == 0 { Seq::empty() } else { cat_rows(c, ents, l.drop_last()) + row_out(c, ents, l.last() as int) }
}

/// `l` is strictly increasing within `lo..hi`.
pub open spec fn rows_in(l: Seq<usize>, lo: int, hi: int) -> bool {
    &&& forall|x: int| 0 <= x < l.len() ==> lo <= #[trigger] l[x] < hi
    &&& forall|x: int, y: int| 0 <= x < y < l.len() ==> #[trigger] l[x] < #[trigger] l[y]
}

/// Every row of `lo..hi` with records is in `l`.
pub open spec fn keeps(c: Ctx, ents: Seq<(usize, usize, usize)>, l: Seq<usize>, lo: int, hi: int) -> bool {
    forall|i: int| lo <= i < hi && (#[trigger] row_out(c, ents, i)).len() > 0 ==> l.contains(i as usize)
}

/// The records of `lo..hi` are those of the kept rows.
proof fn lemma_block(c: Ctx, ents: Seq<(usize, usize, usize)>, l: Seq<usize>, lo: int, hi: int)
    requires 0 <= lo <= hi, hi <= usize::MAX, rows_in(l, lo, hi), keeps(c, ents, l, lo, hi),
    ensures contrib(c, ents, lo, hi) == cat_rows(c, ents, l),
    decreases hi - lo,
{
    if hi == lo {
        if l.len() > 0 {
            assert(lo <= l[0] < hi);
        }
        assert(contrib(c, ents, lo, hi) =~= Seq::<(usize, usize, i128)>::empty());
    } else if l.len() > 0 && l.last() as int == hi - 1 {
        let l2 = l.drop_last();
        assert forall|x: int| 0 <= x < l2.len() implies lo <= #[trigger] l2[x] < hi - 1 by {
            assert(l2[x] == l[x]);
            assert(l[x] < l[l.len() - 1]);
        }
        assert forall|x: int, y: int| 0 <= x < y < l2.len() implies #[trigger] l2[x] < #[trigger] l2[y] by {
            assert(l2[x] == l[x] && l2[y] == l[y]);
        }
        assert forall|i: int| lo <= i < hi - 1 && (#[trigger] row_out(c, ents, i)).len() > 0 implies l2.contains(i as usize) by {
            let w = choose|w: int| 0 <= w < l.len() && l[w] == i as usize;
            assert(w != l.len() - 1);
            assert(l2[w] == l[w]);
        }
        lemma_block(c, ents, l2, lo, hi - 1);
    } else {
        assert forall|x: int| 0 <= x < l.len() implies lo <= #[trigger] l[x] < hi - 1 by {
            if x < l.len() - 1 {
                assert(l[x] < l[l.len() - 1]);
            }
        }
        if row_out(c, ents, hi - 1).len() > 0 {
            assert(l.contains((hi - 1) as usize));
            let w = choose|w: int| 0 <= w < l.len() && l[w] == (hi - 1) as usize;
            assert(l[w] as int == hi - 1);
            assert(l[w] < hi - 1);
        }
        assert(row_out(c, ents, hi - 1) =~= Seq::<(usize, usize, i128)>::empty());
        lemma_block(c, ents, l, lo, hi - 1);
        assert(contrib(c, ents, lo, hi) =~= contrib(c, ents, lo, hi - 1) + row_out(c, ents, hi - 1));
    }
}

/// One row more in a filtered list: a kept row extends the list, a dropped one (without records) does not.
proof fn lemma_filter_step(c: Ctx, ents: Seq<(usize, usize, usize)>, kept: Seq<usize>, rest: Seq<usize>, i: usize,
    keep: bool, lo: int, hi: int)
    requires
        0 <= lo, hi <= usize::MAX, rest.len() > 0, rest[0] == i, keeps(c, ents, kept + rest, lo, hi),
        !keep ==> row_out(c, ents, i as int).len() == 0,
    ensures keeps(c, ents, (if keep { kept.push(i) } else { kept }) + rest.drop_first(), lo, hi),
{
    let nk = if keep { kept.push(i) } else { kept };
    let r2 = rest.drop_first();
    assert forall|i2: int| lo <= i2 < hi && (#[trigger] row_out(c, ents, i2)).len() > 0 implies (nk + r2).contains(i2 as usize) by {
        let w = choose|w: int| 0 <= w < (kept + rest).len() && (kept + rest)[w] == i2 as usize;
        if w < kept.len() {
            assert((nk + r2)[w] == kept[w]);
        } else if w == kept.len() {
            assert(rest[0] == i);
            assert((kept + rest)[w] == rest[0]);
            assert(i2 == i as int);
            assert(keep);
            assert((nk + r2)[w] == i);
        } else {
            let w2 = if keep { w } else { w - 1 };
            assert((kept + rest)[w] == rest[w - kept.len()]);
            assert(r2[w - kept.len() - 1] == rest[w - kept.len()]);
            assert((nk + r2)[w2] == r2[w - kept.len() - 1]);
        }
    }
}

/// The cheap first filter of row `i`: `false` only when the row has no records.
fn pre_filter(s: &NumScan, i: usize, Ghost(c): Ghost<Ctx>) -> (pass: bool)
    requires num_scan_ok(s, c), (i as int) < c.n,
    ensures !pass ==> row_out(c, s.ex.list@, i as int).len() == 0,
    no_unwind
{
    proof { reveal(num_scan_ok); }
    if s.adsh_first {
        let (a, al) = text_val(&s.n_adsh, i, Ghost(c.n));
        let ha = text_hash(0, a, al);
        let r = may_contain(&s.sx.chains, ha);
        if !r {
            proof {
                lemma_row_empty_nosub(s, c, i as int, a@, ha);
            }
        }
        r
    } else {
        // The length from the offsets alone rejects most rows without touching the bytes.
        if text_len(&s.n_uom, i, Ghost(c.n)) != s.uom_len {
            proof {
                lemma_row_empty(s, c, i as int);
            }
            return false;
        }
        let (u, ul) = text_val(&s.n_uom, i, Ghost(c.n));
        let r = bytes_eq(u, ul, s.uom, s.uom_len);
        if !r {
            proof {
                lemma_row_empty(s, c, i as int);
            }
        }
        r
    }
}



/// The selected sub row of row `i`'s adsh (bytes `a .. b`), `NONE` (and no records) when there is none.
fn sub_row_at(s: &NumScan, i: usize, a: usize, b: usize, Ghost(c): Ghost<Ctx>) -> (j: usize)
    requires
        num_scan_ok(s, c), (i as int) < c.n,
        a as int == s.n_adsh@.offsets[i as int], b as int == s.n_adsh@.offsets[i + 1],
    ensures
        j != NONE ==> sub_of(c, j as int, n_adsh(c, i as int)),
        j == NONE ==> row_out(c, s.ex.list@, i as int).len() == 0,
    no_unwind
{
    proof {
        reveal(num_scan_ok);
        assert(s.n_adsh.bytes@ == s.n_adsh@.bytes);
    }
    let (x, xl) = bytes_range(s.n_adsh.bytes, a, b);
    proof {
        assert(x@ == n_adsh(c, i as int));
    }
    let ha = text_hash(0, x, xl);
    let j = sub_find(&*s.sx, x, xl, ha, Ghost(c));
    if j == NONE {
        proof {
            lemma_row_empty(s, c, i as int);
        }
        return NONE;
    }
    j
}

/// Row `i` has `uom = $1` (its uom is bytes `a .. b`); `false`: no records.
fn uom_ok_at(s: &NumScan, i: usize, a: usize, b: usize, Ghost(c): Ghost<Ctx>) -> (r: bool)
    requires
        num_scan_ok(s, c), (i as int) < c.n,
        a as int == s.n_uom@.offsets[i as int], b as int == s.n_uom@.offsets[i + 1],
    ensures r == (n_uom(c, i as int) == c.uom), !r ==> row_out(c, s.ex.list@, i as int).len() == 0,
    no_unwind
{
    proof {
        reveal(num_scan_ok);
        assert(s.n_uom.bytes@ == s.n_uom@.bytes);
    }
    let (u, ul) = bytes_range(s.n_uom.bytes, a, b);
    proof {
        assert(u@ == n_uom(c, i as int));
    }
    let r = bytes_eq(u, ul, s.uom, s.uom_len);
    if !r {
        proof {
            lemma_row_empty(s, c, i as int);
        }
    }
    r
}

/// The text columns of the num scan are well formed (`num_scan_ok` is hidden).
proof fn lemma_scan_cols(s: &NumScan, c: Ctx)
    requires num_scan_ok(s, c),
    ensures text_wf(s.n_adsh@, c.n), text_wf(s.n_uom@, c.n),
{
    reveal(num_scan_ok);
}

/// The rows of a block list lie in the block.
proof fn lemma_rows_bound(l: Seq<usize>, k: int, lo: int, hi: int)
    requires 0 <= k <= l.len(), rows_in(l.subrange(0, k), lo, hi),
    ensures forall|x: int| 0 <= x < k ==> lo <= (#[trigger] l[x] as int) < hi,
{
    assert forall|x: int| 0 <= x < k implies lo <= (#[trigger] l[x] as int) < hi by {
        assert(l.subrange(0, k)[x] == l[x]);
    }
}


/// `ta[x] .. tb[x]` and `va[x] .. vb[x]` are the tag and version byte ranges of row `l[x]`, for `x < k`.
pub open spec fn offs_ok(s: &NumScan, l: Seq<usize>, ta: Seq<usize>, tb: Seq<usize>, va: Seq<usize>, vb: Seq<usize>,
    k: int) -> bool
{
    forall|x: int| 0 <= x < k ==> {
        &&& #[trigger] ta[x] as int == s.n_tag@.offsets[l[x] as int] && tb[x] as int == s.n_tag@.offsets[l[x] + 1]
        &&& va[x] as int == s.n_ver@.offsets[l[x] as int] && vb[x] as int == s.n_ver@.offsets[l[x] + 1]
    }
}

/// The probe hash of row `i` with sub row `j` (its tag and version are bytes `ta .. tb` and `va .. vb`), and
/// whether the entry bitmap may hold it (`false`: no records).
fn probe_key_at(s: &NumScan, i: usize, j: usize, ta: usize, tb: usize, va: usize, vb: usize, Ghost(c): Ghost<Ctx>)
    -> (r: (bool, u64))
    requires
        num_scan_ok(s, c), (i as int) < c.n, sub_of(c, j as int, n_adsh(c, i as int)),
        ta as int == s.n_tag@.offsets[i as int], tb as int == s.n_tag@.offsets[i + 1],
        va as int == s.n_ver@.offsets[i as int], vb as int == s.n_ver@.offsets[i + 1],
    ensures
        r.1 == key_hash(pair_hash_spec(1, n_tag(c, i as int), n_ver(c, i as int)), j),
        !r.0 ==> row_out(c, s.ex.list@, i as int).len() == 0,
    no_unwind
{
    proof {
        reveal(num_scan_ok);
        assert(s.n_tag.bytes@ == s.n_tag@.bytes && s.n_ver.bytes@ == s.n_ver@.bytes);
    }
    let (t, tl) = bytes_range(s.n_tag.bytes, ta, tb);
    let (v, vl) = bytes_range(s.n_ver.bytes, va, vb);
    proof {
        assert(t@ == n_tag(c, i as int));
        assert(v@ == n_ver(c, i as int));
    }
    let tvh = pair_hash(1, t, tl, v, vl);
    let h = mix(tvh, j as u64);
    let keep = may_contain(&s.ex.chains, h);
    if !keep {
        proof {
            lemma_no_entry(s, c, i as int, j, h);
        }
    }
    (keep, h)
}

/// (C, first loop) The tag and version offsets of the rows `s2[0..k2]`: independent loads, all issued before any
/// value byte is read, so that their cache misses overlap.
#[verifier::spinoff_prover]
fn gather_c(s: &NumScan, b0: usize, b1: usize, s2: &Vec<usize>, k2: usize, ta: &mut Vec<usize>, tb: &mut Vec<usize>,
    va: &mut Vec<usize>, vb: &mut Vec<usize>, Ghost(c): Ghost<Ctx>)
    requires
        num_scan_ok(s, c), b0 <= b1, (b1 as int) <= c.n, s2@.len() == BLK, k2 <= BLK,
        rows_in(s2@.subrange(0, k2 as int), b0 as int, b1 as int),
        old(ta)@.len() == BLK, old(tb)@.len() == BLK, old(va)@.len() == BLK, old(vb)@.len() == BLK,
    ensures
        final(ta)@.len() == BLK, final(tb)@.len() == BLK, final(va)@.len() == BLK, final(vb)@.len() == BLK,
        offs_ok(s, s2@, final(ta)@, final(tb)@, final(va)@, final(vb)@, k2 as int),
    no_unwind
{
    proof { reveal(num_scan_ok); }
    let ghost l = s2@.subrange(0, k2 as int);
    let ghost n = c.n;
    let mut q: usize = 0;
    while q < k2
        invariant
            (b1 as int) <= n, s2@.len() == BLK, k2 <= BLK, q <= k2,
            l == s2@.subrange(0, k2 as int), rows_in(l, b0 as int, b1 as int),
            text_wf(s.n_tag@, n), text_wf(s.n_ver@, n),
            ta@.len() == BLK, tb@.len() == BLK, va@.len() == BLK, vb@.len() == BLK,
            offs_ok(s, s2@, ta@, tb@, va@, vb@, q as int),
        decreases k2 - q,
    {
        let i = s2[q];
        proof {
            assert(l[q as int] == i);
            assert(i < b1);
        }
        let t0 = s.n_tag.offsets[i];
        let t1 = s.n_tag.offsets[i + 1];
        let v0 = s.n_ver.offsets[i];
        let v1 = s.n_ver.offsets[i + 1];
        proof {
            assert(s.n_tag@.offsets[i as int] == t0 && s.n_tag@.offsets[i + 1] == t1);
            assert(s.n_ver@.offsets[i as int] == v0 && s.n_ver@.offsets[i + 1] == v1);
            assert(0 <= t0 && 0 <= t1 && 0 <= v0 && 0 <= v1);
            // The offsets are at most the byte lengths, which are `usize` slice lengths.
            assert(s.n_tag.bytes@.len() == s.n_tag.bytes.len() as int && s.n_tag@.bytes == s.n_tag.bytes@);
            assert(s.n_ver.bytes@.len() == s.n_ver.bytes.len() as int && s.n_ver@.bytes == s.n_ver.bytes@);
            assert(t1 <= s.n_tag@.bytes.len() && v1 <= s.n_ver@.bytes.len());
        }
        let ghost ta0 = ta@;
        let ghost tb0 = tb@;
        let ghost va0 = va@;
        let ghost vb0 = vb@;
        crate::gendb_entry::work::put(ta, q, t0 as usize);
        crate::gendb_entry::work::put(tb, q, t1 as usize);
        crate::gendb_entry::work::put(va, q, v0 as usize);
        crate::gendb_entry::work::put(vb, q, v1 as usize);
        proof {
            assert forall|x: int| 0 <= x < q + 1 implies {
                &&& #[trigger] ta@[x] as int == s.n_tag@.offsets[s2@[x] as int] && tb@[x] as int == s.n_tag@.offsets[s2@[x] + 1]
                &&& va@[x] as int == s.n_ver@.offsets[s2@[x] as int] && vb@[x] as int == s.n_ver@.offsets[s2@[x] + 1]
            } by {
                if x < q {
                    assert(ta@[x] == ta0[x] && tb@[x] == tb0[x] && va@[x] == va0[x] && vb@[x] == vb0[x]);
                } else {
                    assert(s2@[x] == i);
                }
            }
        }
        q = q + 1;
    }
}

/// `hd[x]` is the first entry of the probe chain of hash `hs[x]` and `vals[x]` the value of row `l[x]`, for `x < k`.
pub open spec fn heads_ok(s: &NumScan, c: Ctx, l: Seq<usize>, hs: Seq<u64>, hd: Seq<usize>, vals: Seq<i128>, k: int)
    -> bool
{
    forall|x: int| 0 <= x < k ==> #[trigger] hd[x] == enc(first_of(s.ex.chains.hashes@, s.ex.chains.shift,
        bucket_of(hs[x], s.ex.chains.shift), 0)) && vals[x] == n_val_s(c)[l[x] as int]
}

/// (D, first loop) The chain heads and values of the rows `l[0..k]` (probe hashes `hs`): independent loads, all
/// issued before the chains are walked.
#[verifier::spinoff_prover]
fn gather_d(s: &NumScan, l: &Vec<usize>, hs: &Vec<u64>, k: usize, hd: &mut Vec<usize>, vals: &mut Vec<i128>,
    Ghost(c): Ghost<Ctx>)
    requires
        num_scan_ok(s, c), k <= l@.len(), k <= hs@.len(), k <= old(hd)@.len(), k <= old(vals)@.len(),
        forall|x: int| 0 <= x < k ==> (#[trigger] l@[x] as int) < c.n,
    ensures
        final(hd)@.len() == old(hd)@.len(), final(vals)@.len() == old(vals)@.len(),
        heads_ok(s, c, l@, hs@, final(hd)@, final(vals)@, k as int),
    no_unwind
{
    proof { reveal(num_scan_ok); }
    let x: &Entries = &*s.ex;
    let mut q: usize = 0;
    while q < k
        invariant
            x == &*s.ex, chains_wf(&x.chains), s.n_val@ == n_val_s(c), s.n_val@.len() == c.n,
            k <= l@.len(), k <= hs@.len(), k <= hd@.len(), k <= vals@.len(),
            hd@.len() == old(hd)@.len(), vals@.len() == old(vals)@.len(),
            forall|y: int| 0 <= y < k ==> (#[trigger] l@[y] as int) < c.n,
            q <= k, heads_ok(s, c, l@, hs@, hd@, vals@, q as int),
        decreases k - q,
    {
        let i = l[q];
        let e = chain_start(&x.chains, hs[q]);
        let v = s.n_val[i];
        let ghost hd0 = hd@;
        let ghost vals0 = vals@;
        crate::gendb_entry::work::put(hd, q, e);
        crate::gendb_entry::work::put(vals, q, v);
        proof {
            assert forall|y: int| 0 <= y < q + 1 implies #[trigger] hd@[y] == enc(first_of(s.ex.chains.hashes@,
                s.ex.chains.shift, bucket_of(hs@[y], s.ex.chains.shift), 0)) && vals@[y] == n_val_s(c)[l@[y] as int] by {
                if y < q {
                    assert(hd@[y] == hd0[y] && vals@[y] == vals0[y]);
                }
            }
        }
        q = q + 1;
    }
}

/// The scratch lists of a block (`BLK` slots each).
pub struct Scratch {
    pub s1: Vec<usize>,
    pub s2: Vec<usize>,
    pub s2j: Vec<usize>,
    pub s3: Vec<usize>,
    pub s3j: Vec<usize>,
    pub s3h: Vec<u64>,
    /// The tag and version offsets of the rows of `s2` (stage C).
    pub ta: Vec<usize>,
    pub tb: Vec<usize>,
    pub va: Vec<usize>,
    pub vb: Vec<usize>,
    /// The adsh offsets of the rows of `s1` (stage B), then the uom offsets of the rows of `s3` (stage D).
    pub aa: Vec<usize>,
    pub ab: Vec<usize>,
    /// The first entry of the probe chain and the value of the rows of `s3` (stage D).
    pub hd: Vec<usize>,
    pub vals: Vec<i128>,
}

pub open spec fn scratch_wf(sc: &Scratch) -> bool {
    &&& sc.s1@.len() == BLK && sc.s2@.len() == BLK && sc.s2j@.len() == BLK
    &&& sc.s3@.len() == BLK && sc.s3j@.len() == BLK && sc.s3h@.len() == BLK
    &&& sc.ta@.len() == BLK && sc.tb@.len() == BLK && sc.va@.len() == BLK && sc.vb@.len() == BLK
    &&& sc.aa@.len() == BLK && sc.ab@.len() == BLK && sc.hd@.len() == BLK && sc.vals@.len() == BLK
}

/// Fresh scratch lists (calling thread).
pub fn scratch_new() -> (sc: Scratch)
    ensures scratch_wf(&sc),
{
    Scratch {
        s1: vec![0usize; BLK], s2: vec![0usize; BLK], s2j: vec![0usize; BLK], s3: vec![0usize; BLK],
        s3j: vec![0usize; BLK], s3h: vec![0u64; BLK], ta: vec![0usize; BLK], tb: vec![0usize; BLK],
        va: vec![0usize; BLK], vb: vec![0usize; BLK], aa: vec![0usize; BLK], ab: vec![0usize; BLK],
        hd: vec![0usize; BLK], vals: vec![0i128; BLK],
    }
}

/// (A) The rows of `b0..b1` passing the cheap filter.
fn stage_a(s: &NumScan, b0: usize, b1: usize, s1: &mut Vec<usize>, Ghost(c): Ghost<Ctx>) -> (k: usize)
    requires num_scan_ok(s, c), b0 <= b1, (b1 as int) <= c.n, b1 - b0 <= BLK, old(s1)@.len() == BLK,
    ensures
        final(s1)@.len() == BLK, k <= b1 - b0,
        rows_in(final(s1)@.subrange(0, k as int), b0 as int, b1 as int),
        keeps(c, s.ex.list@, final(s1)@.subrange(0, k as int), b0 as int, b1 as int),
    no_unwind
{
    let ghost ents = s.ex.list@;
    let mut k: usize = 0;
    let mut i = b0;
    while i < b1
        invariant
            num_scan_ok(s, c), ents == s.ex.list@, b0 <= i <= b1, (b1 as int) <= c.n, b1 - b0 <= BLK,
            s1@.len() == BLK, k <= i - b0,
            rows_in(s1@.subrange(0, k as int), b0 as int, i as int),
            keeps(c, ents, s1@.subrange(0, k as int), b0 as int, i as int),
        decreases b1 - i,
    {
        let pass = pre_filter(s, i, Ghost(c));
        let ghost l0 = s1@.subrange(0, k as int);
        crate::gendb_entry::work::put(s1, k, i);
        proof {
            assert(s1@.subrange(0, k as int) =~= l0);
            assert(s1@.subrange(0, k + 1) =~= l0.push(i));
        }
        if pass {
            k = k + 1;
        }
        proof {
            let l1 = s1@.subrange(0, k as int);
            assert forall|x: int| 0 <= x < l1.len() implies b0 <= #[trigger] l1[x] < i + 1 by {
                if x < l0.len() {
                    assert(l1[x] == l0[x]);
                }
            }
            assert forall|x: int, y: int| 0 <= x < y < l1.len() implies #[trigger] l1[x] < #[trigger] l1[y] by {
                if y < l0.len() {
                    assert(l1[x] == l0[x] && l1[y] == l0[y]);
                } else {
                    assert(l1[x] == l0[x]);
                }
            }
            assert forall|i2: int| b0 <= i2 < i + 1 && (#[trigger] row_out(c, ents, i2)).len() > 0 implies l1.contains(i2 as usize) by {
                if i2 < i {
                    let w = choose|w: int| 0 <= w < l0.len() && l0[w] == i2 as usize;
                    assert(l1[w] == l0[w]);
                } else {
                    assert(l1[l1.len() - 1] == i);
                }
            }
        }
        i = i + 1;
    }
    k
}

/// The facts of the rows kept by (B): each has a selected sub row.
pub open spec fn facts_b(c: Ctx, l: Seq<usize>, js: Seq<usize>) -> bool {
    forall|x: int| 0 <= x < l.len() ==> sub_of(c, #[trigger] js[x] as int, n_adsh(c, l[x] as int))
}

/// (B) The rows of `s1[0..k1]` with a selected sub row, with their sub rows.
fn stage_b(s: &NumScan, b0: usize, b1: usize, s1: &Vec<usize>, k1: usize, aa: &Vec<usize>, ab: &Vec<usize>,
    s2: &mut Vec<usize>, s2j: &mut Vec<usize>, Ghost(c): Ghost<Ctx>) -> (k: usize)
    requires
        num_scan_ok(s, c), b0 <= b1, (b1 as int) <= c.n, s1@.len() == BLK, k1 <= BLK,
        aa@.len() == BLK, ab@.len() == BLK, col_offs(s.n_adsh@, s1@, aa@, ab@, k1 as int),
        old(s2)@.len() == BLK, old(s2j)@.len() == BLK,
        rows_in(s1@.subrange(0, k1 as int), b0 as int, b1 as int),
        keeps(c, s.ex.list@, s1@.subrange(0, k1 as int), b0 as int, b1 as int),
    ensures
        final(s2)@.len() == BLK, final(s2j)@.len() == BLK, k <= k1,
        rows_in(final(s2)@.subrange(0, k as int), b0 as int, b1 as int),
        keeps(c, s.ex.list@, final(s2)@.subrange(0, k as int), b0 as int, b1 as int),
        facts_b(c, final(s2)@.subrange(0, k as int), final(s2j)@.subrange(0, k as int)),
    no_unwind
{
    let ghost ents = s.ex.list@;
    let ghost l1 = s1@.subrange(0, k1 as int);
    let mut k: usize = 0;
    let mut q: usize = 0;
    proof {
        assert(s2@.subrange(0, 0) + l1.subrange(0, k1 as int) =~= l1);
    }
    while q < k1
        invariant
            num_scan_ok(s, c), ents == s.ex.list@, b0 <= b1, (b1 as int) <= c.n, s1@.len() == BLK, k1 <= BLK,
            l1 == s1@.subrange(0, k1 as int), rows_in(l1, b0 as int, b1 as int),
            aa@.len() == BLK, ab@.len() == BLK, col_offs(s.n_adsh@, s1@, aa@, ab@, k1 as int),
            s2@.len() == BLK, s2j@.len() == BLK, k <= q, q <= k1,
            rows_in(s2@.subrange(0, k as int), b0 as int, b1 as int),
            q < k1 ==> forall|x: int| 0 <= x < k ==> #[trigger] s2@[x] < l1[q as int],
            keeps(c, ents, s2@.subrange(0, k as int) + l1.subrange(q as int, k1 as int), b0 as int, b1 as int),
            facts_b(c, s2@.subrange(0, k as int), s2j@.subrange(0, k as int)),
        decreases k1 - q,
    {
        let i = s1[q];
        proof {
            assert(l1[q as int] == i);
            assert(b0 <= i < b1);
        }
        proof {
            assert(aa@[q as int] as int == s.n_adsh@.offsets[s1@[q as int] as int]);
        }
        let j = sub_row_at(s, i, aa[q], ab[q], Ghost(c));
        let ghost l2 = s2@.subrange(0, k as int);
        let ghost j2 = s2j@.subrange(0, k as int);
        crate::gendb_entry::work::put(s2, k, i);
        crate::gendb_entry::work::put(s2j, k, j);
        proof {
            assert(s2@.subrange(0, k as int) =~= l2);
            assert(s2j@.subrange(0, k as int) =~= j2);
            assert(s2@.subrange(0, k + 1) =~= l2.push(i));
            assert(s2j@.subrange(0, k + 1) =~= j2.push(j));
            let rest = l1.subrange(q as int, k1 as int);
            assert(rest[0] == i);
            assert(rest.drop_first() =~= l1.subrange(q + 1, k1 as int));
            lemma_filter_step(c, ents, l2, rest, i, j != NONE, b0 as int, b1 as int);
        }
        if j != NONE {
            k = k + 1;
        }
        proof {
            let n2 = s2@.subrange(0, k as int);
            let nj = s2j@.subrange(0, k as int);
            assert(n2 == if j != NONE { l2.push(i) } else { l2 });
            assert forall|x: int| 0 <= x < n2.len() implies b0 <= #[trigger] n2[x] < b1 by {
                if x < l2.len() {
                    assert(n2[x] == l2[x]);
                }
            }
            assert forall|x: int, y: int| 0 <= x < y < n2.len() implies #[trigger] n2[x] < #[trigger] n2[y] by {
                if y < l2.len() {
                    assert(n2[x] == l2[x] && n2[y] == l2[y]);
                } else {
                    assert(n2[x] == l2[x]);
                    assert(s2@[x] < l1[q as int]);
                }
            }
            if q + 1 < k1 {
                assert(l1[q as int] < l1[q + 1]);
                assert forall|x: int| 0 <= x < k implies #[trigger] s2@[x] < l1[q + 1] by {
                    if x < l2.len() {
                        assert(s2@[x] == l2[x]);
                    }
                }
            }
            assert forall|x: int| 0 <= x < n2.len() implies sub_of(c, #[trigger] nj[x] as int, n_adsh(c, n2[x] as int)) by {
                if x < l2.len() {
                    assert(n2[x] == l2[x] && nj[x] == j2[x]);
                }
            }
        }
        q = q + 1;
    }
    proof {
        assert(l1.subrange(k1 as int, k1 as int) =~= Seq::<usize>::empty());
        assert(s2@.subrange(0, k as int) + l1.subrange(k1 as int, k1 as int) =~= s2@.subrange(0, k as int));
    }
    k
}

/// The facts of the rows kept by (C): as (B), with their probe hashes.
pub open spec fn facts_c(c: Ctx, l: Seq<usize>, js: Seq<usize>, hs: Seq<u64>) -> bool {
    &&& facts_b(c, l, js)
    &&& forall|x: int| 0 <= x < l.len() ==> #[trigger] hs[x] == key_hash(pair_hash_spec(1, n_tag(c, l[x] as int), n_ver(c, l[x] as int)), js[x])
}

/// (C) The rows of `s2[0..k2]` whose probe hash may be in the entry bitmap, with their sub rows and hashes.
fn stage_c(s: &NumScan, b0: usize, b1: usize, s2: &Vec<usize>, s2j: &Vec<usize>, k2: usize, ta: &Vec<usize>,
    tb: &Vec<usize>, va: &Vec<usize>, vb: &Vec<usize>, sc3: &mut Vec<usize>, sc3j: &mut Vec<usize>,
    sc3h: &mut Vec<u64>, Ghost(c): Ghost<Ctx>) -> (k: usize)
    requires
        num_scan_ok(s, c), b0 <= b1, (b1 as int) <= c.n, s2@.len() == BLK, s2j@.len() == BLK, k2 <= BLK,
        ta@.len() == BLK, tb@.len() == BLK, va@.len() == BLK, vb@.len() == BLK,
        offs_ok(s, s2@, ta@, tb@, va@, vb@, k2 as int),
        old(sc3)@.len() == BLK, old(sc3j)@.len() == BLK, old(sc3h)@.len() == BLK,
        rows_in(s2@.subrange(0, k2 as int), b0 as int, b1 as int),
        keeps(c, s.ex.list@, s2@.subrange(0, k2 as int), b0 as int, b1 as int),
        facts_b(c, s2@.subrange(0, k2 as int), s2j@.subrange(0, k2 as int)),
    ensures
        final(sc3)@.len() == BLK, final(sc3j)@.len() == BLK, final(sc3h)@.len() == BLK, k <= k2,
        rows_in(final(sc3)@.subrange(0, k as int), b0 as int, b1 as int),
        keeps(c, s.ex.list@, final(sc3)@.subrange(0, k as int), b0 as int, b1 as int),
        facts_c(c, final(sc3)@.subrange(0, k as int), final(sc3j)@.subrange(0, k as int), final(sc3h)@.subrange(0, k as int)),
    no_unwind
{
    let ghost ents = s.ex.list@;
    let ghost l1 = s2@.subrange(0, k2 as int);
    let ghost j1 = s2j@.subrange(0, k2 as int);
    let mut k: usize = 0;
    let mut q: usize = 0;
    proof {
        assert(sc3@.subrange(0, 0) + l1.subrange(0, k2 as int) =~= l1);
    }
    while q < k2
        invariant
            num_scan_ok(s, c), ents == s.ex.list@, b0 <= b1, (b1 as int) <= c.n, s2@.len() == BLK, s2j@.len() == BLK,
            k2 <= BLK, l1 == s2@.subrange(0, k2 as int), j1 == s2j@.subrange(0, k2 as int),
            ta@.len() == BLK, tb@.len() == BLK, va@.len() == BLK, vb@.len() == BLK,
            offs_ok(s, s2@, ta@, tb@, va@, vb@, k2 as int),
            rows_in(l1, b0 as int, b1 as int), facts_b(c, l1, j1),
            sc3@.len() == BLK, sc3j@.len() == BLK, sc3h@.len() == BLK, k <= q, q <= k2,
            rows_in(sc3@.subrange(0, k as int), b0 as int, b1 as int),
            q < k2 ==> forall|x: int| 0 <= x < k ==> #[trigger] sc3@[x] < l1[q as int],
            keeps(c, ents, sc3@.subrange(0, k as int) + l1.subrange(q as int, k2 as int), b0 as int, b1 as int),
            facts_c(c, sc3@.subrange(0, k as int), sc3j@.subrange(0, k as int), sc3h@.subrange(0, k as int)),
        decreases k2 - q,
    {
        let i = s2[q];
        let j = s2j[q];
        proof {
            assert(l1[q as int] == i && j1[q as int] == j);
            assert(b0 <= i < b1);
        }
        proof {
            assert(ta@[q as int] as int == s.n_tag@.offsets[s2@[q as int] as int]);
        }
        let (keep, h) = probe_key_at(s, i, j, ta[q], tb[q], va[q], vb[q], Ghost(c));
        let ghost l2 = sc3@.subrange(0, k as int);
        let ghost j2 = sc3j@.subrange(0, k as int);
        let ghost h2 = sc3h@.subrange(0, k as int);
        crate::gendb_entry::work::put(sc3, k, i);
        crate::gendb_entry::work::put(sc3j, k, j);
        crate::gendb_entry::work::put(sc3h, k, h);
        proof {
            assert(sc3@.subrange(0, k as int) =~= l2);
            assert(sc3j@.subrange(0, k as int) =~= j2);
            assert(sc3h@.subrange(0, k as int) =~= h2);
            assert(sc3@.subrange(0, k + 1) =~= l2.push(i));
            assert(sc3j@.subrange(0, k + 1) =~= j2.push(j));
            assert(sc3h@.subrange(0, k + 1) =~= h2.push(h));
            let rest = l1.subrange(q as int, k2 as int);
            assert(rest[0] == i);
            assert(rest.drop_first() =~= l1.subrange(q + 1, k2 as int));
            lemma_filter_step(c, ents, l2, rest, i, keep, b0 as int, b1 as int);
        }
        if keep {
            k = k + 1;
        }
        proof {
            let n2 = sc3@.subrange(0, k as int);
            let nj = sc3j@.subrange(0, k as int);
            let nh = sc3h@.subrange(0, k as int);
            assert(n2 == if keep { l2.push(i) } else { l2 });
            assert forall|x: int| 0 <= x < n2.len() implies b0 <= #[trigger] n2[x] < b1 by {
                if x < l2.len() {
                    assert(n2[x] == l2[x]);
                }
            }
            assert forall|x: int, y: int| 0 <= x < y < n2.len() implies #[trigger] n2[x] < #[trigger] n2[y] by {
                if y < l2.len() {
                    assert(n2[x] == l2[x] && n2[y] == l2[y]);
                } else {
                    assert(n2[x] == l2[x]);
                    assert(sc3@[x] < l1[q as int]);
                }
            }
            if q + 1 < k2 {
                assert(l1[q as int] < l1[q + 1]);
                assert forall|x: int| 0 <= x < k implies #[trigger] sc3@[x] < l1[q + 1] by {
                    if x < l2.len() {
                        assert(sc3@[x] == l2[x]);
                    }
                }
            }
            assert forall|x: int| 0 <= x < n2.len() implies sub_of(c, #[trigger] nj[x] as int, n_adsh(c, n2[x] as int)) by {
                if x < l2.len() {
                    assert(n2[x] == l2[x] && nj[x] == j2[x]);
                }
            }
            assert forall|x: int| 0 <= x < n2.len() implies #[trigger] nh[x] == key_hash(pair_hash_spec(1, n_tag(c, n2[x] as int), n_ver(c, n2[x] as int)), nj[x]) by {
                if x < l2.len() {
                    assert(n2[x] == l2[x] && nj[x] == j2[x] && nh[x] == h2[x]);
                }
            }
        }
        q = q + 1;
    }
    proof {
        assert(l1.subrange(k2 as int, k2 as int) =~= Seq::<usize>::empty());
        assert(sc3@.subrange(0, k as int) + l1.subrange(k2 as int, k2 as int) =~= sc3@.subrange(0, k as int));
    }
    k
}

/// The records of a block before the `q`-th kept row are those of the kept rows before it.
proof fn lemma_stop_prefix(c: Ctx, ents: Seq<(usize, usize, usize)>, l: Seq<usize>, q: int, b0: int, b1: int)
    requires 0 <= b0 <= b1, b1 <= usize::MAX, rows_in(l, b0, b1), keeps(c, ents, l, b0, b1), 0 <= q < l.len(),
    ensures contrib(c, ents, b0, l[q] as int) == cat_rows(c, ents, l.subrange(0, q)),
{
    let lq = l.subrange(0, q);
    let i = l[q] as int;
    assert forall|x: int| 0 <= x < lq.len() implies b0 <= #[trigger] lq[x] < i by {
        assert(lq[x] == l[x]);
        assert(l[x] < l[q]);
    }
    assert forall|x: int, y: int| 0 <= x < y < lq.len() implies #[trigger] lq[x] < #[trigger] lq[y] by {
        assert(lq[x] == l[x] && lq[y] == l[y]);
    }
    assert forall|i2: int| b0 <= i2 < i && (#[trigger] row_out(c, ents, i2)).len() > 0 implies lq.contains(i2 as usize) by {
        let w = choose|w: int| 0 <= w < l.len() && l[w] == i2 as usize;
        if w > q {
            assert(l[q] < l[w]);
        }
        assert(w != q);
        assert(lq[w] == l[w]);
    }
    lemma_block(c, ents, lq, b0, i);
}

/// One kept row more.
proof fn lemma_cat_step(c: Ctx, ents: Seq<(usize, usize, usize)>, l: Seq<usize>, q: int)
    requires 0 <= q < l.len(),
    ensures cat_rows(c, ents, l.subrange(0, q + 1)) == cat_rows(c, ents, l.subrange(0, q)) + row_out(c, ents, l[q] as int),
{
    assert(l.subrange(0, q + 1).drop_last() =~= l.subrange(0, q));
}

/// (D) The records of the rows `s3[0..k3]` pushed onto `out` while they fit: `NONE` when all fit, otherwise the
/// first row whose records did not fit (`out` then holds the records of the rows before it).
#[verifier::spinoff_prover]
fn stage_d(s: &NumScan, b0: usize, b1: usize, sc3: &Vec<usize>, sc3j: &Vec<usize>, sc3h: &Vec<u64>, k3: usize,
    ua: &Vec<usize>, ub: &Vec<usize>, hd: &Vec<usize>, vals: &Vec<i128>, out: &mut Buf<(usize, usize, i128)>,
    Ghost(c): Ghost<Ctx>) -> (stop: usize)
    requires
        hd@.len() == BLK, vals@.len() == BLK, heads_ok(s, c, sc3@, sc3h@, hd@, vals@, k3 as int),
        num_scan_ok(s, c), b0 <= b1, (b1 as int) <= c.n, sc3@.len() == BLK, sc3j@.len() == BLK, sc3h@.len() == BLK,
        ua@.len() == BLK, ub@.len() == BLK, col_offs(s.n_uom@, sc3@, ua@, ub@, k3 as int),
        k3 <= BLK, old(out).wf(),
        rows_in(sc3@.subrange(0, k3 as int), b0 as int, b1 as int),
        keeps(c, s.ex.list@, sc3@.subrange(0, k3 as int), b0 as int, b1 as int),
        facts_c(c, sc3@.subrange(0, k3 as int), sc3j@.subrange(0, k3 as int), sc3h@.subrange(0, k3 as int)),
    ensures
        final(out).wf(), final(out).capacity() == old(out).capacity(),
        stop == NONE ==> final(out).view() == old(out).view() + contrib(c, s.ex.list@, b0 as int, b1 as int),
        stop != NONE ==> b0 <= stop < b1 && final(out).view() == old(out).view() + contrib(c, s.ex.list@, b0 as int, stop as int),
        k3 <= 1 && old(out).view().len() + s.ex.list@.len() < old(out).capacity() ==> stop == NONE,
    no_unwind
{
    let ghost ents = s.ex.list@;
    let ghost l = sc3@.subrange(0, k3 as int);
    let ghost js = sc3j@.subrange(0, k3 as int);
    let ghost hs = sc3h@.subrange(0, k3 as int);
    let ghost o0 = out.view();
    let mut q: usize = 0;
    proof {
        assert(l.subrange(0, 0) =~= Seq::<usize>::empty());
        assert(o0 + cat_rows(c, ents, l.subrange(0, 0)) =~= o0);
        reveal(num_scan_ok);
    }
    while q < k3
        invariant
            num_scan_ok(s, c), ents == s.ex.list@, b0 <= b1, (b1 as int) <= c.n,
            sc3@.len() == BLK, sc3j@.len() == BLK, sc3h@.len() == BLK, k3 <= BLK, q <= k3,
            ua@.len() == BLK, ub@.len() == BLK, col_offs(s.n_uom@, sc3@, ua@, ub@, k3 as int),
            hd@.len() == BLK, vals@.len() == BLK, heads_ok(s, c, sc3@, sc3h@, hd@, vals@, k3 as int),
            l == sc3@.subrange(0, k3 as int), js == sc3j@.subrange(0, k3 as int), hs == sc3h@.subrange(0, k3 as int),
            rows_in(l, b0 as int, b1 as int), keeps(c, ents, l, b0 as int, b1 as int), facts_c(c, l, js, hs),
            out.wf(), out.capacity() == old(out).capacity(), o0 == old(out).view(),
            out.view() == o0 + cat_rows(c, ents, l.subrange(0, q as int)),
            q == 0 ==> out.view() == o0,
        decreases k3 - q,
    {
        proof { reveal(num_scan_ok); }
        let i = sc3[q];
        let j = sc3j[q];
        let h = sc3h[q];
        proof {
            assert(l[q as int] == i && js[q as int] == j && hs[q as int] == h);
            assert(b0 <= i < b1);
        }
        let ghost oq = out.view();
        let mut done = true;
        proof {
            assert(ua@[q as int] as int == s.n_uom@.offsets[sc3@[q as int] as int]);
            assert(hd@[q as int] == enc(first_of(s.ex.chains.hashes@, s.ex.chains.shift,
                bucket_of(sc3h@[q as int], s.ex.chains.shift), 0)));
        }
        if uom_ok_at(s, i, ua[q], ub[q], Ghost(c)) {
            proof {
                assert(sub_of(c, j as int, n_adsh(c, i as int)));
                assert(num_sel(c, i as int));
            }
            let (t, tl) = text_val(&s.n_tag, i, Ghost(c.n));
            let (v, vl) = text_val(&s.n_ver, i, Ghost(c.n));
            done = walk_entries(s, i, j, t, tl, v, vl, h, hd[q], vals[q], out, Ghost(c));
        } else {
            proof {
                assert(row_out(c, ents, i as int) =~= Seq::<(usize, usize, i128)>::empty());
                assert(out.view() =~= oq + row_out(c, ents, i as int));
            }
        }
        if !done {
            proof {
                lemma_stop_prefix(c, ents, l, q as int, b0 as int, b1 as int);
            }
            return i;
        }
        proof {
            lemma_cat_step(c, ents, l, q as int);
            assert(out.view() =~= o0 + cat_rows(c, ents, l.subrange(0, q + 1)));
        }
        q = q + 1;
    }
    proof {
        assert(l.subrange(0, k3 as int) =~= l);
        lemma_block(c, ents, l, b0 as int, b1 as int);
    }
    NONE
}

/// The records of rows `b0..b1` (one block) pushed onto `out` while they fit (as `stage_d`).
fn scan_block(s: &NumScan, b0: usize, b1: usize, sc: &mut Scratch, out: &mut Buf<(usize, usize, i128)>,
    Ghost(c): Ghost<Ctx>) -> (stop: usize)
    requires num_scan_ok(s, c), b0 <= b1, (b1 as int) <= c.n, b1 - b0 <= BLK, scratch_wf(old(sc)), old(out).wf(),
    ensures
        scratch_wf(final(sc)), final(out).wf(), final(out).capacity() == old(out).capacity(),
        stop == NONE ==> final(out).view() == old(out).view() + contrib(c, s.ex.list@, b0 as int, b1 as int),
        stop != NONE ==> b0 <= stop < b1 && final(out).view() == old(out).view() + contrib(c, s.ex.list@, b0 as int, stop as int),
        b1 == b0 + 1 && old(out).view().len() + s.ex.list@.len() < old(out).capacity() ==> stop == NONE,
    no_unwind
{
    proof {
        lemma_scan_cols(s, c);
    }
    let k1 = stage_a(s, b0, b1, &mut sc.s1, Ghost(c));
    proof {
        lemma_rows_bound(sc.s1@, k1 as int, b0 as int, b1 as int);
    }
    gather_offs(&s.n_adsh, Ghost(c.n), &sc.s1, k1, &mut sc.aa, &mut sc.ab);
    let k2 = stage_b(s, b0, b1, &sc.s1, k1, &sc.aa, &sc.ab, &mut sc.s2, &mut sc.s2j, Ghost(c));
    gather_c(s, b0, b1, &sc.s2, k2, &mut sc.ta, &mut sc.tb, &mut sc.va, &mut sc.vb, Ghost(c));
    let k3 = stage_c(s, b0, b1, &sc.s2, &sc.s2j, k2, &sc.ta, &sc.tb, &sc.va, &sc.vb, &mut sc.s3, &mut sc.s3j,
        &mut sc.s3h, Ghost(c));
    proof {
        lemma_rows_bound(sc.s3@, k3 as int, b0 as int, b1 as int);
    }
    gather_offs(&s.n_uom, Ghost(c.n), &sc.s3, k3, &mut sc.aa, &mut sc.ab);
    gather_d(s, &sc.s3, &sc.s3h, k3, &mut sc.hd, &mut sc.vals, Ghost(c));
    stage_d(s, b0, b1, &sc.s3, &sc.s3j, &sc.s3h, k3, &sc.aa, &sc.ab, &sc.hd, &sc.vals, out, Ghost(c))
}

/// One num scan task: rows `lo..hi`.
pub struct ScanTask {
    pub lo: usize,
    pub hi: usize,
    pub scan: NumScan,
    pub out: Buf<(usize, usize, i128)>,
    pub sc: Scratch,
    pub ctx: Ghost<Ctx>,
}

pub struct ScanOut {
    pub out: Buf<(usize, usize, i128)>,
    pub stopped: usize,
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        &&& num_scan_ok(&self.scan, self.ctx@)
        &&& self.lo <= self.hi && (self.hi as int) <= self.ctx@.n
        &&& self.out.wf() && self.out.view().len() == 0
        &&& scratch_wf(&self.sc)
    }

    open spec fn post(&self, r: ScanOut) -> bool {
        &&& r.out.wf()
        &&& self.lo <= r.stopped <= self.hi
        &&& r.out.view() == contrib(self.ctx@, self.scan.ex.list@, self.lo as int, r.stopped as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (r: ScanOut) {
        let ScanTask { lo, hi, scan, out, sc, ctx } = self;
        let ghost c = ctx@;
        let ghost ents = scan.ex.list@;
        let mut out = out;
        let mut sc = sc;
        let mut b0 = lo;
        let mut stopped = hi;
        let mut full = false;
        proof {
            assert(out.view() =~= contrib(c, ents, lo as int, lo as int));
        }
        while b0 < hi && !full
            invariant
                num_scan_ok(&scan, c), ents == scan.ex.list@, lo <= b0 <= hi, (hi as int) <= c.n, scratch_wf(&sc),
                out.wf(), lo <= stopped <= hi,
                !full ==> stopped == hi && out.view() == contrib(c, ents, lo as int, b0 as int),
                full ==> out.view() == contrib(c, ents, lo as int, stopped as int),
            decreases hi - b0, if full { 0int } else { 1int },
        {
            let b1 = if hi - b0 > BLK { b0 + BLK } else { hi };
            let ghost o0 = out.view();
            let stop = scan_block(&scan, b0, b1, &mut sc, &mut out, Ghost(c));
            if stop != NONE {
                proof {
                    lemma_contrib_split(c, ents, lo as int, b0 as int, stop as int);
                }
                stopped = stop;
                full = true;
            } else {
                proof {
                    lemma_contrib_split(c, ents, lo as int, b0 as int, b1 as int);
                }
                b0 = b1;
            }
        }
        ScanOut { out, stopped }
    }
}

/// The records of rows `lo..hi` on the calling thread (finishes a task that stopped early): one buffer with room
/// for every entry, emptied after each row.
pub fn scan_serial(s: &NumScan, lo: usize, hi: usize, Ghost(c): Ghost<Ctx>) -> (out: Vec<(usize, usize, i128)>)
    requires num_scan_ok(s, c), lo <= hi, (hi as int) <= c.n,
    ensures out@ == contrib(c, s.ex.list@, lo as int, hi as int),
{
    proof { reveal(num_scan_ok); }
    let ghost ents = s.ex.list@;
    let ne = s.ex.list.len();
    proof {
        assert(ne < NONE) by {
            assert(s.ex.chains.hashes@.len() == ne);
        }
    }
    let mut buf: Buf<(usize, usize, i128)> = Buf::new(ne + 1, (0, 0, 0));
    let mut sc = scratch_new();
    let mut out: Vec<(usize, usize, i128)> = Vec::new();
    let mut i = lo;
    proof {
        assert(out@ =~= contrib(c, ents, lo as int, lo as int));
    }
    while i < hi
        invariant
            num_scan_ok(s, c), ents == s.ex.list@, ne == ents.len(), lo <= i <= hi, (hi as int) <= c.n,
            buf.wf(), buf.capacity() == ne + 1, scratch_wf(&sc),
            out@ == contrib(c, ents, lo as int, i as int),
        decreases hi - i,
    {
        buf.clear();
        let stop = scan_block(s, i, i + 1, &mut sc, &mut buf, Ghost(c));
        proof {
            assert(stop == NONE);
            assert(buf.view() =~= contrib(c, ents, i as int, i + 1));
            lemma_contrib_split(c, ents, lo as int, i as int, i + 1);
        }
        buf.drain_into(&mut out);
        i = i + 1;
    }
    out
}

/// A copy of the scan's handles is a scan of the same context.
pub proof fn lemma_num_scan_copy(s: &NumScan, r: &NumScan, c: Ctx)
    requires
        num_scan_ok(s, c),
        r.n_uom@ == s.n_uom@ && r.n_adsh@ == s.n_adsh@ && r.n_tag@ == s.n_tag@ && r.n_ver@ == s.n_ver@ && r.n_val@ == s.n_val@
            && r.uom@ == s.uom@ && r.uom_len == s.uom_len && *r.sx == *s.sx && *r.ex == *s.ex,
    ensures num_scan_ok(r, c),
{
    reveal(num_scan_ok);
}

} // verus!
