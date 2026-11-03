//! The value-order walk (one thread). Unit `$1` is uom code `uc`: its runs are `[r0, r1)` and its stored rows
//! `[lo, hi)`; storage `num_vord` lists those rows by value descending at `vorder[lo..hi)`. For each position `p`,
//! row `i = vorder[p]` is found in its run (binary search over the unit's run starts), its filing in sub (the sub row
//! at num's adsh code in `adsh_order`, which almost always holds it, else a binary search), and it is a candidate
//! (`vstored::row_emit`) when the filing has `fy = $2` and `i` holds the largest value of its tag in the run (the
//! adjacent rows of that tag are compared). Candidates enter a top-100 buffer. Once the buffer is full and row `i`'s
//! value is below the buffer's last value, every later row (values only decrease) would be rejected: the walk stops.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::text::lex_cmp;
use crate::bridge::order::lemma_lex_cmp_antisym;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::gendb_entry::layout::PartView;
use crate::stores::num_vord::interface as numi;
use crate::stores::sub::interface as subi;
use crate::stores::num_vord::interface::common::text::{text_entry, text_parts_wf, u64_part, u8_part, text_entry_of,
    compare_bytes, lemma_dict_codes};
use crate::stores::num_vord::interface::common::cols::{i32_part, i128_part};
use crate::stores::num_vord::interface::common::runs::*;
use crate::agent::stored::*;
use crate::agent::vstored::*;
use crate::agent::kernel::*;
use crate::agent::common::topk::*;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// The slices the walk reads, the parts they are, and unit `$1` (uom code `uc`).
#[derive(Clone, Copy)]
pub struct WalkInput {
    pub p1: i64,
    pub fy: &'static [i32],
    pub fy_valid: &'static [u8],
    pub sub_adsh_off: &'static [u64],
    pub sub_adsh_bytes: &'static [u8],
    pub sub_rows: usize,
    pub name_codes: &'static [u64],
    pub adsh_order: &'static [u64],
    pub adsh_off: &'static [u64],
    pub adsh_bytes: &'static [u8],
    pub adsh_count: usize,
    pub run_adsh: &'static [u64],
    pub run_start: &'static [u64],
    pub tv: &'static [u64],
    pub pair_tag: &'static [u64],
    pub value: &'static [i128],
    pub vorder: &'static [u64],
    pub nrows: usize,
    pub r0: usize,
    pub r1: usize,
    pub lo: usize,
    pub hi: usize,
    pub uc: Ghost<int>,
    pub np: Ghost<Seq<PartView>>,
    pub sp: Ghost<Seq<PartView>>,
    pub u: Ghost<Seq<u8>>,
}

pub open spec fn win_ok(w: WalkInput) -> bool {
    let np = w.np@;
    let sp = w.sp@;
    let uc = w.uc@;
    &&& kfacts(np, sp)
    &&& w.fy@ == i32_part(sp[subi::P_FY as int])
    &&& w.fy_valid@ == u8_part(sp[subi::P_FY_VALID as int])
    &&& w.sub_adsh_off@ == u64_part(sp[subi::P_ADSH_OFF as int])
    &&& w.sub_adsh_bytes@ == u8_part(sp[subi::P_ADSH_BYTES as int])
    &&& w.sub_rows == subi::row_count(sp)
    &&& w.name_codes@ == u64_part(sp[subi::P_NAME_CODES as int])
    &&& w.adsh_order@ == subi::adsh_order(sp)
    &&& w.adsh_off@ == u64_part(np[numi::P_ADSH_OFF as int])
    &&& w.adsh_bytes@ == u8_part(np[numi::P_ADSH_BYTES as int])
    &&& w.adsh_count == numi::adsh_count(np)
    &&& w.run_adsh@ == numi::u64s(np, numi::P_RUN_ADSH)
    &&& w.run_start@ == n_start(np)
    &&& w.tv@ == numi::u64s(np, numi::P_TV)
    &&& w.pair_tag@ == numi::u64s(np, numi::P_PAIR_TAG)
    &&& w.value@ == n_value(np)
    &&& w.vorder@ == vord(np)
    &&& w.nrows == numi::row_count(np)
    &&& 0 <= uc < numi::uom_count(np)
    &&& numi::dict_entry(np, numi::P_UOM_OFF, uc) == w.u@
    &&& w.r0 == numi::u64s(np, numi::P_UOM_RUNS)[uc]
    &&& w.r1 == numi::u64s(np, numi::P_UOM_RUNS)[uc + 1]
    &&& w.lo == numi::unit_row(np, uc)
    &&& w.hi == numi::unit_row(np, uc + 1)
}

/// The unit's runs, rows and value order.
pub proof fn lemma_unit_facts(w: WalkInput)
    requires win_ok(w),
    ensures ({
        let np = w.np@;
        &&& w.r0 <= w.r1 <= numi::run_count(np)
        &&& w.run_start@.len() == numi::run_count(np) + 1
        &&& w.lo == w.run_start@[w.r0 as int] && w.hi == w.run_start@[w.r1 as int]
        &&& w.lo <= w.hi <= numi::row_count(np)
        &&& w.vorder@.len() == numi::row_count(np)
        &&& forall|r: int| w.r0 <= r < w.r1 ==> #[trigger] numi::u64s(np, numi::P_RUN_UOM)[r] == w.uc@
        &&& forall|p: int, q: int| w.lo <= p < q < w.hi ==> #[trigger] w.value@[w.vorder@[p] as int] >= #[trigger] w.value@[w.vorder@[q] as int]
        &&& w.vorder@.subrange(w.lo as int, w.hi as int).to_multiset() == numi::span(w.lo as int, w.hi as int).to_multiset()
    }),
{
    let np = w.np@;
    let sp = w.sp@;
    lemma_kf_uom(np, sp, w.uc@);
    lemma_kf_num(np, sp);
    lemma_kf_vorder(np, sp, w.uc@);
    let st = n_start(np);
    let nr = numi::run_count(np);
    if (w.r1 as int) < nr {
        assert(st[w.r1 as int] < st[nr]);
    }
    if w.r0 < w.r1 {
        assert(st[w.r0 as int] < st[w.r1 as int]);
    }
}

/// A position of the unit holds a row of the unit.
pub proof fn lemma_vord_in(w: WalkInput, p: int)
    requires win_ok(w), w.lo <= p < w.hi,
    ensures w.lo <= w.vorder@[p] < w.hi,
{
    lemma_unit_facts(w);
    let (lo, hi) = (w.lo as int, w.hi as int);
    let s = w.vorder@.subrange(lo, hi);
    let x = w.vorder@[p];
    assert(s[p - lo] == x);
    assert(s.contains(x));
    assert(s.to_multiset().count(x) > 0);
    let sp = numi::span(lo, hi);
    assert(sp.to_multiset().count(x) > 0);
    let k = choose|k: int| 0 <= k < sp.len() && sp[k] == x;
    assert(sp[k] == (lo + k) as u64);
}

/// The run of stored row `i` among the runs `[r0, r1)` whose rows contain it.
pub fn find_run(start: &[u64], r0: usize, r1: usize, i: usize) -> (r: usize)
    requires r0 < r1 < start@.len(), start@[r0 as int] <= i < start@[r1 as int],
    ensures r0 <= r < r1, start@[r as int] <= i < start@[r + 1],
    no_unwind
{
    let mut a = r0;
    let mut b = r1;
    while b - a > 1
        invariant r0 <= a < b <= r1 < start@.len(), start@[a as int] <= i < start@[b as int],
        decreases b - a,
    {
        let mid = a + (b - a) / 2;
        if start[mid] <= i as u64 {
            a = mid;
        } else {
            b = mid;
        }
    }
    a
}

impl WalkInput {
    /// The sub row whose adsh is num's adsh dictionary entry `k`, if any.
    fn find_sub(&self, k: usize) -> (r: Option<usize>)
        requires win_ok(*self), k < self.adsh_count,
        ensures
            r matches Some(j) ==> j < self.sub_rows && subi::adsh_bytes(self.sp@, j as int) == adsh_entry(self.np@, k as int),
            r is None ==> !has_sub(self.sp@, adsh_entry(self.np@, k as int)),
        no_unwind
    {
        let ghost np = self.np@;
        let ghost sp = self.sp@;
        proof {
            lemma_kf_dicts(np, sp);
            lemma_kf_sub(np, sp);
        }
        let n = self.sub_rows;
        let (key, klen) = text_entry_of(self.adsh_off, self.adsh_bytes, self.adsh_count, k);
        // The two dictionaries nearly coincide: try sorted position `k` first.
        if k < n {
            let j = self.adsh_order[k] as usize;
            let (e, en) = text_entry_of(self.sub_adsh_off, self.sub_adsh_bytes, n, j);
            if compare_bytes(e, en, key, klen) == 0 {
                proof { lemma_lex_cmp_zero(e@, key@); }
                return Some(j);
            }
        }
        // The first sorted position whose adsh is not below the key.
        let mut a: usize = 0;
        let mut b: usize = n;
        while a < b
            invariant
                win_ok(*self), np == self.np@, sp == self.sp@, n == self.sub_rows,
                a <= b <= n, key@ == adsh_entry(np, k as int), klen == key@.len(),
                forall|q: int| 0 <= q < a ==> lex_cmp(#[trigger] sub_key(sp, self.adsh_order@[q] as int), key@) < 0,
                b < n ==> lex_cmp(sub_key(sp, self.adsh_order@[b as int] as int), key@) >= 0,
            decreases b - a,
        {
            proof { lemma_kf_sub(np, sp); }
            let mid = a + (b - a) / 2;
            let j = self.adsh_order[mid] as usize;
            let (e, en) = text_entry_of(self.sub_adsh_off, self.sub_adsh_bytes, n, j);
            let c = compare_bytes(e, en, key, klen);
            if c < 0 {
                proof {
                    assert forall|q: int| 0 <= q <= mid implies lex_cmp(#[trigger] sub_key(sp, self.adsh_order@[q] as int), key@) < 0 by {
                        if q < mid {
                            lemma_lt_le_to_lt(sub_key(sp, self.adsh_order@[q] as int), sub_key(sp, self.adsh_order@[mid as int] as int), key@);
                        }
                    }
                }
                a = mid + 1;
            } else {
                b = mid;
            }
        }
        if a < n {
            let j = self.adsh_order[a] as usize;
            let (e, en) = text_entry_of(self.sub_adsh_off, self.sub_adsh_bytes, n, j);
            let c = compare_bytes(e, en, key, klen);
            if c == 0 {
                proof { lemma_lex_cmp_zero(e@, key@); }
                return Some(j);
            }
            proof { lemma_no_sub(*self, k as int, a as int); }
        } else {
            proof { lemma_no_sub(*self, k as int, a as int); }
        }
        None
    }

    /// The tag code of stored row `k`.
    fn tag_at(&self, k: usize) -> (t: u64)
        requires win_ok(*self), k < self.nrows,
        ensures t as int == tagc(self.np@, k as int),
        no_unwind
    {
        proof { lemma_kf_num(self.np@, self.sp@); }
        let q = self.tv[k];
        proof { assert(q < self.pair_tag@.len()); }
        self.pair_tag[q as usize]
    }

    /// Stored row `i` of run `r` holds the largest value of its tag in the run.
    fn seg_max_at(&self, i: usize, r: usize) -> (b: bool)
        requires
            win_ok(*self),
            r < numi::run_count(self.np@),
            n_start(self.np@)[r as int] <= i < n_start(self.np@)[r + 1],
        ensures b == seg_max(self.np@, r as int, i as int),
        no_unwind
    {
        let ghost np = self.np@;
        let ghost sp = self.sp@;
        proof {
            lemma_kf_num(np, sp);
            assert(n_start(np)[r as int] <= n_start(np)[r + 1] <= self.nrows);
        }
        let s = self.run_start[r] as usize;
        let e = self.run_start[r + 1] as usize;
        let tc = self.tag_at(i);
        let v = self.value[i];
        proof { lemma_seg_one(np, i as int, tc as int, v as int); }
        // Rows before `i` with its tag.
        let mut a = i;
        let mut go = true;
        while go && a > s
            invariant
                win_ok(*self), np == self.np@, sp == self.sp@,
                r < numi::run_count(np), s == n_start(np)[r as int], e == n_start(np)[r + 1],
                s <= a <= i < e <= numi::row_count(np),
                self.value@.len() == numi::row_count(np),
                tc as int == tagc(np, i as int), v == n_value(np)[i as int],
                !go ==> a > s && tagc(np, a - 1) != tc,
                seg_le(np, a as int, i + 1, tc as int, v as int),
            decreases a + (if go { 1int } else { 0int }),
        {
            let t = self.tag_at(a - 1);
            if t != tc {
                go = false;
            } else {
                if self.value[a - 1] > v {
                    proof { assert(tagc(np, a - 1) == tagc(np, i as int)); }
                    return false;
                }
                proof { lemma_seg_extend_down(np, a as int, i + 1, tc as int, v as int); }
                a = a - 1;
            }
        }
        // Rows after `i` with its tag.
        let mut b = i + 1;
        let mut go2 = true;
        while go2 && b < e
            invariant
                win_ok(*self), np == self.np@, sp == self.sp@,
                r < numi::run_count(np), s == n_start(np)[r as int], e == n_start(np)[r + 1],
                s <= a <= i < b <= e <= numi::row_count(np),
                self.value@.len() == numi::row_count(np),
                tc as int == tagc(np, i as int), v == n_value(np)[i as int],
                a == s || tagc(np, a - 1) != tc,
                !go2 ==> b < e && tagc(np, b as int) != tc,
                seg_le(np, a as int, b as int, tc as int, v as int),
            decreases e - b + (if go2 { 1int } else { 0int }),
        {
            let t = self.tag_at(b);
            if t != tc {
                go2 = false;
            } else {
                if self.value[b] > v {
                    proof { assert(tagc(np, b as int) == tagc(np, i as int)); }
                    return false;
                }
                proof { lemma_seg_extend_up(np, a as int, b as int, tc as int, v as int); }
                b = b + 1;
            }
        }
        proof {
            // The rows of the run with this tag are exactly `[a, b)`.
            assert forall|i2: int| s <= i2 < e && #[trigger] tagc(np, i2) == tagc(np, i as int)
                implies n_value(np)[i2] <= n_value(np)[i as int] by {
                if i2 < a {
                    lemma_kf_tag_mono(np, sp, r as int, i2, a - 1);
                    lemma_kf_tag_mono(np, sp, r as int, a - 1, a as int);
                    lemma_seg_at(np, a as int, b as int, tc as int, v as int, a as int);
                } else if i2 >= b {
                    lemma_kf_tag_mono(np, sp, r as int, b as int, i2);
                    lemma_kf_tag_mono(np, sp, r as int, i as int, b as int);
                } else {
                    lemma_seg_at(np, a as int, b as int, tc as int, v as int, i2);
                }
            }
        }
        true
    }

    /// The candidate of the row at position `p` added to the top-k buffer.
    fn visit(&self, buf: &mut Vec<Cand>, len: usize, p: usize, Ghost(all): Ghost<Seq<Row>>, Ghost(rest): Ghost<Seq<Row>>)
        -> (out: (usize, Ghost<Seq<Row>>))
        requires
            win_ok(*self),
            self.lo <= p < self.hi,
            buf_ok(self.np@, self.sp@, old(buf)@, len as int),
            topk_ok(qkeys(), qfams(), TOPK as nat, all, tview(self.np@, self.sp@, old(buf)@, len as int), rest),
        ensures
            buf_ok(self.np@, self.sp@, final(buf)@, out.0 as int),
            topk_ok(qkeys(), qfams(), TOPK as nat,
                all + row_emit(self.np@, self.sp@, self.u@, self.p1 as int, vord(self.np@)[p as int] as int),
                tview(self.np@, self.sp@, final(buf)@, out.0 as int), out.1@),
        no_unwind
    {
        let ghost np = self.np@;
        let ghost sp = self.sp@;
        let ghost u = self.u@;
        let ghost y = self.p1 as int;
        proof {
            lemma_unit_facts(*self);
            lemma_vord_in(*self, p as int);
            lemma_kf_num(np, sp);
            lemma_kf_sub(np, sp);
            lemma_kf_dicts(np, sp);
        }
        let i = self.vorder[p] as usize;
        let r = find_run(self.run_start, self.r0, self.r1, i);
        let ghost a = numi::run_adsh_of(np, r as int);
        proof {
            lemma_run_of(n_start(np), numi::run_count(np), numi::row_count(np), i as int);
            assert(in_run(n_start(np), r as int, i as int));
            assert(run_at(np, i as int) == r);
            assert(numi::u64s(np, numi::P_RUN_UOM)[r as int] == self.uc@);
            assert(numi::run_uom_of(np, r as int) == u);
            lemma_kf_run_adsh(np, sp, r as int);
        }
        let ghost em = row_emit(np, sp, u, y, i as int);
        let k = self.run_adsh[r] as usize;
        match self.find_sub(k) {
            None => {
                proof {
                    assert(em =~= Seq::<Row>::empty());
                    assert(all + em =~= all);
                }
                (len, Ghost(rest))
            },
            Some(j) => {
                proof {
                    assert(has_sub(sp, a));
                    lemma_kf_pk(np, sp, sub_of(sp, a), j as int);
                    assert(sub_of(sp, a) == j);
                }
                if self.fy_valid[j] != 0 && self.fy[j] as i64 == self.p1 && self.seg_max_at(i, r) {
                    let c = Cand { value: self.value[i], name: self.name_codes[j], tag: self.tag_at(i) };
                    proof {
                        assert(cand_ok(np, sp, c));
                        assert(cview(np, sp, c) == cand_row(np, sp, j as int, i as int));
                        assert(em == seq![cand_row(np, sp, j as int, i as int)]);
                        assert(all + em =~= all.push(cview(np, sp, c)));
                    }
                    topk_add(buf, len, c, Ghost(np), Ghost(sp), Ghost(all), Ghost(rest))
                } else {
                    proof {
                        assert(em =~= Seq::<Row>::empty());
                        assert(all + em =~= all);
                    }
                    (len, Ghost(rest))
                }
            },
        }
    }

    /// The top-100 split of the candidates of all the unit's positions.
    pub fn walk(&self, buf: &mut Vec<Cand>) -> (out: (usize, Ghost<Seq<Row>>))
        requires win_ok(*self), old(buf)@.len() == TOPK,
        ensures
            buf_ok(self.np@, self.sp@, final(buf)@, out.0 as int),
            topk_ok(qkeys(), qfams(), TOPK as nat, v_emits(self.np@, self.sp@, self.u@, self.p1 as int, self.lo as int, self.hi as int),
                tview(self.np@, self.sp@, final(buf)@, out.0 as int), out.1@),
    {
        let ghost np = self.np@;
        let ghost sp = self.sp@;
        let ghost u = self.u@;
        let ghost y = self.p1 as int;
        let ghost lo = self.lo as int;
        proof {
            lemma_unit_facts(*self);
            lemma_topk_empty(qkeys(), qfams(), TOPK as nat);
            assert(tview(np, sp, buf@, 0) =~= Seq::<Row>::empty());
            assert(v_emits(np, sp, u, y, lo, lo) =~= Seq::<Row>::empty());
        }
        let mut len: usize = 0;
        let ghost mut rest = Seq::<Row>::empty();
        let mut p = self.lo;
        while p < self.hi
            invariant
                win_ok(*self),
                np == self.np@, sp == self.sp@, u == self.u@, y == self.p1 as int, lo == self.lo,
                self.lo <= p <= self.hi,
                buf_ok(np, sp, buf@, len as int),
                topk_ok(qkeys(), qfams(), TOPK as nat, v_emits(np, sp, u, y, lo, p as int), tview(np, sp, buf@, len as int), rest),
            decreases self.hi - p,
        {
            proof {
                lemma_unit_facts(*self);
                lemma_vord_in(*self, p as int);
                lemma_kf_num(np, sp);
            }
            let i = self.vorder[p] as usize;
            if len == TOPK && self.value[i] < buf[TOPK - 1].value {
                // Every later row has a value below the last top row's: all are rejected.
                let ghost t = tview(np, sp, buf@, len as int);
                proof {
                    lemma_tail_rejected(*self, p as int, self.hi as int, v_emits(np, sp, u, y, lo, p as int), t, rest, buf@[TOPK - 1]);
                    lemma_v_emits_split(np, sp, u, y, lo, p as int, self.hi as int);
                }
                return (len, Ghost(rest + v_emits(np, sp, u, y, p as int, self.hi as int)));
            }
            let ghost prev = v_emits(np, sp, u, y, lo, p as int);
            let (nl, Ghost(nr)) = self.visit(buf, len, p, Ghost(prev), Ghost(rest));
            proof {
                rest = nr;
                assert(v_emits(np, sp, u, y, lo, p + 1) == prev + row_emit(np, sp, u, y, vord(np)[p as int] as int));
            }
            len = nl;
            p = p + 1;
        }
        (len, Ghost(rest))
    }
}

/// Every stored row in `[lo, hi)` has tag code `tc` and a value of at most `v`.
#[verifier::opaque]
pub open spec fn seg_le(np: Seq<PartView>, lo: int, hi: int, tc: int, v: int) -> bool {
    forall|k: int| lo <= k < hi ==> #[trigger] tagc(np, k) == tc && n_value(np)[k] <= v
}

proof fn lemma_seg_one(np: Seq<PartView>, i: int, tc: int, v: int)
    requires tagc(np, i) == tc, n_value(np)[i] == v,
    ensures seg_le(np, i, i + 1, tc, v),
{
    reveal(seg_le);
}

proof fn lemma_seg_extend_down(np: Seq<PartView>, lo: int, hi: int, tc: int, v: int)
    requires seg_le(np, lo, hi, tc, v), tagc(np, lo - 1) == tc, n_value(np)[lo - 1] <= v,
    ensures seg_le(np, lo - 1, hi, tc, v),
{
    reveal(seg_le);
}

proof fn lemma_seg_extend_up(np: Seq<PartView>, lo: int, hi: int, tc: int, v: int)
    requires seg_le(np, lo, hi, tc, v), tagc(np, hi) == tc, n_value(np)[hi] <= v,
    ensures seg_le(np, lo, hi + 1, tc, v),
{
    reveal(seg_le);
}

proof fn lemma_seg_at(np: Seq<PartView>, lo: int, hi: int, tc: int, v: int, k: int)
    requires seg_le(np, lo, hi, tc, v), lo <= k < hi,
    ensures tagc(np, k) == tc, n_value(np)[k] <= v,
{
    reveal(seg_le);
    let t = tagc(np, k);
    assert(t == tc);
    assert(n_value(np)[k] <= v);
}

/// `a < b <= c` gives `a < c`.
proof fn lemma_lt_le_to_lt(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires lex_cmp(a, b) <= 0, lex_cmp(b, c) < 0,
    ensures lex_cmp(a, c) < 0,
{
    crate::bridge::order::lemma_lex_cmp_trans(a, b, c);
    lemma_lex_cmp_zero(a, c);
    lemma_lex_cmp_zero(a, b);
    if a == c {
        lemma_lex_cmp_antisym(b, c);
    }
}

/// The binary search ended at sorted position `a`: no sub row has adsh `adsh_entry(k)`.
proof fn lemma_no_sub(w: WalkInput, k: int, a: int)
    requires
        win_ok(w), 0 <= k < w.adsh_count, 0 <= a <= w.sub_rows,
        forall|q: int| 0 <= q < a ==> lex_cmp(#[trigger] sub_key(w.sp@, w.adsh_order@[q] as int), adsh_entry(w.np@, k)) < 0,
        a < w.sub_rows ==> lex_cmp(sub_key(w.sp@, w.adsh_order@[a] as int), adsh_entry(w.np@, k)) > 0,
    ensures !has_sub(w.sp@, adsh_entry(w.np@, k)),
{
    let (np, sp) = (w.np@, w.sp@);
    let key = adsh_entry(np, k);
    lemma_kf_sub(np, sp);
    let n = w.sub_rows as int;
    let order = subi::adsh_order(sp);
    if has_sub(sp, key) {
        let j = choose|j: int| 0 <= j < subi::row_count(sp) && #[trigger] subi::adsh_bytes(sp, j) == key;
        lemma_kf_order_pos(np, sp, j);
        let q = choose|q: int| 0 <= q < n && order[q] == j;
        lemma_lex_cmp_zero(sub_key(sp, j), key);
        if q < a {
            assert(lex_cmp(sub_key(sp, order[q] as int), key) < 0);
        } else if q == a {
        } else {
            // key < sub_key(order[a]) <= sub_key(order[q]) = key: impossible.
            assert(lex_cmp(sub_key(sp, order[a] as int), sub_key(sp, order[q] as int)) <= 0);
            lemma_lex_cmp_antisym(sub_key(sp, order[a] as int), key);
            lemma_lt_le_to_lt(key, key, key);
            crate::bridge::order::lemma_lex_cmp_trans(key, sub_key(sp, order[a] as int), sub_key(sp, order[q] as int));
            lemma_lex_cmp_zero(key, sub_key(sp, order[a] as int));
            lemma_lex_cmp_antisym(sub_key(sp, order[a] as int), sub_key(sp, order[q] as int));
        }
    }
}

/// With a full buffer whose last row's value exceeds the value at position `p`, the candidates of positions
/// `[p, q)` all join the rest.
proof fn lemma_tail_rejected(w: WalkInput, p: int, q: int, all: Seq<Row>, t: Seq<Row>, rest: Seq<Row>, last: Cand)
    requires
        win_ok(w), w.lo <= p < w.hi, p <= q <= w.hi,
        topk_ok(qkeys(), qfams(), TOPK as nat, all, t, rest),
        t.len() == TOPK,
        cand_ok(w.np@, w.sp@, last),
        t.last() == cview(w.np@, w.sp@, last),
        w.value@[w.vorder@[p] as int] < last.value,
    ensures ({
        let e = v_emits(w.np@, w.sp@, w.u@, w.p1 as int, p, q);
        topk_ok(qkeys(), qfams(), TOPK as nat, all + e, t, rest + e)
    }),
    decreases q - p,
{
    let (np, sp, u, y) = (w.np@, w.sp@, w.u@, w.p1 as int);
    if q == p {
        assert(v_emits(np, sp, u, y, p, q) =~= Seq::<Row>::empty());
        assert(all + v_emits(np, sp, u, y, p, q) =~= all);
        assert(rest + v_emits(np, sp, u, y, p, q) =~= rest);
    } else {
        lemma_tail_rejected(w, p, q - 1, all, t, rest, last);
        let e0 = v_emits(np, sp, u, y, p, q - 1);
        let i = vord(np)[q - 1] as int;
        let em = row_emit(np, sp, u, y, i);
        assert(v_emits(np, sp, u, y, p, q) == e0 + em);
        if em.len() == 0 {
            assert(em =~= Seq::<Row>::empty());
            assert(all + (e0 + em) =~= all + e0);
            assert(rest + (e0 + em) =~= rest + e0);
        } else {
            lemma_unit_facts(w);
            lemma_vord_in(w, q - 1);
            lemma_kf_num(np, sp);
            lemma_kf_sub(np, sp);
            lemma_kf_dicts(np, sp);
            let r = run_at(np, i);
            let j = sub_of(sp, numi::run_adsh_of(np, r));
            assert(0 <= j < subi::row_count(sp));
            let xc = Cand { value: n_value(np)[i], name: name_code(sp, j) as u64, tag: tagc(np, i) as u64 };
            assert(cand_ok(np, sp, xc));
            let x = cview(np, sp, xc);
            assert(x == cand_row(np, sp, j, i));
            assert(em == seq![x]);
            if q - 1 > p {
                assert(w.value@[w.vorder@[p] as int] >= w.value@[w.vorder@[q - 1] as int]);
            }
            lemma_cview_cmp(np, sp, last, xc);
            lemma_cview_cmp(np, sp, xc, xc);
            lemma_topk_reject(qkeys(), qfams(), TOPK as nat, all + e0, t, rest + e0, x);
            assert(all + (e0 + em) =~= (all + e0).push(x));
            assert(rest + (e0 + em) =~= (rest + e0).push(x));
        }
    }
}

} // verus!
