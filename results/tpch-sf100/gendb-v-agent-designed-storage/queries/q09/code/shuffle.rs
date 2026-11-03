//! The lineitem rows of the matching parts, by scan task (phase 1 of the directory path). Storage `factspk` keeps
//! facts' l_partkey key index (key-index position `r` -> stored lineitem row `irow_m(r)`, sorted by key) with a
//! directory: under `fastdir_ok` (dense part keys `c + 1`, `kb == 1`, one entry per part row and one past) the rows
//! of part row `c` are exactly the positions `[dir[c], dir[c + 1])` (`lemma_dir_part`).
//!
//! One `ShufTask` per range of part rows `[c_lo, c_hi)` walks the matching parts (filter bits) twice: pass A counts
//! the rows per destination chunk (`CH` stored rows, chunk `j / CH` of row `j`), pass B writes each row into its
//! chunk's segment `buf[st[h] .. cur[h])` of a preallocated buffer, with its part's payload at the same position of
//! `pay` (`pay_ok`: the part's compact partsupp table and its entries' index there, so the kernel never reads
//! `l_partkey`). Pass A only sizes the segments; pass B checks every write against the segment end (a full segment
//! fails the task, `ok == false`), so the proof never needs pass A.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::put;
use crate::stores::facts::interface::common::keyidx::{irow, fidx, idx_map, keyidx_ok, lemma_sorted_le, lemma_irow_bound};
use crate::stores::facts::interface::common::colfmt::{is_perm, covered};
use super::model::*;
use super::cols::*;
use super::lookups::*;
use super::qspec::*;
use super::scan::{bit_of, bits_ok, pm, rank_of, BLOCK};
use super::common::popcnt::count_below;
use super::common::grp::*;

verus! {

// ------------------------------------------------------------------------------------------------ the directory

/// The directory layout the shuffle needs, checked at run time (`drive`).
pub open spec fn fastdir_ok(m: M) -> bool {
    &&& p_dense_ok(m)
    &&& pdir_ok(m)
    &&& m.l_kind == 2
    &&& m.kb == 1
    &&& m.dir.len() == m.p_n + 1
    &&& m.l_n <= 0xffff_ffff
}

/// The stored lineitem row at key-index position `r`.
pub open spec fn irow_m(m: M, r: int) -> int {
    irow(m.l_kind, m.l_ic, m.l_ib, m.l_bs, r)
}

/// Key-index positions are stored rows, and every stored row has a position.
proof fn lemma_irow(m: M, r: int)
    requires model_ok(m), fastdir_ok(m), 0 <= r < m.l_n,
    ensures 0 <= irow_m(m, r) < m.l_n, irow_m(m, r) == fidx(m.l_ic, m.l_ib, m.l_bs, r),
{
    lemma_irow_bound(m.l_pk_c, m.l_pk_b, m.l_ic, m.l_ib, m.l_bs, m.l_kind, m.l_n, r);
}

/// Every stored row is at some key-index position.
proof fn lemma_row_pos(m: M, j: int) -> (r: int)
    requires model_ok(m), fastdir_ok(m), 0 <= j < m.l_n,
    ensures 0 <= r < m.l_n, irow_m(m, r) == j,
{
    let im = idx_map(m.l_ic, m.l_ib, m.l_bs, m.l_n);
    assert(is_perm(im, m.l_n));
    assert(covered(im, j));
    let r = choose|r: int| 0 <= r < im.len() && im[r] == j;
    assert(im[r] == fidx(m.l_ic, m.l_ib, m.l_bs, r));
    r
}

/// Keys never decrease along the key index.
proof fn lemma_lkey_le(m: M, a: int, b: int)
    requires model_ok(m), fastdir_ok(m), 0 <= a <= b < m.l_n,
    ensures lkey(m, a) <= lkey(m, b),
{
    lemma_sorted_le(m.l_pk_c, m.l_pk_b, m.l_ic, m.l_ib, m.l_bs, m.l_kind, m.l_n, a, b);
}

/// The positions of part row `c`'s rows are `[dir[c], dir[c + 1])`.
pub proof fn lemma_dir_part(m: M, c: int, r: int)
    requires model_ok(m), fastdir_ok(m), 0 <= c < m.p_n, 0 <= r < m.l_n,
    ensures (m.dir[c] <= r < m.dir[c + 1]) <==> lkey(m, r) == c + 1,
{
    assert(dentry(m, c));
    assert(dentry(m, c + 1));
    let d0 = m.dir[c] as int;
    let d1 = m.dir[c + 1] as int;
    if d0 <= r < d1 {
        assert(lkey(m, r) < m.kb + c + 1);
        lemma_lkey_le(m, d0, r);
    }
    if lkey(m, r) == c + 1 {
        if r < d0 {
            assert(lkey(m, r) < m.kb + c);
        }
        if r >= d1 {
            lemma_lkey_le(m, d1, r);
        }
    }
}

/// A row on a position of part row `c` has part row `c`.
proof fn lemma_part_of(m: M, c: int, r: int)
    requires model_ok(m), fastdir_ok(m), 0 <= c < m.p_n, 0 <= r < m.l_n, lkey(m, r) == c + 1,
    ensures lc(m, irow_m(m, r)) == c, lpk(m, irow_m(m, r)) == c + 1,
{
    assert(pkey(m, c) == c + 1);
    lemma_ppos(m, c + 1, c);
}

/// A matching row's part row has the row at one of its positions.
proof fn lemma_row_of_part(m: M, p: QP, j: int) -> (r: int)
    requires model_ok(m), fastdir_ok(m), 0 <= j < m.l_n, pm(m, p, j),
    ensures 0 <= r < m.l_n, irow_m(m, r) == j, m.dir[lc(m, j)] <= r < m.dir[lc(m, j) + 1],
{
    let c = lc(m, j);
    lemma_ppos(m, lpk(m, j), 0);
    assert(pkey(m, c) == c + 1);
    let r = lemma_row_pos(m, j);
    lemma_dir_part(m, c, r);
    r
}

// ------------------------------------------------------------------------------------------------ destinations

/// Stored lineitem rows per destination chunk (a power of two and a multiple of `BLOCK`).
pub const CH: usize = 262144;

/// The destination chunk of row `j`.
pub open spec fn dt(j: int) -> int {
    j / CH as int
}

/// The number of destination chunks of `n` rows (the last one may be empty).
pub open spec fn nchunks(n: int) -> int {
    n / CH as int + 1
}

/// The context of a payload: the filter bits, their word prefixes, the first rank of every compact partsupp table
/// and the part rows per table.
pub struct PA {
    pub bits: Seq<u64>,
    pub wpre: Seq<u32>,
    pub k0s: Seq<u64>,
    pub per: int,
}

/// Bits of a payload's entries index (below its table).
pub const PSH: u32 = 26;

/// Payload `e` of part row `c`: its table `c / per` (bits from `PSH`) and its entries' index there, its rank minus
/// the table's first rank (bits below `PSH`).
pub open spec fn pay_ok(e: u32, a: PA, c: int) -> bool {
    &&& a.per >= 1
    &&& 0 <= c / a.per < a.k0s.len()
    &&& (e >> 26u32) as int == c / a.per
    &&& (e & 0x3ff_ffffu32) as int == rank_of(a.bits, a.wpre, c) - a.k0s[c / a.per] as int
}

/// Row value `v` with payload `e` belongs to segment `h`: a matching stored row of chunk `h` with its part's payload.
#[verifier::opaque]
pub open spec fn rin(m: M, p: QP, a: PA, v: u32, e: u32, h: int) -> bool {
    &&& (v as int) < m.l_n
    &&& dt(v as int) == h
    &&& pm(m, p, v as int)
    &&& pay_ok(e, a, lc(m, v as int))
}

/// Row `j` is in its chunk's segment.
pub open spec fn placed(buf: Seq<u32>, st: Seq<usize>, cur: Seq<usize>, j: int) -> bool {
    &&& dt(j) < cur.len()
    &&& exists|x: int| st[dt(j)] <= x < cur[dt(j)] && buf[x] as int == j
}

/// Every segment entry is a matching row of its chunk, with its payload.
#[verifier::opaque]
pub open spec fn segs_rin(m: M, p: QP, a: PA, buf: Seq<u32>, pay: Seq<u32>, st: Seq<usize>, cur: Seq<usize>, nd: int) -> bool {
    forall|u: int, x: int| 0 <= u < nd && st[u] <= x < cur[u] ==> #[trigger] rin(m, p, a, buf[x], pay[x], u)
}

/// Every matching row of part rows `[c_lo, k)` is placed.
#[verifier::opaque]
pub open spec fn placed_upto(m: M, p: QP, buf: Seq<u32>, st: Seq<usize>, cur: Seq<usize>, c_lo: int, k: int) -> bool {
    forall|j: int| 0 <= j < m.l_n && pm(m, p, j) && c_lo <= lc(m, j) < k ==> #[trigger] placed(buf, st, cur, j)
}

/// The rows at key-index positions `[r0, r)` are placed.
#[verifier::opaque]
pub open spec fn placed_pos(m: M, buf: Seq<u32>, st: Seq<usize>, cur: Seq<usize>, r0: int, r: int) -> bool {
    forall|q: int| r0 <= q < r ==> #[trigger] placed(buf, st, cur, irow_m(m, q))
}

/// Segments `[st[h], cur[h])` in order.
pub open spec fn segs_order(st: Seq<usize>, cur: Seq<usize>, nd: int) -> bool {
    &&& st.len() == nd + 1 && cur.len() == nd
    &&& forall|h: int| 0 <= h < nd ==> #[trigger] st[h] <= cur[h] && cur[h] <= st[h + 1]
}

/// Segments `[st[h], cur[h])` inside the buffers, disjoint and in order.
pub open spec fn segs_wf(buf: Seq<u32>, pay: Seq<u32>, st: Seq<usize>, cur: Seq<usize>, nd: int) -> bool {
    &&& segs_order(st, cur, nd)
    &&& st[nd] <= buf.len()
    &&& pay.len() == buf.len()
}

// ------------------------------------------------------------------------------------------------ the task

pub struct ShufTask {
    pub cols: Cols,
    pub divs: Divs,
    pub bits: Arc<Vec<u64>>,
    pub wpre: Arc<Vec<u32>>,
    pub k0s: Arc<Vec<u64>>,
    pub edv: Div,
    pub nd: usize,
    pub c_lo: usize,
    pub c_hi: usize,
    pub buf: Vec<u32>,
    pub pay: Vec<u32>,
    pub st: Vec<usize>,
    pub cur: Vec<usize>,
    pub m: Ghost<M>,
    pub p: Ghost<QP>,
}

/// A shuffle task's segments (`ok == false`: the fast layout failed), with its part rows `[c_lo, c_hi)`.
pub struct ShufOut {
    pub ok: bool,
    pub buf: Vec<u32>,
    pub pay: Vec<u32>,
    pub st: Vec<usize>,
    pub cur: Vec<usize>,
    pub c_lo: Ghost<int>,
    pub c_hi: Ghost<int>,
}

/// The payload context of a task.
pub open spec fn pa_of(t: ShufTask) -> PA {
    PA { bits: (*t.bits)@, wpre: (*t.wpre)@, k0s: (*t.k0s)@, per: t.edv.bs as int }
}

pub open spec fn shuf_pre(t: ShufTask) -> bool {
    let m = t.m@;
    &&& look_ok(t.cols, t.divs, m)
    &&& fastdir_ok(m)
    &&& bits_ok((*t.bits)@, m, t.p@)
    &&& (*t.wpre)@.len() * 64 >= m.p_n
    &&& div_ok(t.edv, t.edv.bs as int)
    &&& t.c_lo <= t.c_hi <= m.p_n
    &&& t.nd as int == nchunks(m.l_n)
    &&& t.st@.len() == t.nd + 1 && t.cur@.len() == t.nd
    &&& t.pay@.len() == t.buf@.len()
}

/// The segment entries of every chunk of one shuffle result (part rows `[o.c_lo, o.c_hi)`): matching rows of the
/// chunk with their payloads, every such row of those part rows.
pub open spec fn res_one_ok(o: ShufOut, m: M, p: QP, a: PA) -> bool {
    let nd = nchunks(m.l_n);
    &&& segs_wf(o.buf@, o.pay@, o.st@, o.cur@, nd)
    &&& forall|u: int, x: int| 0 <= u < nd && o.st@[u] <= x < o.cur@[u] ==> #[trigger] rin(m, p, a, o.buf@[x], o.pay@[x], u)
    &&& forall|j: int| 0 <= j < m.l_n && pm(m, p, j) && o.c_lo@ <= lc(m, j) < o.c_hi@ ==> #[trigger] placed(o.buf@, o.st@, o.cur@, j)
}

/// The rows of the task's matching parts, each in its chunk's segment with its payload, and nothing else.
pub open spec fn shuf_post(t: ShufTask, out: ShufOut) -> bool {
    &&& out.st@.len() == t.nd + 1 && out.cur@.len() == t.nd
    &&& out.c_lo@ == t.c_lo && out.c_hi@ == t.c_hi
    &&& out.ok ==> res_one_ok(out, t.m@, t.p@, pa_of(t))
}

/// The stored row at key-index position `r` (fast layout).
fn row_at(c: &Cols, d: &Divs, r: usize, Ghost(m): Ghost<M>) -> (j: usize)
    requires look_ok(*c, *d, m), model_ok(m), fastdir_ok(m), r < m.l_n,
    ensures j as int == irow_m(m, r as int), j < m.l_n,
    no_unwind
{
    proof {
        lemma_irow(m, r as int);
        lemma_block(r as int, m.l_bs, m.l_n, m.l_nb);
        assert(keyidx_ok(m.l_pk_c, m.l_pk_b, m.l_ic, m.l_ib, m.l_bs, m.l_kind, m.l_n));
        crate::stores::facts::interface::common::read::lemma_div_lt(r as int, m.l_bs, m.l_ib.len() as int);
    }
    let g = grp(r, d.l);
    let v = c.l_ib[g] as u128 + c.l_ic[r] as u128;
    v as usize
}

/// Bit `c` of the filter bits.
fn bit_at(bits: &Vec<u64>, c: usize) -> (b: bool)
    requires c / 64 < bits@.len(),
    ensures b == bit_of(bits@, c as int),
    no_unwind
{
    (bits[c / 64] >> ((c % 64) as u64)) & 1u64 == 1u64
}

/// The directory entry of part row `c` (`c <= p_n`).
fn dir_at(c: &Cols, i: usize, Ghost(m): Ghost<M>) -> (d: usize)
    requires cols_ok(*c, m), fastdir_ok(m), i <= m.p_n,
    ensures d as int == m.dir[i as int] as int, d <= m.l_n,
    no_unwind
{
    proof { assert(dentry(m, i as int)); }
    c.dir[i] as usize
}

/// Pass A: the rows of the matching parts of `[c_lo, c_hi)` per destination chunk, added to `cnt` (`false`: some
/// count would exceed `cap`).
fn count_rows(c: &Cols, d: &Divs, bits: &Vec<u64>, c_lo: usize, c_hi: usize, cap: usize, cnt: &mut Vec<usize>,
    Ghost(m): Ghost<M>) -> (ok: bool)
    requires
        look_ok(*c, *d, m), model_ok(m), fastdir_ok(m),
        bits@.len() * 64 >= m.p_n,
        c_lo <= c_hi <= m.p_n,
        old(cnt)@.len() == nchunks(m.l_n),
    ensures
        final(cnt)@.len() == old(cnt)@.len(),
    no_unwind
{
    let mut ok = true;
    let mut k = c_lo;
    while k < c_hi && ok
        invariant
            look_ok(*c, *d, m), model_ok(m), fastdir_ok(m),
            bits@.len() * 64 >= m.p_n,
            c_lo <= k <= c_hi <= m.p_n,
            cnt@.len() == nchunks(m.l_n),
        decreases c_hi - k,
    {
        proof { lemma_word_of(k as int, m.p_n, bits@.len() as int); }
        if bit_at(bits, k) {
            let r1 = dir_at(c, k + 1, Ghost(m));
            let mut r = dir_at(c, k, Ghost(m));
            while r < r1 && ok
                invariant
                    look_ok(*c, *d, m), model_ok(m), fastdir_ok(m),
                    r1 <= m.l_n,
                    cnt@.len() == nchunks(m.l_n),
                decreases r1 - r,
            {
                let j = row_at(c, d, r, Ghost(m));
                proof { lemma_chunk_lt(j as int, m.l_n); }
                let h = j / CH;
                if cnt[h] < cap {
                    let x = cnt[h] + 1;
                    put(cnt, h, x);
                } else {
                    ok = false;
                }
                r = r + 1;
            }
        }
        k = k + 1;
    }
    ok
}

/// A row below `n` has its chunk below `nchunks(n)`.
proof fn lemma_chunk_lt(j: int, n: int)
    requires 0 <= j < n,
    ensures 0 <= dt(j) < nchunks(n),
{
    assert(j / 262144 <= n / 262144) by (nonlinear_arith) requires 0 <= j < n;
}

/// A part row below `n <= len * 64` has its word below `len`.
proof fn lemma_word_of(c: int, n: int, len: int)
    requires 0 <= c < n, n <= len * 64,
    ensures 0 <= c / 64 < len,
{
    assert(c / 64 < len) by (nonlinear_arith) requires 0 <= c < len * 64;
}

/// Segment starts from the counts in `cur`: `st[h]` = the counts before `h`, then `cur[h] = st[h]` (`false`: the
/// total exceeds `cap`).
fn seg_starts(st: &mut Vec<usize>, cur: &mut Vec<usize>, nd: usize, cap: usize) -> (ok: bool)
    requires
        old(st)@.len() == nd + 1, old(cur)@.len() == nd,
    ensures
        final(st)@.len() == nd + 1, final(cur)@.len() == nd,
        ok ==> final(st)@[nd as int] <= cap && segs_order(final(st)@, final(cur)@, nd as int),
        ok ==> forall|h: int| 0 <= h < nd ==> #[trigger] final(cur)@[h] == final(st)@[h],
    no_unwind
{
    let mut acc: usize = 0;
    let mut t: usize = 0;
    while t < nd
        invariant
            st@.len() == nd + 1, cur@.len() == nd,
            t <= nd, acc <= cap,
            forall|u: int| 0 <= u < t ==> #[trigger] st@[u] <= (if u + 1 < t { st@[u + 1] as int } else { acc as int }) && cur@[u] == st@[u],
        decreases nd - t,
    {
        let n_t = cur[t];
        if n_t > cap - acc {
            return false;
        }
        let ghost s0 = st@;
        let ghost c0 = cur@;
        put(st, t, acc);
        put(cur, t, acc);
        proof {
            assert forall|u: int| 0 <= u < t + 1 implies #[trigger] st@[u] <= (if u + 1 < t + 1 { st@[u + 1] as int } else { (acc + n_t) as int }) && cur@[u] == st@[u] by {
                if u < t {
                    assert(st@[u] == s0[u] && cur@[u] == c0[u]);
                    if u + 1 < t { assert(st@[u + 1] == s0[u + 1]); } else { assert(st@[u + 1] == acc); }
                }
            }
        }
        acc = acc + n_t;
        t = t + 1;
    }
    let ghost s0 = st@;
    put(st, nd, acc);
    proof {
        assert forall|u: int| 0 <= u < nd implies #[trigger] st@[u] <= cur@[u] && cur@[u] <= st@[u + 1] by {
            assert(st@[u] == s0[u]);
            if u + 1 < nd { assert(st@[u + 1] == s0[u + 1]); }
        }
        assert forall|u: int| 0 <= u < nd implies #[trigger] cur@[u] == st@[u] by {
            assert(st@[u] == s0[u]);
        }
    }
    true
}

/// The payload of matching part row `k`: its table `k / per` and its entries' index there (`None`: they do not fit
/// the halves or the tables).
fn part_pay(bits: &Vec<u64>, wpre: &Vec<u32>, k0s: &Vec<u64>, edv: Div, k: usize, Ghost(a): Ghost<PA>) -> (r: Option<u32>)
    requires
        a.bits == bits@, a.wpre == wpre@, a.k0s == k0s@, a.per == edv.bs as int, div_ok(edv, edv.bs as int),
        k / 64 < bits@.len(), k / 64 < wpre@.len(),
    ensures r matches Some(e) ==> pay_ok(e, a, k as int),
    no_unwind
{
    let w = k / 64;
    let rank = wpre[w] as u64 + count_below(bits[w], (k % 64) as u64);
    let tb = grp(k, edv);
    if tb >= k0s.len() || tb >= 64 {
        return None;
    }
    let k0 = k0s[tb];
    if rank < k0 || rank - k0 > 0x3ff_ffff {
        return None;
    }
    let local = (rank - k0) as u32;
    let tb32 = tb as u32;
    let e = (tb32 << 26u32) | local;
    proof {
        assert((e >> 26u32) == tb32) by (bit_vector) requires e == (tb32 << 26u32) | local, tb32 < 64u32, local <= 0x3ff_ffffu32;
        assert((e & 0x3ff_ffffu32) == local) by (bit_vector) requires e == (tb32 << 26u32) | local, tb32 < 64u32, local <= 0x3ff_ffffu32;
        assert(rank as int == rank_of(a.bits, a.wpre, k as int));
    }
    Some(e)
}

impl WorkerTask for ShufTask {
    type Output = ShufOut;

    open spec fn pre(&self) -> bool {
        shuf_pre(*self)
    }

    open spec fn post(&self, out: ShufOut) -> bool {
        shuf_post(*self, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.c_lo as u64, self.c_hi as u64)
    }

    fn run(self) -> (out: ShufOut) {
        let ghost task = self;
        let ghost a = pa_of(task);
        let ShufTask { cols, divs, bits, wpre, k0s, edv, nd, c_lo, c_hi, buf, pay, st, cur, m: gm, p: gp } = self;
        let ghost m = gm@;
        let ghost p = gp@;
        let c = cols;
        let d = divs;
        let mut buf = buf;
        let mut pay = pay;
        let mut st = st;
        let mut cur = cur;
        let cap = buf.len();
        let ok = count_rows(&c, &d, &bits, c_lo, c_hi, cap, &mut cur, Ghost(m));
        if !ok {
            return ShufOut { ok: false, buf, pay, st, cur, c_lo: Ghost(c_lo as int), c_hi: Ghost(c_hi as int) };
        }
        let ok = seg_starts(&mut st, &mut cur, nd, cap);
        if !ok {
            return ShufOut { ok: false, buf, pay, st, cur, c_lo: Ghost(c_lo as int), c_hi: Ghost(c_hi as int) };
        }
        let ghost st0 = st@;
        proof {
            reveal(segs_rin);
            reveal(placed_upto);
            assert forall|u: int| 0 <= u < nd implies #[trigger] st@[u] <= cur@[u] && cur@[u] <= st@[u + 1] by {
                assert(cur@[u] == st@[u]);
            }
        }
        let mut ok = true;
        let mut k = c_lo;
        while k < c_hi && ok
            invariant
                task.pre(), m == task.m@, p == task.p@, a == pa_of(task),
                c == task.cols, d == task.divs, bits == task.bits, wpre == task.wpre, k0s == task.k0s, edv == task.edv,
                nd == task.nd, c_lo == task.c_lo, c_hi == task.c_hi,
                c_lo <= k <= c_hi,
                buf@.len() == cap, st@ == st0, cur@.len() == nd,
                segs_wf(buf@, pay@, st@, cur@, nd as int),
                segs_rin(m, p, a, buf@, pay@, st@, cur@, nd as int),
                ok ==> placed_upto(m, p, buf@, st@, cur@, c_lo as int, k as int),
            decreases c_hi - k,
        {
            proof {
                lemma_word_of(k as int, m.p_n, (*bits)@.len() as int);
                lemma_word_of(k as int, m.p_n, (*wpre)@.len() as int);
            }
            if bit_at(&bits, k) {
                match part_pay(&bits, &wpre, &k0s, edv, k, Ghost(a)) {
                    None => {
                        ok = false;
                    },
                    Some(e) => {
                        let r0 = dir_at(&c, k, Ghost(m));
                        let r1 = dir_at(&c, k + 1, Ghost(m));
                        let mut r = r0;
                        proof { reveal(placed_pos); }
                        while r < r1 && ok
                            invariant
                                task.pre(), m == task.m@, p == task.p@, a == pa_of(task),
                                c == task.cols, d == task.divs, bits == task.bits, nd == task.nd,
                                c_lo == task.c_lo, c_hi == task.c_hi,
                                c_lo <= k < c_hi, bit_of((*bits)@, k as int), pay_ok(e, a, k as int),
                                r0 as int == m.dir[k as int], r1 as int == m.dir[k + 1], r0 <= r, r1 <= m.l_n,
                                buf@.len() == cap, st@ == st0, cur@.len() == nd,
                                segs_wf(buf@, pay@, st@, cur@, nd as int),
                                segs_rin(m, p, a, buf@, pay@, st@, cur@, nd as int),
                                ok ==> placed_upto(m, p, buf@, st@, cur@, c_lo as int, k as int),
                                ok ==> placed_pos(m, buf@, st@, cur@, r0 as int, r as int),
                            decreases r1 - r,
                        {
                            let j = row_at(&c, &d, r, Ghost(m));
                            proof {
                                lemma_chunk_lt(j as int, m.l_n);
                                lemma_dir_part(m, k as int, r as int);
                                lemma_part_of(m, k as int, r as int);
                                assert(pm(m, p, j as int));
                                reveal(rin);
                                assert(rin(m, p, a, j as u32, e, dt(j as int)));
                            }
                            let h = j / CH;
                            let ghost b0 = buf@;
                            let ghost u0 = cur@;
                            let placed_ok = place_row(&mut buf, &mut pay, &mut cur, &st, h, j, e, nd, Ghost(m), Ghost(p), Ghost(a));
                            proof {
                                if ok && placed_ok {
                                    lemma_upto_keep(m, p, b0, buf@, st@, u0, cur@, c_lo as int, k as int);
                                    reveal(placed_pos);
                                    assert forall|q: int| r0 <= q < r + 1 implies #[trigger] placed(buf@, st@, cur@, irow_m(m, q)) by {
                                        if q < r {
                                            assert(placed(b0, st@, u0, irow_m(m, q)));
                                        }
                                    }
                                }
                            }
                            ok = ok && placed_ok;
                            r = r + 1;
                        }
                        proof {
                            if ok {
                                reveal(placed_upto);
                                reveal(placed_pos);
                                assert forall|j: int| 0 <= j < m.l_n && pm(m, p, j) && c_lo <= lc(m, j) < k + 1 implies
                                    #[trigger] placed(buf@, st@, cur@, j) by {
                                    if lc(m, j) == k {
                                        let q = lemma_row_of_part(m, p, j);
                                        assert(placed(buf@, st@, cur@, irow_m(m, q)));
                                    }
                                }
                            }
                        }
                    },
                }
            } else {
                proof {
                    if ok {
                        reveal(placed_upto);
                        assert forall|j: int| 0 <= j < m.l_n && pm(m, p, j) && c_lo <= lc(m, j) < k + 1 implies
                            #[trigger] placed(buf@, st@, cur@, j) by {
                            if lc(m, j) == k {
                                assert(pmatch(m, p, k as int));
                            }
                        }
                    }
                }
            }
            k = k + 1;
        }
        proof {
            reveal(segs_rin);
            reveal(placed_upto);
        }
        ShufOut { ok, buf, pay, st, cur, c_lo: Ghost(c_lo as int), c_hi: Ghost(c_hi as int) }
    }
}

/// Writing row `j` at the end of its segment keeps every placed row placed and places `j`.
proof fn lemma_place_step(b0: Seq<u32>, b1: Seq<u32>, st: Seq<usize>, u0: Seq<usize>, u1: Seq<usize>, nd: int, h: int, j: int)
    requires
        segs_order(st, u0, nd), st[nd] <= b0.len(),
        0 <= h < nd, u0[h] < st[h + 1],
        b1 == b0.update(u0[h] as int, j as u32), 0 <= j <= u32::MAX,
        u1 == u0.update(h, (u0[h] + 1) as usize),
        dt(j) == h,
    ensures
        segs_order(st, u1, nd),
        placed(b1, st, u1, j),
        forall|j2: int| #[trigger] placed(b0, st, u0, j2) ==> placed(b1, st, u1, j2),
{
    lemma_st_mono(st, u0, nd, h + 1, nd);
    assert(b1[u0[h] as int] as int == j);
    assert forall|j2: int| #[trigger] placed(b0, st, u0, j2) implies placed(b1, st, u1, j2) by {
        let h2 = dt(j2);
        let x = choose|x: int| st[h2] <= x < u0[h2] && b0[x] as int == j2;
        assert(0 <= h2 < nd);
        if h2 == h {
            assert(x != u0[h]);
        } else {
            assert(x != u0[h]) by {
                if h2 < h { assert(u0[h2] <= st[h2 + 1]); lemma_st_mono(st, u0, nd, h2 + 1, h); }
                else { lemma_st_mono(st, u0, nd, h + 1, h2); }
            }
        }
        assert(b1[x] == b0[x]);
    }
    assert forall|u: int| 0 <= u < nd implies #[trigger] st[u] <= u1[u] && u1[u] <= st[u + 1] by {}
}

/// Writing a row of chunk `h` with its payload at the end of its segment keeps every segment entry a row of its
/// chunk with its payload.
proof fn lemma_rin_step(m: M, p: QP, a: PA, b0: Seq<u32>, b1: Seq<u32>, y0: Seq<u32>, y1: Seq<u32>, st: Seq<usize>,
    u0: Seq<usize>, u1: Seq<usize>, nd: int, h: int, v: u32, e: u32)
    requires
        segs_wf(b0, y0, st, u0, nd),
        segs_rin(m, p, a, b0, y0, st, u0, nd),
        0 <= h < nd, u0[h] < st[h + 1],
        b1 == b0.update(u0[h] as int, v),
        y1 == y0.update(u0[h] as int, e),
        u1 == u0.update(h, (u0[h] + 1) as usize),
        rin(m, p, a, v, e, h),
    ensures segs_rin(m, p, a, b1, y1, st, u1, nd),
{
    reveal(segs_rin);
    let x = u0[h] as int;
    assert forall|u: int, y: int| 0 <= u < nd && st[u] <= y < u1[u] implies #[trigger] rin(m, p, a, b1[y], y1[y], u) by {
        lemma_st_mono(st, u0, nd, u + 1, nd);
        assert(u1[u] <= st[u + 1]);
        if u == h && y == x {
        } else {
            assert(y != x) by {
                if u < h { lemma_st_mono(st, u0, nd, u + 1, h); }
                if u > h { lemma_st_mono(st, u0, nd, h + 1, u); }
            }
            assert(b1[y] == b0[y]);
            assert(y1[y] == y0[y]);
            assert(y < u0[u]);
        }
    }
}

/// A write that keeps every placed row placed keeps `placed_upto`.
proof fn lemma_upto_keep(m: M, p: QP, b0: Seq<u32>, b1: Seq<u32>, st: Seq<usize>, u0: Seq<usize>, u1: Seq<usize>, c_lo: int, k: int)
    requires
        placed_upto(m, p, b0, st, u0, c_lo, k),
        forall|j2: int| #[trigger] placed(b0, st, u0, j2) ==> placed(b1, st, u1, j2),
    ensures placed_upto(m, p, b1, st, u1, c_lo, k),
{
    reveal(placed_upto);
    assert forall|j: int| 0 <= j < m.l_n && pm(m, p, j) && c_lo <= lc(m, j) < k implies #[trigger] placed(b1, st, u1, j) by {
        assert(placed(b0, st, u0, j));
    }
}

/// Segment starts never decrease.
pub proof fn lemma_st_mono(st: Seq<usize>, cur: Seq<usize>, nd: int, a: int, b: int)
    requires segs_order(st, cur, nd), 0 <= a <= b <= nd,
    ensures st[a] <= st[b],
    decreases b - a,
{
    if a < b {
        lemma_st_mono(st, cur, nd, a + 1, b);
        assert(st[a] <= cur[a] && cur[a] <= st[a + 1]);
    }
}

/// Write matching row `j` of chunk `h` with payload `e` at the end of its segment (`false`: the segment is full;
/// nothing changes).
fn place_row(buf: &mut Vec<u32>, pay: &mut Vec<u32>, cur: &mut Vec<usize>, st: &Vec<usize>, h: usize, j: usize, e: u32, nd: usize,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(a): Ghost<PA>) -> (ok: bool)
    requires
        segs_wf(old(buf)@, old(pay)@, st@, old(cur)@, nd as int),
        segs_rin(m, p, a, old(buf)@, old(pay)@, st@, old(cur)@, nd as int),
        h < nd, dt(j as int) == h, j <= u32::MAX,
        rin(m, p, a, j as u32, e, h as int),
    ensures
        final(buf)@.len() == old(buf)@.len(), final(cur)@.len() == old(cur)@.len(),
        segs_wf(final(buf)@, final(pay)@, st@, final(cur)@, nd as int),
        segs_rin(m, p, a, final(buf)@, final(pay)@, st@, final(cur)@, nd as int),
        forall|j2: int| #[trigger] placed(old(buf)@, st@, old(cur)@, j2) ==> placed(final(buf)@, st@, final(cur)@, j2),
        ok ==> placed(final(buf)@, st@, final(cur)@, j as int),
    no_unwind
{
    if cur[h] < st[h + 1] {
        let ghost b0 = buf@;
        let ghost y0 = pay@;
        let ghost u0 = cur@;
        let x = cur[h];
        proof { lemma_st_mono(st@, u0, nd as int, h + 1, nd as int); }
        put(buf, x, j as u32);
        put(pay, x, e);
        put(cur, h, x + 1);
        proof {
            lemma_place_step(b0, buf@, st@, u0, cur@, nd as int, h as int, j as int);
            lemma_rin_step(m, p, a, b0, buf@, y0, pay@, st@, u0, cur@, nd as int, h as int, j as u32, e);
        }
        true
    } else {
        false
    }
}

// ------------------------------------------------------------------------------------------------ scan task ranges

/// First row of scan task `t` (task ends `his`).
pub open spec fn lo_of(his: Seq<usize>, t: int) -> int {
    if t == 0 { 0 } else { his[t - 1] as int }
}

/// Scan task ends over the rows `[0, n)`: nondecreasing, the last is `n`.
pub open spec fn his_ok(his: Seq<usize>, n: int) -> bool {
    &&& his.len() >= 1
    &&& his[his.len() - 1] == n
    &&& forall|t: int| 0 <= t < his.len() ==> #[trigger] his[t] <= n && lo_of(his, t) <= his[t]
}

// ------------------------------------------------------------------------------------------------ the driver

/// The shuffle results of consecutive part ranges covering every part row, each with its chunks' segments.
pub open spec fn res_ok(rs: Seq<ShufOut>, m: M, p: QP, a: PA) -> bool {
    &&& rs.len() >= 1
    &&& rs[0].c_lo@ == 0
    &&& rs[rs.len() - 1].c_hi@ >= m.p_n
    &&& forall|s: int| 0 <= s < rs.len() - 1 ==> #[trigger] rs[s].c_hi@ == rs[s + 1].c_lo@
    &&& forall|s: int| 0 <= s < rs.len() ==> #[trigger] res_one_ok(rs[s], m, p, a)
}

/// Consecutive shuffle tasks over the part rows `[0, hi)`, with the shared fields.
pub open spec fn stasks_ok(ts: Seq<ShufTask>, c: Cols, d: Divs, bits: Arc<Vec<u64>>, wpre: Arc<Vec<u32>>, k0s: Arc<Vec<u64>>,
    edv: Div, nd: int, m: M, p: QP, hi: int) -> bool {
    &&& forall|s: int| 0 <= s < ts.len() ==> #[trigger] shuf_pre(ts[s])
    &&& forall|s: int| 0 <= s < ts.len() ==> (#[trigger] ts[s]).cols == c && ts[s].divs == d && ts[s].bits == bits
            && ts[s].wpre == wpre && ts[s].k0s == k0s && ts[s].edv == edv && ts[s].nd == nd && ts[s].m@ == m && ts[s].p@ == p
    &&& ts.len() >= 1 ==> ts[0].c_lo == 0 && ts[ts.len() - 1].c_hi == hi
    &&& ts.len() == 0 ==> hi == 0
    &&& forall|s: int| 0 <= s < ts.len() - 1 ==> #[trigger] ts[s].c_hi == ts[s + 1].c_lo
}

/// The matching rows of every destination chunk from the directory, in the segments of one result per part range,
/// with their payloads (`None`: the fast layout does not hold, or a payload or a segment did not fit).
pub fn shuffle_rows(c: Cols, d: Divs, bits: &Arc<Vec<u64>>, wpre: &Arc<Vec<u32>>, k0s: &Arc<Vec<u64>>, edv: Div,
    p_dense: bool, workers: usize, dispatch: &mut Dispatch, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: Result<Option<Arc<Vec<ShufOut>>>, QueryError>)
    requires
        look_ok(c, d, m), pdir_ok(m),
        bits_ok((**bits)@, m, p),
        (**wpre)@.len() * 64 >= m.p_n,
        div_ok(edv, edv.bs as int),
        p_dense ==> p_dense_ok(m),
        1 <= workers <= 64,
    ensures
        r matches Ok(Some(rs)) ==> fastdir_ok(m) && res_ok((*rs)@, m, p, PA { bits: (**bits)@, wpre: (**wpre)@, k0s: (**k0s)@, per: edv.bs as int }),
        r matches Err(e) ==> e is WorkerFailed,
{
    let n = c.p_n;
    if !p_dense || c.l_kind != 2 || c.kb != 1 || c.dir.len() == 0 || c.dir.len() - 1 != n || c.l_n > 0xf000_0000 || n == 0 {
        return Ok(None);
    }
    proof { assert(fastdir_ok(m)); }
    let ghost a = PA { bits: (**bits)@, wpre: (**wpre)@, k0s: (**k0s)@, per: edv.bs as int };
    let nd = c.l_n / CH + 1;
    let per = n / workers + 1;
    let mut tasks: Vec<ShufTask> = Vec::new();
    let mut lo: usize = 0;
    while lo < n
        invariant
            look_ok(c, d, m), fastdir_ok(m), bits_ok((**bits)@, m, p),
            (**wpre)@.len() * 64 >= m.p_n, div_ok(edv, edv.bs as int),
            nd as int == nchunks(m.l_n), n == m.p_n, n >= 1,
            1 <= workers <= 64, per >= 1,
            lo <= n, tasks.len() <= workers, tasks.len() == workers ==> lo == n,
            stasks_ok(tasks@, c, d, *bits, *wpre, *k0s, edv, nd as int, m, p, lo as int),
        decreases n - lo,
    {
        let last = tasks.len() + 1 == workers || n - lo <= per;
        let hi = if last { n } else { lo + per };
        proof { assert(dentry(m, lo as int) && dentry(m, hi as int)); }
        let d0 = c.dir[lo] as usize;
        let d1 = c.dir[hi] as usize;
        let cap = if d1 >= d0 { d1 - d0 } else { 0 };
        let t = ShufTask { cols: c, divs: d, bits: bits.clone(), wpre: wpre.clone(), k0s: k0s.clone(), edv, nd, c_lo: lo, c_hi: hi,
            buf: vec![0u32; cap], pay: vec![0u32; cap], st: vec![0usize; nd + 1], cur: vec![0usize; nd], m: Ghost(m), p: Ghost(p) };
        let ghost t0 = tasks@;
        tasks.push(t);
        proof {
            assert(tasks@[tasks.len() - 1] == t);
            assert forall|s: int| 0 <= s < tasks.len() implies #[trigger] shuf_pre(tasks@[s]) by {
                if s < t0.len() { assert(tasks@[s] == t0[s]); }
            }
            assert forall|s: int| 0 <= s < tasks.len() implies (#[trigger] tasks@[s]).cols == c && tasks@[s].divs == d
                && tasks@[s].bits == *bits && tasks@[s].wpre == *wpre && tasks@[s].k0s == *k0s && tasks@[s].edv == edv
                && tasks@[s].nd == nd && tasks@[s].m@ == m && tasks@[s].p@ == p by {
                if s < t0.len() { assert(tasks@[s] == t0[s]); }
            }
            assert forall|s: int| 0 <= s < tasks.len() - 1 implies #[trigger] tasks@[s].c_hi == tasks@[s + 1].c_lo by {
                assert(tasks@[s] == t0[s]);
                if s + 1 < t0.len() { assert(tasks@[s + 1] == t0[s + 1]); }
            }
            if t0.len() > 0 { assert(tasks@[0] == t0[0]); }
        }
        lo = hi;
    }
    let ghost ts = tasks@;
    let ns = tasks.len();
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    let mut k: usize = 0;
    while k < ns
        invariant ns == outs.len(), ns == ts.len(), k <= ns,
            forall|s: int| 0 <= s < k ==> (#[trigger] outs@[s]).ok,
        decreases ns - k,
    {
        if !outs[k].ok {
            return Ok(None);
        }
        k = k + 1;
    }
    proof {
        assert(ns >= 1);
        assert forall|s: int| 0 <= s < ns implies #[trigger] res_one_ok(outs@[s], m, p, a) by {
            assert(ts[s].post(outs@[s]));
            assert(outs@[s].ok);
            assert(pa_of(ts[s]) == a);
        }
        assert forall|s: int| 0 <= s < ns - 1 implies #[trigger] outs@[s].c_hi@ == outs@[s + 1].c_lo@ by {
            assert(ts[s].post(outs@[s]));
            assert(ts[s + 1].post(outs@[s + 1]));
        }
        assert(ts[0].post(outs@[0]));
        assert(ts[ns - 1].post(outs@[ns - 1]));
    }
    Ok(Some(Arc::new(outs)))
}

} // verus!
