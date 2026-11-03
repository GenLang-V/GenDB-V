//! Q21 scan tasks over storage `li_ordruns` (facts' columns and the l_orderkey run lengths; model: `super::model`). A task covers stored orders rows `[q0, q1)` and the
//! co-clustered lineitem rows of those orders: the lines of each order are one contiguous run, so the task's lines
//! are `[lineitem_start(q0), lineitem_start(q1))` (`merge_inv`, found by binary search over the cursor condition, so
//! tasks are independent; with one run per order, `lineitem_start(q)` is `rstart(q)`, the start of the task's run
//! cursor). Only rows up to the lines of the task's last order with status `F` (`last_f`) are
//! scanned, by the word scan `wscan::scan_range`, which writes the counting rows as an event list (`hits_ok`). The
//! tail task also checks the slot names (`side::names_increasing`). Segments (`Seg`) track the lineitem row group of
//! a cursor incrementally (no division per row). `count_fallback` counts serially for any row order.
use vstd::prelude::*;
use super::common::occ::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::stores::facts::interface::common::keyidx::{fkey, key_find};
use super::model::*;
use super::supp::*;
use super::side::*;
use super::runs::*;

verus! {


/// The stored orders row of stored lineitem row `j`'s order (`rpos`), by the orders key index.
pub fn order_pos_at(c: &Cols, k: Ghost<int>, j: usize) -> (p: usize)
    requires
        cols_ok(*c, k@),
        keys_distinct(*c),
        j < c.n_l,
    ensures
        p as int == rpos(*c, lkey(*c, j as int)),
    no_unwind
{
    proof {
        lemma_div_below(j as int, c.bs_l as int, c.lk_bases@.len() as int);
        assert(in_i64(lkey(*c, j as int)));
    }
    let g = j / c.bs_l;
    let kk = c.lk_bases[g] as i128 + c.lk_codes[j] as i128;
    match key_find(c.ok_codes, c.ok_bases, c.oi_codes, c.oi_bases, c.bs_o, c.oi_kind, c.n_o, kk) {
        Some(p) => {
            proof {
                assert(okey(*c, p as int) == kk);
                lemma_rpos_of(*c, p as int);
            }
            p
        },
        None => {
            proof {
                assert forall|q: int| 0 <= q < c.n_o implies #[trigger] okey(*c, q) != kk by {
                    assert(fkey(c.ok_codes@, c.ok_bases@, c.bs_o as int, q) != kk);
                }
                lemma_rpos_none(*c, kk as int);
            }
            c.n_o
        },
    }
}

/// The first stored lineitem row whose order is at or after stored orders row `q` (binary search; the rows' orders
/// are nondecreasing).
pub fn lineitem_start(c: &Cols, k: Ghost<int>, q: usize) -> (r: usize)
    requires
        cols_ok(*c, k@),
        keys_distinct(*c),
        lines_clustered(*c),
    ensures
        merge_inv(*c, q as int, r as int),
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = c.n_l;
    while lo < hi
        invariant
            cols_ok(*c, k@),
            keys_distinct(*c),
            lines_clustered(*c),
            lo <= hi <= c.n_l,
            lo > 0 ==> rpos(*c, lkey(*c, lo - 1)) < q,
            hi < c.n_l ==> rpos(*c, lkey(*c, hi as int)) >= q,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if order_pos_at(c, k, mid) < q {
            lo = mid + 1;
        } else {
            proof {
                if hi < c.n_l {
                    lemma_lines_le(*c, mid as int, hi as int);
                }
            }
            hi = mid;
        }
    }
    lo
}

/// The lineitem cursor with its group: `gl` is the group of `cur` (when `cur` is a row).
pub open spec fn cursor_ok(c: Cols, cur: int, gl: int) -> bool {
    &&& 0 <= gl
    &&& gl * c.bs_l <= cur
    &&& cur < c.n_l ==> cur < gl * c.bs_l + c.bs_l
}

/// The end of the cursor's group segment: the next group's first row, or the end of the rows.
pub fn seg_end(c: &Cols, k: Ghost<int>, cur: usize, gl: usize) -> (e: usize)
    requires
        cols_ok(*c, k@),
        cur < c.n_l,
        cursor_ok(*c, cur as int, gl as int),
    ensures
        cur <= e <= c.n_l,
        e < c.n_l ==> e == gl * c.bs_l + c.bs_l,
        e <= gl * c.bs_l + c.bs_l,
    no_unwind
{
    let start = gl * c.bs_l;
    if c.bs_l <= c.n_l - start { start + c.bs_l } else { c.n_l }
}

/// The late test of a group's lines as one comparison of codes: `l_commitdate < l_receiptdate` is
/// `lc_code - lr_code < lr_base - lc_base`, the right side clamped to `[-65536, 65536]` (codes are below 65536).
pub fn late_delta(c: &Cols, k: Ghost<int>, gl: usize) -> (d: i64)
    requires
        cols_ok(*c, k@),
        gl < c.lk_bases@.len(),
    ensures
        dl_ok(d as int, c.lr_bases@[gl as int] - c.lc_bases@[gl as int]),
    no_unwind
{
    let dl = c.lr_bases[gl] as i128 - c.lc_bases[gl] as i128;
    if dl >= 65536 {
        65536
    } else if dl <= -65536 {
        -65536
    } else {
        dl as i64
    }
}

/// The code a line of group `gl` has exactly when its key is `key` (`None`: no line of the group has it).
fn key_code(c: &Cols, k: Ghost<int>, gl: usize, key: i64) -> (r: Option<u32>)
    requires
        cols_ok(*c, k@),
        gl < c.lk_bases@.len(),
    ensures
        r matches Some(kc) ==> kc as int == key - c.lk_bases@[gl as int],
        r is None ==> (key - c.lk_bases@[gl as int] < 0 || key - c.lk_bases@[gl as int] > u32::MAX),
    no_unwind
{
    let d = key as i128 - c.lk_bases[gl] as i128;
    if d < 0 || d > 0xffff_ffffi128 {
        None
    } else {
        Some(d as u32)
    }
}

/// Facts of a row in the cursor's group.
pub proof fn lemma_in_group(c: Cols, k: int, j: int, gl: int)
    requires
        cols_ok(c, k),
        0 <= j < c.n_l,
        gl * c.bs_l <= j < gl * c.bs_l + c.bs_l,
    ensures
        j / (c.bs_l as int) == gl,
        0 <= gl < c.lk_bases@.len(),
        lkey(c, j) == c.lk_bases@[gl] + c.lk_codes@[j],
        lsupp(c, j) == c.ls_bases@[gl] + c.ls_codes@[j],
        late(c, j) == (c.lc_codes@[j] - c.lr_codes@[j] < c.lr_bases@[gl] - c.lc_bases@[gl]),
        in_i64(lkey(c, j)) && in_i64(lsupp(c, j)),
{
    lemma_div_group(j, c.bs_l as int, gl);
    lemma_div_below(j, c.bs_l as int, c.lk_bases@.len() as int);
}

/// The cursor's group segment with the group's bases read once: the group `gl`, the end of its rows `gend`, the
/// l_orderkey and l_suppkey bases, and the late test's clamped base difference (`late_delta`).
#[derive(Clone, Copy)]
pub struct Seg {
    pub gl: usize,
    pub gend: usize,
    pub kb: i64,
    pub sb: i64,
    pub dl: i64,
}

/// `dl` is the base difference `diff` clamped to `[-65536, 65536]`.
pub open spec fn dl_ok(dl: int, diff: int) -> bool {
    if diff >= 65536 { dl == 65536 } else if diff <= -65536 { dl == -65536 } else { dl == diff }
}

/// Against a code difference (in `(-65536, 65536)`) the clamped difference decides like the exact one.
pub proof fn lemma_dl(dl: int, diff: int, x: int)
    requires dl_ok(dl, diff), -65536 < x < 65536,
    ensures (x < dl) == (x < diff),
{
}

/// `s` is the segment of row `cur` (nothing is asked at the end of the rows).
pub open spec fn seg_ok(c: Cols, cur: int, s: Seg) -> bool {
    cur < c.n_l ==> {
        &&& s.gl * c.bs_l <= cur < s.gl * c.bs_l + c.bs_l
        &&& s.gl < c.lk_bases@.len()
        &&& cur < s.gend <= c.n_l
        &&& s.gend <= s.gl * c.bs_l + c.bs_l
        &&& s.gend < c.n_l ==> s.gend == s.gl * c.bs_l + c.bs_l
        &&& s.kb == c.lk_bases@[s.gl as int]
        &&& s.sb == c.ls_bases@[s.gl as int]
        &&& dl_ok(s.dl as int, c.lr_bases@[s.gl as int] - c.lc_bases@[s.gl as int])
    }
}

/// The segment of row `cur` in group `gl`.
pub fn seg_at(c: &Cols, k: Ghost<int>, cur: usize, gl: usize) -> (s: Seg)
    requires
        cols_ok(*c, k@),
        cur < c.n_l,
        gl * c.bs_l <= cur < gl * c.bs_l + c.bs_l,
    ensures
        seg_ok(*c, cur as int, s),
        s.gl == gl,
    no_unwind
{
    proof { lemma_in_group(*c, k@, cur as int, gl as int); }
    let gend = seg_end(c, k, cur, gl);
    let dl = late_delta(c, k, gl);
    Seg { gl, gend, kb: c.lk_bases[gl], sb: c.ls_bases[gl], dl }
}

/// The segment of row `cur`, or a placeholder at the end of the rows.
pub fn seg_of(c: &Cols, k: Ghost<int>, cur: usize) -> (s: Seg)
    requires
        cols_ok(*c, k@),
        cur <= c.n_l,
    ensures
        seg_ok(*c, cur as int, s),
    no_unwind
{
    if cur < c.n_l {
        proof { lemma_group_of_row(cur as int, c.bs_l as int); }
        seg_at(c, k, cur, cur / c.bs_l)
    } else {
        Seg { gl: 0, gend: 0, kb: 0, sb: 0, dl: 0 }
    }
}

/// The next segment, when the cursor reached the end of its segment (and not the end of the rows).
pub fn seg_next(c: &Cols, k: Ghost<int>, cur: usize, s: Seg) -> (s2: Seg)
    requires
        cols_ok(*c, k@),
        cur < c.n_l,
        s.gl * c.bs_l <= s.gend,
        cur == s.gend,
        s.gend < c.n_l ==> s.gend == s.gl * c.bs_l + c.bs_l,
    ensures
        seg_ok(*c, cur as int, s2),
    no_unwind
{
    proof {
        lemma_next_group(s.gl as int, c.bs_l as int);
        assert(s.gl <= s.gl * c.bs_l) by (nonlinear_arith) requires c.bs_l >= 1, s.gl >= 0;
    }
    seg_at(c, k, cur, s.gl + 1)
}

/// `a | b` of two flags is their disjunction.
proof fn lemma_or_flag(a: u8, b: u8)
    requires a <= 1, b <= 1,
    ensures (a | b) <= 1, ((a | b) == 1) == (a == 1 || b == 1),
{
    assert((a | b) <= 1 && (((a | b) == 1) == (a == 1 || b == 1))) by (bit_vector) requires a <= 1, b <= 1;
}

/// Whether the codes `cs` hold `t` (a loop without early exit, which the compiler vectorizes).
pub fn has_code(cs: &[u8], n: usize, t: u8) -> (r: bool)
    requires n == cs@.len(),
    ensures r == exists|i: int| 0 <= i < cs@.len() && cs@[i] == t,
    no_unwind
{
    let mut any: u8 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            n == cs@.len(),
            i <= n,
            any <= 1,
            (any == 1) == exists|u: int| 0 <= u < i && cs@[u] == t,
        decreases n - i,
    {
        let b = (cs[i] == t) as u8;
        proof {
            lemma_or_flag(any, b);
            if any | b == 1 && any == 0 {
                assert(cs@[i as int] == t);
            }
            if exists|u: int| 0 <= u < i + 1 && cs@[u] == t {
                let u = choose|u: int| 0 <= u < i + 1 && cs@[u] == t;
                if u < i {
                    assert(any == 1);
                }
            }
        }
        any = any | b;
        i = i + 1;
    }
    any == 1
}

/// Whether stored orders rows `[a, b)` of group `g` (`a < b`) hold status index `f` (code `f - base`).
pub fn seg_has_f(c: &Cols, k: Ghost<int>, g: usize, a: usize, b: usize, f: u64) -> (r: bool)
    requires
        cols_ok(*c, k@),
        a < b <= c.n_o,
        g * c.bs_o <= a,
        b <= g * c.bs_o + c.bs_o,
    ensures r == exists|p: int| a <= p < b && #[trigger] ostat(*c, p) == f,
    no_unwind
{
    proof {
        lemma_div_group(a as int, c.bs_o as int, g as int);
        lemma_div_below(a as int, c.bs_o as int, c.ok_bases@.len() as int);
    }
    let base = c.os_bases[g];
    if base > f || f - base > 255 {
        proof {
            assert forall|p: int| a <= p < b implies #[trigger] ostat(*c, p) != f by {
                lemma_div_group(p, c.bs_o as int, g as int);
            }
        }
        return false;
    }
    let t = (f - base) as u8;
    let (_, tail) = c.os_codes.split_at(a);
    let (seg, _) = tail.split_at(b - a);
    proof { assert(seg@ =~= c.os_codes@.subrange(a as int, b as int)); }
    let r = has_code(seg, b - a, t);
    proof {
        if r {
            let i = choose|i: int| 0 <= i < seg@.len() && seg@[i] == t;
            lemma_div_group(a + i, c.bs_o as int, g as int);
            assert(ostat(*c, a + i) == f);
        }
        assert forall|p: int| a <= p < b && #[trigger] ostat(*c, p) == f implies r by {
            lemma_div_group(p, c.bs_o as int, g as int);
            assert(seg@[p - a] == t);
        }
    }
    r
}

/// One past the last stored orders row of `[q0, q1)` with status index `f`, or `q0` when there is none: group
/// segments are tested from the last one down (`seg_has_f`), then the last segment holding one is walked down.
pub fn last_f(c: &Cols, k: Ghost<int>, f: u64, q0: usize, q1: usize) -> (e: usize)
    requires
        cols_ok(*c, k@),
        q0 <= q1 <= c.n_o,
    ensures
        q0 <= e <= q1,
        forall|p: int| e <= p < q1 ==> #[trigger] ostat(*c, p) != f,
    no_unwind
{
    let bs = c.bs_o;
    let mut hi = q1;
    while hi > q0
        invariant
            cols_ok(*c, k@),
            bs == c.bs_o,
            q0 <= hi <= q1 <= c.n_o,
            forall|p: int| hi <= p < q1 ==> #[trigger] ostat(*c, p) != f,
        decreases hi,
    {
        // The segment of hi - 1's group below hi.
        let g = (hi - 1) / bs;
        proof { lemma_group_of_row((hi - 1) as int, bs as int); }
        let gs = g * bs;
        let a = if gs > q0 { gs } else { q0 };
        if seg_has_f(c, k, g, a, hi, f) {
            let mut p = hi;
            while p > a
                invariant
                    cols_ok(*c, k@),
                    bs == c.bs_o,
                    q0 <= a <= p <= hi <= q1 <= c.n_o,
                    g * bs <= a,
                    hi <= g * bs + bs,
                    forall|u: int| p <= u < q1 ==> #[trigger] ostat(*c, u) != f,
                decreases p,
            {
                proof {
                    lemma_div_group((p - 1) as int, bs as int, g as int);
                    lemma_div_below((p - 1) as int, bs as int, c.ok_bases@.len() as int);
                    assert(0 <= ostat(*c, (p - 1) as int) < k@);
                }
                if c.os_bases[g] + c.os_codes[p - 1] as u64 == f {
                    return p;
                }
                p = p - 1;
            }
            return a;
        }
        hi = a;
    }
    hi
}

/// One scan task: stored orders rows `[q0, q1)`, status index `f`, an event buffer of `cap` entries (filled from
/// its start). The slot map is dense (`scan_range`).
pub struct ScanTask {
    pub cols: Cols,
    pub nk: usize,
    pub sm: SuppMap,
    pub f: u64,
    pub q0: usize,
    pub q1: usize,
    pub buf: Vec<u32>,
    pub cap: usize,
    /// Whether this task also decides `names_inc` of the slot rows `srows` (`ns` of them) of the suppliers `sc`,
    /// so the name reads overlap the scan instead of following it.
    pub names: bool,
    pub sc: SCols,
    pub srows: Vec<usize>,
    pub ns: usize,
}

/// A task's result: the lineitem rows `[lo, hi)` are the lines of its orders; the event list `buf[0 .. used)` holds
/// the counts of `[lo, mid)`, and the rows `[mid, hi)` are left to the caller (only when the buffer ran short).
pub struct ScanOut {
    pub buf: Vec<u32>,
    pub used: usize,
    pub lo: usize,
    pub mid: usize,
    pub hi: usize,
    /// `names_inc` of the task's slot rows (when it decided it).
    pub inc: bool,
    /// The run holding row `mid` (when `mid < hi`): run `rc` starts at row `rs`.
    pub rc: usize,
    pub rs: usize,
}

/// The counters `v` are the counts of `[lo, hi)` for every slot key of `ks`.
pub open spec fn counts_ok(c: Cols, f: int, ks: Seq<i64>, v: Seq<usize>, lo: int, hi: int) -> bool {
    &&& v.len() == ks.len()
    &&& forall|t: int| 0 <= t < ks.len() ==> #[trigger] v[t] as int == cnt(c, f, ks[t] as int, lo, hi)
}

/// The event list `v` (one entry per counting row, naming its slot) holds the counts of `[lo, hi)` for every slot
/// key of `ks`.
pub open spec fn hits_ok(c: Cols, f: int, ks: Seq<i64>, v: Seq<u32>, lo: int, hi: int) -> bool {
    &&& forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i] as int) < ks.len()
    &&& forall|t: int| 0 <= t < ks.len() ==> #[trigger] occ(v, t) as int == cnt(c, f, ks[t] as int, lo, hi)
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        &&& cols_ok(self.cols, self.nk as int)
        &&& keys_distinct(self.cols)
        &&& lines_clustered(self.cols)
        &&& runs_model(self.cols)
        &&& runs_aligned(self.cols)
        &&& smap_ok(self.sm)
        &&& self.sm.dense
        &&& self.sm.range <= 0x400_0000
        &&& self.q0 <= self.q1 <= self.cols.n_o
        &&& self.cap == self.buf@.len()
        &&& self.names ==> scols_ok(self.sc)
        &&& self.names ==> self.ns == self.srows@.len()
        &&& self.names ==> forall|t: int| 0 <= t < self.srows@.len() ==> #[trigger] self.srows@[t] < self.sc.n_s
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        &&& out.lo <= out.mid <= out.hi
        &&& merge_inv(self.cols, self.q0 as int, out.lo as int)
        &&& merge_inv(self.cols, self.q1 as int, out.hi as int)
        &&& out.used <= out.buf@.len()
        &&& hits_ok(self.cols, self.f as int, self.sm.skeys@, out.buf@.subrange(0, out.used as int), out.lo as int,
            out.mid as int)
        &&& self.names ==> out.inc == names_inc(self.sc, self.srows@)
        &&& out.mid < out.hi ==> cur_ok(self.cols, out.rc as int, out.rs as int, out.mid as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.q0 as u64, self.q1 as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let c = self.cols;
        let ghost kk = self.nk as int;
        let sm = self.sm;
        let ghost ks = sm.skeys@;
        let (q0, q1, f) = (self.q0, self.q1, self.f);
        let inc = if self.names { names_increasing(&self.sc, &self.srows, self.ns) } else { false };
        // Word scan of the rows up to the lines of the last order with status f (`wscan`).
        let e = last_f(&c, Ghost(kk), f, q0, q1);
        let lo = lineitem_start(&c, Ghost(kk), q0);
        let hi = lineitem_start(&c, Ghost(kk), q1);
        let le = if e < q1 { lineitem_start(&c, Ghost(kk), e) } else { hi };
        proof {
            lemma_merge_le(c, q0 as int, e as int, lo as int, le as int);
            lemma_merge_le(c, e as int, q1 as int, le as int, hi as int);
            // The lines of the task start with run q0.
            if lo < le {
                if q0 == c.n_o {
                    lemma_merge_le(c, q1 as int, q0 as int, hi as int, lo as int);
                }
                assert(q0 < c.n_o);
                lemma_run_lines(c, q0 as int);
                lemma_merge_le(c, q0 as int, q0 as int, lo as int, rstart(c, q0 as int));
                lemma_merge_le(c, q0 as int, q0 as int, rstart(c, q0 as int), lo as int);
                assert(cur_ok(c, q0 as int, lo as int, lo as int));
            }
        }
        let (buf, used, stop, rc, rs) = super::wscan::scan_range(&c, Ghost(kk), &sm, f, lo, le, q0, lo, self.buf, self.cap);
        // The lines past the last order with status f never count.
        let mid = if stop == le { hi } else { stop };
        proof {
            lemma_merge_gap(c, f as int, 0, e as int, q1 as int, le as int, hi as int);
            assert(lo <= le <= hi);
            if stop == le {
                let hv = buf@.subrange(0, used as int);
                assert forall|t: int| 0 <= t < ks.len() implies #[trigger] occ(hv, t) as int
                    == cnt(c, f as int, ks[t] as int, lo as int, hi as int) by {
                    lemma_merge_gap(c, f as int, ks[t] as int, e as int, q1 as int, le as int, hi as int);
                    lemma_cnt_split(c, f as int, ks[t] as int, lo as int, le as int, hi as int);
                }
            }
        }
        ScanOut { buf, used, lo, mid, hi, inc, rc, rs }
    }
}



/// Merge cursors are monotone in the orders row.
pub proof fn lemma_merge_le(c: Cols, p1: int, p2: int, a: int, b: int)
    requires lines_clustered(c), p1 <= p2, merge_inv(c, p1, a), merge_inv(c, p2, b),
    ensures a <= b,
{
    if b < a {
        lemma_lines_le(c, b, a - 1);
    }
}

// ------------------------------------------------------------------------------------------------ fallback

/// Whether some stored lineitem row of order key `key` has a supplier other than `s` (and, with `need_late`, is
/// late): a scan of every row.
fn has_other(c: &Cols, k: Ghost<int>, key: i64, s: i64, need_late: bool) -> (r: bool)
    requires cols_ok(*c, k@),
    ensures
        r == exists|i: int| 0 <= i < c.n_l && lkey(*c, i) == key && lsupp(*c, i) != s && (!need_late || late(*c, i)),
        !need_late ==> r == has_other_spec(*c, key as int, s as int),
        need_late ==> r == has_late_other_spec(*c, key as int, s as int),
{
    let n_l = c.n_l;
    let mut i: usize = 0;
    while i < n_l
        invariant
            cols_ok(*c, k@),
            n_l == c.n_l,
            i <= n_l,
            forall|u: int| 0 <= u < i ==> !(lkey(*c, u) == key && lsupp(*c, u) != s && (!need_late || late(*c, u))),
        decreases n_l - i,
    {
        proof {
            lemma_div_below(i as int, c.bs_l as int, c.lk_bases@.len() as int);
            assert(in_i64(lkey(*c, i as int)) && in_i64(lsupp(*c, i as int)));
            assert(in_i64(lcmt(*c, i as int)) && in_i64(lrcp(*c, i as int)));
        }
        let g = i / c.bs_l;
        if c.lk_bases[g] + c.lk_codes[i] as i64 == key && c.ls_bases[g] + c.ls_codes[i] as i64 != s {
            if !need_late || c.lc_bases[g] + (c.lc_codes[i] as i64) < c.lr_bases[g] + (c.lr_codes[i] as i64) {
                proof {
                    assert(lkey(*c, i as int) == key && lsupp(*c, i as int) != s);
                }
                return true;
            }
        }
        i = i + 1;
    }
    proof {
        if has_other_spec(*c, key as int, s as int) && !need_late {
            let u = choose|u: int| 0 <= u < c.n_l && lkey(*c, u) == key && lsupp(*c, u) != s;
            assert(!(lkey(*c, u) == key && lsupp(*c, u) != s && (!need_late || late(*c, u))));
        }
        if has_late_other_spec(*c, key as int, s as int) && need_late {
            let u = choose|u: int| 0 <= u < c.n_l && lkey(*c, u) == key && lsupp(*c, u) != s && late(*c, u);
            assert(!(lkey(*c, u) == key && lsupp(*c, u) != s && (!need_late || late(*c, u))));
        }
    }
    false
}

/// The counts over every stored lineitem row for any row order (serial; used when the co-clustering flag is not
/// set): per late row, its order by the orders key index and both subqueries by scans.
pub fn count_fallback(c: &Cols, k: Ghost<int>, sm: &SuppMap, f: u64) -> (v: Vec<usize>)
    requires
        cols_ok(*c, k@),
        keys_distinct(*c),
        smap_ok(*sm),
    ensures
        counts_ok(*c, f as int, sm.skeys@, v@, 0, c.n_l as int),
{
    let ghost ks = sm.skeys@;
    let n_l = c.n_l;
    let mut counts: Vec<usize> = super::common::fill::fill_usize(sm.ns, 0usize);
    let mut j: usize = 0;
    proof {
        assert forall|t: int| 0 <= t < ks.len() implies #[trigger] counts@[t] as int == cnt(*c, f as int, ks[t] as int, 0, 0) by {}
    }
    while j < n_l
        invariant
            cols_ok(*c, k@),
            keys_distinct(*c),
            smap_ok(*sm),
            ks == sm.skeys@,
            n_l == c.n_l,
            j <= n_l,
            counts_ok(*c, f as int, ks, counts@, 0, j as int),
        decreases n_l - j,
    {
        proof {
            lemma_div_below(j as int, c.bs_l as int, c.lk_bases@.len() as int);
            assert(in_i64(lkey(*c, j as int)) && in_i64(lsupp(*c, j as int)));
            assert(in_i64(lcmt(*c, j as int)) && in_i64(lrcp(*c, j as int)));
        }
        let g = j / c.bs_l;
        let lt = c.lc_bases[g] + (c.lc_codes[j] as i64) < c.lr_bases[g] + (c.lr_codes[j] as i64);
        let key = c.lk_bases[g] + c.lk_codes[j] as i64;
        let s = c.ls_bases[g] + c.ls_codes[j] as i64;
        let mut q = false;
        if lt {
            let p = order_pos_at(c, k, j);
            if p < c.n_o {
                proof {
                    lemma_div_below(p as int, c.bs_o as int, c.ok_bases@.len() as int);
                    assert(0 <= ostat(*c, p as int) < k@);
                }
                if c.os_bases[p / c.bs_o] + c.os_codes[p] as u64 == f {
                    if has_other(c, k, key, s, false) && !has_other(c, k, key, s, true) {
                        q = true;
                    }
                }
            }
        }
        let ghost old_counts = counts@;
        proof {
            let jj = j as int;
            assert(key as int == lkey(*c, jj) && s as int == lsupp(*c, jj) && lt == late(*c, jj));
            if lt {
                assert(ex2(*c, jj) == has_other_spec(*c, key as int, s as int)) by {
                    if ex2(*c, jj) {
                        let i = choose|i: int| 0 <= i < c.n_l && #[trigger] other(*c, i, jj);
                        assert(lkey(*c, i) == key && lsupp(*c, i) != s);
                    }
                    if has_other_spec(*c, key as int, s as int) {
                        let i = choose|i: int| 0 <= i < c.n_l && lkey(*c, i) == key && lsupp(*c, i) != s;
                        assert(other(*c, i, jj));
                    }
                }
                assert(ex3(*c, jj) == has_late_other_spec(*c, key as int, s as int)) by {
                    if ex3(*c, jj) {
                        let i = choose|i: int| 0 <= i < c.n_l && #[trigger] other(*c, i, jj) && late(*c, i);
                        assert(lkey(*c, i) == key && lsupp(*c, i) != s && late(*c, i));
                    }
                    if has_late_other_spec(*c, key as int, s as int) {
                        let i = choose|i: int| 0 <= i < c.n_l && lkey(*c, i) == key && lsupp(*c, i) != s && late(*c, i);
                        assert(other(*c, i, jj) && late(*c, i));
                    }
                }
            }
            assert(q == lineq(*c, f as int, jj));
        }
        if q {
            match slot_of(sm, s) {
                Some(t) => {
                    proof { lemma_cnt_bound(*c, f as int, ks[t as int] as int, 0, j as int); }
                    counts[t] = counts[t] + 1;
                },
                None => {},
            }
        }
        proof {
            assert forall|t: int| 0 <= t < ks.len() implies #[trigger] counts@[t] as int == cnt(*c, f as int, ks[t] as int, 0, j + 1) by {
                lemma_cnt_step(*c, f as int, ks[t] as int, 0, j as int);
                assert(old_counts[t] as int == cnt(*c, f as int, ks[t] as int, 0, j as int));
            }
        }
        j = j + 1;
    }
    counts
}

pub open spec fn has_other_spec(c: Cols, key: int, s: int) -> bool {
    exists|i: int| 0 <= i < c.n_l && lkey(c, i) == key && lsupp(c, i) != s
}

pub open spec fn has_late_other_spec(c: Cols, key: int, s: int) -> bool {
    exists|i: int| 0 <= i < c.n_l && lkey(c, i) == key && lsupp(c, i) != s && late(c, i)
}

} // verus!
