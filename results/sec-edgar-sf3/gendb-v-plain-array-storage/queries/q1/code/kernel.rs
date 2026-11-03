//! The scan of one row range `[lo, hi)` of `pre` (the body of a worker task).
//!
//! It keeps up to `GCAP` local groups (`rep[g]`: the first row of group `g`; groups are told apart by their
//! (stmt, rfile) bytes, through an injective 64-bit code for short values), a per-group count and line sum, and
//! per `sub` row `id` the set of local groups having a row whose adsh is `sub` row `id`'s value (`mask[id]`, a
//! `u16` bit set). The adsh value of a row is resolved to its `sub` row with the dictionary once per run of equal
//! adsh values. Counts, sums and the groups of the current adsh run are kept in registers while they do not
//! change (`acc_cnt`, `acc_sum`, `cmask`) and written back on a change (`inv` accounts for them as pending).
//!
//! Blocks of `BLK` rows whose adsh, stmt and rfile values are all 20, 2 and 1 bytes wide and whose stmt is never
//! NULL take a fast path that reads the values at computed positions; other blocks read the offsets of every row.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::agent::cols::*;
use crate::agent::spec::*;
use crate::agent::dict::*;
use crate::agent::common::bytes::*;
use crate::agent::common::bits::*;

verus! {

/// Largest number of groups one task tracks.
pub const GCAP: usize = 16;

/// Rows per block of the scan.
pub const BLK: usize = 512;

/// Scan status: every qualifying row was counted.
pub const ST_OK: u8 = 0;
/// More than `GCAP` groups in the range.
pub const ST_GROUPS: u8 = 1;
/// Some adsh value was not found in the dictionary.
pub const ST_MISSING: u8 = 2;

/// Per-task buffers, allocated by the calling thread: the group table (`GCAP` entries each), the code hint
/// table (64 entries) and the adsh-id bit sets (`m` entries).
pub struct Acc {
    pub rep: Vec<usize>,
    pub cnt: Vec<u64>,
    pub sum: Vec<i128>,
    pub scodes: Vec<u64>,
    pub rcodes: Vec<u64>,
    pub hint: Vec<u8>,
    pub mask: Vec<u16>,
}

/// Scan state between rows.
pub struct St {
    pub ng: usize,
    pub have_g: bool,
    pub cg: usize,
    pub cbit: u16,
    pub ccs: u64,
    pub ccr: u64,
    pub acc_cnt: u64,
    pub acc_sum: i64,
    pub have_a: bool,
    pub pa0: usize,
    pub pa1: usize,
    pub pw0: u64,
    pub pw1: u64,
    pub pw2: u64,
    pub cid: usize,
    pub cmask: u16,
}

/// Key of local group `g`.
pub open spec fn gkey(t: Seq<Row>, rep: Seq<usize>, g: int) -> Row {
    key_of(t[rep[g] as int])
}

pub open spec fn shapes(c: Cols, a: Acc) -> bool {
    &&& a.rep@.len() == GCAP
    &&& a.cnt@.len() == GCAP
    &&& a.sum@.len() == GCAP
    &&& a.scodes@.len() == GCAP
    &&& a.rcodes@.len() == GCAP
    &&& a.hint@.len() == 64
    &&& a.mask@.len() == c.m
}

/// The first rows of the local groups: rows of the range that qualify.
pub open spec fn reps_ok(t: Seq<Row>, lo: int, hi: int, ng: int, rep: Seq<usize>) -> bool {
    &&& 0 <= ng <= GCAP
    &&& forall|g: int| 0 <= g < ng ==> lo <= #[trigger] rep[g] < hi && qual(t[rep[g] as int])
}

/// The local groups: rows of the range, qualifying, with pairwise different keys, covering the qualifying rows
/// of `[lo, i)`.
pub open spec fn groups_ok(t: Seq<Row>, lo: int, hi: int, i: int, ng: int, rep: Seq<usize>) -> bool {
    &&& reps_ok(t, lo, hi, ng, rep)
    &&& forall|g1: int, g2: int| 0 <= g1 < ng && 0 <= g2 < ng && g1 != g2
        ==> #[trigger] gkey(t, rep, g1) != #[trigger] gkey(t, rep, g2)
    &&& forall|j: int| lo <= j < i && qual(#[trigger] t[j]) ==> exists|g: int| 0 <= g < ng && key_of(t[j]) == gkey(t, rep, g)
}

/// Group codes: a nonzero code pair is the codes of the group's stmt and rfile bytes.
pub open spec fn codes_ok(c: Cols, ng: int, rep: Seq<usize>, scodes: Seq<u64>, rcodes: Seq<u64>) -> bool {
    forall|g: int| 0 <= g < ng && #[trigger] scodes[g] != 0 ==> {
        &&& scodes[g] == scode(c.stext(rep[g] as int))
        &&& rcodes[g] == scode(c.rtext(rep[g] as int))
        &&& rcodes[g] != 0
    }
}

/// The current group and its pending count and sum.
pub open spec fn cur_ok(c: Cols, st: St, rep: Seq<usize>) -> bool {
    &&& st.have_g ==> {
        &&& st.cg < st.ng
        &&& st.cbit == 1u16 << (st.cg as u16)
        &&& st.ccs != 0 ==> st.ccs == scode(c.stext(rep[st.cg as int] as int)) && st.ccr == scode(c.rtext(rep[st.cg as int] as int)) && st.ccr != 0
    }
    &&& st.acc_cnt <= 0x4000_0000
    &&& -0x8000_0000 * st.acc_cnt <= st.acc_sum <= 0x8000_0000 * st.acc_cnt
    &&& !st.have_g ==> st.acc_cnt == 0 && st.acc_sum == 0
}

pub open spec fn pend_cnt(st: St, g: int) -> int {
    if st.have_g && g == st.cg { st.acc_cnt as int } else { 0 }
}

pub open spec fn pend_sum(st: St, g: int) -> int {
    if st.have_g && g == st.cg { st.acc_sum as int } else { 0 }
}

/// Counts and sums (with the pending ones) are those of the processed rows; unused entries are zero.
pub open spec fn acc_ok(t: Seq<Row>, lo: int, i: int, st: St, rep: Seq<usize>, cnt: Seq<u64>, sum: Seq<i128>) -> bool {
    &&& forall|g: int| 0 <= g < st.ng ==> #[trigger] cnt[g] + pend_cnt(st, g) == cnt_r(t, gkey(t, rep, g), lo, i)
    &&& forall|g: int| 0 <= g < st.ng ==> #[trigger] sum[g] + pend_sum(st, g) == sum_r(t, gkey(t, rep, g), lo, i)
    &&& forall|g: int| st.ng <= g < GCAP ==> #[trigger] cnt[g] == 0 && sum[g] == 0
}

/// The current adsh run: its bytes, words and `sub` row.
pub open spec fn run_ok(c: Cols, st: St) -> bool {
    &&& st.have_a ==> {
        &&& st.cid < c.m
        &&& st.pa0 <= st.pa1 <= c.adsh_len
        &&& c.subtext(st.cid as int) == c.adsh@.subrange(st.pa0 as int, st.pa1 as int)
        &&& 8 <= st.pa1 - st.pa0 <= 24 ==> (st.pw0, st.pw1, st.pw2) == w3(c.adsh@.subrange(st.pa0 as int, st.pa1 as int))
    }
    &&& !st.have_a ==> st.cmask == 0
}

/// The bit sets with the current run's pending groups written back.
pub open spec fn eff(st: St, mask: Seq<u16>) -> Seq<u16> {
    if st.have_a { mask.update(st.cid as int, mask[st.cid as int] | st.cmask) } else { mask }
}

/// Every set bit stands for a value of the group.
pub open spec fn mask_sound(c: Cols, t: Seq<Row>, lo: int, i: int, ng: int, rep: Seq<usize>, em: Seq<u16>) -> bool {
    forall|id: int, b: u16| 0 <= id < c.m && b < 16 && #[trigger] bit16(em[id], b)
        ==> b < ng && aset_r(t, gkey(t, rep, b as int), lo, i).contains(Val::Text(c.subtext(id)))
}

/// Every value of a group has a `sub` row with the group's bit set.
pub open spec fn mask_complete(c: Cols, t: Seq<Row>, lo: int, i: int, ng: int, rep: Seq<usize>, em: Seq<u16>) -> bool {
    forall|g: int, v: Val| 0 <= g < ng && #[trigger] aset_r(t, gkey(t, rep, g), lo, i).contains(v)
        ==> exists|id: int| 0 <= id < c.m && Val::Text(c.subtext(id)) == v && #[trigger] bit16(em[id], g as u16)
}

/// The scan state after the rows `[lo, i)`.
#[verifier::opaque]
pub open spec fn inv(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc) -> bool {
    &&& cols_wf(c)
    &&& corr(c, t)
    &&& 0 <= lo <= i <= hi <= c.n
    &&& shapes(c, a)
    &&& groups_ok(t, lo, hi, i, st.ng as int, a.rep@)
    &&& codes_ok(c, st.ng as int, a.rep@, a.scodes@, a.rcodes@)
    &&& cur_ok(c, st, a.rep@)
    &&& acc_ok(t, lo, i, st, a.rep@, a.cnt@, a.sum@)
    &&& run_ok(c, st)
    &&& mask_sound(c, t, lo, i, st.ng as int, a.rep@, eff(st, a.mask@))
    &&& mask_complete(c, t, lo, i, st.ng as int, a.rep@, eff(st, a.mask@))
}

/// Group bits of a range scan: `b` in `mask[id]` exactly when group `b` has a row of `sub` row `id`'s value.
pub open spec fn out_ok(c: Cols, t: Seq<Row>, lo: int, hi: int, ng: int, a: Acc) -> bool {
    &&& cols_wf(c)
    &&& corr(c, t)
    &&& 0 <= lo <= hi <= c.n
    &&& shapes(c, a)
    &&& groups_ok(t, lo, hi, hi, ng, a.rep@)
    &&& forall|g: int| 0 <= g < ng ==> #[trigger] a.cnt@[g] == cnt_r(t, gkey(t, a.rep@, g), lo, hi)
    &&& forall|g: int| 0 <= g < ng ==> #[trigger] a.sum@[g] == sum_r(t, gkey(t, a.rep@, g), lo, hi)
    &&& mask_sound(c, t, lo, hi, ng, a.rep@, a.mask@)
    &&& mask_complete(c, t, lo, hi, ng, a.rep@, a.mask@)
}

/// One more row outside group `k` leaves its accumulators unchanged.
pub proof fn lemma_nohit_step(t: Seq<Row>, k: Row, lo: int, i: int)
    requires lo <= i, !hit(t[i], k),
    ensures
        cnt_r(t, k, lo, i + 1) == cnt_r(t, k, lo, i),
        sum_r(t, k, lo, i + 1) == sum_r(t, k, lo, i),
        aset_r(t, k, lo, i + 1) == aset_r(t, k, lo, i),
{
}

/// A row that does not qualify changes nothing.
pub proof fn lemma_skip(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc)
    requires inv(c, t, lo, hi, i, st, a), i < hi, !qual(t[i]),
    ensures inv(c, t, lo, hi, i + 1, st, a),
{
    reveal(inv);
    let rep = a.rep@;
    let ng = st.ng as int;
    let em = eff(st, a.mask@);
    assert forall|k: Row| #[trigger] aset_r(t, k, lo, i + 1) == aset_r(t, k, lo, i) by {
        lemma_nohit_step(t, k, lo, i);
    }
    assert forall|k: Row| #[trigger] cnt_r(t, k, lo, i + 1) == cnt_r(t, k, lo, i) by {
        lemma_nohit_step(t, k, lo, i);
    }
    assert forall|k: Row| #[trigger] sum_r(t, k, lo, i + 1) == sum_r(t, k, lo, i) by {
        lemma_nohit_step(t, k, lo, i);
    }
    assert forall|j: int| lo <= j < i + 1 && qual(#[trigger] t[j]) implies exists|g: int| 0 <= g < ng && key_of(t[j]) == gkey(t, rep, g) by {
        assert(j < i);
    }
    assert(groups_ok(t, lo, hi, i + 1, ng, rep));
    assert(acc_ok(t, lo, i + 1, st, rep, a.cnt@, a.sum@));
    assert(mask_sound(c, t, lo, i + 1, ng, rep, em));
    assert forall|g: int, v: Val| 0 <= g < ng && #[trigger] aset_r(t, gkey(t, rep, g), lo, i + 1).contains(v)
        implies exists|id: int| 0 <= id < c.m && Val::Text(c.subtext(id)) == v && #[trigger] bit16(em[id], g as u16) by {
        assert(aset_r(t, gkey(t, rep, g), lo, i).contains(v));
    }
}

/// The state after counting row `i` (qualifying, in the current group and the current adsh run): one more pending
/// row, its line added, the group's bit added to the run's pending groups.
pub open spec fn counted(st: St, line: i32) -> St {
    St { acc_cnt: (st.acc_cnt + 1) as u64, acc_sum: (st.acc_sum + line) as i64, cmask: st.cmask | st.cbit, ..st }
}

/// One more row of group `k`: its count, sum and value set grow by the row.
pub proof fn lemma_hit_step(t: Seq<Row>, k: Row, lo: int, i: int)
    requires lo <= i, hit(t[i], k),
    ensures
        cnt_r(t, k, lo, i + 1) == cnt_r(t, k, lo, i) + 1,
        sum_r(t, k, lo, i + 1) == sum_r(t, k, lo, i) + line_of(t[i]),
        aset_r(t, k, lo, i + 1) == aset_r(t, k, lo, i).insert(t[i][0]),
{
}

/// Bits of the effective sets only grow when the run's pending set grows.
proof fn lemma_eff_grow(st: St, mask: Seq<u16>, id: int, b: u16)
    requires st.have_a, 0 <= st.cid < mask.len(), b < 16, 0 <= id < mask.len(),
    ensures
        bit16(eff(counted(st, 0), mask)[id], b) == (bit16(eff(st, mask)[id], b) || (id == st.cid && bit16(st.cbit, b))),
{
    let st2 = counted(st, 0);
    if id == st.cid {
        lemma_or16(mask[id], st.cmask, b);
        lemma_or16(mask[id], st.cmask | st.cbit, b);
        lemma_or16(st.cmask, st.cbit, b);
    }
}

/// Counting a qualifying row of the current group and adsh run keeps the invariant one row further.
pub proof fn lemma_row(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc)
    requires
        inv(c, t, lo, hi, i, st, a), i < hi, qual(t[i]),
        st.have_g, st.have_a, st.acc_cnt < 0x4000_0000,
        gkey(t, a.rep@, st.cg as int) == key_of(t[i]),
        c.subtext(st.cid as int) == c.atext(i),
    ensures
        inv(c, t, lo, hi, i + 1, counted(st, c.line@[i]), a),
{
    reveal(inv);
    let rep = a.rep@;
    let ng = st.ng as int;
    let cg = st.cg as int;
    let st2 = counted(st, c.line@[i]);
    let em = eff(st, a.mask@);
    let em2 = eff(st2, a.mask@);
    assert(row_corr(c, t[i], i));
    let k = key_of(t[i]);
    lemma_hit_step(t, k, lo, i);
    assert(line_of(t[i]) == c.line@[i] as int);
    assert(t[i][0] == Val::Text(c.subtext(st.cid as int)));
    lemma_one16(st.cg as u16, st.cg as u16);
    // Groups other than the current one are unchanged.
    assert forall|g: int| 0 <= g < ng && g != cg implies !hit(t[i], #[trigger] gkey(t, rep, g)) by {
        assert(gkey(t, rep, g) != gkey(t, rep, cg));
    }
    assert forall|g: int| 0 <= g < ng && g != cg implies
        #[trigger] cnt_r(t, gkey(t, rep, g), lo, i + 1) == cnt_r(t, gkey(t, rep, g), lo, i)
        && sum_r(t, gkey(t, rep, g), lo, i + 1) == sum_r(t, gkey(t, rep, g), lo, i)
        && aset_r(t, gkey(t, rep, g), lo, i + 1) == aset_r(t, gkey(t, rep, g), lo, i) by {
        lemma_nohit_step(t, gkey(t, rep, g), lo, i);
    }
    // Counts and sums.
    assert forall|g: int| 0 <= g < st2.ng implies #[trigger] a.cnt@[g] + pend_cnt(st2, g) == cnt_r(t, gkey(t, rep, g), lo, i + 1) by {
        if g != cg {
            assert(cnt_r(t, gkey(t, rep, g), lo, i + 1) == cnt_r(t, gkey(t, rep, g), lo, i));
        }
    }
    assert forall|g: int| 0 <= g < st2.ng implies #[trigger] a.sum@[g] + pend_sum(st2, g) == sum_r(t, gkey(t, rep, g), lo, i + 1) by {
        if g != cg {
            assert(sum_r(t, gkey(t, rep, g), lo, i + 1) == sum_r(t, gkey(t, rep, g), lo, i));
        }
    }
    assert(acc_ok(t, lo, i + 1, st2, rep, a.cnt@, a.sum@));
    // Coverage.
    assert forall|j: int| lo <= j < i + 1 && qual(#[trigger] t[j]) implies exists|g: int| 0 <= g < ng && key_of(t[j]) == gkey(t, rep, g) by {
        if j == i {
            assert(key_of(t[j]) == gkey(t, rep, cg));
        }
    }
    assert(groups_ok(t, lo, hi, i + 1, ng, rep));
    // Value sets only grow.
    assert forall|g: int| 0 <= g < ng implies
        aset_r(t, #[trigger] gkey(t, rep, g), lo, i).subset_of(aset_r(t, gkey(t, rep, g), lo, i + 1)) by {
        if g != cg {
        } else {
        }
    }
    // Soundness of the bits.
    assert forall|id: int, b: u16| 0 <= id < c.m && b < 16 && #[trigger] bit16(em2[id], b)
        implies b < ng && aset_r(t, gkey(t, rep, b as int), lo, i + 1).contains(Val::Text(c.subtext(id))) by {
        lemma_eff_grow(st, a.mask@, id, b);
        assert(counted(st, 0).cmask == st2.cmask);
        if bit16(em[id], b) {
            assert(aset_r(t, gkey(t, rep, b as int), lo, i).subset_of(aset_r(t, gkey(t, rep, b as int), lo, i + 1)));
        } else {
            lemma_one16(st.cg as u16, b);
            assert(id == st.cid && b as int == cg);
        }
    }
    // Completeness.
    assert forall|g: int, v: Val| 0 <= g < ng && #[trigger] aset_r(t, gkey(t, rep, g), lo, i + 1).contains(v)
        implies exists|id: int| 0 <= id < c.m && Val::Text(c.subtext(id)) == v && #[trigger] bit16(em2[id], g as u16) by {
        if g == cg && v == t[i][0] {
            let id = st.cid as int;
            lemma_eff_grow(st, a.mask@, id, g as u16);
            assert(counted(st, 0).cmask == st2.cmask);
            assert(bit16(em2[id], g as u16));
        } else {
            assert(aset_r(t, gkey(t, rep, g), lo, i).contains(v));
            let id = choose|id: int| 0 <= id < c.m && Val::Text(c.subtext(id)) == v && #[trigger] bit16(em[id], g as u16);
            lemma_eff_grow(st, a.mask@, id, g as u16);
            assert(counted(st, 0).cmask == st2.cmask);
            assert(bit16(em2[id], g as u16));
        }
    }
}

/// The unused count and sum entries are zero.
proof fn lemma_acc_tail(t: Seq<Row>, lo: int, i: int, st: St, rep: Seq<usize>, cnt: Seq<u64>, sum: Seq<i128>, g: int)
    requires acc_ok(t, lo, i, st, rep, cnt, sum), st.ng <= g < GCAP,
    ensures cnt[g] == 0, sum[g] == 0,
{
    assert(cnt[g] == 0);
}

/// The state with the current group's pending count and sum written back and no current group.
pub open spec fn flushed(st: St) -> St {
    St { have_g: false, acc_cnt: 0, acc_sum: 0, ..st }
}

/// Counts are bounded by the range length and sums by `2^31` per row.
proof fn lemma_bounds(c: Cols, t: Seq<Row>, lo: int, i: int, k: Row)
    requires corr(c, t), 0 <= lo <= i <= c.n,
    ensures
        cnt_r(t, k, lo, i) <= i - lo,
        -0x8000_0000 * cnt_r(t, k, lo, i) <= sum_r(t, k, lo, i) <= 0x8000_0000 * cnt_r(t, k, lo, i),
{
    lemma_cnt_le(t, k, lo, i);
    assert forall|j: int| lo <= j < i implies -0x8000_0000 <= #[trigger] line_of(t[j]) < 0x8000_0000 by {
        assert(row_corr(c, t[j], j));
    }
    lemma_sum_bound(t, k, lo, i);
}

proof fn lemma_hix(x: u64)
    ensures x >> 58u64 < 64,
{
    assert(x >> 58u64 < 64) by (bit_vector);
}

/// Writes back the current group's pending count and sum; then there is no current group.
fn flush_group(Ghost(c): Ghost<Cols>, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>,
    Ghost(i): Ghost<int>, st: &mut St, a: &mut Acc)
    requires inv(c, t, lo, hi, i, *old(st), *old(a)),
    ensures
        inv(c, t, lo, hi, i, *final(st), *final(a)),
        *final(st) == flushed(*old(st)),
        final(a).rep@ == old(a).rep@, final(a).scodes@ == old(a).scodes@, final(a).rcodes@ == old(a).rcodes@,
        final(a).mask@ == old(a).mask@, final(a).hint@ == old(a).hint@,
    no_unwind
{
    reveal(inv);
    let ghost st0 = *st;
    if st.have_g {
        let g = st.cg;
        proof {
            lemma_bounds(c, t, lo, i, gkey(t, a.rep@, g as int));
            assert(a.cnt@[g as int] + pend_cnt(*st, g as int) == cnt_r(t, gkey(t, a.rep@, g as int), lo, i));
            assert(a.sum@[g as int] + pend_sum(*st, g as int) == sum_r(t, gkey(t, a.rep@, g as int), lo, i));
        }
        a.cnt[g] = a.cnt[g] + st.acc_cnt;
        a.sum[g] = a.sum[g] + st.acc_sum as i128;
    }
    st.have_g = false;
    st.acc_cnt = 0;
    st.acc_sum = 0;
    proof {
        assert(eff(*st, a.mask@) == eff(st0, a.mask@));
        assert(acc_ok(t, lo, i, *st, a.rep@, a.cnt@, a.sum@));
    }
}

/// The key bytes of row `i` (offsets `s0..s1`, `r0..r1`) and its codes (0 or the codes).
pub open spec fn key_args(c: Cols, i: int, s0: usize, s1: usize, r0: usize, r1: usize, cs: u64, cr: u64) -> bool {
    &&& s0 as int == c.stmt_off@[i] && s1 as int == c.stmt_off@[i + 1]
    &&& r0 as int == c.rfile_off@[i] && r1 as int == c.rfile_off@[i + 1]
    &&& s0 <= s1 <= c.stmt_len && r0 <= r1 <= c.rfile_len
    &&& cs == 0 || (s1 - s0 <= 7 && cs == scode(c.stext(i)))
    &&& cr == 0 || (r1 - r0 <= 7 && cr == scode(c.rtext(i)))
}

/// Codes match exactly when the keys do (for a group with codes and a row with codes).
proof fn lemma_codes_match(c: Cols, t: Seq<Row>, r: int, i: int, sc: u64, rc: u64, cs: u64, cr: u64)
    requires
        corr(c, t), 0 <= r < c.n, 0 <= i < c.n, qual(t[r]), qual(t[i]),
        sc != 0, sc == scode(c.stext(r)), rc == scode(c.rtext(r)), rc != 0,
        cs != 0, cs == scode(c.stext(i)), cr != 0, cr == scode(c.rtext(i)),
    ensures (sc == cs && rc == cr) == (key_of(t[r]) == key_of(t[i])),
{
    lemma_key_eq(c, t, r, i);
    if sc == cs && rc == cr {
        lemma_scode_inj(c.stext(r), c.stext(i));
        lemma_scode_inj(c.rtext(r), c.rtext(i));
    }
}

/// Whether local group `g` has row `i`'s key: by codes when both have them, else by bytes.
#[inline(always)]
fn group_matches(c: &Cols, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>, i: usize,
    a: &Acc, g: usize, s0: usize, s1: usize, r0: usize, r1: usize, cs: u64, cr: u64) -> (m: bool)
    requires
        cols_wf(*c), corr(*c, t), 0 <= lo <= i < hi <= c.n, shapes(*c, *a),
        g < GCAP, lo <= a.rep@[g as int] < hi, qual(t[a.rep@[g as int] as int]),
        a.scodes@[g as int] != 0 ==> {
            &&& a.scodes@[g as int] == scode(c.stext(a.rep@[g as int] as int))
            &&& a.rcodes@[g as int] == scode(c.rtext(a.rep@[g as int] as int))
            &&& a.rcodes@[g as int] != 0
        },
        qual(t[i as int]),
        key_args(*c, i as int, s0, s1, r0, r1, cs, cr),
    ensures
        m == (gkey(t, a.rep@, g as int) == key_of(t[i as int])),
    no_unwind
{
    let r = a.rep[g];
    proof {
        lemma_key_eq(*c, t, r as int, i as int);
    }
    if cs != 0 && cr != 0 && a.scodes[g] != 0 {
        proof {
            lemma_codes_match(*c, t, r as int, i as int, a.scodes@[g as int], a.rcodes@[g as int], cs, cr);
        }
        a.scodes[g] == cs && a.rcodes[g] == cr
    } else {
        let t0 = c.stmt_off[r] as usize;
        let t1 = c.stmt_off[r + 1] as usize;
        let u0 = c.rfile_off[r] as usize;
        let u1 = c.rfile_off[r + 1] as usize;
        proof {
            assert(0 <= c.stmt_off@[r as int] <= c.stmt_off@[r + 1] <= c.stmt@.len());
            assert(0 <= c.rfile_off@[r as int] <= c.rfile_off@[r + 1] <= c.rfile@.len());
        }
        eq_ranges(c.stmt, c.stmt_len, s0, s1, c.stmt, c.stmt_len, t0, t1)
            && eq_ranges(c.rfile, c.rfile_len, r0, r1, c.rfile, c.rfile_len, u0, u1)
    }
}

/// The local group with row `i`'s key, if any.
fn find_group(c: &Cols, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>, i: usize,
    st: &St, a: &Acc, s0: usize, s1: usize, r0: usize, r1: usize, cs: u64, cr: u64, hix: usize) -> (r: (bool, usize))
    requires
        cols_wf(*c), corr(*c, t), 0 <= lo <= i < hi <= c.n, shapes(*c, *a),
        reps_ok(t, lo, hi, st.ng as int, a.rep@),
        codes_ok(*c, st.ng as int, a.rep@, a.scodes@, a.rcodes@),
        qual(t[i as int]),
        key_args(*c, i as int, s0, s1, r0, r1, cs, cr), hix < 64,
    ensures
        r.0 ==> r.1 < st.ng && gkey(t, a.rep@, r.1 as int) == key_of(t[i as int]),
        !r.0 ==> forall|g: int| 0 <= g < st.ng ==> #[trigger] gkey(t, a.rep@, g) != key_of(t[i as int]),
    no_unwind
{
    let ghost key = key_of(t[i as int]);
    if cs != 0 && cr != 0 {
        let hg = a.hint[hix] as usize;
        if hg > 0 && hg <= st.ng && a.scodes[hg - 1] == cs && a.rcodes[hg - 1] == cr {
            if group_matches(c, Ghost(t), Ghost(lo), Ghost(hi), i, a, hg - 1, s0, s1, r0, r1, cs, cr) {
                return (true, hg - 1);
            }
        }
    }
    let mut g: usize = 0;
    while g < st.ng
        invariant
            cols_wf(*c), corr(*c, t), 0 <= lo <= i < hi <= c.n, shapes(*c, *a),
            reps_ok(t, lo, hi, st.ng as int, a.rep@),
            codes_ok(*c, st.ng as int, a.rep@, a.scodes@, a.rcodes@),
            qual(t[i as int]), key == key_of(t[i as int]),
            key_args(*c, i as int, s0, s1, r0, r1, cs, cr),
            g <= st.ng,
            forall|g2: int| 0 <= g2 < g ==> #[trigger] gkey(t, a.rep@, g2) != key,
        decreases st.ng - g,
    {
        proof {
            assert(lo <= a.rep@[g as int] < hi);
            if a.scodes@[g as int] != 0 {
                assert(codes_ok(*c, st.ng as int, a.rep@, a.scodes@, a.rcodes@));
            }
        }
        if group_matches(c, Ghost(t), Ghost(lo), Ghost(hi), i, a, g, s0, s1, r0, r1, cs, cr) {
            return (true, g);
        }
        g = g + 1;
    }
    (false, 0)
}

/// Adding a group for row `i`, whose key no local group has, keeps the invariant (with no current group).
#[verifier::spinoff_prover]
proof fn lemma_add_group(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc, st2: St, a2: Acc, sc: u64, rc: u64)
    requires
        inv(c, t, lo, hi, i, st, a), i < hi, qual(t[i]), !st.have_g, st.ng < GCAP,
        forall|g: int| 0 <= g < st.ng ==> #[trigger] gkey(t, a.rep@, g) != key_of(t[i]),
        sc != 0 ==> sc == scode(c.stext(i)) && rc == scode(c.rtext(i)) && rc != 0,
        a2.rep@ == a.rep@.update(st.ng as int, i as usize),
        a2.scodes@ == a.scodes@.update(st.ng as int, sc),
        a2.rcodes@ == a.rcodes@.update(st.ng as int, rc),
        a2.cnt@ == a.cnt@, a2.sum@ == a.sum@, a2.mask@ == a.mask@, a2.hint@ == a.hint@,
        st2 == (St { ng: (st.ng + 1) as usize, ..st }),
    ensures
        inv(c, t, lo, hi, i, st2, a2),
        gkey(t, a2.rep@, st.ng as int) == key_of(t[i]),
{
    reveal(inv);
    let ng = st.ng as int;
    let rep = a.rep@;
    let rep2 = a2.rep@;
    let key = key_of(t[i]);
    assert forall|g: int| 0 <= g < ng implies #[trigger] gkey(t, rep2, g) == gkey(t, rep, g) by {
        assert(rep2[g] == rep[g]);
    }
    assert(gkey(t, rep2, ng) == key);
    // No processed row has the new key: it would be in an existing group.
    assert forall|j: int| lo <= j < i implies !#[trigger] hit(t[j], key) by {
        if hit(t[j], key) {
            let g2 = choose|g2: int| 0 <= g2 < ng && key_of(t[j]) == gkey(t, rep, g2);
            assert(gkey(t, rep, g2) != key);
        }
    }
    lemma_no_hit(t, key, lo, i);
    assert(groups_ok(t, lo, hi, i, ng + 1, rep2)) by {
        assert forall|g1: int, g2: int| 0 <= g1 < ng + 1 && 0 <= g2 < ng + 1 && g1 != g2
            implies #[trigger] gkey(t, rep2, g1) != #[trigger] gkey(t, rep2, g2) by {
            if g1 < ng && g2 < ng {
                assert(gkey(t, rep, g1) != gkey(t, rep, g2));
            }
        }
        assert forall|j: int| lo <= j < i && qual(#[trigger] t[j]) implies exists|g3: int| 0 <= g3 < ng + 1 && key_of(t[j]) == gkey(t, rep2, g3) by {
            let g3 = choose|g3: int| 0 <= g3 < ng && key_of(t[j]) == gkey(t, rep, g3);
            assert(gkey(t, rep2, g3) == gkey(t, rep, g3));
        }
    }
    assert(codes_ok(c, ng + 1, rep2, a2.scodes@, a2.rcodes@)) by {
        assert forall|g2: int| 0 <= g2 < ng + 1 && #[trigger] a2.scodes@[g2] != 0 implies {
            &&& a2.scodes@[g2] == scode(c.stext(rep2[g2] as int))
            &&& a2.rcodes@[g2] == scode(c.rtext(rep2[g2] as int))
            &&& a2.rcodes@[g2] != 0
        } by {
            if g2 < ng {
                assert(a.scodes@[g2] != 0);
                assert(rep2[g2] == rep[g2]);
            }
        }
    }
    assert(acc_ok(t, lo, i, st2, rep2, a2.cnt@, a2.sum@)) by {
        assert forall|g: int| 0 <= g < st2.ng implies #[trigger] a2.cnt@[g] + pend_cnt(st2, g) == cnt_r(t, gkey(t, rep2, g), lo, i) by {
            if g < ng {
                assert(a.cnt@[g] + pend_cnt(st, g) == cnt_r(t, gkey(t, rep, g), lo, i));
            } else {
                lemma_acc_tail(t, lo, i, st, rep, a.cnt@, a.sum@, g);
            }
        }
        assert forall|g: int| 0 <= g < st2.ng implies #[trigger] a2.sum@[g] + pend_sum(st2, g) == sum_r(t, gkey(t, rep2, g), lo, i) by {
            if g < ng {
                assert(a.sum@[g] + pend_sum(st, g) == sum_r(t, gkey(t, rep, g), lo, i));
            } else {
                lemma_acc_tail(t, lo, i, st, rep, a.cnt@, a.sum@, g);
            }
        }
        assert forall|g: int| st2.ng <= g < GCAP implies #[trigger] a2.cnt@[g] == 0 && a2.sum@[g] == 0 by {
            lemma_acc_tail(t, lo, i, st, rep, a.cnt@, a.sum@, g);
        }
    }
    let em = eff(st2, a2.mask@);
    assert(em == eff(st, a.mask@));
    assert(mask_sound(c, t, lo, i, ng + 1, rep2, em)) by {
        assert forall|id: int, b: u16| 0 <= id < c.m && b < 16 && #[trigger] bit16(em[id], b)
            implies b < ng + 1 && aset_r(t, gkey(t, rep2, b as int), lo, i).contains(Val::Text(c.subtext(id))) by {
            assert(b < ng);
            assert(gkey(t, rep2, b as int) == gkey(t, rep, b as int));
        }
    }
    assert(mask_complete(c, t, lo, i, ng + 1, rep2, em)) by {
        assert forall|g2: int, v: Val| 0 <= g2 < ng + 1 && #[trigger] aset_r(t, gkey(t, rep2, g2), lo, i).contains(v)
            implies exists|id: int| 0 <= id < c.m && Val::Text(c.subtext(id)) == v && #[trigger] bit16(em[id], g2 as u16) by {
            if g2 == ng {
                assert(aset_r(t, key, lo, i) == Set::<Val>::empty());
            } else {
                assert(gkey(t, rep2, g2) == gkey(t, rep, g2));
            }
        }
    }
}

/// Makes local group `g` (holding row `i`'s key) current with no pending rows.
proof fn lemma_set_current(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc, st2: St, g: int,
    cs: u64, cr: u64)
    requires
        inv(c, t, lo, hi, i, st, a), i < hi, qual(t[i]), !st.have_g,
        0 <= g < st.ng, gkey(t, a.rep@, g) == key_of(t[i]),
        cs != 0 ==> cs == scode(c.stext(i)) && cr == scode(c.rtext(i)) && cr != 0,
        st2 == (St { have_g: true, cg: g as usize, cbit: 1u16 << (g as u16), ccs: cs, ccr: cr, ..st }),
    ensures
        inv(c, t, lo, hi, i, st2, a),
{
    reveal(inv);
    let r = a.rep@[g] as int;
    assert(row_corr(c, t[r], r));
    lemma_key_eq(c, t, r, i);
    assert(eff(st2, a.mask@) == eff(st, a.mask@));
    assert(acc_ok(t, lo, i, st2, a.rep@, a.cnt@, a.sum@)) by {
        assert forall|g2: int| 0 <= g2 < st2.ng implies #[trigger] a.cnt@[g2] + pend_cnt(st2, g2) == cnt_r(t, gkey(t, a.rep@, g2), lo, i) by {
            assert(a.cnt@[g2] + pend_cnt(st, g2) == cnt_r(t, gkey(t, a.rep@, g2), lo, i));
        }
        assert forall|g2: int| 0 <= g2 < st2.ng implies #[trigger] a.sum@[g2] + pend_sum(st2, g2) == sum_r(t, gkey(t, a.rep@, g2), lo, i) by {
            assert(a.sum@[g2] + pend_sum(st, g2) == sum_r(t, gkey(t, a.rep@, g2), lo, i));
        }
    }
}

/// Makes the group of row `i` the current group, finding it or adding it; false when the range has more than
/// `GCAP` groups. `cs`, `cr` are 0 or the codes of the row's stmt and rfile bytes.
#[inline(never)]
pub fn switch_group(c: &Cols, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>, i: usize,
    st: &mut St, a: &mut Acc, s0: usize, s1: usize, r0: usize, r1: usize, cs: u64, cr: u64) -> (ok: bool)
    requires
        inv(*c, t, lo, hi, i as int, *old(st), *old(a)), i < hi, qual(t[i as int]),
        key_args(*c, i as int, s0, s1, r0, r1, cs, cr),
    ensures
        ok ==> {
            &&& inv(*c, t, lo, hi, i as int, *final(st), *final(a))
            &&& final(st).have_g && final(st).acc_cnt == 0
            &&& gkey(t, final(a).rep@, final(st).cg as int) == key_of(t[i as int])
            &&& final(st).have_a == old(st).have_a && final(st).cid == old(st).cid && final(st).cmask == old(st).cmask
            &&& final(st).pa0 == old(st).pa0 && final(st).pa1 == old(st).pa1
            &&& final(st).pw0 == old(st).pw0 && final(st).pw1 == old(st).pw1 && final(st).pw2 == old(st).pw2
            &&& (cs != 0 && cr != 0) ==> final(st).ccs == cs && final(st).ccr == cr
        },
    no_unwind
{
    let ghost ii = i as int;
    flush_group(Ghost(*c), Ghost(t), Ghost(lo), Ghost(hi), Ghost(ii), st, a);
    let short = cs != 0 && cr != 0;
    let hx = ((cs ^ (cr << 7u64)) as u128 * 0x9E37_79B9_7F4A_7C15u128) as u64;
    let hix = (hx >> 58u64) as usize;
    proof { lemma_hix(hx); }
    proof { reveal(inv); }
    let (found, fg) = find_group(c, Ghost(t), Ghost(lo), Ghost(hi), i, st, a, s0, s1, r0, r1, cs, cr, hix);
    let mut g = fg;
    if !found {
        if st.ng == GCAP {
            return false;
        }
        let ng = st.ng;
        let ghost st0 = *st;
        let ghost a0 = *a;
        let sc = if short { cs } else { 0 };
        proof {
            if sc != 0 {
                lemma_scode_nonzero(c.rtext(ii));
            }
        }
        a.rep[ng] = i;
        a.scodes[ng] = sc;
        a.rcodes[ng] = cr;
        st.ng = ng + 1;
        proof { lemma_add_group(*c, t, lo, hi, ii, st0, a0, *st, *a, sc, cr); }
        g = ng;
    }
    if short {
        a.hint[hix] = (g + 1) as u8;
    }
    let ghost st1 = *st;
    let ccs = if short { cs } else { 0 };
    proof {
        if ccs != 0 {
            lemma_scode_nonzero(c.rtext(ii));
        }
    }
    st.cg = g;
    st.cbit = 1u16 << (g as u16);
    st.ccs = ccs;
    st.ccr = cr;
    st.have_g = true;
    proof {
        assert(inv(*c, t, lo, hi, ii, st1, *a));
        lemma_set_current(*c, t, lo, hi, ii, st1, *a, *st, g as int, ccs, cr);
    }
    true
}

/// The bytes of row `i`'s adsh (offsets `a0..a1`) and, for 8 to 24 bytes, its covering words.
pub open spec fn adsh_args(c: Cols, i: int, a0: usize, a1: usize, w0: u64, w1: u64, w2: u64) -> bool {
    &&& a0 as int == c.adsh_off@[i] && a1 as int == c.adsh_off@[i + 1]
    &&& a0 <= a1 <= c.adsh_len
    &&& 8 <= a1 - a0 <= 24 ==> (w0, w1, w2) == w3(c.adsh@.subrange(a0 as int, a1 as int))
}

/// The state of a new adsh run with `sub` row `cid`.
pub open spec fn new_run(st: St, a0: usize, a1: usize, w0: u64, w1: u64, w2: u64, cid: usize) -> St {
    St { have_a: true, pa0: a0, pa1: a1, pw0: w0, pw1: w1, pw2: w2, cid, cmask: 0, ..st }
}

/// Writing back the run's groups and starting a new run (no pending groups) keeps the effective bit sets.
proof fn lemma_new_run(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc, a2: Acc, st2: St)
    requires
        inv(c, t, lo, hi, i, st, a),
        a2.mask@ == (if st.have_a { a.mask@.update(st.cid as int, a.mask@[st.cid as int] | st.cmask) } else { a.mask@ }),
        a2.rep@ == a.rep@, a2.cnt@ == a.cnt@, a2.sum@ == a.sum@, a2.scodes@ == a.scodes@, a2.rcodes@ == a.rcodes@,
        a2.hint@ == a.hint@,
        st2.have_a, st2.cmask == 0, st2.cid < c.m, st2.pa0 <= st2.pa1 <= c.adsh_len,
        c.subtext(st2.cid as int) == c.adsh@.subrange(st2.pa0 as int, st2.pa1 as int),
        8 <= st2.pa1 - st2.pa0 <= 24 ==> (st2.pw0, st2.pw1, st2.pw2) == w3(c.adsh@.subrange(st2.pa0 as int, st2.pa1 as int)),
        st2.ng == st.ng, st2.have_g == st.have_g, st2.cg == st.cg, st2.cbit == st.cbit, st2.ccs == st.ccs,
        st2.ccr == st.ccr, st2.acc_cnt == st.acc_cnt, st2.acc_sum == st.acc_sum,
    ensures
        inv(c, t, lo, hi, i, st2, a2),
{
    reveal(inv);
    let x = a2.mask@[st2.cid as int];
    assert(x | 0u16 == x) by (bit_vector);
    assert(eff(st2, a2.mask@) =~= eff(st, a.mask@));
    assert(acc_ok(t, lo, i, st2, a2.rep@, a2.cnt@, a2.sum@)) by {
        assert forall|g: int| 0 <= g < st2.ng implies #[trigger] a2.cnt@[g] + pend_cnt(st2, g) == cnt_r(t, gkey(t, a2.rep@, g), lo, i) by {
            assert(a.cnt@[g] + pend_cnt(st, g) == cnt_r(t, gkey(t, a.rep@, g), lo, i));
        }
        assert forall|g: int| 0 <= g < st2.ng implies #[trigger] a2.sum@[g] + pend_sum(st2, g) == sum_r(t, gkey(t, a2.rep@, g), lo, i) by {
            assert(a.sum@[g] + pend_sum(st, g) == sum_r(t, gkey(t, a.rep@, g), lo, i));
        }
    }
}

/// Starts a new adsh run at row `i`: writes back the previous run's groups and resolves the value to its `sub`
/// row; false when the dictionary does not find it.
#[inline(never)]
pub fn switch_adsh(c: &Cols, d: &Dict, cache: &mut Vec<u64>, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>,
    Ghost(hi): Ghost<int>, i: usize, st: &mut St, a: &mut Acc, a0: usize, a1: usize, w0: u64, w1: u64, w2: u64) -> (ok: bool)
    requires
        inv(*c, t, lo, hi, i as int, *old(st), *old(a)), i < hi, dict_wf(*c, *d), cache_ok(*c, old(cache)@),
        adsh_args(*c, i as int, a0, a1, w0, w1, w2),
    ensures
        cache_ok(*c, final(cache)@),
        ok ==> {
            &&& inv(*c, t, lo, hi, i as int, *final(st), *final(a))
            &&& final(st).have_a && c.subtext(final(st).cid as int) == c.atext(i as int)
            &&& *final(st) == new_run(*old(st), a0, a1, w0, w1, w2, final(st).cid)
            &&& final(a).rep@ == old(a).rep@
        },
    no_unwind
{
    let ghost st0 = *st;
    let ghost a00 = *a;
    proof { reveal(inv); }
    if st.have_a {
        let id = st.cid;
        a.mask[id] = a.mask[id] | st.cmask;
    }
    let r = if a1 - a0 == 20 { cached_lookup(c, d, cache, a0, a1, w0, w1, w2) } else { lookup(c, d, a0, a1, w0, w1, w2) };
    match r {
        Some(x) => {
            st.cid = x;
        },
        None => {
            return false;
        },
    }
    st.pa0 = a0;
    st.pa1 = a1;
    st.pw0 = w0;
    st.pw1 = w1;
    st.pw2 = w2;
    st.have_a = true;
    st.cmask = 0;
    proof {
        lemma_new_run(*c, t, lo, hi, i as int, st0, a00, *a, *st);
    }
    true
}

/// The parts of the invariant the row loops read directly.
proof fn lemma_inv_basic(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc)
    requires inv(c, t, lo, hi, i, st, a),
    ensures
        cols_wf(c), corr(c, t), 0 <= lo <= i <= hi <= c.n, shapes(c, a), cur_ok(c, st, a.rep@), run_ok(c, st),
        st.ng <= GCAP,
{
    reveal(inv);
}

/// A row whose codes equal the current group's codes is in the current group.
proof fn lemma_same_group(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc, cs: u64, cr: u64)
    requires
        inv(c, t, lo, hi, i, st, a), i < hi, qual(t[i]), st.have_g,
        cs != 0, cs == scode(c.stext(i)), cr != 0, cr == scode(c.rtext(i)), cs == st.ccs, cr == st.ccr,
    ensures
        gkey(t, a.rep@, st.cg as int) == key_of(t[i]),
{
    reveal(inv);
    let r = a.rep@[st.cg as int] as int;
    lemma_codes_match(c, t, r, i, st.ccs, st.ccr, cs, cr);
}

/// A row whose adsh words (or bytes) equal the current run's has the run's value.
proof fn lemma_same_run(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc, a0: usize, a1: usize)
    requires
        inv(c, t, lo, hi, i, st, a), i < hi, st.have_a,
        a0 as int == c.adsh_off@[i], a1 as int == c.adsh_off@[i + 1],
        c.adsh@.subrange(a0 as int, a1 as int) == c.adsh@.subrange(st.pa0 as int, st.pa1 as int),
    ensures
        c.subtext(st.cid as int) == c.atext(i),
{
    reveal(inv);
}

/// Covering words decide equality of a row's adsh with the run's.
proof fn lemma_run_words(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc, a0: usize, a1: usize,
    w0: u64, w1: u64, w2: u64)
    requires
        inv(c, t, lo, hi, i, st, a), st.have_a, a0 <= a1 <= c.adsh_len,
        8 <= a1 - a0 <= 24, a1 - a0 == st.pa1 - st.pa0,
        (w0, w1, w2) == w3(c.adsh@.subrange(a0 as int, a1 as int)),
        w0 == st.pw0, w1 == st.pw1, w2 == st.pw2,
    ensures
        c.adsh@.subrange(a0 as int, a1 as int) == c.adsh@.subrange(st.pa0 as int, st.pa1 as int),
{
    reveal(inv);
    lemma_w3_eq(c.adsh@.subrange(a0 as int, a1 as int), c.adsh@.subrange(st.pa0 as int, st.pa1 as int));
}

/// The offsets of row `i`'s adsh.
pub open spec fn adsh_pos(c: Cols, i: int, a0: usize, a1: usize) -> bool {
    &&& a0 as int == c.adsh_off@[i] && a1 as int == c.adsh_off@[i + 1]
    &&& a0 <= a1 <= c.adsh_len
}

/// Counts row `i` (qualifying) into the current group and adsh run, switching either when the row leaves it.
/// `same_g`: the row's codes equal the current group's; `same_a`: its adsh equals the current run's.
#[inline(always)]
fn count_row(c: &Cols, d: &Dict, cache: &mut Vec<u64>, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>,
    Ghost(hi): Ghost<int>, i: usize, st: &mut St, a: &mut Acc, s0: usize, s1: usize, r0: usize, r1: usize, cs: u64,
    cr: u64, a0: usize, a1: usize, w0: u64, w1: u64, w2: u64, same_a: bool, line: i32) -> (res: u8)
    requires
        inv(*c, t, lo, hi, i as int, *old(st), *old(a)), i < hi, qual(t[i as int]), dict_wf(*c, *d),
        cache_ok(*c, old(cache)@),
        key_args(*c, i as int, s0, s1, r0, r1, cs, cr),
        adsh_pos(*c, i as int, a0, a1),
        adsh_args(*c, i as int, a0, a1, w0, w1, w2),
        same_a ==> old(st).have_a && c.adsh@.subrange(a0 as int, a1 as int) == c.adsh@.subrange(old(st).pa0 as int, old(st).pa1 as int),
        line == c.line@[i as int],
    ensures
        res == ST_OK ==> inv(*c, t, lo, hi, i + 1, *final(st), *final(a)),
        cache_ok(*c, final(cache)@),
    no_unwind
{
    let ghost ii = i as int;
    proof { lemma_inv_basic(*c, t, lo, hi, ii, *st, *a); }
    if cs == 0 || cr == 0 || cs != st.ccs || cr != st.ccr || !st.have_g || st.acc_cnt >= 0x4000_0000 {
        if !switch_group(c, Ghost(t), Ghost(lo), Ghost(hi), i, st, a, s0, s1, r0, r1, cs, cr) {
            return ST_GROUPS;
        }
    } else {
        proof { lemma_same_group(*c, t, lo, hi, ii, *st, *a, cs, cr); }
    }
    let ghost stg = *st;
    if same_a {
        proof { lemma_same_run(*c, t, lo, hi, ii, *st, *a, a0, a1); }
    } else {
        if !switch_adsh(c, d, cache, Ghost(t), Ghost(lo), Ghost(hi), i, st, a, a0, a1, w0, w1, w2) {
            return ST_MISSING;
        }
    }
    proof {
        lemma_inv_basic(*c, t, lo, hi, ii, *st, *a);
        assert(gkey(t, a.rep@, st.cg as int) == key_of(t[ii]));
    }
    let ghost st1 = *st;
    st.acc_cnt = st.acc_cnt + 1;
    st.acc_sum = st.acc_sum + line as i64;
    st.cmask = st.cmask | st.cbit;
    proof {
        assert(*st == counted(st1, c.line@[ii]));
        lemma_row(*c, t, lo, hi, ii, st1, *a);
    }
    ST_OK
}

/// Rows `b0 .. b0 + nb` of any widths (`ao`, `so`, `ro`: their offsets; `va`, `ln`: validity and line).
fn generic_block(c: &Cols, d: &Dict, cache: &mut Vec<u64>, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>,
    Ghost(hi): Ghost<int>, st: &mut St, a: &mut Acc, b0: usize, nb: usize, ao: &[i64], so: &[i64], ro: &[i64], va: &[u8],
    ln: &[i32]) -> (res: u8)
    requires
        inv(*c, t, lo, hi, b0 as int, *old(st), *old(a)), b0 + nb <= hi, dict_wf(*c, *d), cache_ok(*c, old(cache)@),
        ao@ == c.adsh_off@.subrange(b0 as int, b0 + nb + 1),
        so@ == c.stmt_off@.subrange(b0 as int, b0 + nb + 1),
        ro@ == c.rfile_off@.subrange(b0 as int, b0 + nb + 1),
        va@ == c.stmt_valid@.subrange(b0 as int, b0 + nb),
        ln@ == c.line@.subrange(b0 as int, b0 + nb),
    ensures
        res == ST_OK ==> inv(*c, t, lo, hi, b0 + nb, *final(st), *final(a)),
        cache_ok(*c, final(cache)@),
    no_unwind
{
    proof { lemma_inv_basic(*c, t, lo, hi, b0 as int, *st, *a); }
    let mut k: usize = 0;
    while k < nb
        invariant
            inv(*c, t, lo, hi, b0 + k, *st, *a), k <= nb, b0 + nb <= hi, hi <= c.n, dict_wf(*c, *d),
            cache_ok(*c, cache@),
            ao@ == c.adsh_off@.subrange(b0 as int, b0 + nb + 1),
            so@ == c.stmt_off@.subrange(b0 as int, b0 + nb + 1),
            ro@ == c.rfile_off@.subrange(b0 as int, b0 + nb + 1),
            va@ == c.stmt_valid@.subrange(b0 as int, b0 + nb),
            ln@ == c.line@.subrange(b0 as int, b0 + nb),
        decreases nb - k,
    {
        let i = b0 + k;
        let ghost ii = i as int;
        proof {
            lemma_inv_basic(*c, t, lo, hi, ii, *st, *a);
            assert(row_corr(*c, t[ii], ii));
            assert(va@[k as int] == c.stmt_valid@[ii]);
        }
        if va[k] != 0 {
            let s0 = so[k] as usize;
            let s1 = so[k + 1] as usize;
            let r0 = ro[k] as usize;
            let r1 = ro[k + 1] as usize;
            let a0 = ao[k] as usize;
            let a1 = ao[k + 1] as usize;
            proof {
                assert(so@[k as int] == c.stmt_off@[ii] && so@[k + 1] == c.stmt_off@[ii + 1]);
                assert(ro@[k as int] == c.rfile_off@[ii] && ro@[k + 1] == c.rfile_off@[ii + 1]);
                assert(ao@[k as int] == c.adsh_off@[ii] && ao@[k + 1] == c.adsh_off@[ii + 1]);
                assert(0 <= c.stmt_off@[ii] <= c.stmt_off@[ii + 1] <= c.stmt@.len());
                assert(0 <= c.rfile_off@[ii] <= c.rfile_off@[ii + 1] <= c.rfile@.len());
                assert(0 <= c.adsh_off@[ii] <= c.adsh_off@[ii + 1] <= c.adsh@.len());
            }
            let cs = short_code(c.stmt, c.stmt_len, s0, s1);
            let cr = short_code(c.rfile, c.rfile_len, r0, r1);
            let al = a1 - a0;
            let mut w0: u64 = 0;
            let mut w1: u64 = 0;
            let mut w2: u64 = 0;
            let same;
            if 8 <= al && al <= 24 {
                let w = words3(c.adsh, c.adsh_len, a0, a1);
                w0 = w.0;
                w1 = w.1;
                w2 = w.2;
                same = st.have_a && al == st.pa1 - st.pa0 && w0 == st.pw0 && w1 == st.pw1 && w2 == st.pw2;
                proof {
                    if same {
                        lemma_run_words(*c, t, lo, hi, ii, *st, *a, a0, a1, w0, w1, w2);
                    }
                }
            } else {
                same = st.have_a && eq_ranges(c.adsh, c.adsh_len, a0, a1, c.adsh, c.adsh_len, st.pa0, st.pa1);
            }
            let r = count_row(c, d, cache, Ghost(t), Ghost(lo), Ghost(hi), i, st, a, s0, s1, r0, r1, cs, cr,
                a0, a1, w0, w1, w2, same, ln[k]);
            if r != ST_OK {
                return r;
            }
        } else {
            proof { lemma_skip(*c, t, lo, hi, ii, *st, *a); }
        }
        k = k + 1;
    }
    ST_OK
}

/// The words a fast block loads for row `b0 + k` are the covering words of its adsh.
proof fn lemma_fast_words(c: Cols, ab: Seq<u8>, a_base: int, nb: int, k: int)
    requires
        0 <= a_base, a_base + 20 * nb <= c.adsh@.len(), 0 <= k < nb,
        ab == c.adsh@.subrange(a_base, a_base + 20 * nb),
    ensures
        (word8(ab, 20 * k), word8(ab, 20 * k + 8), word8(ab, 20 * k + 12))
            == w3(c.adsh@.subrange(a_base + 20 * k, a_base + 20 * k + 20)),
{
    let x0 = a_base + 20 * k;
    lemma_word8_sub(c.adsh@, a_base, a_base + 20 * nb, 20 * k);
    lemma_word8_sub(c.adsh@, a_base, a_base + 20 * nb, 20 * k + 8);
    lemma_word8_sub(c.adsh@, a_base, a_base + 20 * nb, 20 * k + 12);
    lemma_word8_sub(c.adsh@, x0, x0 + 20, 0);
    lemma_word8_sub(c.adsh@, x0, x0 + 20, 8);
    lemma_word8_sub(c.adsh@, x0, x0 + 20, 12);
    assert(wmid(20) == 8);
}

/// What a block of fixed widths is: its offsets advance by 20, 2 and 1 bytes from `a_base`, `s_base`, `r_base`
/// (within the byte parts) and its stmt is never NULL; `ao`..`ln` are the block's slices of the offsets,
/// validity and line parts.
pub open spec fn fixed_ok(c: Cols, b0: int, nb: int, ao: Seq<i64>, so: Seq<i64>, ro: Seq<i64>, va: Seq<u8>,
    ln: Seq<i32>, a_base: int, s_base: int, r_base: int) -> bool {
    &&& ao == c.adsh_off@.subrange(b0, b0 + nb + 1)
    &&& so == c.stmt_off@.subrange(b0, b0 + nb + 1)
    &&& ro == c.rfile_off@.subrange(b0, b0 + nb + 1)
    &&& va == c.stmt_valid@.subrange(b0, b0 + nb)
    &&& ln == c.line@.subrange(b0, b0 + nb)
    &&& forall|k: int| 0 <= k <= nb ==> #[trigger] ao[k] == a_base + 20 * k
    &&& forall|k: int| 0 <= k <= nb ==> #[trigger] so[k] == s_base + 2 * k
    &&& forall|k: int| 0 <= k <= nb ==> #[trigger] ro[k] == r_base + k
    &&& forall|k: int| 0 <= k < nb ==> #[trigger] va[k] != 0
    &&& 0 <= a_base && a_base + 20 * nb <= c.adsh_len
    &&& 0 <= s_base && s_base + 2 * nb <= c.stmt_len
    &&& 0 <= r_base && r_base + nb <= c.rfile_len
}

/// The stmt code a fast block computes for row `k` of its stmt bytes `sb`.
pub open spec fn fcode_s(sb: Seq<u8>, k: int) -> u64 {
    (sb[2 * k] as u64) | ((sb[2 * k + 1] as u64) << 8u64) | (3u64 << 56u64)
}

/// The rfile code a fast block computes for row `k` of its rfile bytes `rb`.
pub open spec fn fcode_r(rb: Seq<u8>, k: int) -> u64 {
    (rb[k] as u64) | (2u64 << 56u64)
}

/// What a fixed-width block knows about its row `b0 + k`: it qualifies; its key bytes, codes, adsh offsets and
/// words are the ones read at computed positions; its line.
proof fn lemma_fixed_row(c: Cols, t: Seq<Row>, b0: int, nb: int, ao: Seq<i64>, so: Seq<i64>, ro: Seq<i64>,
    va: Seq<u8>, ln: Seq<i32>, ab: Seq<u8>, sb: Seq<u8>, rb: Seq<u8>, a_base: int, s_base: int, r_base: int, k: int)
    requires
        cols_wf(c), corr(c, t), 0 <= b0, b0 + nb <= c.n, 0 <= k < nb,
        fixed_ok(c, b0, nb, ao, so, ro, va, ln, a_base, s_base, r_base),
        ab == c.adsh@.subrange(a_base, a_base + 20 * nb),
        sb == c.stmt@.subrange(s_base, s_base + 2 * nb),
        rb == c.rfile@.subrange(r_base, r_base + nb),
    ensures
        qual(t[b0 + k]),
        key_args(c, b0 + k, (s_base + 2 * k) as usize, (s_base + 2 * k + 2) as usize, (r_base + k) as usize,
            (r_base + k + 1) as usize, fcode_s(sb, k), fcode_r(rb, k)),
        fcode_s(sb, k) == scode(c.stext(b0 + k)), fcode_s(sb, k) != 0,
        fcode_r(rb, k) == scode(c.rtext(b0 + k)), fcode_r(rb, k) != 0,
        adsh_pos(c, b0 + k, (a_base + 20 * k) as usize, (a_base + 20 * k + 20) as usize),
        adsh_args(c, b0 + k, (a_base + 20 * k) as usize, (a_base + 20 * k + 20) as usize,
            word8(ab, 20 * k), word8(ab, 20 * k + 8), word8(ab, 20 * k + 12)),
        ln[k] == c.line@[b0 + k],
{
    let i = b0 + k;
    assert(row_corr(c, t[i], i));
    assert(va[k] == c.stmt_valid@[i]);
    assert(so[k] == c.stmt_off@[i] && so[k + 1] == c.stmt_off@[i + 1]);
    assert(ro[k] == c.rfile_off@[i] && ro[k + 1] == c.rfile_off@[i + 1]);
    assert(ao[k] == c.adsh_off@[i] && ao[k + 1] == c.adsh_off@[i + 1]);
    assert(so[k + 1] == s_base + 2 * k + 2);
    assert(ro[k + 1] == r_base + k + 1);
    assert(ao[k + 1] == a_base + 20 * k + 20);
    let sv = c.stext(i);
    let rv = c.rtext(i);
    assert(sv[0] == sb[2 * k] && sv[1] == sb[2 * k + 1]);
    assert(rv[0] == rb[k]);
    lemma_scode_2_1(sv, rv);
    let (x, y, z) = (sb[2 * k] as u64, sb[2 * k + 1] as u64, rb[k] as u64);
    assert(x | (y << 8u64) | (3u64 << 56u64) != 0 && z | (2u64 << 56u64) != 0) by (bit_vector);
    lemma_fast_words(c, ab, a_base, nb, k);
}

/// Counts row `i` (qualifying, 20-byte adsh) when it leaves the current group or adsh run (or the pending count
/// reached its bound): `count_row` out of the block loop.
#[inline(never)]
fn slow_row(c: &Cols, d: &Dict, cache: &mut Vec<u64>, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>,
    Ghost(hi): Ghost<int>, i: usize, st: &mut St, a: &mut Acc, s0: usize, s1: usize, r0: usize, r1: usize, cs: u64,
    cr: u64, a0: usize, a1: usize, w0: u64, w1: u64, w2: u64, line: i32) -> (res: u8)
    requires
        inv(*c, t, lo, hi, i as int, *old(st), *old(a)), i < hi, qual(t[i as int]), dict_wf(*c, *d),
        cache_ok(*c, old(cache)@),
        key_args(*c, i as int, s0, s1, r0, r1, cs, cr),
        adsh_pos(*c, i as int, a0, a1), a1 - a0 == 20,
        adsh_args(*c, i as int, a0, a1, w0, w1, w2),
        line == c.line@[i as int],
    ensures
        res == ST_OK ==> inv(*c, t, lo, hi, i + 1, *final(st), *final(a)),
        cache_ok(*c, final(cache)@),
    no_unwind
{
    proof { lemma_inv_basic(*c, t, lo, hi, i as int, *st, *a); }
    let same = st.have_a && st.pa1 - st.pa0 == 20 && w0 == st.pw0 && w1 == st.pw1 && w2 == st.pw2;
    proof {
        if same {
            lemma_run_words(*c, t, lo, hi, i as int, *st, *a, a0, a1, w0, w1, w2);
        }
    }
    count_row(c, d, cache, Ghost(t), Ghost(lo), Ghost(hi), i, st, a, s0, s1, r0, r1, cs, cr, a0, a1, w0, w1, w2, same, line)
}

/// The state with the pending count and sum held in locals.
pub open spec fn with_pending(st: St, acnt: u64, asum: i64) -> St {
    St { acc_cnt: acnt, acc_sum: asum, ..st }
}

/// No row key: the 24-bit key of a row (`stmt[0] | stmt[1] << 8 | rfile[0] << 16`) never equals it.
pub const NO_KEY: u64 = 0xffff_ffff;

/// `ckey` (unless `NO_KEY`) is the key of the current group, whose codes are those of a 2-byte stmt and a 1-byte
/// rfile; the current adsh run has a 20-byte value; and the run's groups already hold the current group, so a row
/// of that key and value only adds to the pending count and sum.
pub open spec fn key_ready(st: St, ckey: u64) -> bool {
    ckey != NO_KEY ==> {
        &&& st.have_g && st.have_a
        &&& st.pa0 <= st.pa1 && st.pa1 - st.pa0 == 20
        &&& st.ccs == (ckey & 0xffffu64) | (3u64 << 56u64)
        &&& st.ccr == (ckey >> 16u64) | (2u64 << 56u64)
        &&& st.cmask | st.cbit == st.cmask
    }
}

#[verifier::bit_vector]
proof fn lemma_ready_key(s: u64, r: u64)
    requires s == (s & 0xffffu64) | (3u64 << 56u64), r == (r & 0xffu64) | (2u64 << 56u64),
    ensures
        (s & 0xffffu64) | ((r & 0xffu64) << 16u64) != 0xffff_ffffu64,
        (((s & 0xffffu64) | ((r & 0xffu64) << 16u64)) & 0xffffu64) | (3u64 << 56u64) == s,
        (((s & 0xffffu64) | ((r & 0xffu64) << 16u64)) >> 16u64) | (2u64 << 56u64) == r,
{
}

/// The key of a row from its stmt bytes `x`, `y` and rfile byte `z`, and the codes it gives back.
#[verifier::bit_vector]
proof fn lemma_row_key(x: u64, y: u64, z: u64)
    requires x < 256, y < 256, z < 256,
    ensures
        x | (y << 8u64) | (z << 16u64) != 0xffff_ffffu64,
        ((x | (y << 8u64) | (z << 16u64)) & 0xffffu64) | (3u64 << 56u64) == x | (y << 8u64) | (3u64 << 56u64),
        ((x | (y << 8u64) | (z << 16u64)) >> 16u64) | (2u64 << 56u64) == z | (2u64 << 56u64),
{
}

proof fn lemma_or_zero4(a: u64, b: u64, c: u64, d: u64)
    requires a | b | c | d == 0,
    ensures a == 0, b == 0, c == 0, d == 0,
{
    assert(a == 0 && b == 0 && c == 0 && d == 0) by (bit_vector)
        requires a | b | c | d == 0;
}

/// The key `fast_block` keeps for state `st` (`key_ready`).
#[inline(always)]
fn ready_key(st: &St) -> (k: u64)
    ensures key_ready(*st, k),
    no_unwind
{
    if st.have_g && st.have_a && st.pa0 <= st.pa1 && st.pa1 - st.pa0 == 20
        && st.ccs == (st.ccs & 0xffffu64) | (3u64 << 56u64) && st.ccr == (st.ccr & 0xffu64) | (2u64 << 56u64)
        && st.cmask | st.cbit == st.cmask {
        proof { lemma_ready_key(st.ccs, st.ccr); }
        (st.ccs & 0xffffu64) | ((st.ccr & 0xffu64) << 16u64)
    } else {
        NO_KEY
    }
}

/// Rows `b0 .. b0 + nb` of a fixed-width block (`fixed_ok`), read at computed positions. A row of the current
/// group and adsh run (the common case on clustered rows) only adds to the pending count and sum, kept in locals
/// with the current key (`key_ready`) and run words; any other row goes through `slow_row`. Returns the status and
/// the number of rows that took it.
fn fast_block(c: &Cols, d: &Dict, cache: &mut Vec<u64>, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>,
    Ghost(hi): Ghost<int>, st: &mut St, a: &mut Acc, b0: usize, nb: usize, ao: &[i64], so: &[i64], ro: &[i64],
    va: &[u8], ln: &[i32], a_base: usize, s_base: usize, r_base: usize) -> (res: (u8, usize))
    requires
        inv(*c, t, lo, hi, b0 as int, *old(st), *old(a)), b0 + nb <= hi, dict_wf(*c, *d), cache_ok(*c, old(cache)@),
        fixed_ok(*c, b0 as int, nb as int, ao@, so@, ro@, va@, ln@, a_base as int, s_base as int, r_base as int),
    ensures
        res.0 == ST_OK ==> inv(*c, t, lo, hi, b0 + nb, *final(st), *final(a)),
        cache_ok(*c, final(cache)@),
    no_unwind
{
    proof { lemma_inv_basic(*c, t, lo, hi, b0 as int, *st, *a); }
    let (_, tl) = c.adsh.split_at(a_base);
    let (ab, _) = tl.split_at(20 * nb);
    let (_, tl) = c.stmt.split_at(s_base);
    let (sb, _) = tl.split_at(2 * nb);
    let (_, tl) = c.rfile.split_at(r_base);
    let (rb, _) = tl.split_at(nb);
    proof {
        assert(ab@ =~= c.adsh@.subrange(a_base as int, a_base + 20 * nb));
        assert(sb@ =~= c.stmt@.subrange(s_base as int, s_base + 2 * nb));
        assert(rb@ =~= c.rfile@.subrange(r_base as int, r_base + nb));
        assert(with_pending(*st, st.acc_cnt, st.acc_sum) == *st);
    }
    let mut acnt = st.acc_cnt;
    let mut asum = st.acc_sum;
    let mut pw0 = st.pw0;
    let mut pw1 = st.pw1;
    let mut pw2 = st.pw2;
    let mut ckey = ready_key(st);
    let mut nslow: usize = 0;
    let mut k: usize = 0;
    while k < nb
        invariant
            inv(*c, t, lo, hi, b0 + k, with_pending(*st, acnt, asum), *a), k <= nb, nslow <= k,
            b0 + nb <= hi, hi <= c.n, dict_wf(*c, *d), cache_ok(*c, cache@),
            fixed_ok(*c, b0 as int, nb as int, ao@, so@, ro@, va@, ln@, a_base as int, s_base as int, r_base as int),
            ab@ == c.adsh@.subrange(a_base as int, a_base + 20 * nb),
            sb@ == c.stmt@.subrange(s_base as int, s_base + 2 * nb),
            rb@ == c.rfile@.subrange(r_base as int, r_base + nb),
            pw0 == st.pw0, pw1 == st.pw1, pw2 == st.pw2, key_ready(*st, ckey),
        decreases nb - k,
    {
        let i = b0 + k;
        let ghost ii = i as int;
        let ghost cur = with_pending(*st, acnt, asum);
        proof {
            lemma_inv_basic(*c, t, lo, hi, ii, cur, *a);
            lemma_fixed_row(*c, t, b0 as int, nb as int, ao@, so@, ro@, va@, ln@, ab@, sb@, rb@,
                a_base as int, s_base as int, r_base as int, k as int);
        }
        let x = sb[2 * k] as u64;
        let y = sb[2 * k + 1] as u64;
        let z = rb[k] as u64;
        let key = x | (y << 8u64) | (z << 16u64);
        let w0 = load8(ab, 20 * nb, 20 * k);
        let w1 = load8(ab, 20 * nb, 20 * k + 8);
        let w2 = load8(ab, 20 * nb, 20 * k + 12);
        let line = ln[k];
        proof { lemma_row_key(x, y, z); }
        let diff = (key ^ ckey) | (w0 ^ pw0) | (w1 ^ pw1) | (w2 ^ pw2);
        if diff == 0 && acnt < 0x4000_0000 {
            proof {
                let a0 = (a_base + 20 * k) as usize;
                lemma_or_zero4(key ^ ckey, w0 ^ pw0, w1 ^ pw1, w2 ^ pw2);
                lemma_xor_zero(key, ckey);
                lemma_xor_zero(w0, pw0);
                lemma_xor_zero(w1, pw1);
                lemma_xor_zero(w2, pw2);
                assert(fcode_s(sb@, k as int) == cur.ccs);
                assert(fcode_r(rb@, k as int) == cur.ccr);
                lemma_same_group(*c, t, lo, hi, ii, cur, *a, fcode_s(sb@, k as int), fcode_r(rb@, k as int));
                lemma_run_words(*c, t, lo, hi, ii, cur, *a, a0, (a0 + 20) as usize, w0, w1, w2);
                lemma_same_run(*c, t, lo, hi, ii, cur, *a, a0, (a0 + 20) as usize);
                lemma_row(*c, t, lo, hi, ii, cur, *a);
                assert(counted(cur, c.line@[ii]) == with_pending(*st, (acnt + 1) as u64, (asum + line) as i64));
            }
            acnt = acnt + 1;
            asum = asum + line as i64;
        } else {
            let cs = (key & 0xffffu64) | (3u64 << 56u64);
            let cr = (key >> 16u64) | (2u64 << 56u64);
            st.acc_cnt = acnt;
            st.acc_sum = asum;
            proof { assert(*st == cur); }
            let r = slow_row(c, d, cache, Ghost(t), Ghost(lo), Ghost(hi), i, st, a, s_base + 2 * k, s_base + 2 * k + 2,
                r_base + k, r_base + k + 1, cs, cr, a_base + 20 * k, a_base + 20 * k + 20, w0, w1, w2, line);
            if r != ST_OK {
                return (r, nslow);
            }
            proof { assert(with_pending(*st, st.acc_cnt, st.acc_sum) == *st); }
            acnt = st.acc_cnt;
            asum = st.acc_sum;
            pw0 = st.pw0;
            pw1 = st.pw1;
            pw2 = st.pw2;
            ckey = ready_key(st);
            nslow = nslow + 1;
        }
        k = k + 1;
    }
    st.acc_cnt = acnt;
    st.acc_sum = asum;
    (ST_OK, nslow)
}

/// The group and line bounds that keep a direct count and sum of group `g` in range.
proof fn lemma_direct_bounds(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc, g: int)
    requires inv(c, t, lo, hi, i, st, a), i < hi, !st.have_g, 0 <= g < st.ng,
    ensures
        a.cnt@[g] < 0xffff_ffff_ffff_ffff,
        -0x8000_0000 * 0x1_0000_0000_0000_0000 <= a.sum@[g] <= 0x8000_0000 * 0x1_0000_0000_0000_0000,
{
    reveal(inv);
    let k = gkey(t, a.rep@, g);
    assert(a.cnt@[g] + pend_cnt(st, g) == cnt_r(t, k, lo, i));
    assert(a.sum@[g] + pend_sum(st, g) == sum_r(t, k, lo, i));
    lemma_bounds(c, t, lo, i, k);
    assert(i - lo < 0xffff_ffff_ffff_ffff);
    assert(-0x8000_0000 * cnt_r(t, k, lo, i) >= -0x8000_0000 * 0x1_0000_0000_0000_0000) by (nonlinear_arith)
        requires cnt_r(t, k, lo, i) <= 0x1_0000_0000_0000_0000;
    assert(0x8000_0000 * cnt_r(t, k, lo, i) <= 0x8000_0000 * 0x1_0000_0000_0000_0000) by (nonlinear_arith)
        requires cnt_r(t, k, lo, i) <= 0x1_0000_0000_0000_0000;
}

/// Counting a qualifying row of group `g` and `sub` row `id` directly into the counts, sums and bit sets (with no
/// current group or run) keeps the invariant one row further.
#[verifier::spinoff_prover]
proof fn lemma_row_direct(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc, a2: Acc, g: int, id: int)
    requires
        inv(c, t, lo, hi, i, st, a), i < hi, qual(t[i]), !st.have_g, !st.have_a,
        0 <= g < st.ng, gkey(t, a.rep@, g) == key_of(t[i]),
        0 <= id < c.m, c.subtext(id) == c.atext(i),
        a2.rep@ == a.rep@, a2.scodes@ == a.scodes@, a2.rcodes@ == a.rcodes@, a2.hint@ == a.hint@,
        a.cnt@[g] < 0xffff_ffff_ffff_ffff,
        -0x8000_0000 * 0x1_0000_0000_0000_0000 <= a.sum@[g] <= 0x8000_0000 * 0x1_0000_0000_0000_0000,
        a2.cnt@ == a.cnt@.update(g, (a.cnt@[g] + 1) as u64),
        a2.sum@ == a.sum@.update(g, (a.sum@[g] + c.line@[i]) as i128),
        a2.mask@ == a.mask@.update(id, a.mask@[id] | (1u16 << (g as u16))),
    ensures
        inv(c, t, lo, hi, i + 1, st, a2),
{
    reveal(inv);
    let rep = a.rep@;
    let ng = st.ng as int;
    let em = eff(st, a.mask@);
    let em2 = eff(st, a2.mask@);
    assert(em == a.mask@);
    assert(em2 == a2.mask@);
    assert(row_corr(c, t[i], i));
    let k = key_of(t[i]);
    lemma_hit_step(t, k, lo, i);
    assert(line_of(t[i]) == c.line@[i] as int);
    assert(t[i][0] == Val::Text(c.subtext(id)));
    assert forall|g2: int| 0 <= g2 < ng && g2 != g implies
        #[trigger] cnt_r(t, gkey(t, rep, g2), lo, i + 1) == cnt_r(t, gkey(t, rep, g2), lo, i)
        && sum_r(t, gkey(t, rep, g2), lo, i + 1) == sum_r(t, gkey(t, rep, g2), lo, i)
        && aset_r(t, gkey(t, rep, g2), lo, i + 1) == aset_r(t, gkey(t, rep, g2), lo, i) by {
        assert(gkey(t, rep, g2) != gkey(t, rep, g));
        lemma_nohit_step(t, gkey(t, rep, g2), lo, i);
    }
    assert forall|g2: int| 0 <= g2 < st.ng implies #[trigger] a2.cnt@[g2] + pend_cnt(st, g2) == cnt_r(t, gkey(t, rep, g2), lo, i + 1) by {
        assert(a.cnt@[g2] + pend_cnt(st, g2) == cnt_r(t, gkey(t, rep, g2), lo, i));
    }
    assert forall|g2: int| 0 <= g2 < st.ng implies #[trigger] a2.sum@[g2] + pend_sum(st, g2) == sum_r(t, gkey(t, rep, g2), lo, i + 1) by {
        assert(a.sum@[g2] + pend_sum(st, g2) == sum_r(t, gkey(t, rep, g2), lo, i));
    }
    assert forall|g2: int| st.ng <= g2 < GCAP implies #[trigger] a2.cnt@[g2] == 0 && a2.sum@[g2] == 0 by {
        lemma_acc_tail(t, lo, i, st, rep, a.cnt@, a.sum@, g2);
    }
    assert(acc_ok(t, lo, i + 1, st, rep, a2.cnt@, a2.sum@));
    assert forall|j: int| lo <= j < i + 1 && qual(#[trigger] t[j]) implies exists|g3: int| 0 <= g3 < ng && key_of(t[j]) == gkey(t, rep, g3) by {
        if j == i {
            assert(key_of(t[j]) == gkey(t, rep, g));
        }
    }
    assert(groups_ok(t, lo, hi, i + 1, ng, rep));
    assert forall|g2: int| 0 <= g2 < ng implies
        aset_r(t, #[trigger] gkey(t, rep, g2), lo, i).subset_of(aset_r(t, gkey(t, rep, g2), lo, i + 1)) by {
    }
    assert(mask_sound(c, t, lo, i + 1, ng, rep, em2)) by {
        assert forall|id2: int, b: u16| 0 <= id2 < c.m && b < 16 && #[trigger] bit16(em2[id2], b)
            implies b < ng && aset_r(t, gkey(t, rep, b as int), lo, i + 1).contains(Val::Text(c.subtext(id2))) by {
            if id2 == id {
                lemma_or16(a.mask@[id], 1u16 << (g as u16), b);
                lemma_one16(g as u16, b);
                if bit16(em[id2], b) {
                    assert(aset_r(t, gkey(t, rep, b as int), lo, i).subset_of(aset_r(t, gkey(t, rep, b as int), lo, i + 1)));
                } else {
                    assert(b as int == g);
                }
            } else {
                assert(em2[id2] == em[id2]);
                assert(aset_r(t, gkey(t, rep, b as int), lo, i).subset_of(aset_r(t, gkey(t, rep, b as int), lo, i + 1)));
            }
        }
    }
    assert(mask_complete(c, t, lo, i + 1, ng, rep, em2)) by {
        assert forall|g2: int, v: Val| 0 <= g2 < ng && #[trigger] aset_r(t, gkey(t, rep, g2), lo, i + 1).contains(v)
            implies exists|id2: int| 0 <= id2 < c.m && Val::Text(c.subtext(id2)) == v && #[trigger] bit16(em2[id2], g2 as u16) by {
            if g2 == g && v == t[i][0] {
                lemma_or16(a.mask@[id], 1u16 << (g as u16), g2 as u16);
                lemma_one16(g as u16, g2 as u16);
                assert(bit16(em2[id], g2 as u16));
            } else {
                assert(aset_r(t, gkey(t, rep, g2), lo, i).contains(v));
                let id2 = choose|id2: int| 0 <= id2 < c.m && Val::Text(c.subtext(id2)) == v && #[trigger] bit16(em[id2], g2 as u16);
                if id2 == id {
                    lemma_or16(a.mask@[id], 1u16 << (g as u16), g2 as u16);
                }
                assert(bit16(em2[id2], g2 as u16));
            }
        }
    }
}

/// The group a hint entry names holds the row's key when the group's codes are the row's.
proof fn lemma_hint_group(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc, g: int, cs: u64, cr: u64)
    requires
        inv(c, t, lo, hi, i, st, a), i < hi, qual(t[i]), 0 <= g < st.ng,
        cs != 0, cs == scode(c.stext(i)), cr != 0, cr == scode(c.rtext(i)),
        a.scodes@[g] == cs, a.rcodes@[g] == cr,
    ensures
        gkey(t, a.rep@, g) == key_of(t[i]),
{
    reveal(inv);
    let r = a.rep@[g] as int;
    assert(codes_ok(c, st.ng as int, a.rep@, a.scodes@, a.rcodes@));
    lemma_codes_match(c, t, r, i, a.scodes@[g], a.rcodes@[g], cs, cr);
}

/// Rows `b0 .. b0 + nb` of a fixed-width block, counted one by one straight into the counts, sums and bit sets:
/// for rows that change group or adsh on most rows (the shuffled part of `pre`), where runs do not pay. The group
/// comes from the hint table, the `sub` row from the task's cache. Needs (and leaves) no current group or run.
/// Returns the status and the number of rows whose adsh differs from the previous row's.
fn dense_block(c: &Cols, d: &Dict, cache: &mut Vec<u64>, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>,
    Ghost(hi): Ghost<int>, st: &mut St, a: &mut Acc, b0: usize, nb: usize, ao: &[i64], so: &[i64], ro: &[i64],
    va: &[u8], ln: &[i32], a_base: usize, s_base: usize, r_base: usize) -> (res: (u8, usize))
    requires
        inv(*c, t, lo, hi, b0 as int, *old(st), *old(a)), b0 + nb <= hi, dict_wf(*c, *d), cache_ok(*c, old(cache)@),
        !old(st).have_g, !old(st).have_a,
        fixed_ok(*c, b0 as int, nb as int, ao@, so@, ro@, va@, ln@, a_base as int, s_base as int, r_base as int),
    ensures
        res.0 == ST_OK ==> inv(*c, t, lo, hi, b0 + nb, *final(st), *final(a)) && !final(st).have_g && !final(st).have_a,
        cache_ok(*c, final(cache)@),
    no_unwind
{
    proof { lemma_inv_basic(*c, t, lo, hi, b0 as int, *st, *a); }
    let (_, tl) = c.adsh.split_at(a_base);
    let (ab, _) = tl.split_at(20 * nb);
    let (_, tl) = c.stmt.split_at(s_base);
    let (sb, _) = tl.split_at(2 * nb);
    let (_, tl) = c.rfile.split_at(r_base);
    let (rb, _) = tl.split_at(nb);
    proof {
        assert(ab@ =~= c.adsh@.subrange(a_base as int, a_base + 20 * nb));
        assert(sb@ =~= c.stmt@.subrange(s_base as int, s_base + 2 * nb));
        assert(rb@ =~= c.rfile@.subrange(r_base as int, r_base + nb));
    }
    let mut lw0: u64 = 0;
    let mut lw1: u64 = 0;
    let mut lw2: u64 = 0;
    let mut nch: usize = 0;
    let mut k: usize = 0;
    while k < nb
        invariant
            inv(*c, t, lo, hi, b0 + k, *st, *a), !st.have_g, !st.have_a, k <= nb, nch <= k,
            b0 + nb <= hi, hi <= c.n, dict_wf(*c, *d), cache_ok(*c, cache@),
            fixed_ok(*c, b0 as int, nb as int, ao@, so@, ro@, va@, ln@, a_base as int, s_base as int, r_base as int),
            ab@ == c.adsh@.subrange(a_base as int, a_base + 20 * nb),
            sb@ == c.stmt@.subrange(s_base as int, s_base + 2 * nb),
            rb@ == c.rfile@.subrange(r_base as int, r_base + nb),
        decreases nb - k,
    {
        let i = b0 + k;
        let ghost ii = i as int;
        proof {
            lemma_inv_basic(*c, t, lo, hi, ii, *st, *a);
            lemma_fixed_row(*c, t, b0 as int, nb as int, ao@, so@, ro@, va@, ln@, ab@, sb@, rb@,
                a_base as int, s_base as int, r_base as int, k as int);
        }
        let cs = (sb[2 * k] as u64) | ((sb[2 * k + 1] as u64) << 8u64) | (3u64 << 56u64);
        let cr = (rb[k] as u64) | (2u64 << 56u64);
        let w0 = load8(ab, 20 * nb, 20 * k);
        let w1 = load8(ab, 20 * nb, 20 * k + 8);
        let w2 = load8(ab, 20 * nb, 20 * k + 12);
        let a0 = a_base + 20 * k;
        let hx = ((cs ^ (cr << 7u64)) as u128 * 0x9E37_79B9_7F4A_7C15u128) as u64;
        let hix = (hx >> 58u64) as usize;
        proof { lemma_hix(hx); }
        let hg = a.hint[hix] as usize;
        let g: usize;
        if hg > 0 && hg <= st.ng && a.scodes[hg - 1] == cs && a.rcodes[hg - 1] == cr {
            g = hg - 1;
            proof { lemma_hint_group(*c, t, lo, hi, ii, *st, *a, g as int, cs, cr); }
        } else {
            if !switch_group(c, Ghost(t), Ghost(lo), Ghost(hi), i, st, a, s_base + 2 * k, s_base + 2 * k + 2,
                r_base + k, r_base + k + 1, cs, cr) {
                return (ST_GROUPS, nch);
            }
            g = st.cg;
            proof { lemma_inv_basic(*c, t, lo, hi, ii, *st, *a); }
            flush_group(Ghost(*c), Ghost(t), Ghost(lo), Ghost(hi), Ghost(ii), st, a);
        }
        let id = match cached_lookup(c, d, cache, a0, a0 + 20, w0, w1, w2) {
            Some(j) => j,
            None => {
                return (ST_MISSING, nch);
            },
        };
        if (w0 ^ lw0) | (w1 ^ lw1) | (w2 ^ lw2) != 0 {
            nch = nch + 1;
        }
        lw0 = w0;
        lw1 = w1;
        lw2 = w2;
        let ghost a1 = *a;
        proof {
            lemma_inv_basic(*c, t, lo, hi, ii, *st, *a);
            lemma_direct_bounds(*c, t, lo, hi, ii, *st, *a, g as int);
        }
        a.cnt[g] = a.cnt[g] + 1;
        a.sum[g] = a.sum[g] + ln[k] as i128;
        a.mask[id] = a.mask[id] | (1u16 << (g as u16));
        proof { lemma_row_direct(*c, t, lo, hi, ii, *st, a1, *a, g as int, id as int); }
        k = k + 1;
    }
    (ST_OK, nch)
}

/// Fresh buffers: all counts, sums and bit sets zero.
pub open spec fn fresh(c: Cols, a: Acc) -> bool {
    &&& shapes(c, a)
    &&& forall|g: int| 0 <= g < GCAP ==> #[trigger] a.cnt@[g] == 0 && a.sum@[g] == 0
    &&& forall|id: int| 0 <= id < c.m ==> #[trigger] a.mask@[id] == 0
}

/// The state before the first row.
pub open spec fn st_init() -> St {
    St { ng: 0, have_g: false, cg: 0, cbit: 0, ccs: 0, ccr: 0, acc_cnt: 0, acc_sum: 0, have_a: false, pa0: 0, pa1: 0,
        pw0: 0, pw1: 0, pw2: 0, cid: 0, cmask: 0 }
}

proof fn lemma_init(c: Cols, t: Seq<Row>, lo: int, hi: int, a: Acc)
    requires cols_wf(c), corr(c, t), 0 <= lo <= hi <= c.n, fresh(c, a),
    ensures inv(c, t, lo, hi, lo, st_init(), a),
{
    reveal(inv);
    let st = st_init();
    assert forall|id: int, b: u16| 0 <= id < c.m && b < 16 && #[trigger] bit16(eff(st, a.mask@)[id], b)
        implies b < 0 && aset_r(t, gkey(t, a.rep@, b as int), lo, lo).contains(Val::Text(c.subtext(id))) by {
        assert(a.mask@[id] == 0);
        lemma_zero16(b);
    }
}

/// With the pending group and run written back, the invariant at `hi` is the range's result.
proof fn lemma_out(c: Cols, t: Seq<Row>, lo: int, hi: int, st: St, a: Acc)
    requires inv(c, t, lo, hi, hi, st, a), !st.have_g, !st.have_a,
    ensures out_ok(c, t, lo, hi, st.ng as int, a),
{
    reveal(inv);
    assert(eff(st, a.mask@) == a.mask@);
    assert forall|g: int| 0 <= g < st.ng implies #[trigger] a.cnt@[g] == cnt_r(t, gkey(t, a.rep@, g), lo, hi) by {
        assert(a.cnt@[g] + pend_cnt(st, g) == cnt_r(t, gkey(t, a.rep@, g), lo, hi));
    }
    assert forall|g: int| 0 <= g < st.ng implies #[trigger] a.sum@[g] == sum_r(t, gkey(t, a.rep@, g), lo, hi) by {
        assert(a.sum@[g] + pend_sum(st, g) == sum_r(t, gkey(t, a.rep@, g), lo, hi));
    }
}

/// Writing back the run's pending groups and ending the run keeps the invariant.
proof fn lemma_end_run(c: Cols, t: Seq<Row>, lo: int, hi: int, i: int, st: St, a: Acc, st2: St, a2: Acc)
    requires
        inv(c, t, lo, hi, i, st, a),
        a2.mask@ == (if st.have_a { a.mask@.update(st.cid as int, a.mask@[st.cid as int] | st.cmask) } else { a.mask@ }),
        a2.rep@ == a.rep@, a2.cnt@ == a.cnt@, a2.sum@ == a.sum@, a2.scodes@ == a.scodes@, a2.rcodes@ == a.rcodes@,
        a2.hint@ == a.hint@,
        st2 == (St { have_a: false, cmask: 0, ..st }),
    ensures
        inv(c, t, lo, hi, i, st2, a2),
{
    reveal(inv);
    assert(eff(st2, a2.mask@) == eff(st, a.mask@));
    assert(acc_ok(t, lo, i, st2, a2.rep@, a2.cnt@, a2.sum@)) by {
        assert forall|g: int| 0 <= g < st2.ng implies #[trigger] a2.cnt@[g] + pend_cnt(st2, g) == cnt_r(t, gkey(t, a2.rep@, g), lo, i) by {
            assert(a.cnt@[g] + pend_cnt(st, g) == cnt_r(t, gkey(t, a.rep@, g), lo, i));
        }
        assert forall|g: int| 0 <= g < st2.ng implies #[trigger] a2.sum@[g] + pend_sum(st2, g) == sum_r(t, gkey(t, a2.rep@, g), lo, i) by {
            assert(a.sum@[g] + pend_sum(st, g) == sum_r(t, gkey(t, a.rep@, g), lo, i));
        }
    }
}

proof fn lemma_or_zero(a: u64, b: u64, c: u64, d: u64, e: u64)
    requires a | b | c | d | e == 0,
    ensures a == 0, b == 0, c == 0, d == 0, e == 0,
{
    assert(a == 0 && b == 0 && c == 0 && d == 0 && e == 0) by (bit_vector)
        requires a | b | c | d | e == 0;
}

proof fn lemma_xor_zero(x: u64, y: u64)
    requires x ^ y == 0,
    ensures x == y,
{
    assert(x == y) by (bit_vector) requires x ^ y == 0;
}

/// Whether the `nb` rows of a block have adsh, stmt and rfile values 20, 2 and 1 bytes wide (consecutive from the
/// first row's offsets) and no NULL stmt (branch-free, so the loop vectorizes).
#[inline(always)]
fn fixed_widths(ao: &[i64], so: &[i64], ro: &[i64], va: &[u8], nb: usize) -> (fixed: bool)
    requires
        ao@.len() == nb + 1, so@.len() == nb + 1, ro@.len() == nb + 1, va@.len() == nb,
        forall|k: int| 0 <= k < nb ==> 0 <= #[trigger] ao@[k] <= ao@[k + 1],
        forall|k: int| 0 <= k < nb ==> 0 <= #[trigger] so@[k] <= so@[k + 1],
        forall|k: int| 0 <= k < nb ==> 0 <= #[trigger] ro@[k] <= ro@[k + 1],
    ensures
        fixed ==> forall|k: int| 0 <= k <= nb ==> #[trigger] ao@[k] == ao@[0] + 20 * k,
        fixed ==> forall|k: int| 0 <= k <= nb ==> #[trigger] so@[k] == so@[0] + 2 * k,
        fixed ==> forall|k: int| 0 <= k <= nb ==> #[trigger] ro@[k] == ro@[0] + k,
        fixed ==> forall|k: int| 0 <= k < nb ==> #[trigger] va@[k] != 0,
    no_unwind
{
    let mut bad: u64 = 0;
    let mut k: usize = 0;
    while k < nb
        invariant
            k <= nb, ao@.len() == nb + 1, so@.len() == nb + 1, ro@.len() == nb + 1, va@.len() == nb,
            forall|k2: int| 0 <= k2 < nb ==> 0 <= #[trigger] ao@[k2] <= ao@[k2 + 1],
            forall|k2: int| 0 <= k2 < nb ==> 0 <= #[trigger] so@[k2] <= so@[k2 + 1],
            forall|k2: int| 0 <= k2 < nb ==> 0 <= #[trigger] ro@[k2] <= ro@[k2 + 1],
            bad == 0 ==> forall|k2: int| 0 <= k2 <= k ==> #[trigger] ao@[k2] == ao@[0] + 20 * k2,
            bad == 0 ==> forall|k2: int| 0 <= k2 <= k ==> #[trigger] so@[k2] == so@[0] + 2 * k2,
            bad == 0 ==> forall|k2: int| 0 <= k2 <= k ==> #[trigger] ro@[k2] == ro@[0] + k2,
            bad == 0 ==> forall|k2: int| 0 <= k2 < k ==> #[trigger] va@[k2] != 0,
        decreases nb - k,
    {
        proof {
            assert(0 <= ao@[k as int] <= ao@[k + 1]);
            assert(0 <= so@[k as int] <= so@[k + 1]);
            assert(0 <= ro@[k as int] <= ro@[k + 1]);
        }
        let d1 = (ao[k + 1] - ao[k]) as u64;
        let d2 = (so[k + 1] - so[k]) as u64;
        let d3 = (ro[k + 1] - ro[k]) as u64;
        let v: u64 = if va[k] == 0 { 1 } else { 0 };
        let ghost bad0 = bad;
        bad = bad | (d1 ^ 20u64) | (d2 ^ 2u64) | (d3 ^ 1u64) | v;
        proof {
            if bad == 0 {
                lemma_or_zero(bad0, d1 ^ 20u64, d2 ^ 2u64, d3 ^ 1u64, v);
                lemma_xor_zero(d1, 20u64);
                lemma_xor_zero(d2, 2u64);
                lemma_xor_zero(d3, 1u64);
            }
        }
        k = k + 1;
    }
    bad == 0
}

/// Scans the block `[b0, b0 + nb)`.
fn scan_block(c: &Cols, d: &Dict, cache: &mut Vec<u64>, Ghost(t): Ghost<Seq<Row>>, Ghost(lo): Ghost<int>,
    Ghost(hi): Ghost<int>, st: &mut St, a: &mut Acc, b0: usize, nb: usize, dense: bool) -> (res: (u8, usize))
    requires
        inv(*c, t, lo, hi, b0 as int, *old(st), *old(a)), b0 + nb <= hi, 1 <= nb <= BLK, dict_wf(*c, *d),
        cache_ok(*c, old(cache)@),
    ensures
        res.0 == ST_OK ==> inv(*c, t, lo, hi, b0 + nb, *final(st), *final(a)),
        cache_ok(*c, final(cache)@),
    no_unwind
{
    proof { lemma_inv_basic(*c, t, lo, hi, b0 as int, *st, *a); }
    let (_, tl) = c.adsh_off.split_at(b0);
    let (ao, _) = tl.split_at(nb + 1);
    let (_, tl) = c.stmt_off.split_at(b0);
    let (so, _) = tl.split_at(nb + 1);
    let (_, tl) = c.rfile_off.split_at(b0);
    let (ro, _) = tl.split_at(nb + 1);
    let (_, tl) = c.stmt_valid.split_at(b0);
    let (va, _) = tl.split_at(nb);
    let (_, tl) = c.line.split_at(b0);
    let (ln, _) = tl.split_at(nb);
    proof {
        assert(ao@ =~= c.adsh_off@.subrange(b0 as int, b0 + nb + 1));
        assert(so@ =~= c.stmt_off@.subrange(b0 as int, b0 + nb + 1));
        assert(ro@ =~= c.rfile_off@.subrange(b0 as int, b0 + nb + 1));
        assert(va@ =~= c.stmt_valid@.subrange(b0 as int, b0 + nb));
        assert(ln@ =~= c.line@.subrange(b0 as int, b0 + nb));
        assert forall|k: int| 0 <= k < nb implies 0 <= #[trigger] ao@[k] <= ao@[k + 1] by {
            assert(ao@[k] == c.adsh_off@[b0 + k] && ao@[k + 1] == c.adsh_off@[b0 + k + 1]);
            assert(0 <= c.adsh_off@[b0 + k] <= c.adsh_off@[b0 + k + 1] <= c.adsh@.len());
        }
        assert forall|k: int| 0 <= k < nb implies 0 <= #[trigger] so@[k] <= so@[k + 1] by {
            assert(so@[k] == c.stmt_off@[b0 + k] && so@[k + 1] == c.stmt_off@[b0 + k + 1]);
            assert(0 <= c.stmt_off@[b0 + k] <= c.stmt_off@[b0 + k + 1] <= c.stmt@.len());
        }
        assert forall|k: int| 0 <= k < nb implies 0 <= #[trigger] ro@[k] <= ro@[k + 1] by {
            assert(ro@[k] == c.rfile_off@[b0 + k] && ro@[k + 1] == c.rfile_off@[b0 + k + 1]);
            assert(0 <= c.rfile_off@[b0 + k] <= c.rfile_off@[b0 + k + 1] <= c.rfile@.len());
        }
        assert(0 <= c.adsh_off@[b0 as int] <= c.adsh@.len());
        assert(0 <= c.stmt_off@[b0 as int] <= c.stmt@.len());
        assert(0 <= c.rfile_off@[b0 as int] <= c.rfile@.len());
    }
    let a_base = ao[0] as usize;
    let s_base = so[0] as usize;
    let r_base = ro[0] as usize;
    let fixed = fixed_widths(ao, so, ro, va, nb);
    if fixed && c.adsh_len - a_base >= 20 * nb && c.stmt_len - s_base >= 2 * nb && c.rfile_len - r_base >= nb {
        proof {
            assert(fixed_ok(*c, b0 as int, nb as int, ao@, so@, ro@, va@, ln@, a_base as int, s_base as int, r_base as int));
        }
        if dense {
            flush_group(Ghost(*c), Ghost(t), Ghost(lo), Ghost(hi), Ghost(b0 as int), st, a);
            let ghost st1 = *st;
            let ghost a1 = *a;
            proof { lemma_inv_basic(*c, t, lo, hi, b0 as int, *st, *a); }
            if st.have_a {
                let id = st.cid;
                a.mask[id] = a.mask[id] | st.cmask;
            }
            st.have_a = false;
            st.cmask = 0;
            proof { lemma_end_run(*c, t, lo, hi, b0 as int, st1, a1, *st, *a); }
            dense_block(c, d, cache, Ghost(t), Ghost(lo), Ghost(hi), st, a, b0, nb, ao, so, ro, va, ln, a_base, s_base, r_base)
        } else {
            fast_block(c, d, cache, Ghost(t), Ghost(lo), Ghost(hi), st, a, b0, nb, ao, so, ro, va, ln, a_base, s_base, r_base)
        }
    } else {
        let r = generic_block(c, d, cache, Ghost(t), Ghost(lo), Ghost(hi), st, a, b0, nb, ao, so, ro, va, ln);
        (r, 0)
    }
}

/// Scans rows `[lo, hi)`: `(status, number of groups, buffers)`; with status `ST_OK` the buffers hold the range's
/// groups, counts, sums and adsh bit sets (`out_ok`).
pub fn scan_range(c: &Cols, d: &Dict, Ghost(t): Ghost<Seq<Row>>, lo: usize, hi: usize, acc: Acc, cache: Vec<u64>)
    -> (r: (u8, usize, Acc))
    requires
        cols_wf(*c), corr(*c, t), dict_wf(*c, *d), lo <= hi <= c.n, fresh(*c, acc), cache_ok(*c, cache@),
    ensures
        r.0 == ST_OK ==> out_ok(*c, t, lo as int, hi as int, r.1 as int, r.2),
    no_unwind
{
    let mut a = acc;
    let mut cache = cache;
    let mut dense = false;
    let mut st = St {
        ng: 0, have_g: false, cg: 0, cbit: 0, ccs: 0, ccr: 0, acc_cnt: 0, acc_sum: 0,
        have_a: false, pa0: 0, pa1: 0, pw0: 0, pw1: 0, pw2: 0, cid: 0, cmask: 0,
    };
    proof { lemma_init(*c, t, lo as int, hi as int, a); }
    let mut b0 = lo;
    while b0 < hi
        invariant
            inv(*c, t, lo as int, hi as int, b0 as int, st, a), lo <= b0 <= hi, hi <= c.n, dict_wf(*c, *d),
            cache_ok(*c, cache@),
        decreases hi - b0,
    {
        let nb = if hi - b0 > BLK { BLK } else { hi - b0 };
        let (res, changes) = scan_block(c, d, &mut cache, Ghost(t), Ghost(lo as int), Ghost(hi as int), &mut st, &mut a,
            b0, nb, dense);
        if res != ST_OK {
            return (res, st.ng, a);
        }
        dense = changes > nb / 4;
        b0 = b0 + nb;
    }
    flush_group(Ghost(*c), Ghost(t), Ghost(lo as int), Ghost(hi as int), Ghost(hi as int), &mut st, &mut a);
    let ghost st1 = st;
    let ghost a1 = a;
    proof { lemma_inv_basic(*c, t, lo as int, hi as int, hi as int, st, a); }
    if st.have_a {
        let id = st.cid;
        a.mask[id] = a.mask[id] | st.cmask;
    }
    st.have_a = false;
    st.cmask = 0;
    proof {
        lemma_end_run(*c, t, lo as int, hi as int, hi as int, st1, a1, st, a);
        lemma_out(*c, t, lo as int, hi as int, st, a);
    }
    (ST_OK, st.ng, a)
}

} // verus!
