//! Phase A of the partitioned plan (`round::fast_counts`): the (local group, supplier row) pairs of the part rows
//! `[lo, hi)`, packed into 32-bit entries and written into per-partition regions.
//!
//! Partitions: local group `g` lies in partition `g / 64` at slot `g % 64` (`GPP` groups per partition). An entry is
//! `slot * 2^20 + supplier row` (`enc`), so the task needs every supplier row below `2^20` (`XLIM`).
//! Pass 1 (`pass1`) scans the part rows block by block with the per-block code tables of `kernel` and lists every
//! coded row by its offset from `lo` (`ptmp`, `listed`), counting the rows of each partition in `cur`. The counts only
//! size the regions: region `p` gets `ratio` entries per counted row (`regions`: `start[p] .. start[p + 1]`), and every
//! write is checked against the region's end. Pass 2 (`pass2`) walks the listed rows: every partsupp row of the row's
//! key (`kernel::ps_rows_of`) with a supplier row of its suppkey (`kernel::supp_of`) gives the entry of the pair
//! (code, supplier row), appended to the partition's region at `cur[p]` (`rhas`: the region holds a pair). A full
//! region stops the task (`ok == false`; the round then runs the general plan).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use super::tables::*;
use super::model::*;
use super::kernel::*;
use super::supp::{SuppTask, SuppOut};
use super::common::bytemask::*;

verus! {

broadcast use vstd::array::group_array_axioms;

/// Local groups per partition.
pub const GPP: usize = 64;
/// Supplier rows of a packed entry are below `XLIM`.
pub const XLIM: usize = 0x10_0000;

/// The packed entry of slot `lc` and supplier row `x`.
pub open spec fn enc(lc: int, x: int) -> int {
    lc * 0x10_0000 + x
}

/// Decoding: slot and supplier row of a packed entry.
pub open spec fn slot_of_ent(v: int) -> int {
    v / 0x10_0000
}

pub open spec fn x_of_ent(v: int) -> int {
    v % 0x10_0000
}

/// An entry is the encoding of its slot and supplier row.
pub proof fn lemma_enc(lc: int, x: int)
    requires 0 <= lc, 0 <= x < 0x10_0000,
    ensures slot_of_ent(enc(lc, x)) == lc, x_of_ent(enc(lc, x)) == x,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(enc(lc, x), 0x10_0000, lc, x);
}

/// Entries `[a, b)` of `out`: slots below `GPP`, supplier rows below `sn`.
pub open spec fn ent_ok(out: Seq<u32>, a: int, b: int, sn: int) -> bool {
    forall|k: int| a <= k < b ==> slot_of_ent(#[trigger] out[k] as int) < 64 && x_of_ent(out[k] as int) < sn
}

/// The regions: `start` sorted, inside the output, region `p` filled up to `cur[p]` with valid entries.
pub open spec fn regs_ok(start: Seq<usize>, cur: Seq<usize>, out: Seq<u32>, np: int, sn: int) -> bool {
    &&& start.len() == np + 1
    &&& cur.len() == np + 1
    &&& forall|p1: int, p2: int| 0 <= p1 <= p2 <= np ==> #[trigger] start[p1] <= #[trigger] start[p2]
    &&& start[np] <= out.len()
    &&& forall|p: int| 0 <= p < np ==> #[trigger] cur[p] >= start[p] && cur[p] <= start[p + 1]
    &&& forall|p: int| 0 <= p < np ==> #[trigger] ent_ok(out, start[p] as int, cur[p] as int, sn)
}

/// The region of local group `g`'s partition holds the entry of (`g`, `x`) (`x` below `2^20`).
pub open spec fn rhas(out: Seq<u32>, start: Seq<usize>, cur: Seq<usize>, g: int, x: int) -> bool {
    &&& 0 <= x < 0x10_0000
    &&& exists|k: int| start[g / 64] <= k < cur[g / 64] && #[trigger] out[k] as int == enc(g % 64, x)
}

/// The part row of listed entry `r`.
pub open spec fn lrow(lo: int, ptmp: Seq<u32>, r: int) -> int {
    lo + ptmp[r] as int
}

/// The pairs of the listed rows below `r`.
pub open spec fn done_pair(q: QualTabs, c: Cols, lo: int, ptmp: Seq<u32>, r: int, g: int, x: int) -> bool {
    exists|r2: int, i: int| 0 <= r2 < r && #[trigger] pair_at(q, c, lrow(lo, ptmp, r2), i, g, x)
}

/// `ptmp[..m]` lists offsets of coded rows of `[lo, j)`, and lists every such row.
pub open spec fn listed(q: QualTabs, p: PCols, lo: int, j: int, ptmp: Seq<u32>, m: int) -> bool {
    &&& 0 <= m <= ptmp.len()
    &&& forall|r: int| 0 <= r < m ==> lo <= #[trigger] lrow(lo, ptmp, r) < j && coded(q, p, lrow(lo, ptmp, r))
    &&& forall|j2: int| lo <= j2 < j && #[trigger] coded(q, p, j2) ==> exists|r: int| 0 <= r < m && #[trigger] lrow(lo, ptmp, r) == j2
}

pub struct SelTask {
    pub env: Arc<PairEnv>,
    /// Local groups of the round and partitions (`ng <= 64 * np`).
    pub ng: usize,
    pub np: usize,
    pub lo: usize,
    pub hi: usize,
    /// Scratch: the listed rows (more than `hi - lo` entries) and their codes (as many).
    pub ptmp: Vec<u32>,
    pub pcode: Vec<u32>,
    /// Scratch: the code tables of the current part block, its size codes, and one chunk's flags and positions.
    pub btab: [u32; 256],
    pub ttab: [u32; 256],
    pub stab: [u32; 256],
    pub cv: [u8; 8],
    pub hits: [u8; 64],
    pub idx: [u8; 64],
    /// Output: the entries; `start` and `cur` (`np + 1` entries each, all zero).
    pub out: Vec<u32>,
    pub start: Vec<usize>,
    pub cur: Vec<usize>,
    /// The supplier rows this task decides for the subquery.
    pub supp: SuppTask,
}

pub struct SelOut {
    pub out: Vec<u32>,
    pub start: Vec<usize>,
    pub cur: Vec<usize>,
    /// False when a region was full (the task stopped).
    pub ok: bool,
    pub supp: SuppOut,
}

/// The region of `g`'s partition in an output holds (`g`, `x`).
pub open spec fn reg_has(o: SelOut, g: int, x: int) -> bool {
    rhas(o.out@, o.start@, o.cur@, g, x)
}

/// A finished output of part rows `[lo, hi)`: valid regions holding exactly the rows' pairs.
pub open spec fn sel_ok(q: QualTabs, c: Cols, lo: int, hi: int, np: int, o: SelOut) -> bool {
    &&& regs_ok(o.start@, o.cur@, o.out@, np, c.s.n as int)
    &&& forall|g: int, x: int| 0 <= g < 64 * np ==> (#[trigger] reg_has(o, g, x) <==> pair_in(q, c, lo, hi, g, x))
}

/// What a task needs: the environment of a round of `ng <= 64 * np` local groups, supplier rows below `2^20`, a row
/// range whose offsets fit `u32`, and room for `hi - lo + 1` listed rows.
pub open spec fn sel_pre(e: PairEnv, ng: int, np: int, lo: int, hi: int, ptmp: Seq<u32>, start: Seq<usize>,
    cur: Seq<usize>) -> bool {
    &&& env_ok(e, ng)
    &&& ng <= 64 * np
    &&& np < 0x1_0000_0000
    &&& e.c.s.n <= 0x10_0000
    &&& 0 <= lo <= hi <= e.c.p.n
    &&& e.c.p.n < 0xFFFF_FFFF
    &&& ptmp.len() > hi - lo
    &&& start.len() == np + 1
    &&& cur.len() == np + 1
    &&& forall|p: int| 0 <= p <= np ==> #[trigger] cur[p] == 0
}

impl WorkerTask for SelTask {
    type Output = SelOut;

    open spec fn pre(&self) -> bool {
        &&& sel_pre(*self.env, self.ng as int, self.np as int, self.lo as int, self.hi as int, self.ptmp@,
            self.start@, self.cur@)
        &&& self.pcode@.len() == self.ptmp@.len()
        &&& self.supp.pre()
    }

    open spec fn post(&self, out: SelOut) -> bool {
        &&& out.ok ==> sel_ok(*self.env.tabs, self.env.c, self.lo as int, self.hi as int, self.np as int, out)
        &&& self.supp.post(out.supp)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: SelOut) {
        let SelTask { env, ng, np, lo, hi, ptmp, pcode, btab, ttab, stab, cv, hits, idx, out, start, cur, supp } = self;
        let so = supp.run();
        let mut ptmp = ptmp;
        let mut pcode = pcode;
        let mut cv = cv;
        let mut hits = hits;
        let mut idx = idx;
        let mut btab = btab;
        let mut ttab = ttab;
        let mut stab = stab;
        let mut out = out;
        let mut start = start;
        let mut cur = cur;
        let e: &PairEnv = &*env;
        let q: &QualTabs = &*e.tabs;
        let m = pass1(e, q, ng, np, lo, hi, &mut ptmp, &mut pcode, &mut cur, &mut btab, &mut ttab, &mut stab, &mut cv, &mut hits,
            &mut idx);
        let olen = out.len();
        if !regions(e.ratio, np, &mut start, &mut cur, olen) {
            return SelOut { out, start, cur, ok: false, supp: so };
        }
        proof {
            assert forall|p: int| 0 <= p < np implies #[trigger] ent_ok(out@, start@[p] as int, cur@[p] as int, e.c.s.n as int) by {}
            assert(regs_ok(start@, cur@, out@, np as int, e.c.s.n as int));
            assert forall|g: int, x: int| 0 <= g < 64 * np implies
                (#[trigger] rhas(out@, start@, cur@, g, x) <==> done_pair(*q, e.c, lo as int, ptmp@, 0, g, x)) by {
                if rhas(out@, start@, cur@, g, x) {
                    lemma_part_div(g, np as int);
                }
            }
        }
        let ok = pass2(e, q, ng, np, lo, hi, &ptmp, &pcode, m, &mut out, &start, &mut cur);
        let r = SelOut { out, start, cur, ok, supp: so };
        r
    }
}

/// A local group below `64 * np` lies in a partition below `np`.
pub proof fn lemma_part_div(g: int, np: int)
    requires 0 <= g < 64 * np,
    ensures 0 <= g / 64 < np, 0 <= g % 64 < 64, g == (g / 64) * 64 + g % 64,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(g, 64);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(g, 64);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(g, 64);
    if g / 64 >= np {
        assert(64 * (g / 64) >= 64 * np) by (nonlinear_arith) requires g / 64 >= np;
    }
}

// ------------------------------------------------------------------------------------------------ pass 1

/// The listed rows' codes: `pcode[r]` is the code of listed row `r`, below `ng`.
pub open spec fn codes_ok(q: QualTabs, p: PCols, lo: int, ptmp: Seq<u32>, pcode: Seq<u32>, m: int, ng: int) -> bool {
    &&& pcode.len() == ptmp.len()
    &&& forall|r: int| 0 <= r < m ==> #[trigger] pcode[r] as int == code_of(q, p, lrow(lo, ptmp, r)) && pcode[r] < ng
}

/// The size codes of a part block: `in8(cv, c)` exactly when code `c` is a listed size (`stab[c]` is a slot).
pub open spec fn cv_ok(cv: [u8; 8], stab: [u32; 256]) -> bool {
    forall|c: u8| #[trigger] in8(cv, c) <==> stab@[c as int] != NONE_BIT
}

/// The state of pass 1 at row `j` (rows `[lo, j)` decided), inside part block `g` with tables `btab`, `ttab`, `stab`.
pub open spec fn p1_ok(e: PairEnv, q: QualTabs, ng: int, np: int, lo: int, hi: int, j: int, g: int, ptmp: Seq<u32>,
    pcode: Seq<u32>, cur: Seq<usize>, m: int, btab: [u32; 256], ttab: [u32; 256], stab: [u32; 256]) -> bool {
    &&& env_ok(e, ng)
    &&& *e.tabs == q
    &&& ng <= 64 * np
    &&& np < 0x1_0000_0000
    &&& lo <= j <= hi <= e.c.p.n
    &&& hi - lo < 0xFFFF_FFFF
    &&& 0 <= g < e.c.p.ng
    &&& g * e.c.p.bs <= j
    &&& block_ok(q, e.c.p.brand_b@[g], e.c.p.type_b@[g], e.c.p.size_b@[g], btab, ttab, stab)
    &&& ptmp.len() > hi - lo
    &&& cur.len() == np + 1
    &&& forall|p: int| 0 <= p <= np ==> #[trigger] cur[p] <= j - lo
    &&& m <= j - lo
    &&& listed(q, e.c.p, lo, j, ptmp, m)
    &&& codes_ok(q, e.c.p, lo, ptmp, pcode, m, ng)
}

/// Rows `[a, b)` of block `g` whose size code is not in `cv` are not coded.
proof fn lemma_not_hit(e: PairEnv, q: QualTabs, ng: int, g: int, r: int, cv: [u8; 8], stab: [u32; 256], btab: [u32; 256],
    ttab: [u32; 256])
    requires
        env_ok(e, ng), *e.tabs == q,
        0 <= g < e.c.p.ng, g * e.c.p.bs <= r < g * e.c.p.bs + e.c.p.bs, r < e.c.p.n,
        block_ok(q, e.c.p.brand_b@[g], e.c.p.type_b@[g], e.c.p.size_b@[g], btab, ttab, stab),
        cv_ok(cv, stab),
        !in8(cv, e.c.p.size_c@[r]),
    ensures !coded(q, e.c.p, r),
{
    lemma_in_group(e.c.p.bs as int, g, r);
    let c = e.c.p.size_c@[r];
    assert(stab@[c as int] == st_of(q, e.c.p.size_b@[g] + c));
    assert(sval(e.c.p, r) == e.c.p.size_b@[g] + c);
}

/// Extending the listed prefix over rows that are not coded.
proof fn lemma_listed_gap(q: QualTabs, p: PCols, lo: int, a: int, b: int, pt: Seq<u32>, m: int)
    requires listed(q, p, lo, a, pt, m), lo <= a <= b, forall|r: int| a <= r < b ==> !#[trigger] coded(q, p, r),
    ensures listed(q, p, lo, b, pt, m),
{
    assert forall|j2: int| lo <= j2 < b && #[trigger] coded(q, p, j2) implies exists|r: int| 0 <= r < m && #[trigger] lrow(lo, pt, r) == j2 by {
        assert(j2 < a);
    }
}

/// Decides part row `j` of block `g`: lists it with its code when it is coded.
fn list_row(e: &PairEnv, q: &QualTabs, ng: usize, np: usize, lo: usize, hi: usize, j: usize, ptmp: &mut Vec<u32>,
    pcode: &mut Vec<u32>, cur: &mut Vec<usize>, m: usize, btab: &[u32; 256], ttab: &[u32; 256], stab: &[u32; 256],
    Ghost(g): Ghost<int>) -> (m2: usize)
    requires
        p1_ok(*e, *q, ng as int, np as int, lo as int, hi as int, j as int, g, old(ptmp)@, old(pcode)@, old(cur)@, m as int,
            *btab, *ttab, *stab),
        j < hi, j < g * e.c.p.bs + e.c.p.bs,
    ensures
        p1_ok(*e, *q, ng as int, np as int, lo as int, hi as int, j + 1, g, final(ptmp)@, final(pcode)@, final(cur)@,
            m2 as int, *btab, *ttab, *stab),
        final(ptmp)@.len() == old(ptmp)@.len(),
    no_unwind
{
    let ghost c = e.c;
    proof {
        lemma_in_group(c.p.bs as int, g, j as int);
    }
    let x = btab[e.c.p.brand_c[j] as usize];
    let y = ttab[e.c.p.type_c[j] as usize];
    let z = stab[e.c.p.size_c[j] as usize];
    proof {
        lemma_code_bits(*q, c.p, j as int, e.nb as int, e.nt as int, ng as int, x, y, z);
    }
    let ghost pt0 = ptmp@;
    let ghost pc0 = pcode@;
    if (x | y | z) & NONE_BIT == 0 {
        let code: u32 = x + y + z;
        proof {
            lemma_part_div(code as int, np as int);
        }
        let p = (code / 64) as usize;
        let cp = cur[p];
        cur[p] = cp + 1;
        ptmp[m] = (j - lo) as u32;
        pcode[m] = code;
        proof {
            assert forall|p2: int| 0 <= p2 <= np implies #[trigger] cur@[p2] <= j + 1 - lo by {}
            lemma_listed_push(*q, c.p, lo as int, j as int, pt0, ptmp@, m as int);
            assert forall|r: int| 0 <= r < m + 1 implies #[trigger] pcode@[r] as int == code_of(*q, c.p, lrow(lo as int, ptmp@, r))
                && pcode@[r] < ng by {
                if r < m {
                    assert(pcode@[r] == pc0[r]);
                    assert(ptmp@[r] == pt0[r]);
                } else {
                    assert(lrow(lo as int, ptmp@, r) == j);
                }
            }
        }
        m + 1
    } else {
        proof {
            lemma_listed_skip(*q, c.p, lo as int, j as int, ptmp@, m as int);
        }
        m
    }
}

/// The size codes of block `g`'s size base `sb`: `cv_ok` against `stab`, or `false` when no listed size has a code
/// (then every entry of `stab` is `NONE_BIT`). Slot `i < ns` holds size `i`'s code when it has one, every other slot
/// the first code found.
fn size_codes(q: &QualTabs, ns: usize, sb: i64, stab: &[u32; 256], cv: &mut [u8; 8]) -> (any: bool)
    requires
        ns == q.sizes@.len(), ns <= 8,
        forall|c: int| 0 <= c < 256 ==> #[trigger] stab@[c] == st_of(*q, sb + c),
    ensures
        any ==> cv_ok(*final(cv), *stab),
        !any ==> forall|c: int| 0 <= c < 256 ==> #[trigger] stab@[c] == NONE_BIT,
    no_unwind
{
    let mut found = false;
    let mut fv: u8 = 0;
    let mut z: usize = 0;
    while z < ns
        invariant
            z <= ns, ns == q.sizes@.len(), ns <= 8,
            found ==> exists|z2: int| 0 <= z2 < ns && #[trigger] q.sizes@[z2] - sb == fv as int,
            !found ==> forall|z2: int| 0 <= z2 < z ==> !(0 <= #[trigger] q.sizes@[z2] - sb < 256),
        decreases ns - z,
    {
        let d: i128 = q.sizes[z] as i128 - sb as i128;
        if !found && 0 <= d && d < 256 {
            fv = d as u8;
            found = true;
        }
        z = z + 1;
    }
    if !found {
        proof {
            assert forall|c: int| 0 <= c < 256 implies #[trigger] stab@[c] == NONE_BIT by {
                if super::model::listed(q.sizes@, sb + c) {
                    let z2 = choose|z2: int| 0 <= z2 < q.sizes@.len() && q.sizes@[z2] == sb + c;
                    assert(0 <= q.sizes@[z2] - sb < 256);
                }
            }
        }
        return false;
    }
    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8, ns == q.sizes@.len(), ns <= 8,
            exists|z2: int| 0 <= z2 < ns && #[trigger] q.sizes@[z2] - sb == fv as int,
            forall|i2: int| 0 <= i2 < i ==> #[trigger] cv@[i2] as int == (if i2 < ns && 0 <= q.sizes@[i2] - sb < 256 {
                q.sizes@[i2] - sb } else { fv as int }),
        decreases 8 - i,
    {
        let mut v = fv;
        if i < ns {
            let d: i128 = q.sizes[i] as i128 - sb as i128;
            if 0 <= d && d < 256 {
                v = d as u8;
            }
        }
        cv[i] = v;
        i = i + 1;
    }
    proof {
        assert forall|c: u8| #[trigger] in8(*cv, c) <==> stab@[c as int] != NONE_BIT by {
            if in8(*cv, c) {
                let i2 = choose|i2: int| 0 <= i2 < 8 && cv@[i2] == c;
                if i2 < ns && 0 <= q.sizes@[i2] - sb < 256 {
                    assert(q.sizes@[i2] == sb + c);
                } else {
                    let z2 = choose|z2: int| 0 <= z2 < ns && #[trigger] q.sizes@[z2] - sb == fv as int;
                    assert(q.sizes@[z2] == sb + c);
                }
                assert(super::model::listed(q.sizes@, sb + c));
            }
            if stab@[c as int] != NONE_BIT {
                assert(super::model::listed(q.sizes@, sb + c));
                let z2 = choose|z2: int| 0 <= z2 < q.sizes@.len() && q.sizes@[z2] == sb + c;
                assert(cv@[z2] == c);
            }
        }
    }
    true
}

/// The 64 rows `[j, j + 64)` of block `g`, flagged by size code (`hits`) and compacted (`idx[..n]`): lists the coded ones.
fn list_chunk(e: &PairEnv, q: &QualTabs, ng: usize, np: usize, lo: usize, hi: usize, j: usize, ptmp: &mut Vec<u32>,
    pcode: &mut Vec<u32>, cur: &mut Vec<usize>, m: usize, btab: &[u32; 256], ttab: &[u32; 256], stab: &[u32; 256],
    cv: &[u8; 8], hits: &[u8; 64], idx: &[u8; 64], n: usize, Ghost(g): Ghost<int>) -> (m2: usize)
    requires
        p1_ok(*e, *q, ng as int, np as int, lo as int, hi as int, j as int, g, old(ptmp)@, old(pcode)@, old(cur)@, m as int,
            *btab, *ttab, *stab),
        j + 64 <= hi, j + 64 <= g * e.c.p.bs + e.c.p.bs,
        cv_ok(*cv, *stab),
        hits_ok(e.c.p.size_c@.subrange(j as int, j + 64), *cv, *hits),
        compact_ok(*hits, *idx, n as int),
    ensures
        p1_ok(*e, *q, ng as int, np as int, lo as int, hi as int, j + 64, g, final(ptmp)@, final(pcode)@, final(cur)@,
            m2 as int, *btab, *ttab, *stab),
        final(ptmp)@.len() == old(ptmp)@.len(),
    no_unwind
{
    let ghost c = e.c;
    let ghost sc = c.p.size_c@.subrange(j as int, j + 64);
    let mut m = m;
    let mut i: usize = 0;
    // `pos`: the rows below it are decided.
    let ghost mut pos: int = j as int;
    while i < n
        invariant
            p1_ok(*e, *q, ng as int, np as int, lo as int, hi as int, pos, g, ptmp@, pcode@, cur@, m as int, *btab, *ttab, *stab),
            ptmp@.len() == old(ptmp)@.len(),
            c == e.c, sc == c.p.size_c@.subrange(j as int, j + 64),
            j + 64 <= hi, j + 64 <= g * c.p.bs + c.p.bs,
            cv_ok(*cv, *stab), hits_ok(sc, *cv, *hits), compact_ok(*hits, *idx, n as int),
            i <= n,
            j <= pos <= j + 64,
            i < n ==> pos <= j + idx@[i as int],
            i > 0 ==> pos == j + idx@[i - 1] + 1,
            i == 0 ==> pos == j,
        decreases n - i,
    {
        let k = idx[i] as usize;
        let r = j + k;
        proof {
            // Rows `[pos, r)` carry no flag, so they are not coded.
            assert forall|r2: int| pos <= r2 < r implies !#[trigger] coded(*q, c.p, r2) by {
                let k2 = r2 - j;
                assert(sc[k2] == c.p.size_c@[r2]);
                if hits@[k2] == 1u8 {
                    let i2 = choose|i2: int| 0 <= i2 < n && idx@[i2] == k2;
                    if i2 < i {
                        if i2 < i - 1 { assert(idx@[i2] < idx@[i - 1]); }
                    } else if i2 > i {
                        assert(idx@[i as int] < idx@[i2]);
                    }
                }
                assert(!in8(*cv, c.p.size_c@[r2]));
                lemma_not_hit(*e, *q, ng as int, g, r2, *cv, *stab, *btab, *ttab);
            }
            lemma_listed_gap(*q, c.p, lo as int, pos, r as int, ptmp@, m as int);
        }
        m = list_row(e, q, ng, np, lo, hi, r, ptmp, pcode, cur, m, btab, ttab, stab, Ghost(g));
        proof {
            pos = r + 1;
            if i + 1 < n {
                assert(idx@[i as int] < idx@[i + 1]);
            }
        }
        i = i + 1;
    }
    proof {
        assert forall|r2: int| pos <= r2 < j + 64 implies !#[trigger] coded(*q, c.p, r2) by {
            let k2 = r2 - j;
            assert(sc[k2] == c.p.size_c@[r2]);
            if hits@[k2] == 1u8 {
                let i2 = choose|i2: int| 0 <= i2 < n && idx@[i2] == k2;
                if i2 < n - 1 { assert(idx@[i2] < idx@[n - 1]); }
            }
            lemma_not_hit(*e, *q, ng as int, g, r2, *cv, *stab, *btab, *ttab);
        }
        lemma_listed_gap(*q, c.p, lo as int, pos, j + 64, ptmp@, m as int);
        assert forall|p: int| 0 <= p <= np implies #[trigger] cur@[p] <= j + 64 - lo by {}
    }
    m
}

/// Pass 1: lists the coded rows of `[lo, hi)` (offsets from `lo`) with their codes, counting rows per partition in
/// `cur`. Per part block: the code tables (`block_tabs`), the block's size codes (`size_codes`; a block without one
/// has no coded row), then chunks of 64 rows flagged by size code (`eq8_hits`, vectorized) whose flagged rows alone
/// are looked up (`list_chunk`); a tail of fewer than 64 rows is decided row by row.
fn pass1(e: &PairEnv, q: &QualTabs, ng: usize, np: usize, lo: usize, hi: usize, ptmp: &mut Vec<u32>, pcode: &mut Vec<u32>,
    cur: &mut Vec<usize>, btab: &mut [u32; 256], ttab: &mut [u32; 256], stab: &mut [u32; 256], cv: &mut [u8; 8],
    hits: &mut [u8; 64], idx: &mut [u8; 64]) -> (m: usize)
    requires
        sel_pre(*e, ng as int, np as int, lo as int, hi as int, old(ptmp)@, old(cur)@, old(cur)@),
        old(pcode)@.len() == old(ptmp)@.len(),
        *q == *e.tabs,
    ensures
        final(ptmp)@.len() == old(ptmp)@.len(),
        final(cur)@.len() == np + 1,
        listed(*q, e.c.p, lo as int, hi as int, final(ptmp)@, m as int),
        codes_ok(*q, e.c.p, lo as int, final(ptmp)@, final(pcode)@, m as int, ng as int),
    no_unwind
{
    let ghost c = e.c;
    let ghost ngi = ng as int;
    let pbs = e.c.p.bs;
    proof {
        assert(hi - lo < 0xFFFF_FFFF);
    }
    let mut m: usize = 0;
    let mut j = lo;
    while j < hi
        invariant
            env_ok(*e, ngi), ngi == ng, c == e.c, *q == *e.tabs,
            ng <= 64 * np, np < 0x1_0000_0000,
            lo <= j <= hi <= c.p.n, hi - lo < 0xFFFF_FFFF,
            pbs == c.p.bs,
            ptmp@.len() > hi - lo,
            ptmp@.len() == old(ptmp)@.len(),
            cur@.len() == np + 1,
            forall|p: int| 0 <= p <= np ==> #[trigger] cur@[p] <= j - lo,
            m <= j - lo,
            listed(*q, c.p, lo as int, j as int, ptmp@, m as int),
            codes_ok(*q, c.p, lo as int, ptmp@, pcode@, m as int, ngi),
        decreases hi - j,
    {
        let g = j / pbs;
        proof {
            lemma_grp_bound(c.p.n as int, pbs as int, c.p.ng as int, j as int);
            lemma_block_start(j as int, pbs as int);
        }
        let gs = g * pbs;
        let seg_end = if hi - gs > pbs { gs + pbs } else { hi };
        proof {
            assert((g + 1) * pbs == g * pbs + pbs) by (nonlinear_arith);
        }
        let bb = e.c.p.brand_b[g];
        let tb = e.c.p.type_b[g];
        let sb = e.c.p.size_b[g];
        block_tabs(q, e.nb, e.nt, e.ns, bb, tb, sb, btab, ttab, stab, Ghost(ngi));
        let any = size_codes(q, e.ns, sb, stab, cv);
        if !any {
            // No listed size has a code in this block: no row of it is coded.
            proof {
                assert forall|r: int| j <= r < seg_end implies !#[trigger] coded(*q, c.p, r) by {
                    lemma_in_group(pbs as int, g as int, r);
                    let cc = c.p.size_c@[r];
                    assert(stab@[cc as int] == st_of(*q, sb + cc));
                    assert(sval(c.p, r) == sb + cc);
                }
                lemma_listed_gap(*q, c.p, lo as int, j as int, seg_end as int, ptmp@, m as int);
            }
            j = seg_end;
        } else {
            while seg_end - j >= 64
                invariant
                    p1_ok(*e, *q, ngi, np as int, lo as int, hi as int, j as int, g as int, ptmp@, pcode@, cur@, m as int,
                        *btab, *ttab, *stab),
                    ptmp@.len() == old(ptmp)@.len(),
                    c == e.c, pbs == c.p.bs, ngi == ng,
                    j <= seg_end <= hi, seg_end <= g * pbs + pbs,
                    cv_ok(*cv, *stab),
                decreases seg_end - j,
            {
                let (_, tail) = e.c.p.size_c.split_at(j);
                let (ch, _) = tail.split_at(64);
                proof {
                    assert(ch@ =~= c.p.size_c@.subrange(j as int, j + 64));
                }
                eq8_hits(ch, cv, hits);
                let n = compact64(hits, idx);
                let ghost gi = g as int;
                m = list_chunk(e, q, ng, np, lo, hi, j, ptmp, pcode, cur, m, &*btab, &*ttab, &*stab, &*cv, &*hits, &*idx, n, Ghost(gi));
                j = j + 64;
            }
            while j < seg_end
                invariant
                    p1_ok(*e, *q, ngi, np as int, lo as int, hi as int, j as int, g as int, ptmp@, pcode@, cur@, m as int,
                        *btab, *ttab, *stab),
                    ptmp@.len() == old(ptmp)@.len(),
                    c == e.c, pbs == c.p.bs, ngi == ng,
                    j <= seg_end <= hi, seg_end <= g * pbs + pbs,
                decreases seg_end - j,
            {
                let ghost gi = g as int;
                m = list_row(e, q, ng, np, lo, hi, j, ptmp, pcode, cur, m, &*btab, &*ttab, &*stab, Ghost(gi));
                j = j + 1;
            }
        }
    }
    m
}

/// Listing coded row `j` at slot `m`.
proof fn lemma_listed_push(q: QualTabs, p: PCols, lo: int, j: int, pt0: Seq<u32>, pt: Seq<u32>, m: int)
    requires
        listed(q, p, lo, j, pt0, m),
        lo <= j,
        coded(q, p, j),
        0 <= m < pt0.len(),
        pt == pt0.update(m, (j - lo) as u32),
        j - lo < 0x1_0000_0000,
    ensures listed(q, p, lo, j + 1, pt, m + 1),
{
    assert forall|r: int| 0 <= r < m + 1 implies lo <= #[trigger] lrow(lo, pt, r) < j + 1 && coded(q, p, lrow(lo, pt, r)) by {
        if r < m {
            assert(pt[r] == pt0[r]);
            assert(lrow(lo, pt, r) == lrow(lo, pt0, r));
        }
    }
    assert forall|j2: int| lo <= j2 < j + 1 && #[trigger] coded(q, p, j2) implies exists|r: int| 0 <= r < m + 1 && #[trigger] lrow(lo, pt, r) == j2 by {
        if j2 < j {
            let r = choose|r: int| 0 <= r < m && #[trigger] lrow(lo, pt0, r) == j2;
            assert(pt[r] == pt0[r]);
            assert(lrow(lo, pt, r) == j2);
        } else {
            assert(lrow(lo, pt, m) == j2);
        }
    }
}

/// An uncoded row adds nothing.
proof fn lemma_listed_skip(q: QualTabs, p: PCols, lo: int, j: int, pt: Seq<u32>, m: int)
    requires listed(q, p, lo, j, pt, m), lo <= j, !coded(q, p, j),
    ensures listed(q, p, lo, j + 1, pt, m),
{
    assert forall|j2: int| lo <= j2 < j + 1 && #[trigger] coded(q, p, j2) implies exists|r: int| 0 <= r < m && #[trigger] lrow(lo, pt, r) == j2 by {
        assert(j2 != j);
    }
}

// ------------------------------------------------------------------------------------------------ regions

/// Region `p` gets `ratio` entries per counted row; `cur[p] = start[p]`. False when the regions exceed `olen`.
fn regions(ratio: usize, np: usize, start: &mut Vec<usize>, cur: &mut Vec<usize>, olen: usize) -> (ok: bool)
    requires old(start)@.len() == np + 1, old(cur)@.len() == np + 1,
    ensures
        final(start)@.len() == np + 1,
        final(cur)@.len() == np + 1,
        ok ==> {
            &&& forall|p1: int, p2: int| 0 <= p1 <= p2 <= np ==> #[trigger] final(start)@[p1] <= #[trigger] final(start)@[p2]
            &&& final(start)@[np as int] <= olen
            &&& forall|p: int| 0 <= p < np ==> #[trigger] final(cur)@[p] == final(start)@[p]
        },
    no_unwind
{
    let mut acc: usize = 0;
    let mut p: usize = 0;
    while p < np
        invariant
            start@.len() == np + 1, cur@.len() == np + 1,
            p <= np,
            acc <= olen,
            forall|p1: int, p2: int| 0 <= p1 <= p2 < p ==> #[trigger] start@[p1] <= #[trigger] start@[p2],
            forall|p1: int| 0 <= p1 < p ==> #[trigger] start@[p1] <= acc,
            forall|p1: int| 0 <= p1 < p ==> #[trigger] cur@[p1] == start@[p1],
        decreases np - p,
    {
        let cnt = cur[p];
        proof {
            let (ci, ri) = (cnt as int, ratio as int);
            assert(ci * ri <= 0xFFFF_FFFF_FFFF_FFFFint * 0xFFFF_FFFF_FFFF_FFFFint) by (nonlinear_arith)
                requires 0 <= ci <= 0xFFFF_FFFF_FFFF_FFFFint, 0 <= ri <= 0xFFFF_FFFF_FFFF_FFFFint;
        }
        let want: u128 = acc as u128 + (cnt as u128) * (ratio as u128);
        if want > olen as u128 {
            return false;
        }
        start[p] = acc;
        cur[p] = acc;
        acc = want as usize;
        p = p + 1;
    }
    start[np] = acc;
    proof {
        assert forall|p1: int, p2: int| 0 <= p1 <= p2 <= np implies #[trigger] start@[p1] <= #[trigger] start@[p2] by {
            if p2 < np {
            } else if p1 < np {
            }
        }
    }
    true
}

// ------------------------------------------------------------------------------------------------ pass 2

/// The pass-2 state after the listed rows below `r`: valid regions holding exactly those rows' pairs.
pub open spec fn p2_ok(q: QualTabs, c: Cols, lo: int, ptmp: Seq<u32>, r: int, np: int, out: Seq<u32>, start: Seq<usize>,
    cur: Seq<usize>) -> bool {
    &&& regs_ok(start, cur, out, np, c.s.n as int)
    &&& forall|g: int, x: int| 0 <= g < 64 * np ==> (#[trigger] rhas(out, start, cur, g, x) <==> done_pair(q, c, lo, ptmp, r, g, x))
}

/// Inside listed row `r` (part row `j`, code `code`) after its partsupp rows below `i` (of `[a, b)`).
pub open spec fn p2_inner(q: QualTabs, c: Cols, lo: int, ptmp: Seq<u32>, r: int, j: int, a: int, i: int, np: int,
    out: Seq<u32>, start: Seq<usize>, cur: Seq<usize>) -> bool {
    &&& regs_ok(start, cur, out, np, c.s.n as int)
    &&& forall|g: int, x: int| 0 <= g < 64 * np ==> (#[trigger] rhas(out, start, cur, g, x) <==>
        (done_pair(q, c, lo, ptmp, r, g, x) || exists|i2: int| a <= i2 < i && #[trigger] pair_at(q, c, j, i2, g, x)))
}

/// Pass 2: appends every pair of the listed rows to its partition's region. False when a region is full.
fn pass2(e: &PairEnv, q: &QualTabs, ng: usize, np: usize, lo: usize, hi: usize, ptmp: &Vec<u32>, pcode: &Vec<u32>,
    m: usize, out: &mut Vec<u32>, start: &Vec<usize>, cur: &mut Vec<usize>) -> (ok: bool)
    requires
        env_ok(*e, ng as int), *q == *e.tabs,
        ng <= 64 * np, np < 0x1_0000_0000,
        e.c.s.n <= 0x10_0000,
        lo <= hi <= e.c.p.n, e.c.p.n < 0xFFFF_FFFF,
        listed(*q, e.c.p, lo as int, hi as int, ptmp@, m as int),
        codes_ok(*q, e.c.p, lo as int, ptmp@, pcode@, m as int, ng as int),
        p2_ok(*q, e.c, lo as int, ptmp@, 0, np as int, old(out)@, start@, old(cur)@),
    ensures
        final(out)@.len() == old(out)@.len(),
        ok ==> regs_ok(start@, final(cur)@, final(out)@, np as int, e.c.s.n as int),
        ok ==> forall|g: int, x: int| 0 <= g < 64 * np ==>
            (#[trigger] rhas(final(out)@, start@, final(cur)@, g, x) <==> pair_in(*q, e.c, lo as int, hi as int, g, x)),
    no_unwind
{
    let ghost c = e.c;
    let ghost ngi = ng as int;
    let ghost npi = np as int;
    let ghost l = lo as int;
    let pbs = e.c.p.bs;
    let mut r: usize = 0;
    while r < m
        invariant
            env_ok(*e, ngi), ngi == ng, c == e.c, *q == *e.tabs, npi == np, l == lo,
            ng <= 64 * np, np < 0x1_0000_0000,
            c.s.n <= 0x10_0000,
            lo <= hi <= c.p.n, c.p.n < 0xFFFF_FFFF,
            pbs == c.p.bs,
            listed(*q, c.p, l, hi as int, ptmp@, m as int),
            codes_ok(*q, c.p, l, ptmp@, pcode@, m as int, ngi),
            r <= m,
            out@.len() == old(out)@.len(),
            p2_ok(*q, c, l, ptmp@, r as int, npi, out@, start@, cur@),
        decreases m - r,
    {
        proof {
            assert(l <= lrow(l, ptmp@, r as int) < hi);
        }
        let j = lo + ptmp[r] as usize;
        proof {
            assert(lrow(l, ptmp@, r as int) == j);
            assert(lo <= j < hi && coded(*q, c.p, j as int));
            lemma_grp_bound(c.p.n as int, pbs as int, c.p.ng as int, j as int);
        }
        let code: u32 = pcode[r];
        proof {
            assert(code as int == code_of(*q, c.p, j as int) && code < ngi);
            lemma_part_div(code as int, npi);
            assert(i64r(pkey(c.p, j as int)));
            if e.pdense {
                assert(pkey(c.p, j as int) == e.pfirst + j);
            }
        }
        let p = (code / 64) as usize;
        let lc: u32 = code % 64;
        // The part key: by position when the part keys are dense (no read of the key column).
        let k: i64 = if e.pdense { e.pfirst + j as i64 } else { e.c.p.key_b[j / pbs] + e.c.p.key_c[j] as i64 };
        let lim = start[p + 1];
        // The partsupp rows of key `k`: psrun's run guess first (inlined), else the general search.
        let guessed = e.c.ps.kind == 1 && e.ratio > 0 && j < e.jmax && run_guess(e, j, k, Ghost(ngi));
        let (a, b, exact) = if guessed {
            proof {
                lemma_guess_rows(*e, ngi, k as int, j * e.ratio, j * e.ratio + e.ratio);
            }
            (j * e.ratio, j * e.ratio + e.ratio, true)
        } else {
            ps_rows_of(e, j, k, Ghost(ngi))
        };
        let mut i = a;
        proof {
            assert(p2_inner(*q, c, l, ptmp@, r as int, j as int, a as int, a as int, npi, out@, start@, cur@)) by {
                assert forall|g2: int, x2: int| 0 <= g2 < 64 * np implies (#[trigger] rhas(out@, start@, cur@, g2, x2) <==>
                    (done_pair(*q, c, l, ptmp@, r as int, g2, x2) || exists|i2: int| a <= i2 < a && #[trigger] pair_at(*q, c, j as int, i2, g2, x2))) by {}
            }
        }
        if exact && e.sdense && a < b && ps_grp(e, a) == ps_grp(e, b - 1) {
            // Fast path: one partsupp block, dense supplier keys.
            if !emit_block(e, q, Ghost(ngi), Ghost(npi), lo, ptmp, Ghost(r as int), j, code, k, a, b, out, start, cur) {
                return false;
            }
            i = b;
        }
        while i < b
            invariant
                env_ok(*e, ngi), ngi == ng, c == e.c, *q == *e.tabs, npi == np, l == lo,
                ng <= 64 * np, np < 0x1_0000_0000,
                c.s.n <= 0x10_0000,
                lo <= j < hi <= c.p.n,
                coded(*q, c.p, j as int), code_of(*q, c.p, j as int) == code as int, (code as int) < ngi,
                p == code / 64, lc == code % 64, p < np,
                lim == start@[p + 1],
                k as int == pkey(c.p, j as int),
                rows_of(*e, k as int, a as int, b as int, exact),
                a <= i <= b,
                out@.len() == old(out)@.len(),
                lrow(l, ptmp@, r as int) == j, r < m,
                p2_inner(*q, c, l, ptmp@, r as int, j as int, a as int, i as int, npi, out@, start@, cur@),
            decreases b - i,
        {
            if exact || ps_key(e, i, Ghost(ngi)) == k {
                proof {
                    if exact { assert(pskey(c.ps, i as int) == k); }
                }
                let skv = ps_supp(e, i, Ghost(ngi));
                match supp_of(e, skv, Ghost(ngi)) {
                    Some(sx) => {
                        let w = cur[p];
                        if w >= lim {
                            return false;
                        }
                        let v: u32 = lc * 0x10_0000 + sx as u32;
                        let ghost o0 = out@;
                        let ghost c0 = cur@;
                        out[w] = v;
                        cur[p] = w + 1;
                        proof {
                            lemma_emit(*q, *e, c, ngi, l, ptmp@, r as int, j as int, a as int, i as int, npi, code as int,
                                sx as int, k as int, o0, c0, out@, start@, cur@);
                        }
                    },
                    None => {
                        proof {
                            lemma_inner_none(*q, c, l, ptmp@, r as int, j as int, a as int, i as int, npi, out@, start@, cur@);
                        }
                    },
                }
            } else {
                proof {
                    lemma_inner_none(*q, c, l, ptmp@, r as int, j as int, a as int, i as int, npi, out@, start@, cur@);
                }
            }
            i = i + 1;
        }
        proof {
            lemma_row_done(*q, *e, c, l, ptmp@, r as int, j as int, a as int, b as int, exact, k as int, npi, out@, start@, cur@);
        }
        r = r + 1;
    }
    proof {
        lemma_all_done(*q, c, l, hi as int, ptmp@, m as int, npi, out@, start@, cur@);
    }
    true
}

/// The pairs of listed row `r` (part row `j`, code `code`, key `k`) whose partsupp rows `[a, b)` are exactly the
/// rows of `k` and lie in one partsupp block, with dense supplier keys: the block's suppkey base is read once, each
/// row's supplier row is `base + code` checked against the supplier row count, and the region's fill position is
/// kept in a local (written back once). False when the region is full.
#[inline(always)]
fn emit_block(e: &PairEnv, q: &QualTabs, Ghost(ng): Ghost<int>, Ghost(np): Ghost<int>, lo: usize, ptmp: &Vec<u32>,
    Ghost(r): Ghost<int>, j: usize, code: u32, k: i64, a: usize, b: usize, out: &mut Vec<u32>, start: &Vec<usize>,
    cur: &mut Vec<usize>) -> (ok: bool)
    requires
        env_ok(*e, ng), *q == *e.tabs,
        e.c.s.n <= 0x10_0000,
        e.sdense,
        0 <= j < e.c.p.n,
        coded(*q, e.c.p, j as int), code_of(*q, e.c.p, j as int) == code as int, (code as int) < 64 * np,
        k as int == pkey(e.c.p, j as int),
        rows_of(*e, k as int, a as int, b as int, true),
        a < b, (a as int) / (e.c.ps.bs as int) == (b - 1) / (e.c.ps.bs as int),
        p2_inner(*q, e.c, lo as int, ptmp@, r, j as int, a as int, a as int, np, old(out)@, start@, old(cur)@),
    ensures
        final(out)@.len() == old(out)@.len(),
        ok ==> p2_inner(*q, e.c, lo as int, ptmp@, r, j as int, a as int, b as int, np, final(out)@, start@, final(cur)@),
    no_unwind
{
    let ghost c = e.c;
    let ghost cur0 = cur@;
    let ghost bs = c.ps.bs as int;
    proof {
        lemma_part_div(code as int, np);
        lemma_grp_bound(c.ps.n as int, bs, c.ps.ng as int, a as int);
    }
    let p = (code / 64) as usize;
    let lc: u32 = code % 64;
    let g = ps_grp(e, a);
    let base: i128 = e.c.ps.supp_b[g] as i128 - e.sfirst as i128;
    let sn: i128 = e.c.s.n as i128;
    let lim = start[p + 1];
    let mut w = cur[p];
    let mut i = a;
    proof {
        assert(cur0.update(p as int, w) =~= cur0);
    }
    while i < b
        invariant
            env_ok(*e, ng), *q == *e.tabs, c == e.c, bs == c.ps.bs as int,
            c.s.n <= 0x10_0000, e.sdense, sn == c.s.n as int,
            0 <= j < c.p.n,
            coded(*q, c.p, j as int), code_of(*q, c.p, j as int) == code as int, (code as int) < 64 * np,
            p == code / 64, lc == code % 64, p < np, lim == start@[p + 1],
            k as int == pkey(c.p, j as int),
            rows_of(*e, k as int, a as int, b as int, true),
            a <= i <= b, (a as int) / bs == (b - 1) / bs, g as int == (a as int) / bs,
            base == c.ps.supp_b@[g as int] - e.sfirst,
            cur@ == cur0,
            out@.len() == old(out)@.len(),
            p2_inner(*q, c, lo as int, ptmp@, r, j as int, a as int, i as int, np, out@, start@, cur0.update(p as int, w)),
        decreases b - i,
    {
        proof {
            // Row `i` lies in block `g`.
            vstd::arithmetic::div_mod::lemma_div_is_ordered(a as int, i as int, bs);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(i as int, b - 1, bs);
            assert(pssupp(c.ps, i as int) == base + e.sfirst + c.ps.supp_c@[i as int]);
        }
        let sx: i128 = base + e.c.ps.supp_c[i] as i128;
        let ghost cv = cur0.update(p as int, w);
        if 0 <= sx && sx < sn {
            if w >= lim {
                return false;
            }
            let v: u32 = lc * 0x10_0000 + sx as u32;
            let ghost o0 = out@;
            out[w] = v;
            proof {
                assert(skey(c.s, sx as int) == e.sfirst + sx);
                assert(cur0.update(p as int, (w + 1) as usize) =~= cv.update(p as int, (cv[p as int] + 1) as usize));
                lemma_emit(*q, *e, c, ng, lo as int, ptmp@, r, j as int, a as int, i as int, np, code as int,
                    sx as int, k as int, o0, cv, out@, start@, cur0.update(p as int, (w + 1) as usize));
            }
            w = w + 1;
        } else {
            proof {
                assert forall|s2: int| 0 <= s2 < c.s.n implies #[trigger] skey(c.s, s2) != pssupp(c.ps, i as int) by {
                    assert(skey(c.s, s2) == e.sfirst + s2);
                }
                lemma_inner_none(*q, c, lo as int, ptmp@, r, j as int, a as int, i as int, np, out@, start@, cv);
            }
        }
        i = i + 1;
    }
    cur[p] = w;
    proof {
        assert(cur@ =~= cur0.update(p as int, w));
    }
    true
}

/// Appending entry `enc(code % 64, sx)` at `cur[p]` (`p = code / 64`) for the pair of partsupp row `i`.
proof fn lemma_emit(q: QualTabs, e: PairEnv, c: Cols, ng: int, lo: int, ptmp: Seq<u32>, r: int, j: int, a: int, i: int,
    np: int, code: int, sx: int, k: int, o0: Seq<u32>, c0: Seq<usize>, out: Seq<u32>, start: Seq<usize>, cur: Seq<usize>)
    requires
        env_ok(e, ng), e.c == c,
        0 <= j < c.p.n,
        coded(q, c.p, j), code_of(q, c.p, j) == code, 0 <= code < 64 * np,
        k == pkey(c.p, j),
        0 <= a <= i < c.ps.n,
        pskey(c.ps, i) == k,
        0 <= sx < c.s.n, skey(c.s, sx) == pssupp(c.ps, i),
        c.s.n <= 0x10_0000,
        p2_inner(q, c, lo, ptmp, r, j, a, i, np, o0, start, c0),
        c0[code / 64] < start[code / 64 + 1],
        out == o0.update(c0[code / 64] as int, (enc(code % 64, sx)) as u32),
        cur == c0.update(code / 64, (c0[code / 64] + 1) as usize),
    ensures p2_inner(q, c, lo, ptmp, r, j, a, i + 1, np, out, start, cur),
{
    let p = code / 64;
    let w = c0[p] as int;
    lemma_part_div(code, np);
    lemma_enc(code % 64, sx);
    assert(pair_at(q, c, j, i, code, sx));
    assert(0 <= enc(code % 64, sx) < 0x1_0000_0000) by {
        assert(enc(code % 64, sx) <= 63 * 0x10_0000 + 0x10_0000);
    }
    assert(out[w] as int == enc(code % 64, sx));
    // The regions.
    assert(regs_ok(start, cur, out, np, c.s.n as int)) by {
        assert forall|p2: int| 0 <= p2 < np implies #[trigger] cur[p2] >= start[p2] && cur[p2] <= start[p2 + 1] by {
            if p2 != p { assert(cur[p2] == c0[p2]); }
        }
        assert forall|p2: int| 0 <= p2 < np implies #[trigger] ent_ok(out, start[p2] as int, cur[p2] as int, c.s.n as int) by {
            assert(ent_ok(o0, start[p2] as int, c0[p2] as int, c.s.n as int));
            assert forall|k2: int| start[p2] <= k2 < cur[p2] implies slot_of_ent(#[trigger] out[k2] as int) < 64
                && x_of_ent(out[k2] as int) < c.s.n by {
                if k2 != w {
                    lemma_regions_apart(start, c0, np, p, p2, k2);
                    assert(out[k2] == o0[k2]);
                }
            }
        }
    }
    // The pairs.
    assert forall|g2: int, x2: int| 0 <= g2 < 64 * np implies (#[trigger] rhas(out, start, cur, g2, x2) <==>
        (done_pair(q, c, lo, ptmp, r, g2, x2) || exists|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2))) by {
        let p2 = g2 / 64;
        lemma_part_div(g2, np);
        // The new entry belongs to (g2, x2) exactly when g2 == code and x2 == sx.
        if rhas(out, start, cur, g2, x2) {
            let k2 = choose|k2: int| start[p2] <= k2 < cur[p2] && #[trigger] out[k2] as int == enc(g2 % 64, x2);
            if k2 == w {
                // Same partition (regions are disjoint) and same entry.
                lemma_regions_apart(start, c0, np, p, p2, k2);
                lemma_enc(g2 % 64, x2);
                assert(g2 == code);
                assert(x2 == sx);
                assert(pair_at(q, c, j, i, g2, x2));
            } else {
                lemma_regions_apart(start, c0, np, p, p2, k2);
                assert(out[k2] == o0[k2]);
                assert(rhas(o0, start, c0, g2, x2));
                if !done_pair(q, c, lo, ptmp, r, g2, x2) {
                    let i2 = choose|i2: int| a <= i2 < i && #[trigger] pair_at(q, c, j, i2, g2, x2);
                    assert(a <= i2 < i + 1);
                }
            }
        }
        if done_pair(q, c, lo, ptmp, r, g2, x2) || exists|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2) {
            let old_has = done_pair(q, c, lo, ptmp, r, g2, x2) || exists|i2: int| a <= i2 < i && #[trigger] pair_at(q, c, j, i2, g2, x2);
            if old_has {
                assert(rhas(o0, start, c0, g2, x2));
                let k2 = choose|k2: int| start[p2] <= k2 < c0[p2] && #[trigger] o0[k2] as int == enc(g2 % 64, x2);
                lemma_regions_apart(start, c0, np, p, p2, k2);
                assert(out[k2] == o0[k2]);
                assert(start[p2] <= k2 < cur[p2]);
            } else {
                let i2 = choose|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2);
                assert(i2 == i);
                // Same part row, so the same code; the supplier row of a suppkey is unique.
                assert(g2 == code);
                assert(skey(c.s, x2) == skey(c.s, sx));
                assert(x2 == sx);
                assert(start[p2] <= w < cur[p2]);
                assert(out[w] as int == enc(g2 % 64, x2));
            }
        }
    }
}

/// An entry at `k2` inside region `p2` (or the slot `cur[p]` of region `p`) lies in exactly one region.
proof fn lemma_regions_apart(start: Seq<usize>, cur: Seq<usize>, np: int, p: int, p2: int, k2: int)
    requires
        start.len() == np + 1, cur.len() == np + 1,
        forall|p1: int, p3: int| 0 <= p1 <= p3 <= np ==> #[trigger] start[p1] <= #[trigger] start[p3],
        forall|p3: int| 0 <= p3 < np ==> #[trigger] cur[p3] >= start[p3] && cur[p3] <= start[p3 + 1],
        0 <= p < np, 0 <= p2 < np,
        cur[p] < start[p + 1],
        start[p2] <= k2 < cur[p2] + (if p2 == p { 1int } else { 0int }),
    ensures k2 == cur[p] ==> p2 == p,
{
    if k2 == cur[p] && p2 != p {
        if p2 < p {
            assert(start[p2 + 1] <= start[p]);
            assert(cur[p2] <= start[p2 + 1]);
            assert(cur[p] >= start[p]);
        } else {
            assert(start[p + 1] <= start[p2]);
        }
    }
}

/// Partsupp row `i` adds no pair (another key, or no supplier row of its suppkey).
proof fn lemma_inner_none(q: QualTabs, c: Cols, lo: int, ptmp: Seq<u32>, r: int, j: int, a: int, i: int, np: int,
    out: Seq<u32>, start: Seq<usize>, cur: Seq<usize>)
    requires
        p2_inner(q, c, lo, ptmp, r, j, a, i, np, out, start, cur),
        pskey(c.ps, i) != pkey(c.p, j) || forall|s: int| 0 <= s < c.s.n ==> #[trigger] skey(c.s, s) != pssupp(c.ps, i),
    ensures p2_inner(q, c, lo, ptmp, r, j, a, i + 1, np, out, start, cur),
{
    assert forall|g2: int, x2: int| 0 <= g2 < 64 * np implies (#[trigger] rhas(out, start, cur, g2, x2) <==>
        (done_pair(q, c, lo, ptmp, r, g2, x2) || exists|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2))) by {
        if exists|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2) {
            let i2 = choose|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2);
            if i2 == i {
                assert(skey(c.s, x2) == pssupp(c.ps, i));
            } else {
                assert(exists|i3: int| a <= i3 < i && #[trigger] pair_at(q, c, j, i3, g2, x2));
            }
        }
    }
}

/// After all partsupp rows of listed row `r`: the regions hold the pairs of the listed rows below `r + 1`.
proof fn lemma_row_done(q: QualTabs, e: PairEnv, c: Cols, lo: int, ptmp: Seq<u32>, r: int, j: int, a: int, b: int,
    exact: bool, k: int, np: int, out: Seq<u32>, start: Seq<usize>, cur: Seq<usize>)
    requires
        e.c == c,
        0 <= r < ptmp.len(),
        lrow(lo, ptmp, r) == j,
        k == pkey(c.p, j),
        rows_of(e, k, a, b, exact),
        p2_inner(q, c, lo, ptmp, r, j, a, b, np, out, start, cur),
    ensures p2_ok(q, c, lo, ptmp, r + 1, np, out, start, cur),
{
    assert forall|g: int, x: int| 0 <= g < 64 * np implies (#[trigger] rhas(out, start, cur, g, x) <==> done_pair(q, c, lo, ptmp, r + 1, g, x)) by {
        if done_pair(q, c, lo, ptmp, r + 1, g, x) {
            let (r2, i2) = choose|r2: int, i2: int| 0 <= r2 < r + 1 && #[trigger] pair_at(q, c, lrow(lo, ptmp, r2), i2, g, x);
            if r2 == r {
                assert(pskey(c.ps, i2) == k);
                assert(a <= i2 < b);
                assert(pair_at(q, c, j, i2, g, x));
            } else {
                assert(done_pair(q, c, lo, ptmp, r, g, x));
            }
        }
        if rhas(out, start, cur, g, x) {
            if done_pair(q, c, lo, ptmp, r, g, x) {
                let (r2, i2) = choose|r2: int, i2: int| 0 <= r2 < r && #[trigger] pair_at(q, c, lrow(lo, ptmp, r2), i2, g, x);
                assert(0 <= r2 < r + 1);
            } else {
                let i2 = choose|i2: int| a <= i2 < b && #[trigger] pair_at(q, c, j, i2, g, x);
                assert(pair_at(q, c, lrow(lo, ptmp, r), i2, g, x));
            }
        }
    }
}

/// The pairs of all listed rows are the pairs of the part rows `[lo, hi)`.
proof fn lemma_all_done(q: QualTabs, c: Cols, lo: int, hi: int, ptmp: Seq<u32>, m: int, np: int, out: Seq<u32>,
    start: Seq<usize>, cur: Seq<usize>)
    requires
        listed(q, c.p, lo, hi, ptmp, m),
        p2_ok(q, c, lo, ptmp, m, np, out, start, cur),
    ensures
        forall|g: int, x: int| 0 <= g < 64 * np ==> (#[trigger] rhas(out, start, cur, g, x) <==> pair_in(q, c, lo, hi, g, x)),
{
    assert forall|g: int, x: int| 0 <= g < 64 * np implies (#[trigger] rhas(out, start, cur, g, x) <==> pair_in(q, c, lo, hi, g, x)) by {
        if pair_in(q, c, lo, hi, g, x) {
            let (j2, i2) = choose|j2: int, i2: int| lo <= j2 < hi && #[trigger] pair_at(q, c, j2, i2, g, x);
            assert(coded(q, c.p, j2));
            let r2 = choose|r2: int| 0 <= r2 < m && #[trigger] lrow(lo, ptmp, r2) == j2;
            assert(pair_at(q, c, lrow(lo, ptmp, r2), i2, g, x));
            assert(done_pair(q, c, lo, ptmp, m, g, x));
        }
        if done_pair(q, c, lo, ptmp, m, g, x) {
            let (r2, i2) = choose|r2: int, i2: int| 0 <= r2 < m && #[trigger] pair_at(q, c, lrow(lo, ptmp, r2), i2, g, x);
            assert(lo <= lrow(lo, ptmp, r2) < hi);
        }
    }
}

} // verus!
