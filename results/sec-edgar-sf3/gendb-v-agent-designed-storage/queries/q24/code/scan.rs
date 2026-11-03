//! The scan of the num runs of one uom: per run (one filing), the rows whose ddate is in range and whose
//! (adsh, tag, version) has no pre row; emitted as (pair code, value) entries in stored order.
//!
//! Layout used (stated as `ScanInput::wf`): num rows are cut into runs by `run_start`, every run has one adsh code
//! (`run_adsh`) and per-run ddate bounds. `amap` maps every num adsh code to the pre adsh code of the same filing
//! (+ 1; 0: no pre rows); the pre rows of pre adsh code `a` are `[sub_start[adsh_subs[a]], sub_start[adsh_subs[a + 1]])`.
//! `npm` maps every num pair code to the pre pair code of the same (tag, version) + 1, or 0. When the storage has its
//! group index (`has_index`), the rows of run `r` are cut into groups `[run_groups[r], run_groups[r + 1])` of one
//! pair code each (`group_key`, rows `[group_start[g], group_start[g + 1])`).
//!
//! Runs are cut into tasks of about equal work (rows of the runs the ddate zone map lets through). Each task owns a
//! bit set over pre pair codes + 1 (`0..=ppairs`, clear between runs). Per run that the zone map lets through it
//! sets the bit `ptv[j] + 1` of every pre row `j` of the filing (no map lookup), then tests one bit per group: bit
//! `npm[key]` (bit 0 is never set, so a pair without pre image is never matched). Only the rows of a group whose bit
//! is clear are read (ddate test, value); then the bits are cleared again. Without the index every row is a group.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::put;
use crate::stores::num_tvg::interface::common::runs::{runs_partition_ok, run_bounds_ok};
use crate::stores::num_tvg::interface::common::text::lemma_dict_codes;
use super::common::dictmap::{Dict, map_ok, map_entry_ok};
use super::common::chunks::{chunks_shape, chunks_seq, chunk_get, chunk_at};
use super::common::bitset::{bit_on, clear_upto, new_bits, bit_set, bit_clear, bit_test};
pub use super::common::groupby::Entry;

verus! {

/// Read-only inputs of the scan.
pub struct ScanInput {
    pub run_start: &'static [u64],
    pub run_adsh: &'static [u64],
    pub run_dmin: &'static [i32],
    pub run_dmax: &'static [i32],
    pub tv: &'static [u64],
    pub ddate: &'static [i32],
    pub value: &'static [i128],
    pub nadsh: Dict,
    pub padsh: Dict,
    pub adsh_subs: &'static [u64],
    pub sub_start: &'static [u64],
    pub ptv: &'static [u64],
    /// Num adsh code -> pre adsh code + 1 (0: no pre adsh with that value).
    pub amap: Arc<Vec<u64>>,
    /// Num pair code -> pre pair code + 1 (0: none): one `u32` vector `npm32` when `use32` (fewer than `u32::MAX`
    /// pre pairs), else in chunks `npm` of `npm_size = 1 << npm_shift` codes.
    pub use32: bool,
    pub npm32: Arc<Vec<u32>>,
    pub npm: Arc<Vec<Vec<u64>>>,
    pub npm_shift: u64,
    pub npm_size: u64,
    /// The group index (meaningful when `has_index`).
    pub run_groups: &'static [u64],
    pub group_start: &'static [u32],
    pub group_key: &'static [u32],
    pub has_index: bool,
    pub ngroups: usize,
    /// Row count, run count, pre row count and pre sub-run count (slice lengths are not `no_unwind`).
    pub n: usize,
    pub runs: usize,
    pub pn: usize,
    pub subs: usize,
    /// Number of num pair codes, of pre pair codes, of num adsh codes.
    pub npairs: usize,
    pub ppairs: usize,
    pub nadsh_n: usize,
    pub dlo: i32,
    pub dhi: i32,
}

/// The pair map as one sequence: the `u32` vector widened, or the chunks.
pub open spec fn npm_view(use32: bool, v32: Seq<u32>, cs: Seq<Vec<u64>>, size: int, n: int) -> Seq<u64> {
    if use32 { Seq::new(n as nat, |p: int| v32[p] as u64) } else { chunks_seq(cs, size, n) }
}

/// The representation of the pair map has `n` entries.
pub open spec fn npm_shape_ok(use32: bool, v32: Seq<u32>, cs: Seq<Vec<u64>>, shift: u64, size: u64, n: int) -> bool {
    &&& use32 ==> v32.len() == n
    &&& !use32 ==> shift < 64 && size == 1u64 << shift && chunks_shape(cs, size as int, n)
}

impl ScanInput {
    /// The pair map as one sequence.
    pub open spec fn npmv(&self) -> Seq<u64> {
        npm_view(self.use32, self.npm32@, self.npm@, self.npm_size as int, self.npairs as int)
    }

    /// The shape of the pair map's representation.
    pub open spec fn npm_shape(&self) -> bool {
        npm_shape_ok(self.use32, self.npm32@, self.npm@, self.npm_shift, self.npm_size, self.npairs as int)
    }

    /// The group index facts (the second case of the storage's `index_ok`).
    pub open spec fn index_wf(&self) -> bool {
        let nr = self.runs as int;
        let ng = self.ngroups as int;
        let start = self.run_start@;
        let rg = self.run_groups@;
        let gs = self.group_start@;
        let gk = self.group_key@;
        &&& rg.len() == nr + 1
        &&& gs.len() == ng + 1
        &&& gk.len() == ng
        &&& forall|a: int, b: int| 0 <= a <= b <= nr ==> #[trigger] rg[a] <= #[trigger] rg[b]
        &&& rg[nr] == ng
        &&& forall|r: int| 0 <= r <= nr ==> #[trigger] gs[rg[r] as int] == start[r]
        &&& forall|a: int, b: int| 0 <= a <= b <= ng ==> #[trigger] gs[a] <= #[trigger] gs[b]
        &&& forall|g: int, i: int| 0 <= g < ng && gs[g] <= i < gs[g + 1] ==> #[trigger] self.tv@[i] == #[trigger] gk[g] as u64
        &&& forall|g: int| 0 <= g < ng ==> (#[trigger] gk[g]) < self.npairs
    }

    pub open spec fn wf(&self) -> bool {
        let start = self.run_start@;
        let tv = self.tv@;
        &&& runs_partition_ok(start, self.runs as int, self.n as int)
        &&& self.run_adsh@.len() == self.runs
        &&& forall|r: int| 0 <= r < self.runs ==> (#[trigger] self.run_adsh@[r]) < self.nadsh.count
        &&& run_bounds_ok(self.ddate@, start, self.run_dmin@, self.run_dmax@)
        &&& tv.len() == self.n && self.ddate@.len() == self.n && self.value@.len() == self.n
        &&& self.nadsh.wf() && self.padsh.wf()
        &&& self.nadsh_n == self.nadsh.count
        &&& map_ok(self.nadsh, self.padsh, self.amap@)
        &&& self.adsh_subs@.len() == self.padsh.count + 1
        &&& forall|a: int| 0 <= a < self.padsh.count ==>
            #[trigger] self.adsh_subs@[a] <= self.adsh_subs@[a + 1] <= self.subs
        &&& self.sub_start@.len() == self.subs + 1
        &&& forall|a: int, b: int| 0 <= a <= b <= self.subs ==> #[trigger] self.sub_start@[a] <= #[trigger] self.sub_start@[b]
        &&& self.sub_start@[self.subs as int] == self.pn
        &&& self.ptv@.len() == self.pn
        &&& self.npm_shape()
        &&& forall|j: int| 0 <= j < self.pn ==> (#[trigger] self.ptv@[j]) < self.ppairs
        &&& forall|p: int| 0 <= p < self.npairs ==> (#[trigger] self.npmv()[p]) <= self.ppairs
        &&& self.n < usize::MAX
        &&& self.npairs < usize::MAX
        &&& self.ppairs < usize::MAX
        &&& forall|i: int| 0 <= i < self.n ==> (#[trigger] tv[i]) < self.npairs
        &&& self.has_index ==> self.index_wf()
    }

    /// First and last pre row (exclusive) of pre adsh code `a`.
    pub open spec fn pre_lo(&self, a: int) -> int {
        self.sub_start@[self.adsh_subs@[a] as int] as int
    }

    pub open spec fn pre_hi(&self, a: int) -> int {
        self.sub_start@[self.adsh_subs@[a + 1] as int] as int
    }

    /// Num row `i` (of run `r`) has a pre row of its filing with its pair: the row's pair maps to that pre row's pair.
    pub open spec fn matched(&self, r: int, i: int) -> bool {
        exists|a: int, j: int| 0 <= a < self.padsh.count && #[trigger] self.padsh.at(a) == self.nadsh.at(self.run_adsh@[r] as int)
            && self.pre_lo(a) <= j < self.pre_hi(a) && #[trigger] self.ptv@[j] + 1 == self.npmv()[self.tv@[i] as int]
    }

    /// Num row `i` of run `r` qualifies.
    pub open spec fn qual(&self, r: int, i: int) -> bool {
        &&& self.dlo <= self.ddate@[i] <= self.dhi
        &&& !self.matched(r, i)
    }

    /// Entries of the qualifying rows `[s, e)` of run `r`, in order.
    pub open spec fn row_ents(&self, r: int, s: int, e: int) -> Seq<Entry>
        decreases e - s,
    {
        if e <= s {
            Seq::empty()
        } else if self.qual(r, e - 1) {
            self.row_ents(r, s, e - 1).push(Entry { key: self.tv@[e - 1], value: self.value@[e - 1] })
        } else {
            self.row_ents(r, s, e - 1)
        }
    }

    /// Entries of runs `[ra, rb)`, in order.
    pub open spec fn run_ents(&self, ra: int, rb: int) -> Seq<Entry>
        decreases rb - ra,
    {
        if rb <= ra {
            Seq::empty()
        } else {
            self.run_ents(ra, rb - 1) + self.row_ents(rb - 1, self.run_start@[rb - 1] as int, self.run_start@[rb] as int)
        }
    }
}

/// Entries of a run's rows: at most one per row, each with a valid pair code.
pub proof fn lemma_row_ents_facts(inp: ScanInput, r: int, s: int, e: int)
    requires inp.wf(), 0 <= s <= e <= inp.n,
    ensures
        inp.row_ents(r, s, e).len() <= e - s,
        forall|m: int| 0 <= m < inp.row_ents(r, s, e).len() ==> (#[trigger] inp.row_ents(r, s, e)[m]).key < inp.npairs,
    decreases e - s,
{
    if e > s {
        lemma_row_ents_facts(inp, r, s, e - 1);
    }
}

/// Entries of runs `[ra, rb)`: at most one per row, each with a valid pair code.
pub proof fn lemma_run_ents_facts(inp: ScanInput, ra: int, rb: int)
    requires inp.wf(), 0 <= ra <= rb <= inp.runs,
    ensures
        inp.run_ents(ra, rb).len() <= inp.run_start@[rb] - inp.run_start@[ra],
        forall|m: int| 0 <= m < inp.run_ents(ra, rb).len() ==> (#[trigger] inp.run_ents(ra, rb)[m]).key < inp.npairs,
    decreases rb - ra,
{
    if rb > ra {
        lemma_run_ents_facts(inp, ra, rb - 1);
        lemma_run_range(inp, rb - 1);
        assert(inp.run_start@[ra] <= inp.run_start@[rb - 1]);
        lemma_row_ents_facts(inp, rb - 1, inp.run_start@[rb - 1] as int, inp.run_start@[rb] as int);
        let a = inp.run_ents(ra, rb - 1);
        let b = inp.row_ents(rb - 1, inp.run_start@[rb - 1] as int, inp.run_start@[rb] as int);
        assert forall|m: int| 0 <= m < (a + b).len() implies (#[trigger] (a + b)[m]).key < inp.npairs by {
            if m < a.len() {
                assert((a + b)[m] == a[m]);
            } else {
                assert((a + b)[m] == b[m - a.len()]);
            }
        }
    } else {
        assert(inp.run_start@[ra] <= inp.run_start@[inp.runs as int]);
    }
}

/// Entries of consecutive run ranges concatenate.
pub proof fn lemma_run_ents_split(inp: ScanInput, ra: int, rb: int, rc: int)
    requires ra <= rb <= rc,
    ensures inp.run_ents(ra, rc) == inp.run_ents(ra, rb) + inp.run_ents(rb, rc),
    decreases rc - rb,
{
    if rc == rb {
        assert(inp.run_ents(ra, rb) + Seq::<Entry>::empty() =~= inp.run_ents(ra, rb));
    } else {
        lemma_run_ents_split(inp, ra, rb, rc - 1);
        let x = inp.row_ents(rc - 1, inp.run_start@[rc - 1] as int, inp.run_start@[rc] as int);
        assert(inp.run_ents(ra, rb) + inp.run_ents(rb, rc - 1) + x =~= inp.run_ents(ra, rb) + (inp.run_ents(rb, rc - 1) + x));
    }
}

/// A run's row range lies inside the rows, and its length.
proof fn lemma_run_range(inp: ScanInput, r: int)
    requires inp.wf(), 0 <= r < inp.runs,
    ensures inp.run_start@[r] < inp.run_start@[r + 1] <= inp.n,
{
    assert(inp.run_start@[r + 1] <= inp.run_start@[inp.runs as int]);
}

/// Rows `[m, e)` of run `r` none of which qualifies add no entry after `[s, m)`.
proof fn lemma_no_qual(inp: ScanInput, r: int, s: int, m: int, e: int)
    requires s <= m <= e, forall|i: int| m <= i < e ==> !#[trigger] inp.qual(r, i),
    ensures inp.row_ents(r, s, e) == inp.row_ents(r, s, m),
    decreases e - m,
{
    if e > m {
        lemma_no_qual(inp, r, s, m, e - 1);
    }
}

/// No row of a run qualifies when none passes the ddate test.
proof fn lemma_no_ents(inp: ScanInput, r: int, s: int, e: int)
    requires forall|i: int| s <= i < e ==> !(inp.dlo <= #[trigger] inp.ddate@[i] <= inp.dhi),
    ensures inp.row_ents(r, s, e) == Seq::<Entry>::empty(),
    decreases e - s,
{
    if e > s {
        lemma_no_ents(inp, r, s, e - 1);
    }
}

/// Bit `x` is the image `ptv[j] + 1` of some pre row `j` of `[j0, j1)`.
pub open spec fn phit(inp: ScanInput, j0: int, j1: int, x: int) -> bool {
    exists|j: int| j0 <= j < j1 && #[trigger] inp.ptv@[j] + 1 == x
}

/// The bits of run `r` (bits of the pre rows `[j0, j1)`): every row's match is its pair's bit.
pub open spec fn bits_match(inp: ScanInput, r: int, bits: Seq<u64>) -> bool {
    forall|k: int| inp.run_start@[r] <= k < inp.run_start@[r + 1]
        ==> (#[trigger] inp.matched(r, k)) == bit_on(bits, inp.npmv()[inp.tv@[k] as int] as int)
}

/// One scan task: runs `[ra, rb)`.
pub struct ScanTask {
    pub inp: Arc<ScanInput>,
    pub ra: usize,
    pub rb: usize,
    /// Bit set over pre pair codes + 1 (`0..=ppairs`), clear between runs.
    pub bits: Vec<u64>,
    pub buf: Vec<Entry>,
}

pub struct ScanOut {
    pub buf: Vec<Entry>,
    pub len: usize,
    pub overflow: bool,
}

impl ScanTask {
    pub open spec fn shape_ok(&self) -> bool {
        let inp = *self.inp;
        &&& inp.wf()
        &&& self.ra <= self.rb <= inp.runs
        &&& self.bits@.len() == inp.ppairs / 64 + 1
        &&& clear_upto(self.bits@, inp.ppairs as int)
    }
}

impl WorkerTask for ScanTask {
    type Output = ScanOut;

    open spec fn pre(&self) -> bool {
        self.shape_ok()
    }

    open spec fn post(&self, out: ScanOut) -> bool {
        &&& out.len <= out.buf@.len()
        &&& !out.overflow ==> out.buf@.subrange(0, out.len as int) == (*self.inp).run_ents(self.ra as int, self.rb as int)
        &&& out.overflow ==> self.buf@.len() < self.inp.run_start@[self.rb as int] - self.inp.run_start@[self.ra as int]
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.ra as u64, self.rb as u64)
    }

    fn run(self) -> (out: ScanOut) {
        let inp_arc = self.inp;
        let inp: &ScanInput = &*inp_arc;
        let ra = self.ra;
        let rb = self.rb;
        let mut bits = self.bits;
        let mut buf = self.buf;
        let cap = buf.len();
        let mut len: usize = 0;
        let mut r = ra;
        while r < rb
            invariant
                (*inp).wf(), ra <= r <= rb <= inp.runs,
                bits@.len() == inp.ppairs / 64 + 1, clear_upto(bits@, inp.ppairs as int),
                cap == buf@.len(), len <= cap, cap == self.buf@.len(),
                buf@.subrange(0, len as int) == (*inp).run_ents(ra as int, r as int),
                len <= inp.run_start@[r as int] - inp.run_start@[ra as int],
                inp.run_start@[ra as int] <= inp.run_start@[r as int],
                *inp == *self.inp, ra == self.ra, rb == self.rb,
            decreases rb - r,
        {
            proof {
                lemma_run_range(*inp, r as int);
            }
            let s = inp.run_start[r] as usize;
            let e = inp.run_start[r + 1] as usize;
            if inp.run_dmax[r] >= inp.dlo && inp.run_dmin[r] <= inp.dhi {
                match scan_run(inp, r, s, e, &mut bits, &mut buf, len) {
                    Some(l2) => {
                        proof {
                            lemma_row_ents_facts(*inp, r as int, s as int, e as int);
                            assert(l2 - len == inp.row_ents(r as int, s as int, e as int).len()) by {
                                assert(buf@.subrange(0, l2 as int).len() == l2);
                            }
                        }
                        len = l2;
                    },
                    None => {
                        return ScanOut { buf, len, overflow: true };
                    },
                }
            } else {
                proof {
                    assert forall|i: int| s <= i < e implies !(inp.dlo <= #[trigger] inp.ddate@[i] <= inp.dhi) by {
                        assert(inp.run_dmin@[r as int] <= inp.ddate@[i] <= inp.run_dmax@[r as int]);
                    }
                    lemma_no_ents(*inp, r as int, s as int, e as int);
                }
            }
            proof {
                assert((*inp).run_ents(ra as int, r + 1) == (*inp).run_ents(ra as int, r as int)
                    + (*inp).row_ents(r as int, s as int, e as int));
                assert(inp.run_start@[ra as int] <= inp.run_start@[r + 1]);
            }
            r = r + 1;
        }
        ScanOut { buf, len, overflow: false }
    }
}

/// The entries of run `r` (rows `[s, e)`) appended to `buf[..len]`; `None` when `buf` has no room.
/// Set the bits of the filing's pre rows (`mark_pre`), emit the qualifying rows by group (`emit_groups`) or by row
/// (`emit_rows`), then clear the bits (`clear_pre`).
fn scan_run(inp: &ScanInput, r: usize, s: usize, e: usize, bits: &mut Vec<u64>, buf: &mut Vec<Entry>, len: usize)
    -> (res: Option<usize>)
    requires
        inp.wf(), r < inp.runs, s == inp.run_start@[r as int], e == inp.run_start@[r + 1],
        old(bits)@.len() == inp.ppairs / 64 + 1, clear_upto(old(bits)@, inp.ppairs as int),
        len <= old(buf)@.len(),
    ensures
        final(bits)@.len() == old(bits)@.len(), clear_upto(final(bits)@, inp.ppairs as int),
        final(buf)@.len() == old(buf)@.len(),
        res matches Some(l2) ==> l2 <= final(buf)@.len()
            && final(buf)@.subrange(0, l2 as int) == old(buf)@.subrange(0, len as int) + inp.row_ents(r as int, s as int, e as int),
        res is None ==> old(buf)@.len() < len + (e - s),
    no_unwind
{
    let (j0, j1) = pre_rows(inp, r);
    mark_pre(inp, j0, j1, bits);
    proof {
        lemma_bits_match(*inp, r as int, j0 as int, j1 as int, bits@);
    }
    let res = if inp.has_index {
        emit_groups(inp, r, s, e, bits, buf, len)
    } else {
        emit_rows(inp, r, s, s, e, bits, buf, len)
    };
    clear_pre(inp, j0, j1, bits);
    res
}

/// The pre rows `[j0, j1)` of run `r`'s filing (empty when pre has no such adsh).
fn pre_rows(inp: &ScanInput, r: usize) -> (js: (usize, usize))
    requires inp.wf(), r < inp.runs,
    ensures
        js.0 <= js.1 <= inp.pn,
        ({
            let c = inp.run_adsh@[r as int] as int;
            let a1 = inp.amap@[c];
            &&& a1 == 0 ==> js.0 == js.1
            &&& a1 != 0 ==> js.0 == inp.pre_lo(a1 - 1) && js.1 == inp.pre_hi(a1 - 1)
        }),
    no_unwind
{
    let c = inp.run_adsh[r] as usize;
    proof {
        assert(c < inp.nadsh.count);
        assert(map_entry_ok(inp.nadsh, inp.padsh, c as int, inp.amap@[c as int]));
    }
    let a1 = inp.amap[c];
    if a1 == 0 {
        (0, 0)
    } else {
        let a = (a1 - 1) as usize;
        proof {
            assert(inp.adsh_subs@[a as int] <= inp.adsh_subs@[a + 1] <= inp.subs);
            assert(inp.sub_start@[inp.adsh_subs@[a as int] as int] <= inp.sub_start@[inp.adsh_subs@[a + 1] as int]);
            assert(inp.sub_start@[inp.adsh_subs@[a + 1] as int] <= inp.sub_start@[inp.subs as int]);
        }
        let j0 = inp.sub_start[inp.adsh_subs[a] as usize] as usize;
        let j1 = inp.sub_start[inp.adsh_subs[a + 1] as usize] as usize;
        (j0, j1)
    }
}

/// The bits of the pre rows of run `r`'s filing give every row's match.
proof fn lemma_bits_match(inp: ScanInput, r: int, j0: int, j1: int, bits: Seq<u64>)
    requires
        inp.wf(), 0 <= r < inp.runs,
        ({
            let a1 = inp.amap@[inp.run_adsh@[r] as int];
            &&& a1 == 0 ==> j0 == j1
            &&& a1 != 0 ==> j0 == inp.pre_lo(a1 - 1) && j1 == inp.pre_hi(a1 - 1)
        }),
        bits.len() == inp.ppairs / 64 + 1,
        forall|x: int| 0 <= x <= inp.ppairs ==> #[trigger] bit_on(bits, x) == phit(inp, j0, j1, x),
    ensures bits_match(inp, r, bits),
{
    let c = inp.run_adsh@[r] as int;
    let a1 = inp.amap@[c];
    assert(c < inp.nadsh.count);
    assert(map_entry_ok(inp.nadsh, inp.padsh, c, a1));
    lemma_run_range(inp, r);
    assert forall|k: int| inp.run_start@[r] <= k < inp.run_start@[r + 1]
        implies (#[trigger] inp.matched(r, k)) == bit_on(bits, inp.npmv()[inp.tv@[k] as int] as int) by {
        let p = inp.tv@[k] as int;
        assert(p < inp.npairs);
        let x = inp.npmv()[p] as int;
        assert(x <= inp.ppairs);
        if inp.matched(r, k) {
            let (a2, j2) = choose|a2: int, j2: int| 0 <= a2 < inp.padsh.count
                && #[trigger] inp.padsh.at(a2) == inp.nadsh.at(inp.run_adsh@[r] as int)
                && inp.pre_lo(a2) <= j2 < inp.pre_hi(a2) && #[trigger] inp.ptv@[j2] + 1 == inp.npmv()[inp.tv@[k] as int];
            assert(a1 != 0);
            lemma_dict_codes(inp.padsh.off@, inp.padsh.bytes@, inp.padsh.count as int, a2, a1 - 1);
            assert(a2 == a1 - 1);
            assert(phit(inp, j0, j1, x));
        }
        if bit_on(bits, x) {
            assert(phit(inp, j0, j1, x));
            let j2 = choose|j2: int| j0 <= j2 < j1 && #[trigger] inp.ptv@[j2] + 1 == x;
            assert(a1 != 0);
            assert(inp.padsh.at(a1 - 1) == inp.nadsh.at(c));
            assert(inp.matched(r, k));
        }
    }
}

/// Set bit `ptv[j] + 1` of every pre row `j` of `[j0, j1)` in the clear bit set.
fn mark_pre(inp: &ScanInput, j0: usize, j1: usize, bits: &mut Vec<u64>)
    requires
        inp.wf(), j0 <= j1 <= inp.pn,
        old(bits)@.len() == inp.ppairs / 64 + 1, clear_upto(old(bits)@, inp.ppairs as int),
    ensures
        final(bits)@.len() == old(bits)@.len(),
        forall|x: int| 0 <= x <= inp.ppairs ==> #[trigger] bit_on(final(bits)@, x) == phit(*inp, j0 as int, j1 as int, x),
    no_unwind
{
    let mut j = j0;
    while j < j1
        invariant
            inp.wf(), j0 <= j <= j1, j1 <= inp.pn,
            bits@.len() == inp.ppairs / 64 + 1,
            forall|x: int| 0 <= x <= inp.ppairs ==> #[trigger] bit_on(bits@, x) == phit(*inp, j0 as int, j as int, x),
        decreases j1 - j,
    {
        let x0 = (inp.ptv[j] + 1) as usize;
        proof {
            assert(inp.ptv@[j as int] < inp.ppairs);
            assert(x0 / 64 <= inp.ppairs / 64) by (nonlinear_arith) requires x0 <= inp.ppairs;
        }
        let ghost b0 = bits@;
        bit_set(bits, x0);
        proof {
            assert forall|x: int| 0 <= x <= inp.ppairs implies #[trigger] bit_on(bits@, x) == phit(*inp, j0 as int, j + 1, x) by {
                assert(x / 64 <= inp.ppairs / 64) by (nonlinear_arith) requires 0 <= x <= inp.ppairs;
                if x == x0 {
                    assert(inp.ptv@[j as int] + 1 == x);
                } else {
                    assert(bit_on(bits@, x) == bit_on(b0, x));
                    if phit(*inp, j0 as int, j + 1, x) {
                        let j2 = choose|j2: int| j0 <= j2 < j + 1 && #[trigger] inp.ptv@[j2] + 1 == x;
                        assert(j2 < j);
                    }
                }
            }
        }
        j = j + 1;
    }
}

/// Clear the bits set by `mark_pre` for pre rows `[j0, j1)`: every bit in `0..=ppairs` is clear again.
fn clear_pre(inp: &ScanInput, j0: usize, j1: usize, bits: &mut Vec<u64>)
    requires
        inp.wf(), j0 <= j1 <= inp.pn,
        old(bits)@.len() == inp.ppairs / 64 + 1,
        forall|x: int| 0 <= x <= inp.ppairs ==> #[trigger] bit_on(old(bits)@, x) == phit(*inp, j0 as int, j1 as int, x),
    ensures
        final(bits)@.len() == old(bits)@.len(), clear_upto(final(bits)@, inp.ppairs as int),
    no_unwind
{
    let mut j = j0;
    while j < j1
        invariant
            inp.wf(), j0 <= j <= j1, j1 <= inp.pn,
            bits@.len() == inp.ppairs / 64 + 1,
            forall|x: int| 0 <= x <= inp.ppairs ==> #[trigger] bit_on(bits@, x)
                == (phit(*inp, j0 as int, j1 as int, x) && !phit(*inp, j0 as int, j as int, x)),
        decreases j1 - j,
    {
        let x0 = (inp.ptv[j] + 1) as usize;
        proof {
            assert(inp.ptv@[j as int] < inp.ppairs);
            assert(x0 / 64 <= inp.ppairs / 64) by (nonlinear_arith) requires x0 <= inp.ppairs;
        }
        let ghost b0 = bits@;
        bit_clear(bits, x0);
        proof {
            assert forall|x: int| 0 <= x <= inp.ppairs implies #[trigger] bit_on(bits@, x)
                == (phit(*inp, j0 as int, j1 as int, x) && !phit(*inp, j0 as int, j + 1, x)) by {
                assert(x / 64 <= inp.ppairs / 64) by (nonlinear_arith) requires 0 <= x <= inp.ppairs;
                if x == x0 {
                    assert(inp.ptv@[j as int] + 1 == x);
                } else {
                    assert(bit_on(bits@, x) == bit_on(b0, x));
                    if phit(*inp, j0 as int, j + 1, x) {
                        let j2 = choose|j2: int| j0 <= j2 < j + 1 && #[trigger] inp.ptv@[j2] + 1 == x;
                        assert(j2 < j);
                    }
                }
            }
        }
        j = j + 1;
    }
    proof {
        assert forall|x: int| 0 <= x <= inp.ppairs implies !#[trigger] bit_on(bits@, x) by {
            if phit(*inp, j0 as int, j1 as int, x) {
                assert(phit(*inp, j0 as int, j as int, x));
            }
        }
    }
}

/// Entry `p` of the pair map.
fn npm_at(inp: &ScanInput, p: usize) -> (x: u64)
    requires inp.wf(), p < inp.npairs,
    ensures x == inp.npmv()[p as int],
    no_unwind
{
    if inp.use32 {
        inp.npm32[p] as u64
    } else {
        chunk_get(&*inp.npm, inp.npm_shift, inp.npm_size, inp.npairs, p)
    }
}

/// The bit of num pair `p`'s image (`npm[p]`, at most `ppairs`).
fn pair_bit(inp: &ScanInput, bits: &Vec<u64>, p: u64) -> (b: bool)
    requires inp.wf(), p < inp.npairs, bits@.len() == inp.ppairs / 64 + 1,
    ensures b == bit_on(bits@, inp.npmv()[p as int] as int),
    no_unwind
{
    let x = npm_at(inp, p as usize);
    proof {
        assert(x == inp.npmv()[p as int]);
        assert(x <= inp.ppairs);
        assert(x / 64 <= inp.ppairs / 64) by (nonlinear_arith) requires x <= inp.ppairs;
    }
    bit_test(bits, x as usize)
}

/// Append the entries of rows `[i0, e)` of run `r` to `buf[..len]` (rows `[s, i0)` already appended): a row is
/// emitted when its ddate is in range and its pair's bit is clear.
fn emit_rows(inp: &ScanInput, r: usize, s: usize, i0: usize, e: usize, bits: &Vec<u64>, buf: &mut Vec<Entry>,
    len: usize) -> (res: Option<usize>)
    requires
        inp.wf(), r < inp.runs, s == inp.run_start@[r as int], e == inp.run_start@[r + 1], s <= i0 <= e,
        bits@.len() == inp.ppairs / 64 + 1, bits_match(*inp, r as int, bits@),
        inp.row_ents(r as int, s as int, i0 as int) == Seq::<Entry>::empty(),
        len <= old(buf)@.len(),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        res matches Some(l2) ==> l2 <= final(buf)@.len()
            && final(buf)@.subrange(0, l2 as int) == old(buf)@.subrange(0, len as int) + inp.row_ents(r as int, s as int, e as int),
        res is None ==> old(buf)@.len() < len + (e - s),
    no_unwind
{
    proof {
        lemma_run_range(*inp, r as int);
        assert(buf@.subrange(0, len as int) + Seq::<Entry>::empty() =~= buf@.subrange(0, len as int));
    }
    let mut l2 = len;
    let mut i = i0;
    let cap = buf.len();
    while i < e
        invariant
            inp.wf(), r < inp.runs, s == inp.run_start@[r as int], e == inp.run_start@[r + 1], e <= inp.n,
            s <= i0 <= i <= e, bits@.len() == inp.ppairs / 64 + 1, bits_match(*inp, r as int, bits@),
            cap == buf@.len(), len <= l2 <= cap, buf@.len() == old(buf)@.len(),
            buf@.subrange(0, l2 as int) == old(buf)@.subrange(0, len as int) + inp.row_ents(r as int, s as int, i as int),
            l2 - len <= i - i0,
        decreases e - i,
    {
        let d = inp.ddate[i];
        let t = inp.tv[i];
        proof {
            assert(t < inp.npairs);
            assert(inp.matched(r as int, i as int) == bit_on(bits@, inp.npmv()[t as int] as int));
        }
        if d >= inp.dlo && d <= inp.dhi && !pair_bit(inp, bits, t) {
            if l2 >= cap {
                return None;
            }
            let ghost b0 = buf@;
            put(buf, l2, Entry { key: t, value: inp.value[i] });
            proof {
                assert(buf@.subrange(0, l2 + 1) =~= b0.subrange(0, l2 as int).push(Entry { key: inp.tv@[i as int], value: inp.value@[i as int] }));
                let pre0 = old(buf)@.subrange(0, len as int);
                let mid = inp.row_ents(r as int, s as int, i as int);
                let x = Entry { key: inp.tv@[i as int], value: inp.value@[i as int] };
                assert((pre0 + mid).push(x) =~= pre0 + mid.push(x));
            }
            l2 = l2 + 1;
        }
        proof {
            assert(inp.row_ents(r as int, s as int, i + 1) == if inp.qual(r as int, i as int) {
                inp.row_ents(r as int, s as int, i as int).push(Entry { key: inp.tv@[i as int], value: inp.value@[i as int] })
            } else {
                inp.row_ents(r as int, s as int, i as int)
            });
        }
        i = i + 1;
    }
    Some(l2)
}

/// The group range of run `r` covers its rows: `group_start[run_groups[r]] == s`, `group_start[run_groups[r + 1]] == e`.
proof fn lemma_run_groups(inp: ScanInput, r: int)
    requires inp.wf(), inp.has_index, 0 <= r < inp.runs,
    ensures ({
        let rg = inp.run_groups@;
        let gs = inp.group_start@;
        &&& rg[r] <= rg[r + 1] <= inp.ngroups
        &&& gs[rg[r] as int] == inp.run_start@[r]
        &&& gs[rg[r + 1] as int] == inp.run_start@[r + 1]
    }),
{
    let rg = inp.run_groups@;
    assert(rg[r] <= rg[r + 1]);
    assert(rg[r + 1] <= rg[inp.runs as int]);
}

/// The first group of `[g, g1)` whose pair's bit is clear, or `g1` when every one's bit is set (the tight loop of
/// the scan: one key, one map entry and one bit per group).
fn first_unmatched(inp: &ScanInput, bits: &Vec<u64>, g: usize, g1: usize) -> (h: usize)
    requires inp.wf(), inp.has_index, g <= g1 <= inp.ngroups, bits@.len() == inp.ppairs / 64 + 1,
    ensures
        g <= h <= g1,
        forall|k: int| g <= k < h ==> bit_on(bits@, inp.npmv()[#[trigger] inp.group_key@[k] as int] as int),
        h < g1 ==> !bit_on(bits@, inp.npmv()[inp.group_key@[h as int] as int] as int),
    no_unwind
{
    if inp.use32 {
        first_unmatched32(inp, bits, g, g1)
    } else {
        first_unmatched_chunks(inp, bits, g, g1)
    }
}

/// `first_unmatched` over the `u32` pair map.
fn first_unmatched32(inp: &ScanInput, bits: &Vec<u64>, g: usize, g1: usize) -> (h: usize)
    requires inp.wf(), inp.has_index, inp.use32, g <= g1 <= inp.ngroups, bits@.len() == inp.ppairs / 64 + 1,
    ensures
        g <= h <= g1,
        forall|k: int| g <= k < h ==> bit_on(bits@, inp.npmv()[#[trigger] inp.group_key@[k] as int] as int),
        h < g1 ==> !bit_on(bits@, inp.npmv()[inp.group_key@[h as int] as int] as int),
    no_unwind
{
    let gk = inp.group_key;
    let m: &Vec<u32> = &*inp.npm32;
    let mut h = g;
    while h < g1
        invariant
            inp.wf(), inp.has_index, inp.use32, g <= h <= g1 <= inp.ngroups, bits@.len() == inp.ppairs / 64 + 1,
            gk@ == inp.group_key@, m@ == inp.npm32@,
            forall|k: int| g <= k < h ==> bit_on(bits@, inp.npmv()[#[trigger] inp.group_key@[k] as int] as int),
        decreases g1 - h,
    {
        let p = gk[h] as usize;
        proof {
            assert(inp.group_key@[h as int] < inp.npairs);
        }
        let x = m[p] as u64;
        proof {
            assert(x == inp.npmv()[p as int]);
            assert(x <= inp.ppairs);
            assert(x / 64 <= inp.ppairs / 64) by (nonlinear_arith) requires x <= inp.ppairs;
        }
        if !bit_test(bits, x as usize) {
            return h;
        }
        h = h + 1;
    }
    h
}

/// `first_unmatched` over the chunked pair map.
fn first_unmatched_chunks(inp: &ScanInput, bits: &Vec<u64>, g: usize, g1: usize) -> (h: usize)
    requires inp.wf(), inp.has_index, !inp.use32, g <= g1 <= inp.ngroups, bits@.len() == inp.ppairs / 64 + 1,
    ensures
        g <= h <= g1,
        forall|k: int| g <= k < h ==> bit_on(bits@, inp.npmv()[#[trigger] inp.group_key@[k] as int] as int),
        h < g1 ==> !bit_on(bits@, inp.npmv()[inp.group_key@[h as int] as int] as int),
    no_unwind
{
    let gk = inp.group_key;
    let cs: &Vec<Vec<u64>> = &*inp.npm;
    let shift = inp.npm_shift;
    let size = inp.npm_size;
    let n = inp.npairs;
    let mut h = g;
    while h < g1
        invariant
            inp.wf(), inp.has_index, !inp.use32, g <= h <= g1 <= inp.ngroups, bits@.len() == inp.ppairs / 64 + 1,
            gk@ == inp.group_key@, *cs == *inp.npm, shift == inp.npm_shift, size == inp.npm_size, n == inp.npairs,
            forall|k: int| g <= k < h ==> bit_on(bits@, inp.npmv()[#[trigger] inp.group_key@[k] as int] as int),
        decreases g1 - h,
    {
        let p = gk[h] as usize;
        proof {
            assert(inp.group_key@[h as int] < inp.npairs);
        }
        let x = chunk_get(cs, shift, size, n, p);
        proof {
            assert(x == inp.npmv()[p as int]);
            assert(x <= inp.ppairs);
            assert(x / 64 <= inp.ppairs / 64) by (nonlinear_arith) requires x <= inp.ppairs;
        }
        if !bit_test(bits, x as usize) {
            return h;
        }
        h = h + 1;
    }
    h
}

/// Groups `[g, h)` of run `r` whose pairs' bits are set add no entry: their rows are all matched.
proof fn lemma_groups_skip(inp: ScanInput, r: int, s: int, g: int, h: int, bits: Seq<u64>)
    requires
        inp.wf(), inp.has_index, 0 <= r < inp.runs, s == inp.run_start@[r],
        inp.run_groups@[r] <= g <= h <= inp.run_groups@[r + 1],
        bits_match(inp, r, bits),
        forall|k: int| g <= k < h ==> bit_on(bits, inp.npmv()[#[trigger] inp.group_key@[k] as int] as int),
    ensures inp.row_ents(r, s, inp.group_start@[h] as int) == inp.row_ents(r, s, inp.group_start@[g] as int),
    decreases h - g,
{
    if h > g {
        lemma_groups_skip(inp, r, s, g, h - 1, bits);
        lemma_run_range(inp, r);
        lemma_run_groups(inp, r);
        let gs = inp.group_start@;
        let k = h - 1;
        let g0 = inp.run_groups@[r] as int;
        let g1 = inp.run_groups@[r + 1] as int;
        assert(gs[g0] <= gs[k] && gs[k] <= gs[h] && gs[h] <= gs[g1]);
        assert(bit_on(bits, inp.npmv()[inp.group_key@[k] as int] as int));
        assert forall|i: int| gs[k] <= i < gs[h] implies !#[trigger] inp.qual(r, i) by {
            assert(inp.tv@[i] == inp.group_key@[k] as u64);
            assert(inp.matched(r, i) == bit_on(bits, inp.npmv()[inp.tv@[i] as int] as int));
        }
        lemma_no_qual(inp, r, s, gs[k] as int, gs[h] as int);
    }
}

/// Append the entries of run `r` (rows `[s, e)`) to `buf[..len]` group by group: the groups whose pair's bit is set
/// are matched and skipped unread (`first_unmatched`); the rows of the other groups are emitted when their ddate is
/// in range.
fn emit_groups(inp: &ScanInput, r: usize, s: usize, e: usize, bits: &Vec<u64>, buf: &mut Vec<Entry>, len: usize)
    -> (res: Option<usize>)
    requires
        inp.wf(), inp.has_index, r < inp.runs, s == inp.run_start@[r as int], e == inp.run_start@[r + 1],
        bits@.len() == inp.ppairs / 64 + 1, bits_match(*inp, r as int, bits@),
        len <= old(buf)@.len(),
    ensures
        final(buf)@.len() == old(buf)@.len(),
        res matches Some(l2) ==> l2 <= final(buf)@.len()
            && final(buf)@.subrange(0, l2 as int) == old(buf)@.subrange(0, len as int) + inp.row_ents(r as int, s as int, e as int),
        res is None ==> old(buf)@.len() < len + (e - s),
    no_unwind
{
    proof {
        lemma_run_range(*inp, r as int);
        lemma_run_groups(*inp, r as int);
        assert(buf@.subrange(0, len as int) + Seq::<Entry>::empty() =~= buf@.subrange(0, len as int));
    }
    let g0 = inp.run_groups[r] as usize;
    let g1 = inp.run_groups[r + 1] as usize;
    let mut l2 = len;
    let mut g = g0;
    let cap = buf.len();
    while g < g1
        invariant
            inp.wf(), inp.has_index, r < inp.runs, s == inp.run_start@[r as int], e == inp.run_start@[r + 1], e <= inp.n,
            g0 == inp.run_groups@[r as int], g1 == inp.run_groups@[r + 1], g0 <= g <= g1 <= inp.ngroups,
            inp.group_start@[g0 as int] == s, inp.group_start@[g1 as int] == e,
            bits@.len() == inp.ppairs / 64 + 1, bits_match(*inp, r as int, bits@),
            cap == buf@.len(), len <= l2 <= cap, buf@.len() == old(buf)@.len(),
            buf@.subrange(0, l2 as int) == old(buf)@.subrange(0, len as int)
                + inp.row_ents(r as int, s as int, inp.group_start@[g as int] as int),
            l2 - len <= inp.group_start@[g as int] - s,
        decreases g1 - g,
    {
        let h = first_unmatched(inp, bits, g, g1);
        proof {
            lemma_groups_skip(*inp, r as int, s as int, g as int, h as int, bits@);
            assert(inp.group_start@[g as int] <= inp.group_start@[h as int]);
        }
        if h == g1 {
            g = g1;
        } else {
            let lo = inp.group_start[h] as usize;
            let hi = inp.group_start[h + 1] as usize;
            let key = inp.group_key[h] as u64;
            proof {
                assert(inp.group_start@[g0 as int] <= inp.group_start@[h as int]);
                assert(inp.group_start@[h as int] <= inp.group_start@[h + 1]);
                assert(inp.group_start@[h + 1] <= inp.group_start@[g1 as int]);
                assert(key < inp.npairs);
            }
            let mut i = lo;
            while i < hi
                invariant
                    inp.wf(), inp.has_index, r < inp.runs, s == inp.run_start@[r as int], e == inp.run_start@[r + 1],
                    s <= lo <= i <= hi <= e, e <= inp.n,
                    forall|k: int| lo <= k < hi ==> #[trigger] inp.tv@[k] == key,
                    !bit_on(bits@, inp.npmv()[key as int] as int), key < inp.npairs,
                    bits_match(*inp, r as int, bits@),
                    cap == buf@.len(), len <= l2 <= cap, buf@.len() == old(buf)@.len(),
                    buf@.subrange(0, l2 as int) == old(buf)@.subrange(0, len as int) + inp.row_ents(r as int, s as int, i as int),
                    l2 - len <= i - s,
                decreases hi - i,
            {
                let d = inp.ddate[i];
                proof {
                    assert(inp.tv@[i as int] == key);
                    assert(!inp.matched(r as int, i as int));
                }
                if d >= inp.dlo && d <= inp.dhi {
                    if l2 >= cap {
                        return None;
                    }
                    let ghost b0 = buf@;
                    put(buf, l2, Entry { key, value: inp.value[i] });
                    proof {
                        assert(buf@.subrange(0, l2 + 1) =~= b0.subrange(0, l2 as int).push(Entry { key: inp.tv@[i as int], value: inp.value@[i as int] }));
                        let pre0 = old(buf)@.subrange(0, len as int);
                        let mid = inp.row_ents(r as int, s as int, i as int);
                        let x = Entry { key: inp.tv@[i as int], value: inp.value@[i as int] };
                        assert((pre0 + mid).push(x) =~= pre0 + mid.push(x));
                    }
                    l2 = l2 + 1;
                }
                proof {
                    assert(inp.row_ents(r as int, s as int, i + 1) == if inp.qual(r as int, i as int) {
                        inp.row_ents(r as int, s as int, i as int).push(Entry { key: inp.tv@[i as int], value: inp.value@[i as int] })
                    } else {
                        inp.row_ents(r as int, s as int, i as int)
                    });
                }
                i = i + 1;
            }
            g = h + 1;
        }
    }
    Some(l2)
}

/// Work estimate of run `r`: its row count when the ddate zone map lets it through, else 0; plus 1 for the visit.
fn run_weight(inp: &ScanInput, r: usize) -> (w: u64)
    requires inp.wf(), r < inp.runs,
    ensures 1 <= w,
{
    proof {
        lemma_run_range(*inp, r as int);
    }
    if inp.run_dmax[r] >= inp.dlo && inp.run_dmin[r] <= inp.dhi {
        inp.run_start[r + 1] - inp.run_start[r] + 1
    } else {
        1
    }
}

/// `a + b`, saturated at `u64::MAX`.
fn add_sat(a: u64, b: u64) -> (r: u64) {
    if a <= u64::MAX - b { a + b } else { u64::MAX }
}

/// Cut runs `[r0, r1)` into `k` consecutive ranges of about equal estimated work (`run_weight`): runs the zone map
/// skips cost almost nothing, so cutting by rows would leave tasks unbalanced. `b[0] = r0`, `b[k] = r1`.
fn run_cuts(inp: &ScanInput, r0: usize, r1: usize, k: usize) -> (b: Vec<usize>)
    requires inp.wf(), r0 <= r1 <= inp.runs, 1 <= k,
    ensures
        b@.len() == k + 1, b@[0] == r0, b@[k as int] == r1,
        forall|t: int| 0 <= t < k ==> #[trigger] step_le(b@, t),
{
    let mut total: u64 = 0;
    let mut r = r0;
    if k > 1 {
        while r < r1
            invariant inp.wf(), r0 <= r <= r1 <= inp.runs,
            decreases r1 - r,
        {
            total = add_sat(total, run_weight(inp, r));
            r = r + 1;
        }
    }
    let mut b: Vec<usize> = Vec::new();
    b.push(r0);
    let mut r = r0;
    let mut acc: u64 = 0;
    let mut t: usize = 1;
    while t < k
        invariant
            inp.wf(), r0 <= r <= r1 <= inp.runs, 1 <= t <= k,
            b@.len() == t, b@[0] == r0, b@[t - 1] == r,
            forall|u: int| 0 <= u < t - 1 ==> #[trigger] step_le(b@, u),
        decreases k - t,
    {
        let goal = super::common::dictmap::cut_exec(total as usize, k, t) as u64;
        let ghost rstart = r;
        while r < r1 && acc < goal
            invariant inp.wf(), r0 <= r <= r1 <= inp.runs, rstart <= r,
            decreases r1 - r,
        {
            acc = add_sat(acc, run_weight(inp, r));
            r = r + 1;
        }
        let ghost b0 = b@;
        b.push(r);
        proof {
            assert forall|u: int| 0 <= u < t implies #[trigger] step_le(b@, u) by {
                if u < t - 1 {
                    assert(step_le(b0, u));
                }
            }
        }
        t = t + 1;
    }
    let ghost b0 = b@;
    b.push(r1);
    proof {
        assert forall|u: int| 0 <= u < k implies #[trigger] step_le(b@, u) by {
            if u < k - 1 {
                assert(step_le(b0, u));
            }
        }
    }
    b
}

/// The entries of one task's runs `[ra, rb)` from its output (re-running it with room for every row when its buffer
/// overflowed).
fn task_entries(inp: Arc<ScanInput>, o: ScanOut, ra: usize, rb: usize) -> (part: Vec<Entry>)
    requires
        (*inp).wf(), ra <= rb <= inp.runs,
        o.len <= o.buf@.len(),
        !o.overflow ==> o.buf@.subrange(0, o.len as int) == (*inp).run_ents(ra as int, rb as int),
    ensures part@ == (*inp).run_ents(ra as int, rb as int),
{
    hide(ScanInput::wf);
    hide(ScanInput::run_ents);
    let ir: &ScanInput = &*inp;
    let mut part: Vec<Entry>;
    if o.overflow {
        proof {
            lemma_start_mono(*ir, ra as int, rb as int);
        }
        let rows = (inp.run_start[rb] - inp.run_start[ra]) as usize;
        let task = ScanTask {
            inp: inp.clone(), ra, rb, bits: new_bits(inp.ppairs), buf: vec![Entry { key: 0, value: 0 }; rows],
        };
        let o2 = task.run();
        assert(!o2.overflow);
        part = o2.buf;
        part.truncate(o2.len);
    } else {
        part = o.buf;
        part.truncate(o.len);
    }
    part
}

/// The entries of runs `[r0, r1)` with at most `workers` threads (on the calling thread when `workers == 1`).
pub fn scan_runs(inp: Arc<ScanInput>, r0: usize, r1: usize, workers: usize, dispatch: &mut Dispatch)
    -> (res: Result<Vec<Entry>, QueryError>)
    requires (*inp).wf(), r0 <= r1 <= inp.runs, 1 <= workers <= MAX_WORKERS,
    ensures
        res matches Ok(es) ==> es@ == (*inp).run_ents(r0 as int, r1 as int),
        res matches Err(e) ==> e is WorkerFailed,
{
    hide(ScanInput::wf);
    hide(ScanInput::run_ents);
    let ir: &ScanInput = &*inp;
    proof {
        lemma_start_mono(*ir, r0 as int, r1 as int);
    }
    let total = (inp.run_start[r1] - inp.run_start[r0]) as usize;
    let mut k = total / 65536;
    if k > workers {
        k = workers;
    }
    if k == 0 {
        k = 1;
    }
    let b = run_cuts(ir, r0, r1, k);
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            (*inp).wf(), *ir == *inp, r0 <= r1 <= inp.runs, 1 <= k <= workers <= MAX_WORKERS, t <= k,
            b@.len() == k + 1, b@[0] == r0, b@[k as int] == r1,
            forall|u: int| 0 <= u < k ==> #[trigger] step_le(b@, u),
            tasks@.len() == t,
            forall|u: int| 0 <= u < t ==> *(#[trigger] tasks@[u]).inp == *inp && tasks@[u].bits@.len() == inp.ppairs / 64 + 1
                && clear_upto(tasks@[u].bits@, inp.ppairs as int)
                && tasks@[u].ra == b@[u] && tasks@[u].rb == b@[u + 1],
        decreases k - t,
    {
        let ra = b[t];
        let rb = b[t + 1];
        proof {
            lemma_cuts_inside(b@, k as int, t as int);
            lemma_start_mono(*ir, ra as int, rb as int);
        }
        let rows = (inp.run_start[rb] - inp.run_start[ra]) as usize;
        let cap = if rows < 1024 { rows } else { 1024 };
        let task = ScanTask {
            inp: inp.clone(), ra, rb, bits: new_bits(inp.ppairs), buf: vec![Entry { key: 0, value: 0 }; cap],
        };
        tasks.push(task);
        t = t + 1;
    }
    proof {
        lemma_tasks_pre(tasks@, *ir, b@, k as int, r0 as int, r1 as int);
    }
    let ghost tv = tasks@;
    let outs = match super::common::tasks::run_tasks(dispatch, tasks, workers == 1) {
        Ok(outs) => outs,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let ghost ov = outs@;
    proof {
        assert forall|u: int| 0 <= u < k implies
            (#[trigger] ov[u]).len <= ov[u].buf@.len()
            && (!ov[u].overflow ==> ov[u].buf@.subrange(0, ov[u].len as int) == (*inp).run_ents(b@[u] as int, b@[u + 1] as int)) by {
            assert(tv[u].post(ov[u]));
        }
    }
    let es = collect_entries(inp, outs, &b, k, r0, r1);
    Ok(es)
}

/// Concatenation of the tasks' entries in task order.
fn collect_entries(inp: Arc<ScanInput>, outs: Vec<ScanOut>, b: &Vec<usize>, k: usize, r0: usize, r1: usize)
    -> (es: Vec<Entry>)
    requires
        (*inp).wf(), r0 <= r1 <= inp.runs,
        b@.len() == k + 1, b@[0] == r0, b@[k as int] == r1,
        forall|u: int| 0 <= u < k ==> #[trigger] step_le(b@, u),
        outs@.len() == k,
        forall|u: int| 0 <= u < k ==> (#[trigger] outs@[u]).len <= outs@[u].buf@.len()
            && (!outs@[u].overflow ==> outs@[u].buf@.subrange(0, outs@[u].len as int) == (*inp).run_ents(b@[u] as int, b@[u + 1] as int)),
    ensures es@ == (*inp).run_ents(r0 as int, r1 as int),
{
    hide(ScanInput::wf);
    hide(ScanInput::run_ents);
    let ir: &ScanInput = &*inp;
    let ghost ov = outs@;
    let mut outs = outs;
    let mut es: Vec<Entry> = Vec::new();
    let mut t: usize = 0;
    proof {
        reveal(ScanInput::run_ents);
        assert(es@ =~= (*inp).run_ents(r0 as int, r0 as int));
    }
    while t < k
        invariant
            (*inp).wf(), *ir == *inp, r0 <= r1 <= inp.runs, t <= k,
            b@.len() == k + 1, b@[0] == r0, b@[k as int] == r1,
            forall|u: int| 0 <= u < k ==> #[trigger] step_le(b@, u),
            ov.len() == k,
            forall|u: int| 0 <= u < k ==> (#[trigger] ov[u]).len <= ov[u].buf@.len()
                && (!ov[u].overflow ==> ov[u].buf@.subrange(0, ov[u].len as int) == (*inp).run_ents(b@[u] as int, b@[u + 1] as int)),
            outs@ == ov.subrange(t as int, k as int),
            es@ == (*inp).run_ents(r0 as int, b@[t as int] as int),
        decreases k - t,
    {
        let o = outs.remove(0);
        proof {
            assert(o == ov[t as int]);
            lemma_cuts_inside(b@, k as int, t as int);
        }
        let ra = b[t];
        let rb = b[t + 1];
        let mut part = task_entries(inp.clone(), o, ra, rb);
        es.append(&mut part);
        proof {
            lemma_run_ents_split(*ir, r0 as int, ra as int, rb as int);
            assert(outs@ =~= ov.subrange(t + 1, k as int));
        }
        t = t + 1;
    }
    es
}

/// One step of a cut: `b[u] <= b[u + 1]` (a function term, so the steps do not trigger each other).
pub open spec fn step_le(b: Seq<usize>, u: int) -> bool {
    b[u] <= b[u + 1]
}

/// Every scan task of the cut has its precondition.
proof fn lemma_tasks_pre(tasks: Seq<ScanTask>, inp: ScanInput, b: Seq<usize>, k: int, r0: int, r1: int)
    requires
        inp.wf(), r0 <= r1 <= inp.runs, tasks.len() == k, b.len() == k + 1, b[0] == r0, b[k] == r1,
        forall|u: int| 0 <= u < k ==> #[trigger] step_le(b, u),
        forall|u: int| 0 <= u < k ==> *(#[trigger] tasks[u]).inp == inp && tasks[u].bits@.len() == inp.ppairs / 64 + 1
            && clear_upto(tasks[u].bits@, inp.ppairs as int) && tasks[u].ra == b[u] && tasks[u].rb == b[u + 1],
    ensures forall|u: int| 0 <= u < k ==> (#[trigger] tasks[u]).pre(),
{
    assert forall|u: int| 0 <= u < k implies (#[trigger] tasks[u]).pre() by {
        lemma_cuts_inside(b, k, u);
    }
}

/// Run starts are nondecreasing.
proof fn lemma_start_mono(inp: ScanInput, a: int, b: int)
    requires inp.wf(), 0 <= a <= b <= inp.runs,
    ensures inp.run_start@[a] <= inp.run_start@[b] <= inp.n, inp.run_start@.len() == inp.runs + 1,
{
    assert(inp.run_start@[b] <= inp.run_start@[inp.runs as int]);
}

/// One cut range lies inside `[r0, r1]`.
proof fn lemma_cuts_inside(b: Seq<usize>, k: int, t: int)
    requires b.len() == k + 1, 0 <= t < k, forall|u: int| 0 <= u < k ==> #[trigger] step_le(b, u),
    ensures b[0] <= b[t] <= b[t + 1] <= b[k],
    decreases k - t,
{
    assert(step_le(b, t));
    if t + 1 < k {
        lemma_cuts_inside(b, k, t + 1);
    }
    lemma_cuts_lo(b, k, t);
}

proof fn lemma_cuts_lo(b: Seq<usize>, k: int, t: int)
    requires b.len() == k + 1, 0 <= t <= k, forall|u: int| 0 <= u < k ==> #[trigger] step_le(b, u),
    ensures b[0] <= b[t],
    decreases t,
{
    if t > 0 {
        assert(step_le(b, t - 1));
        lemma_cuts_lo(b, k, t - 1);
    }
}

} // verus!
