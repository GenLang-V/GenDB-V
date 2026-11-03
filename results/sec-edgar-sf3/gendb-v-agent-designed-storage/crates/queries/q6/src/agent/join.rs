//! Phase D: join, partial aggregates, groups and the best groups of one task's filings (one range of name codes,
//! sorted by name code).
//!
//! For each filing and each of its sub-runs with stmt `$2`, every row `q` gets the num pair `d` of its pre pair code
//! (`pair_of_code`: the task's own answers, from its need list and map with one worker or its sorted code list with
//! several, else resolved directly); the `num` rows of the filing's run with pair code `d` are one contiguous range
//! (runs are sorted by pair code), found by galloping forward (answers increase along a sub-run). Each row with matches gives one partial aggregate (`Partial`: count, sum,
//! absolute mass, with their exact values as ghosts) of the group key `(name code, pre tag code, plabel key)`
//! (`kd`). The partials of one filing sum, per key, to the filing's contribution (`fspec::fsum`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::work::put;
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::sort::{sort_range, KeyOrder, SortOrder, key_le};
use crate::agent::common::radix::{radix_sort_low, RADIX_BUCKETS};
use crate::stores::num::interface as ni;
use crate::stores::pre::interface as pi;
use crate::stores::sub::interface as si;
use crate::stores::pre::interface::common::text as ptext;
use crate::stores::sub::interface::common::text as stext;
use crate::stores::pre::interface::common::cols::{u64s as pu64s, list_entry};
use crate::stores::num::interface::common::cols::i128_part;
use crate::agent::meaning::{p_stmt, ps_ok};
use crate::agent::views::*;
use crate::agent::reorg::wt;
use crate::agent::fspec::*;
use crate::agent::filings::{Filing, bucket_of, stmt_key_ok};
use crate::agent::pairs::{answer_needed, PairDicts, NONE, NEEDED, ANSWERED, pd_ok, pair_ans, answers_ok, local_ok};
use crate::agent::common::sums::*;
use crate::agent::common::search::{gallop_u64, sorted_on, is_lb, find_key};

verus! {

/// Count of a group whose count exceeds int8 (`CNT_OVER`), and mass of a group whose absolute mass exceeds i128
/// (`MASS_OVER`; its sum is then meaningless).
pub const CNT_OVER: u64 = 0xffff_ffff_ffff_ffff;
pub const MASS_OVER: i128 = -1;
pub const INT8_MAX: u64 = 0x7fff_ffff_ffff_ffff;
pub const TOP: usize = 200;

/// A partial aggregate (one `pre` row of one filing) or, after merging, a group: key `(nm, tag, pk)` (name code,
/// pre tag code, plabel key: 0 for NULL, else code + 1), row count, sum and absolute mass of the values
/// (numeric(28,4) coefficients), and the exact count, sum and mass as ghosts.
#[derive(Clone, Copy)]
pub struct Partial {
    pub nm: u64,
    pub tag: u64,
    pub pk: u64,
    pub cnt: u64,
    pub sum: i128,
    pub mass: i128,
    pub gc: Ghost<int>,
    pub gs: Ghost<int>,
    pub gm: Ghost<int>,
}

pub fn empty_partial() -> (p: Partial) {
    Partial { nm: 0, tag: 0, pk: 0, cnt: 0, sum: 0, mass: 0, gc: Ghost(0), gs: Ghost(0), gm: Ghost(0) }
}

/// The exact value `w` of a partial or group: count (0), sum (1), mass (2).
pub open spec fn pval(x: Partial, w: int) -> int {
    if w == 0 { x.gc@ } else if w == 1 { x.gs@ } else { x.gm@ }
}

/// The executable fields agree with the exact values (or flag that they are out of range).
pub open spec fn exact_ok(x: Partial) -> bool {
    &&& x.gc@ > 0
    &&& 0 <= x.gm@ && abs(x.gs@) <= x.gm@
    &&& x.cnt != CNT_OVER ==> x.cnt as int == x.gc@ && x.gc@ <= INT8_MAX
    &&& x.cnt == CNT_OVER ==> x.gc@ > INT8_MAX
    &&& x.mass != MASS_OVER ==> x.mass as int == x.gm@ && x.sum as int == x.gs@
    &&& x.mass == MASS_OVER ==> x.gm@ > i128::MAX
}

/// The group key of a partial, decoded from its codes.
pub open spec fn kd(sv: StoresView, ps: Seq<Literal>, x: Partial) -> Row {
    seq![
        Val::Text(stext::text_entry(stext::u64_part(sv.sub[si::P_NAME_DICT_OFF as int]),
            stext::u8_part(sv.sub[si::P_NAME_DICT_BYTES as int]), x.nm as int)),
        Val::Text(p_stmt(ps)),
        Val::Text(list_entry(sv.pre, pi::P_TAG_OFF, x.tag as int)),
        if x.pk == 0 { Val::Null } else { Val::Text(list_entry(sv.pre, pi::P_PLABEL_OFF, x.pk - 1)) },
    ]
}

/// The term of `x` in the sum of key `k`'s value `w`.
pub open spec fn pterm(sv: StoresView, ps: Seq<Literal>, x: Partial, k: Row, w: int) -> int {
    if kd(sv, ps, x) == k { pval(x, w) } else { 0 }
}

/// The sum over `a[lo..hi)` of key `k`'s value `w`.
pub open spec fn psum(sv: StoresView, ps: Seq<Literal>, a: Seq<Partial>, lo: int, hi: int, k: Row, w: int) -> int {
    isum(lo, hi, |t: int| pterm(sv, ps, a[t], k, w))
}

/// The task's slices are the storages' parts; its filings are sorted by name and are filings.
pub struct JoinTask {
    pub filings: Vec<Filing>,
    pub nf: usize,
    pub dicts: PairDicts,
    pub cuts: Vec<u64>,
    pub nbuckets: usize,
    pub cbufs: Vec<Vec<u64>>,
    pub dbufs: Vec<Vec<u64>>,
    pub lens: Vec<usize>,
    pub cursors: Vec<usize>,
    pub sub_start: &'static [u64],
    pub sub_group: &'static [u64],
    pub nsubs: usize,
    pub group_stmt: &'static [u64],
    pub stmt_key: u64,
    pub pre_tv: &'static [u64],
    pub npre: usize,
    pub plabel_codes: &'static [u64],
    pub plabel_valid: &'static [u8],
    pub nplabel: usize,
    pub num_tv: &'static [u64],
    pub num_val: &'static [i128],
    pub nrows: usize,
    pub parts: Vec<Partial>,
    pub tmp: Vec<Partial>,
    pub cap: usize,
    pub top: Vec<Partial>,
    /// Local pair answers (one-worker path; both empty otherwise): `need[c]` is `NEEDED` for a pre pair code of a
    /// selected row, then `ANSWERED` with the code's num pair in `lmap[c]`.
    pub need: Vec<u8>,
    pub lmap: Vec<u64>,
    /// Own pair answers (several-worker path; empty otherwise): the pre pair codes of the task's selected rows,
    /// radix-sorted, in `codes[0..ncodes)`, and `cans[i]` the num pair of `codes[i]` (`own_ok`); `pair_of_code`
    /// finds a code by binary search.
    pub codes: Vec<u64>,
    pub cans: Vec<u64>,
    pub ncodes: usize,
    /// Scratch of the radix sort of `codes` (`RADIX_BUCKETS` entries on the several-worker path).
    pub counts: Vec<usize>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

pub open spec fn jinputs_ok(t: JoinTask) -> bool {
    let sv = t.sv@;
    let ps = t.ps@;
    let pp = sv.pre;
    &&& layouts(sv) && ps_ok(ps)
    &&& pd_ok(t.dicts, sv)
    &&& t.nbuckets >= 1 && t.cuts@.len() == t.nbuckets + 1
    &&& answers_ok(sv, t.dicts.npp as int, t.cbufs@, t.dbufs@, t.lens@)
    &&& t.lens@.len() == t.nbuckets && t.cursors@.len() == t.nbuckets
    &&& t.sub_start@ == p_start(sv)
    &&& t.sub_group@ == pu64s(pp, pi::P_SUB_GROUP)
    &&& t.nsubs == pi::sub_count(pp)
    &&& t.group_stmt@ == pu64s(pp, pi::P_GROUP_STMT)
    &&& stmt_key_ok(sv, ps, t.stmt_key)
    &&& t.pre_tv@ == pu64s(pp, pi::P_TV)
    &&& t.npre == p_count(sv)
    &&& t.plabel_codes@ == pu64s(pp, pi::P_PLABEL_CODES)
    &&& t.plabel_valid@ == ptext::u8_part(pp[pi::P_PLABEL_VALID as int])
    &&& t.nplabel as int == crate::stores::pre::interface::common::cols::text_count(pp, pi::P_PLABEL_OFF as int)
    &&& t.num_tv@ == ni::u64s(sv.num, ni::P_TV)
    &&& t.num_val@ == i128_part(sv.num[ni::P_VALUE as int])
    &&& t.nrows == n_count(sv)
    &&& t.nf <= t.filings@.len()
    &&& forall|x: int| 0 <= x < t.nf ==> filing_ok(sv, ps, #[trigger] t.filings@[x])
    &&& forall|x: int, y: int| 0 <= x < y < t.nf ==> (#[trigger] t.filings@[x]).nm <= (#[trigger] t.filings@[y]).nm
    &&& t.parts@.len() == t.cap && t.tmp@.len() == t.cap
    &&& t.top@.len() == TOP
    &&& local_ok(sv, t.need@, t.lmap@)
    &&& own_ok(sv, t.codes@, t.cans@, t.ncodes as int)
}

/// The task's own answers: `cans[i]` is the answer for pre pair code `codes[i]` for every `i < n` (opaque: revealed
/// where the lists are written or read).
#[verifier::opaque]
pub open spec fn own_ok(sv: StoresView, codes: Seq<u64>, cans: Seq<u64>, n: int) -> bool {
    &&& 0 <= n <= codes.len() && n <= cans.len()
    &&& forall|i: int| 0 <= i < n && codes[i] < pi::pair_count(sv.pre) ==> #[trigger] pair_ans(sv, codes[i] as int, cans[i])
}

/// Run `r`'s pair codes are nondecreasing.
pub proof fn lemma_run_sorted(sv: StoresView, r: int)
    requires layouts(sv), 0 <= r < ni::run_count(sv.num),
    ensures sorted_on(ni::u64s(sv.num, ni::P_TV), n_start(sv)[r] as int, n_start(sv)[r + 1] as int),
{
    let np = sv.num;
    assert(ni::num_layout_ok(np));
    let st = n_start(sv);
    let tv = ni::u64s(np, ni::P_TV);
    assert forall|a: int, b: int| st[r] <= a <= b < st[r + 1] implies #[trigger] tv[a] <= #[trigger] tv[b] by {
        if a < b {
            assert(st[r] <= a < b < st[r + 1]);
        }
    }
}

impl JoinTask {
    /// The num pair of pre pair `c`: the next routed answer of its bucket when it is for `c`, else resolved.
    fn pair_of_code(&mut self, c: u64) -> (d: u64)
        requires jinputs_ok(*old(self)), c < old(self).dicts.npp,
        ensures
            pair_ans(old(self).sv@, c as int, d),
            jinputs_ok(*final(self)),
            final(self).parts@ == old(self).parts@,
            final(self).filings@ == old(self).filings@, final(self).nf == old(self).nf,
            final(self).sv == old(self).sv, final(self).ps == old(self).ps, final(self).cap == old(self).cap,
            final(self).dicts == old(self).dicts, final(self).top@ == old(self).top@,
        no_unwind
    {
        let ghost sv = self.sv@;
        let cu = c as usize;
        if self.ncodes > 0 {
            proof { reveal(own_ok); }
            match find_key(&self.codes, self.ncodes, c) {
                Some(i) => {
                    proof { assert(pair_ans(sv, self.codes@[i as int] as int, self.cans@[i as int])); }
                    return self.cans[i];
                },
                None => {},
            }
        }
        if cu < self.need.len() && self.need[cu] == ANSWERED {
            proof { reveal(local_ok); }
            return self.lmap[cu];
        }
        let v = bucket_of(&self.cuts, self.nbuckets, c);
        let k = self.cursors[v];
        if k < self.lens[v] {
            proof { assert(answers_ok(sv, self.dicts.npp as int, self.cbufs@, self.dbufs@, self.lens@)); }
            let cc = self.cbufs[v][k];
            let dd = self.dbufs[v][k];
            put(&mut self.cursors, v, k + 1);
            if cc == c {
                return dd;
            }
        }
        self.dicts.resolve(c as usize)
    }
}


/// The plabel key of stored `pre` row `q`: 0 for NULL, else its code + 1.
pub open spec fn pk_of(sv: StoresView, q: int) -> u64 {
    if ptext::u8_part(sv.pre[pi::P_PLABEL_VALID as int])[q] == 0 { 0 } else { (pu64s(sv.pre, pi::P_PLABEL_CODES)[q] + 1) as u64 }
}

/// The key codes are dictionary codes (plabel key: at most the dictionary size).
pub open spec fn codes_ok(sv: StoresView, x: Partial) -> bool {
    &&& x.nm < crate::stores::sub::interface::common::cols::text_count(sv.sub, si::P_NAME_DICT_OFF as int)
    &&& x.tag < pi::tag_count(sv.pre)
    &&& x.pk <= crate::stores::pre::interface::common::cols::text_count(sv.pre, pi::P_PLABEL_OFF as int)
}

/// The exact values of the run rows matching row `q`: count, sum, mass.
pub open spec fn row_ok(sv: StoresView, ps: Seq<Literal>, f: Filing, q: int, x: Partial) -> bool {
    &&& exact_ok(x)
    &&& codes_ok(sv, x)
    &&& x.gc@ == row_w(sv, f, q, 0) && x.gs@ == row_w(sv, f, q, 1) && x.gm@ == row_w(sv, f, q, 2)
    &&& kd(sv, ps, x) == kd_row(sv, ps, f.j as int, q)
    &&& x.nm == f.nm
}

/// The weight of the run rows with pair code `d` is their range's weight.
proof fn lemma_row_range(sv: StoresView, f: Filing, q: int, d: int, lo: int, hi: int, w: int)
    requires
        f.rs <= lo <= hi <= f.re,
        pair_of(sv, p_tv(sv, q) as int) == d,
        forall|i: int| f.rs <= i < f.re ==> ((n_tv(sv, i) as int == d) == (lo <= i < hi)),
    ensures row_w(sv, f, q, w) == isum(lo, hi, |i: int| wt(sv, w, i)),
{
    let g = |i: int| if n_tv(sv, i) as int == pair_of(sv, p_tv(sv, q) as int) { wt(sv, w, i) } else { 0 };
    assert forall|i: int| f.rs <= i < f.re && !(lo <= i < hi) implies #[trigger] g(i) == 0 by {}
    lemma_isum_restrict(f.rs as int, f.re as int, lo, hi, g);
    lemma_isum_ext(lo, hi, g, |i: int| wt(sv, w, i));
}

impl JoinTask {
    /// The partial of stored `pre` row `q` of filing `f` (`None` when no run row matches it), and the next hint.
    fn join_row(&mut self, f: Filing, q: usize, h: usize) -> (r: (Option<Partial>, usize))
        requires
            jinputs_ok(*old(self)), filing_ok(old(self).sv@, old(self).ps@, f), q < old(self).npre,
            f.rs <= h <= f.re,
        ensures
            jinputs_ok(*final(self)),
            final(self).parts@ == old(self).parts@,
            final(self).filings@ == old(self).filings@, final(self).nf == old(self).nf,
            final(self).sv == old(self).sv, final(self).ps == old(self).ps, final(self).cap == old(self).cap,
            final(self).dicts == old(self).dicts, final(self).top@ == old(self).top@,
            f.rs <= r.1 <= f.re,
            r.0 matches Some(x) ==> row_ok(old(self).sv@, old(self).ps@, f, q as int, x),
            r.0 is None ==> row_w(old(self).sv@, f, q as int, 0) == 0 && row_w(old(self).sv@, f, q as int, 1) == 0
                && row_w(old(self).sv@, f, q as int, 2) == 0,
        no_unwind
    {
        let ghost sv = self.sv@;
        let ghost ps = self.ps@;
        let ghost pp = sv.pre;
        proof {
            assert(pi::pre_layout_ok(pp));
            assert(ni::num_layout_ok(sv.num));
            lemma_run_bounds(sv, f.gr@);
            lemma_run_sorted(sv, f.gr@);
        }
        let c = self.pre_tv[q];
        let d = self.pair_of_code(c);
        let rs = f.rs as usize;
        let re = f.re as usize;
        if d == NONE {
            proof {
                assert(pair_of(sv, c as int) == -1);
                assert forall|w: int| #![auto] row_w(sv, f, q as int, w) == 0 by {
                    lemma_isum_zero(f.rs as int, f.re as int,
                        |i: int| if n_tv(sv, i) as int == pair_of(sv, p_tv(sv, q as int) as int) { wt(sv, w, i) } else { 0 });
                }
            }
            return (None, h);
        }
        let mut hh = h;
        if hh > rs && self.num_tv[hh - 1] >= d {
            hh = rs;
        }
        proof {
            assert forall|i: int| rs <= i < hh implies #[trigger] self.num_tv@[i] < d by {
                assert(self.num_tv@[i] <= self.num_tv@[hh - 1]);
            }
            assert forall|a: int, b: int| hh <= a <= b < re implies #[trigger] self.num_tv@[a] <= #[trigger] self.num_tv@[b] by {}
        }
        let lo = gallop_u64(self.num_tv, hh, re, d);
        let mut p = lo;
        let mut sum: i128 = 0;
        let mut mass: i128 = 0;
        let ghost mut gs: int = 0;
        let ghost mut gm: int = 0;
        while p < re && self.num_tv[p] == d
            invariant
                jinputs_ok(*self), self.sv@ == sv, lo <= p <= re, re <= self.nrows, rs <= lo,
                forall|i: int| lo <= i < p ==> #[trigger] self.num_tv@[i] == d,
                gs == isum(lo as int, p as int, |i: int| wt(sv, 1, i)),
                gm == isum(lo as int, p as int, |i: int| wt(sv, 2, i)),
                0 <= gm, abs(gs) <= gm,
                mass != MASS_OVER ==> mass as int == gm && sum as int == gs,
                mass == MASS_OVER ==> gm > i128::MAX,
            decreases re - p,
        {
            let v = self.num_val[p];
            proof {
                assert(wt(sv, 1, p as int) == v as int);
                assert(wt(sv, 2, p as int) == abs(v as int));
                gs = gs + v as int;
                gm = gm + abs(v as int);
            }
            if mass != MASS_OVER {
                if v == i128::MIN {
                    mass = MASS_OVER;
                } else {
                    let av: i128 = if v < 0 { 0 - v } else { v };
                    if mass <= i128::MAX - av {
                        mass = mass + av;
                        sum = sum + v;
                    } else {
                        mass = MASS_OVER;
                    }
                }
            }
            p = p + 1;
        }
        proof {
            assert forall|i: int| f.rs <= i < f.re implies ((n_tv(sv, i) as int == d as int) == (lo <= i < p)) by {
                if i < hh {
                } else if i < lo {
                } else if i >= p {
                    assert(p < re);
                    assert(self.num_tv@[p as int] >= d);
                    assert(self.num_tv@[p as int] != d);
                    assert(self.num_tv@[p as int] <= self.num_tv@[i]);
                }
            }
            assert(pair_of(sv, c as int) == d as int);
            lemma_row_range(sv, f, q as int, d as int, lo as int, p as int, 0);
            lemma_row_range(sv, f, q as int, d as int, lo as int, p as int, 1);
            lemma_row_range(sv, f, q as int, d as int, lo as int, p as int, 2);
            lemma_isum_count(lo as int, p as int, |i: int| wt(sv, 0, i));
        }
        if p == lo {
            return (None, lo);
        }
        let n = p - lo;
        let cnt: u64 = if n as u64 > INT8_MAX { CNT_OVER } else { n as u64 };
        let pk: u64 = if self.plabel_valid[q] != 0 { self.plabel_codes[q] + 1 } else { 0 };
        let x = Partial {
            nm: f.nm,
            tag: self.dicts.ppair_tag[c as usize],
            pk,
            cnt,
            sum,
            mass,
            gc: Ghost(n as int),
            gs: Ghost(gs),
            gm: Ghost(gm),
        };
        proof {
            assert(kd(sv, ps, x) =~= kd_row(sv, ps, f.j as int, q as int));
            assert(si::sub_layout_ok(sv.sub));
            assert(pi::pre_layout_ok(pp));
            assert(pu64s(pp, pi::P_PAIR_TAG)[c as int] < pi::tag_count(pp));
        }
        (Some(x), lo)
    }
}


/// Writing `x` at position `len` adds its term to the sums over `[len0, len + 1)`.
pub proof fn lemma_psum_push(sv: StoresView, ps: Seq<Literal>, a: Seq<Partial>, len0: int, len: int, x: Partial, k: Row, w: int)
    requires 0 <= len0 <= len < a.len(),
    ensures psum(sv, ps, a.update(len, x), len0, len + 1, k, w) == psum(sv, ps, a, len0, len, k, w) + pterm(sv, ps, x, k, w),
{
    let a2 = a.update(len, x);
    lemma_isum_ext(len0, len, |t: int| pterm(sv, ps, a2[t], k, w), |t: int| pterm(sv, ps, a[t], k, w));
}

/// The sums over a range only read the range.
pub proof fn lemma_psum_frame(sv: StoresView, ps: Seq<Literal>, a: Seq<Partial>, b: Seq<Partial>, lo: int, hi: int, k: Row, w: int)
    requires forall|t: int| lo <= t < hi ==> a[t] == b[t],
    ensures psum(sv, ps, a, lo, hi, k, w) == psum(sv, ps, b, lo, hi, k, w),
{
    lemma_isum_ext(lo, hi, |t: int| pterm(sv, ps, a[t], k, w), |t: int| pterm(sv, ps, b[t], k, w));
}

/// A row's weights for every value selector (2 and above are the mass).
proof fn lemma_row_w_sel(sv: StoresView, f: Filing, q: int, w: int)
    requires w != 0 && w != 1,
    ensures row_w(sv, f, q, w) == row_w(sv, f, q, 2),
{
    let c = pair_of(sv, p_tv(sv, q) as int);
    lemma_isum_ext(f.rs as int, f.re as int,
        |i: int| if n_tv(sv, i) as int == c { wt(sv, w, i) } else { 0 },
        |i: int| if n_tv(sv, i) as int == c { wt(sv, 2, i) } else { 0 });
}

/// The term of a row's partial is the filing's row term.
proof fn lemma_row_term(sv: StoresView, ps: Seq<Literal>, f: Filing, q: int, x: Partial, k: Row, w: int)
    requires row_ok(sv, ps, f, q, x),
    ensures pterm(sv, ps, x, k, w) == frow(sv, ps, f, k, w, q),
{
    if w != 0 && w != 1 { lemma_row_w_sel(sv, f, q, w); }
}

/// A row without partial has no term.
proof fn lemma_row_none(sv: StoresView, ps: Seq<Literal>, f: Filing, q: int, k: Row, w: int)
    requires row_w(sv, f, q, 0) == 0 && row_w(sv, f, q, 1) == 0 && row_w(sv, f, q, 2) == 0,
    ensures frow(sv, ps, f, k, w, q) == 0,
{
    if w != 0 && w != 1 { lemma_row_w_sel(sv, f, q, w); }
}

/// A selected sub-run finished: the filing's partials so far sum to the sub-runs up to and including it.
proof fn lemma_sub_done(sv: StoresView, ps: Seq<Literal>, f: Filing, s: int, a: Seq<Partial>, a_s: Seq<Partial>,
    len0: int, len_s: int, len: int, k: Row, w: int)
    requires
        sel_sub(sv, ps, s), 0 <= len0 <= len_s <= len, f.sa <= s,
        forall|x: int| 0 <= x < len_s ==> a[x] == a_s[x],
        psum(sv, ps, a_s, len0, len_s, k, w) == isum(f.sa as int, s, |s2: int| fsub(sv, ps, f, k, w, s2)),
        psum(sv, ps, a, len_s, len, k, w) == isum(p_start(sv)[s] as int, p_start(sv)[s + 1] as int, |l: int| frow(sv, ps, f, k, w, l)),
    ensures psum(sv, ps, a, len0, len, k, w) == isum(f.sa as int, s + 1, |s2: int| fsub(sv, ps, f, k, w, s2)),
{
    lemma_psum_frame(sv, ps, a, a_s, len0, len_s, k, w);
    lemma_isum_split(len0, len_s, len, |t: int| pterm(sv, ps, a[t], k, w));
    let fsf = |s2: int| fsub(sv, ps, f, k, w, s2);
    assert(isum(f.sa as int, s + 1, fsf) == isum(f.sa as int, s, fsf) + fsf(s));
}

/// The selected rows of a filing up to and including sub-run `s` are at most all of them.
proof fn lemma_sel_rows_split(sv: StoresView, ps: Seq<Literal>, f: Filing, s: int)
    requires layouts(sv), filing_ok(sv, ps, f), f.sa <= s < f.sb,
    ensures sel_rows(sv, ps, f.sa as int, s) + sel_len(sv, ps, s) <= f.rows,
{
    lemma_subs_bounds(sv, f.gb@);
    let sl = |s2: int| sel_len(sv, ps, s2);
    assert forall|x: int| f.sa <= x < f.sb implies #[trigger] sl(x) >= 0 by {
        lemma_sub_step(sv, x);
    }
    lemma_isum_split(f.sa as int, s + 1, f.sb as int, sl);
    lemma_isum_nonneg(s + 1, f.sb as int, sl);
    assert(isum(f.sa as int, s + 1, sl) == isum(f.sa as int, s, sl) + sl(s));
}

/// Selected rows of the filings `fl[lo..hi)`.
pub open spec fn rows_sum(fl: Seq<Filing>, lo: int, hi: int) -> int {
    isum(lo, hi, |x: int| fl[x].rows as int)
}

pub proof fn lemma_rows_sum_mono(fl: Seq<Filing>, a: int, b: int, c: int, d: int)
    requires 0 <= a <= b <= c <= d,
    ensures rows_sum(fl, b, c) <= rows_sum(fl, a, d),
{
    let r = |x: int| fl[x].rows as int;
    lemma_isum_split(a, b, d, r);
    lemma_isum_split(b, c, d, r);
    assert forall|x: int| a <= x < d implies #[trigger] r(x) >= 0 by {}
    lemma_isum_nonneg(a, b, r);
    lemma_isum_nonneg(c, d, r);
}

impl JoinTask {
    /// Marks the pre pair code of every selected row of filing `fi` as `NEEDED` in the local need list.
    fn mark_filing(&mut self, fi: usize)
        requires jinputs_ok(*old(self)), fi < old(self).nf,
        ensures
            jinputs_ok(*final(self)),
            final(self).filings == old(self).filings, final(self).nf == old(self).nf,
            final(self).sv == old(self).sv, final(self).ps == old(self).ps, final(self).cap == old(self).cap,
            final(self).dicts == old(self).dicts, final(self).top == old(self).top, final(self).lmap == old(self).lmap,
            final(self).need@.len() == old(self).need@.len(),
        no_unwind
    {
        let ghost sv = self.sv@;
        let ghost ps = self.ps@;
        let ghost pp = sv.pre;
        let f = self.filings[fi];
        proof {
            assert(filing_ok(sv, ps, f));
            lemma_subs_bounds(sv, f.gb@);
            assert(pi::pre_layout_ok(pp));
        }
        let n = self.need.len();
        let mut s = f.sa as usize;
        let sb = f.sb as usize;
        while s < sb
            invariant
                jinputs_ok(*self), self.sv@ == sv, self.ps@ == ps, pp == sv.pre,
                self.filings == old(self).filings, self.nf == old(self).nf,
                self.sv == old(self).sv, self.ps == old(self).ps, self.cap == old(self).cap,
                self.dicts == old(self).dicts, self.top == old(self).top, self.lmap == old(self).lmap,
                self.need@.len() == n, n == old(self).need@.len(),
                f.sa <= s <= sb, sb <= pi::sub_count(pp),
            decreases sb - s,
        {
            proof {
                lemma_sub_step(sv, s as int);
                assert(sub_stmt(sv, s as int) == pi::group_stmt_of(pp, self.sub_group@[s as int] as int));
                assert(pu64s(pp, pi::P_SUB_ADSH)[s as int] < pi::adsh_count(pp) && pu64s(pp, pi::P_SUB_GROUP)[s as int] < pi::group_count(pp));
            }
            if self.group_stmt[self.sub_group[s] as usize] == self.stmt_key {
                let q1 = self.sub_start[s + 1] as usize;
                let mut q = self.sub_start[s] as usize;
                while q < q1
                    invariant
                        jinputs_ok(*self), self.sv@ == sv, self.ps@ == ps, pp == sv.pre,
                        self.filings == old(self).filings, self.nf == old(self).nf,
                        self.sv == old(self).sv, self.ps == old(self).ps, self.cap == old(self).cap,
                        self.dicts == old(self).dicts, self.top == old(self).top, self.lmap == old(self).lmap,
                        self.need@.len() == n, n == old(self).need@.len(),
                        q1 <= p_count(sv),
                    decreases q1 - q,
                {
                    let c = self.pre_tv[q] as usize;
                    if c < n {
                        let ghost before = self.need@;
                        put(&mut self.need, c, NEEDED);
                        proof {
                            reveal(local_ok);
                            assert forall|x: int| 0 <= x < self.need@.len() && #[trigger] self.need@[x] == ANSWERED
                                implies pair_ans(sv, x, self.lmap@[x]) by {
                                assert(self.need@[x] == before[x]);
                            }
                        }
                    }
                    q = q + 1;
                }
            }
            s = s + 1;
        }
    }

    /// Lists the pre pair code of every selected row of filing `fi` in `codes[n0..n)` (rows beyond the list's
    /// length are left out: the list only speeds up `pair_of_code`).
    fn list_filing(&mut self, fi: usize, n0: usize) -> (n: usize)
        requires jinputs_ok(*old(self)), fi < old(self).nf, old(self).ncodes == 0, n0 <= old(self).codes@.len(),
        ensures
            jinputs_ok(*final(self)), n0 <= n <= final(self).codes@.len(),
            final(self).filings == old(self).filings, final(self).nf == old(self).nf,
            final(self).sv == old(self).sv, final(self).ps == old(self).ps, final(self).cap == old(self).cap,
            final(self).dicts == old(self).dicts, final(self).top == old(self).top,
            final(self).need == old(self).need, final(self).lmap == old(self).lmap,
            final(self).codes@.len() == old(self).codes@.len(), final(self).cans == old(self).cans,
            final(self).ncodes == 0, final(self).counts == old(self).counts,
        no_unwind
    {
        let ghost sv = self.sv@;
        let ghost ps = self.ps@;
        let ghost pp = sv.pre;
        let f = self.filings[fi];
        proof {
            assert(filing_ok(sv, ps, f));
            lemma_subs_bounds(sv, f.gb@);
            assert(pi::pre_layout_ok(pp));
        }
        let m = self.codes.len();
        let mut n = n0;
        let mut s = f.sa as usize;
        let sb = f.sb as usize;
        while s < sb
            invariant
                jinputs_ok(*self), self.sv@ == sv, self.ps@ == ps, pp == sv.pre,
                self.filings == old(self).filings, self.nf == old(self).nf,
                self.sv == old(self).sv, self.ps == old(self).ps, self.cap == old(self).cap,
                self.dicts == old(self).dicts, self.top == old(self).top,
                self.need == old(self).need, self.lmap == old(self).lmap,
                self.codes@.len() == m, m == old(self).codes@.len(), self.cans == old(self).cans, self.ncodes == 0,
                        self.counts == old(self).counts,
                n0 <= n <= m, f.sa <= s <= sb, sb <= pi::sub_count(pp),
            decreases sb - s,
        {
            proof {
                lemma_sub_step(sv, s as int);
                assert(sub_stmt(sv, s as int) == pi::group_stmt_of(pp, self.sub_group@[s as int] as int));
                assert(pu64s(pp, pi::P_SUB_ADSH)[s as int] < pi::adsh_count(pp) && pu64s(pp, pi::P_SUB_GROUP)[s as int] < pi::group_count(pp));
            }
            if self.group_stmt[self.sub_group[s] as usize] == self.stmt_key {
                let q1 = self.sub_start[s + 1] as usize;
                let mut q = self.sub_start[s] as usize;
                while q < q1 && n < m
                    invariant
                        jinputs_ok(*self), self.sv@ == sv, self.ps@ == ps, pp == sv.pre,
                        self.filings == old(self).filings, self.nf == old(self).nf,
                        self.sv == old(self).sv, self.ps == old(self).ps, self.cap == old(self).cap,
                        self.dicts == old(self).dicts, self.top == old(self).top,
                        self.need == old(self).need, self.lmap == old(self).lmap,
                        self.codes@.len() == m, m == old(self).codes@.len(), self.cans == old(self).cans, self.ncodes == 0,
                        self.counts == old(self).counts,
                        n0 <= n <= m, q1 <= p_count(sv),
                    decreases q1 - q,
                {
                    let c = self.pre_tv[q];
                    put(&mut self.codes, n, c);
                    proof { reveal(own_ok); }
                    n = n + 1;
                    q = q + 1;
                }
            }
            s = s + 1;
        }
        n
    }

    /// The partials of filing `fi`, appended to `parts[len0..)`: `(len, true)`, or `(_, false)` when the buffer
    /// is full.
    fn join_filing(&mut self, fi: usize, len0: usize) -> (r: (usize, bool))
        requires jinputs_ok(*old(self)), fi < old(self).nf, len0 <= old(self).cap,
        ensures
            jinputs_ok(*final(self)),
            final(self).filings@ == old(self).filings@, final(self).nf == old(self).nf,
            final(self).sv == old(self).sv, final(self).ps == old(self).ps, final(self).cap == old(self).cap,
            final(self).dicts == old(self).dicts, final(self).top@ == old(self).top@,
            len0 <= r.0 <= final(self).cap,
            forall|x: int| 0 <= x < len0 ==> final(self).parts@[x] == old(self).parts@[x],
            r.1 ==> forall|x: int| len0 <= x < r.0 ==> exact_ok(#[trigger] final(self).parts@[x])
                && codes_ok(old(self).sv@, final(self).parts@[x])
                && final(self).parts@[x].nm == old(self).filings@[fi as int].nm,
            r.1 ==> forall|k: Row, w: int| #[trigger] psum(old(self).sv@, old(self).ps@, final(self).parts@, len0 as int, r.0 as int, k, w)
                == fsum(old(self).sv@, old(self).ps@, old(self).filings@[fi as int], k, w),
            r.1 ==> r.0 - len0 <= old(self).filings@[fi as int].rows,
            !r.1 ==> old(self).cap < len0 + old(self).filings@[fi as int].rows,
        no_unwind
    {
        let ghost sv = self.sv@;
        let ghost ps = self.ps@;
        let ghost pp = sv.pre;
        let ghost p0 = self.parts@;
        let f = self.filings[fi];
        proof {
            assert(filing_ok(sv, ps, f));
            lemma_subs_bounds(sv, f.gb@);
            lemma_run_bounds(sv, f.gr@);
            assert(pi::pre_layout_ok(pp));
        }
        let ghost fs = |s2: int| (|k: Row, w: int| fsub(sv, ps, f, k, w, s2));
        let mut len = len0;
        let mut s = f.sa as usize;
        let sb = f.sb as usize;
        while s < sb
            invariant
                jinputs_ok(*self), self.sv@ == sv, self.ps@ == ps, pp == sv.pre,
                self.sv == old(self).sv, self.ps == old(self).ps,
                self.filings@ == old(self).filings@, self.nf == old(self).nf, self.cap == old(self).cap,
                self.dicts == old(self).dicts, self.filings@[fi as int] == f, filing_ok(sv, ps, f),
                self.top@ == old(self).top@,
                f.sa <= s <= sb, sb == f.sb, sb <= pi::sub_count(pp), len0 <= len <= self.cap,
                f.rs <= f.re <= n_count(sv),
                forall|x: int| 0 <= x < len0 ==> self.parts@[x] == p0[x], p0 == old(self).parts@,
                forall|x: int| len0 <= x < len ==> exact_ok(#[trigger] self.parts@[x]) && codes_ok(sv, self.parts@[x])
                    && self.parts@[x].nm == f.nm,
                forall|k: Row, w: int| #[trigger] psum(sv, ps, self.parts@, len0 as int, len as int, k, w)
                    == isum(f.sa as int, s as int, |s2: int| fsub(sv, ps, f, k, w, s2)),
                len - len0 <= sel_rows(sv, ps, f.sa as int, s as int),
            decreases sb - s,
        {
            proof {
                lemma_sub_step(sv, s as int);
                assert(sub_stmt(sv, s as int) == pi::group_stmt_of(pp, self.sub_group@[s as int] as int));
                assert(pu64s(pp, pi::P_SUB_ADSH)[s as int] < pi::adsh_count(pp) && pu64s(pp, pi::P_SUB_GROUP)[s as int] < pi::group_count(pp));
            }
            let ghost len_s = len;
            let ghost ps_s = self.parts@;
            if self.group_stmt[self.sub_group[s] as usize] == self.stmt_key {
                let q0 = self.sub_start[s] as usize;
                let q1 = self.sub_start[s + 1] as usize;
                let mut q = q0;
                let mut h = f.rs as usize;
                proof { assert(sel_sub(sv, ps, s as int)); }
                while q < q1
                    invariant
                        jinputs_ok(*self), self.sv@ == sv, self.ps@ == ps, pp == sv.pre,
                        self.sv == old(self).sv, self.ps == old(self).ps,
                        self.filings@ == old(self).filings@, self.nf == old(self).nf, self.cap == old(self).cap,
                        self.dicts == old(self).dicts, self.filings@[fi as int] == f, filing_ok(sv, ps, f),
                        self.top@ == old(self).top@,
                        f.sa <= s < sb, sb == f.sb, sb <= pi::sub_count(pp), len_s <= len <= self.cap, len0 <= len_s,
                        q0 <= q <= q1, q0 == p_start(sv)[s as int], q1 == p_start(sv)[s + 1], q1 <= p_count(sv),
                        f.rs <= h <= f.re, f.re <= n_count(sv),
                        forall|x: int| 0 <= x < len_s ==> self.parts@[x] == ps_s[x],
                        forall|x: int| 0 <= x < len0 ==> self.parts@[x] == p0[x], p0 == old(self).parts@,
                        forall|x: int| len0 <= x < len ==> exact_ok(#[trigger] self.parts@[x]) && codes_ok(sv, self.parts@[x])
                            && self.parts@[x].nm == f.nm,
                        forall|k: Row, w: int| #[trigger] psum(sv, ps, ps_s, len0 as int, len_s as int, k, w)
                            == isum(f.sa as int, s as int, |s2: int| fsub(sv, ps, f, k, w, s2)),
                        forall|k: Row, w: int| #[trigger] psum(sv, ps, self.parts@, len_s as int, len as int, k, w)
                            == isum(q0 as int, q as int, |l: int| frow(sv, ps, f, k, w, l)),
                        len - len0 <= sel_rows(sv, ps, f.sa as int, s as int) + (q - q0),
                        sel_sub(sv, ps, s as int),
                    decreases q1 - q,
                {
                    let ghost before = self.parts@;
                    let (opt, h2) = self.join_row(f, q, h);
                    h = h2;
                    match opt {
                        Some(x) => {
                            if len >= self.cap {
                                proof {
                                    lemma_sel_rows_split(sv, ps, f, s as int);
                                    assert(sel_len(sv, ps, s as int) == q1 - q0);
                                }
                                return (len, false);
                            }
                            put(&mut self.parts, len, x);
                            proof {
                                assert forall|k: Row, w: int| #[trigger] psum(sv, ps, self.parts@, len_s as int, len + 1, k, w)
                                    == isum(q0 as int, q + 1, |l: int| frow(sv, ps, f, k, w, l)) by {
                                    lemma_psum_push(sv, ps, before, len_s as int, len as int, x, k, w);
                                    lemma_row_term(sv, ps, f, q as int, x, k, w);
                                }
                            }
                            len = len + 1;
                        },
                        None => {
                            proof {
                                assert forall|k: Row, w: int| #[trigger] psum(sv, ps, self.parts@, len_s as int, len as int, k, w)
                                    == isum(q0 as int, q + 1, |l: int| frow(sv, ps, f, k, w, l)) by {
                                    lemma_row_none(sv, ps, f, q as int, k, w);
                                }
                            }
                        },
                    }
                    q = q + 1;
                }
                proof {
                    assert(sel_sub(sv, ps, s as int));
                    assert forall|k: Row, w: int| #[trigger] psum(sv, ps, self.parts@, len0 as int, len as int, k, w)
                        == isum(f.sa as int, s + 1, |s2: int| fsub(sv, ps, f, k, w, s2)) by {
                        lemma_sub_done(sv, ps, f, s as int, self.parts@, ps_s, len0 as int, len_s as int, len as int, k, w);
                    }
                    assert(sel_len(sv, ps, s as int) == q1 - q0);
                    let sl = |s2: int| sel_len(sv, ps, s2);
                    assert(isum(f.sa as int, s + 1, sl) == isum(f.sa as int, s as int, sl) + sl(s as int));
                }
            } else {
                proof {
                    assert(!sel_sub(sv, ps, s as int));
                    assert forall|k: Row, w: int| #[trigger] psum(sv, ps, self.parts@, len0 as int, len as int, k, w)
                        == isum(f.sa as int, s + 1, |s2: int| fsub(sv, ps, f, k, w, s2)) by {
                        let fsf = |s2: int| fsub(sv, ps, f, k, w, s2);
                        assert(isum(f.sa as int, s + 1, fsf) == isum(f.sa as int, s as int, fsf) + fsf(s as int));
                    }
                    let sl = |s2: int| sel_len(sv, ps, s2);
                    assert(isum(f.sa as int, s + 1, sl) == isum(f.sa as int, s as int, sl) + sl(s as int));
                }
            }
            s = s + 1;
        }
        (len, true)
    }
}


// ------------------------------------------------------------------------------------------------ groups

pub open spec fn same_code(a: Partial, b: Partial) -> bool {
    a.nm == b.nm && a.tag == b.tag && a.pk == b.pk
}

/// Strict lexicographic order of the key codes.
pub open spec fn key_lt(a: Partial, b: Partial) -> bool {
    a.nm < b.nm || (a.nm == b.nm && (a.tag < b.tag || (a.tag == b.tag && a.pk < b.pk)))
}

/// Keys decode injectively from in-range codes.
pub proof fn lemma_kd_inj(sv: StoresView, ps: Seq<Literal>, a: Partial, b: Partial)
    requires layouts(sv), codes_ok(sv, a), codes_ok(sv, b), kd(sv, ps, a) == kd(sv, ps, b),
    ensures same_code(a, b),
{
    let sp = sv.sub;
    let pp = sv.pre;
    assert(si::sub_layout_ok(sp));
    assert(pi::pre_layout_ok(pp));
    let (ka, kb) = (kd(sv, ps, a), kd(sv, ps, b));
    assert(ka[0] == kb[0] && ka[2] == kb[2] && ka[3] == kb[3]);
    stext::lemma_dict_codes(stext::u64_part(sp[si::P_NAME_DICT_OFF as int]), stext::u8_part(sp[si::P_NAME_DICT_BYTES as int]),
        crate::stores::sub::interface::common::cols::text_count(sp, si::P_NAME_DICT_OFF as int), a.nm as int, b.nm as int);
    ptext::lemma_dict_codes(ptext::u64_part(pp[pi::P_TAG_OFF as int]), ptext::u8_part(pp[pi::P_TAG_OFF + 1]),
        pi::tag_count(pp), a.tag as int, b.tag as int);
    if a.pk != 0 && b.pk != 0 {
        ptext::lemma_dict_codes(ptext::u64_part(pp[pi::P_PLABEL_OFF as int]), ptext::u8_part(pp[pi::P_PLABEL_OFF + 1]),
            crate::stores::pre::interface::common::cols::text_count(pp, pi::P_PLABEL_OFF as int), a.pk - 1, b.pk - 1);
    }
}

/// `x` and `y` merged (same key codes): counts, sums and masses add.
pub open spec fn merged(x: Partial, y: Partial, z: Partial) -> bool {
    &&& same_code(z, x)
    &&& z.gc@ == x.gc@ + y.gc@ && z.gs@ == x.gs@ + y.gs@ && z.gm@ == x.gm@ + y.gm@
}

/// Merge `y` into `x` (same key codes), with the checked count and mass.
fn merge(x: Partial, y: Partial) -> (z: Partial)
    requires exact_ok(x), exact_ok(y), same_code(x, y),
    ensures exact_ok(z), merged(x, y, z),
    no_unwind
{
    let cnt = if x.cnt == CNT_OVER || y.cnt == CNT_OVER || x.cnt > INT8_MAX - y.cnt { CNT_OVER } else { x.cnt + y.cnt };
    let over = x.mass == MASS_OVER || y.mass == MASS_OVER || x.mass > i128::MAX - y.mass;
    let mass = if over { MASS_OVER } else { x.mass + y.mass };
    let sum = if over { 0 } else { x.sum + y.sum };
    Partial {
        nm: x.nm,
        tag: x.tag,
        pk: x.pk,
        cnt,
        sum,
        mass,
        gc: Ghost(x.gc@ + y.gc@),
        gs: Ghost(x.gs@ + y.gs@),
        gm: Ghost(x.gm@ + y.gm@),
    }
}

/// The term of a merge is the sum of the terms.
proof fn lemma_merged_term(sv: StoresView, ps: Seq<Literal>, x: Partial, y: Partial, z: Partial, k: Row, w: int)
    requires merged(x, y, z), same_code(x, y),
    ensures pterm(sv, ps, z, k, w) == pterm(sv, ps, x, k, w) + pterm(sv, ps, y, k, w),
{
    assert(kd(sv, ps, z) == kd(sv, ps, x));
    assert(kd(sv, ps, y) == kd(sv, ps, x));
}

impl JoinTask {
    /// Merge the sorted partials `parts[0..len)` (all of name code `nmv`) with equal key codes into groups
    /// `parts[0..g)`: strictly increasing key codes, the same sums per key.
    fn aggregate(&mut self, len: usize, Ghost(nmv): Ghost<u64>) -> (g: usize)
        requires
            jinputs_ok(*old(self)), len <= old(self).cap,
            forall|x: int| 0 <= x < len ==> exact_ok(#[trigger] old(self).parts@[x]) && codes_ok(old(self).sv@, old(self).parts@[x])
                && old(self).parts@[x].nm == nmv,
            forall|x: int, y: int| 0 <= x < y < len ==> crate::agent::common::sort::key_le(#[trigger] old(self).parts@[x], #[trigger] old(self).parts@[y]),
        ensures
            jinputs_ok(*final(self)),
            final(self).filings@ == old(self).filings@, final(self).nf == old(self).nf,
            final(self).sv == old(self).sv, final(self).ps == old(self).ps, final(self).cap == old(self).cap,
            final(self).dicts == old(self).dicts, final(self).top@ == old(self).top@,
            g <= len,
            forall|x: int| 0 <= x < g ==> exact_ok(#[trigger] final(self).parts@[x]) && codes_ok(final(self).sv@, final(self).parts@[x])
                && final(self).parts@[x].nm == nmv,
            forall|x: int, y: int| 0 <= x < y < g ==> key_lt(#[trigger] final(self).parts@[x], #[trigger] final(self).parts@[y]),
            forall|k: Row, w: int| #[trigger] psum(old(self).sv@, old(self).ps@, final(self).parts@, 0, g as int, k, w)
                == psum(old(self).sv@, old(self).ps@, old(self).parts@, 0, len as int, k, w),
        no_unwind
    {
        let ghost sv = self.sv@;
        let ghost ps = self.ps@;
        let ghost p = self.parts@;
        let mut g: usize = 0;
        let mut i: usize = 0;
        while i < len
            invariant
                jinputs_ok(*self), self.sv@ == sv, self.ps@ == ps, p == old(self).parts@,
                self.sv == old(self).sv, self.ps == old(self).ps,
                self.filings@ == old(self).filings@, self.nf == old(self).nf, self.cap == old(self).cap,
                self.dicts == old(self).dicts, self.top@ == old(self).top@,
                len <= self.cap, g <= i <= len,
                forall|x: int| i <= x < len ==> self.parts@[x] == p[x],
                forall|x: int| 0 <= x < len ==> exact_ok(#[trigger] p[x]) && codes_ok(sv, p[x]) && p[x].nm == nmv,
                forall|x: int, y: int| 0 <= x < y < len ==> crate::agent::common::sort::key_le(#[trigger] p[x], #[trigger] p[y]),
                forall|x: int| 0 <= x < g ==> exact_ok(#[trigger] self.parts@[x]) && codes_ok(sv, self.parts@[x])
                    && self.parts@[x].nm == nmv,
                forall|x: int, y: int| 0 <= x < y < g ==> key_lt(#[trigger] self.parts@[x], #[trigger] self.parts@[y]),
                g > 0 && i < len ==> key_lt(self.parts@[g - 1], p[i as int]),
                forall|k: Row, w: int| #[trigger] psum(sv, ps, self.parts@, 0, g as int, k, w) == psum(sv, ps, p, 0, i as int, k, w),
            decreases len - i,
        {
            let i0 = i;
            let mut acc = self.parts[i];
            i = i + 1;
            proof {
                assert forall|k: Row, w: int| #[trigger] pterm(sv, ps, acc, k, w) == psum(sv, ps, p, i0 as int, i as int, k, w) by {
                    let f = |t: int| pterm(sv, ps, p[t], k, w);
                    assert(isum(i0 as int, i as int, f) == isum(i0 as int, i0 as int, f) + f(i0 as int));
                }
            }
            while i < len && self.parts[i].nm == acc.nm && self.parts[i].tag == acc.tag && self.parts[i].pk == acc.pk
                invariant
                    jinputs_ok(*self), self.sv@ == sv, self.ps@ == ps, p == old(self).parts@,
                    self.sv == old(self).sv, self.ps == old(self).ps,
                    self.filings@ == old(self).filings@, self.nf == old(self).nf, self.cap == old(self).cap,
                    self.dicts == old(self).dicts, self.top@ == old(self).top@,
                    len <= self.cap, g <= i0 < i <= len,
                    forall|x: int| i0 <= x < len ==> self.parts@[x] == p[x],
                    forall|x: int| 0 <= x < len ==> exact_ok(#[trigger] p[x]) && codes_ok(sv, p[x]) && p[x].nm == nmv,
                    forall|x: int, y: int| 0 <= x < y < len ==> crate::agent::common::sort::key_le(#[trigger] p[x], #[trigger] p[y]),
                    forall|x: int| 0 <= x < g ==> exact_ok(#[trigger] self.parts@[x]) && codes_ok(sv, self.parts@[x])
                        && self.parts@[x].nm == nmv,
                    forall|x: int, y: int| 0 <= x < y < g ==> key_lt(#[trigger] self.parts@[x], #[trigger] self.parts@[y]),
                    g > 0 ==> key_lt(self.parts@[g - 1], p[i0 as int]),
                    forall|k: Row, w: int| #[trigger] psum(sv, ps, self.parts@, 0, g as int, k, w) == psum(sv, ps, p, 0, i0 as int, k, w),
                    exact_ok(acc), codes_ok(sv, acc), same_code(acc, p[i0 as int]), acc.nm == nmv,
                    forall|k: Row, w: int| #[trigger] pterm(sv, ps, acc, k, w) == psum(sv, ps, p, i0 as int, i as int, k, w),
                decreases len - i,
            {
                let y = self.parts[i];
                proof {
                    assert(y == p[i as int]);
                    assert(exact_ok(p[i as int]));
                }
                let ghost a0 = acc;
                acc = merge(acc, y);
                proof {
                    assert forall|k: Row, w: int| #[trigger] pterm(sv, ps, acc, k, w) == psum(sv, ps, p, i0 as int, i + 1, k, w) by {
                        lemma_merged_term(sv, ps, a0, y, acc, k, w);
                        let f = |t: int| pterm(sv, ps, p[t], k, w);
                        assert(isum(i0 as int, i + 1, f) == isum(i0 as int, i as int, f) + f(i as int));
                    }
                }
                i = i + 1;
            }
            let ghost before = self.parts@;
            put(&mut self.parts, g, acc);
            proof {
                assert forall|k: Row, w: int| #[trigger] psum(sv, ps, self.parts@, 0, g + 1, k, w) == psum(sv, ps, p, 0, i as int, k, w) by {
                    lemma_psum_push(sv, ps, before, 0, g as int, acc, k, w);
                    lemma_isum_split(0, i0 as int, i as int, |t: int| pterm(sv, ps, p[t], k, w));
                }
                if i < len {
                    assert(crate::agent::common::sort::key_le(p[i0 as int], p[i as int]));
                    assert(!same_code(self.parts@[i as int], acc));
                }
                assert forall|x: int, y: int| 0 <= x < y < g + 1 implies key_lt(#[trigger] self.parts@[x], #[trigger] self.parts@[y]) by {
                    if y == g && x < g - 1 {
                        assert(key_lt(before[x], before[g - 1]));
                    }
                }
            }
            g = g + 1;
        }
        g
    }
}

// ------------------------------------------------------------------------------------------------ best groups

/// The best-`TOP` list `top[0..tl)` and the other groups `rest` are together the groups `all`; every other group's
/// sum is at most every listed sum; there are others only when the list is full.
pub open spec fn top_ok(top: Seq<Partial>, tl: int, rest: Seq<Partial>, all: Seq<Partial>) -> bool {
    &&& 0 <= tl <= TOP && top.len() == TOP
    &&& all.to_multiset() == top.subrange(0, tl).to_multiset().add(rest.to_multiset())
    &&& tl < TOP ==> rest.len() == 0
    &&& forall|r: int, t: int| 0 <= r < rest.len() && 0 <= t < tl ==> #[trigger] rest[r].sum <= #[trigger] top[t].sum
}

/// `top[m]` has the least sum of `top[0..tl)`.
pub open spec fn min_ok(top: Seq<Partial>, tl: int, m: int) -> bool {
    tl > 0 ==> 0 <= m < tl && forall|t: int| 0 <= t < tl ==> top[m].sum <= #[trigger] top[t].sum
}

impl JoinTask {
    /// Offer group `x` to the best-`TOP` list `top[0..tl)` (least sum at `tm`): the new length and least position,
    /// and the group left out (`x` itself, an evicted one, or none when the list grew).
    fn offer(&mut self, x: Partial, tl: usize, tm: usize) -> (r: (usize, usize, Ghost<Option<Partial>>))
        requires old(self).top@.len() == TOP, tl <= TOP, min_ok(old(self).top@, tl as int, tm as int),
        ensures
            final(self).top@.len() == TOP,
            final(self).filings@ == old(self).filings@, final(self).nf == old(self).nf,
            final(self).sv == old(self).sv, final(self).ps == old(self).ps, final(self).cap == old(self).cap,
            final(self).dicts == old(self).dicts, final(self).parts@ == old(self).parts@,
            jinputs_ok(*old(self)) ==> jinputs_ok(*final(self)),
            r.1 <= TOP, min_ok(final(self).top@, r.0 as int, r.1 as int),
            r.2@ is None ==> tl < TOP && r.0 == tl + 1
                && final(self).top@.subrange(0, r.0 as int) == old(self).top@.subrange(0, tl as int).push(x),
            r.2@ matches Some(e) ==> tl == TOP && r.0 == TOP
                && final(self).top@.to_multiset().insert(e) == old(self).top@.to_multiset().insert(x)
                && (forall|t: int| 0 <= t < TOP ==> e.sum <= #[trigger] final(self).top@[t].sum)
                && (forall|t: int| 0 <= t < TOP ==> old(self).top@[tm as int].sum <= #[trigger] final(self).top@[t].sum)
                && e.sum <= old(self).top@[tm as int].sum,
        no_unwind
    {
        broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms,
            vstd::seq_lib::to_multiset_build, vstd::seq_lib::to_multiset_update};
        if tl < TOP {
            let ghost before = self.top@;
            put(&mut self.top, tl, x);
            proof {
                assert(self.top@.subrange(0, tl + 1) =~= before.subrange(0, tl as int).push(x));
            }
            let m = if tl == 0 || x.sum < self.top[tm].sum { tl } else { tm };
            (tl + 1, m, Ghost(None))
        } else if x.sum > self.top[tm].sum {
            let ghost before = self.top@;
            let e = self.top[tm];
            put(&mut self.top, tm, x);
            let mut m: usize = 0;
            let mut i: usize = 1;
            while i < TOP
                invariant
                    self.top@.len() == TOP, 1 <= i <= TOP, m < i,
                    forall|t: int| 0 <= t < i ==> self.top@[m as int].sum <= #[trigger] self.top@[t].sum,
                decreases TOP - i,
            {
                if self.top[i].sum < self.top[m].sum {
                    m = i;
                }
                i = i + 1;
            }
            proof {
                assert(self.top@.subrange(0, TOP as int) =~= self.top@);
                assert forall|t: int| 0 <= t < TOP implies e.sum <= #[trigger] self.top@[t].sum by {
                    if t != tm { assert(self.top@[t] == before[t]); }
                }
            }
            (TOP, m, Ghost(Some(e)))
        } else {
            proof {
                assert(self.top@.subrange(0, TOP as int) =~= self.top@);
            }
            (tl, tm, Ghost(Some(x)))
        }
    }
}

/// Output of a phase-D task: its best groups `top[0..len)`, whether some group's count exceeds int8 / some group's
/// mass exceeds i128, whether its partial buffer overflowed (then it is run again with a larger one), and as ghosts
/// all its groups and the ones not in the list.
pub struct JoinOut {
    pub filings: Vec<Filing>,
    pub top: Vec<Partial>,
    pub len: usize,
    pub cnt_over: bool,
    pub mass_over: bool,
    pub overflow: bool,
    pub groups: Ghost<Seq<Partial>>,
    pub rest: Ghost<Seq<Partial>>,
}

/// The groups of a task: per key, the sum of its filings' contributions; distinct key codes; exact values; flags.
pub open spec fn groups_ok(sv: StoresView, ps: Seq<Literal>, fl: Seq<Filing>, nf: int, out: JoinOut) -> bool {
    let all = out.groups@;
    &&& forall|k: Row, w: int| #[trigger] psum(sv, ps, all, 0, all.len() as int, k, w)
        == isum(0, nf, |x: int| fsum(sv, ps, fl[x], k, w))
    &&& forall|x: int| 0 <= x < all.len() ==> exact_ok(#[trigger] all[x]) && codes_ok(sv, all[x])
        && exists|y: int| 0 <= y < nf && all[x].nm == #[trigger] fl[y].nm
    &&& forall|x: int, y: int| 0 <= x < y < all.len() ==> !same_code(#[trigger] all[x], #[trigger] all[y])
    &&& out.cnt_over == exists|x: int| 0 <= x < all.len() && (#[trigger] all[x]).cnt == CNT_OVER
    &&& out.mass_over == exists|x: int| 0 <= x < all.len() && (#[trigger] all[x]).mass == MASS_OVER
    &&& top_ok(out.top@, out.len as int, out.rest@, all)
}


/// The sum over a range is the sum over the range's elements (so it does not depend on their order).
pub proof fn lemma_psum_tsum(sv: StoresView, ps: Seq<Literal>, a: Seq<Partial>, lo: int, hi: int, k: Row, w: int)
    requires 0 <= lo <= hi <= a.len(),
    ensures psum(sv, ps, a, lo, hi, k, w) == tsum(a.subrange(lo, hi), |x: Partial| pterm(sv, ps, x, k, w)),
    decreases hi - lo,
{
    if hi > lo {
        lemma_psum_tsum(sv, ps, a, lo, hi - 1, k, w);
        assert(a.subrange(lo, hi).drop_last() =~= a.subrange(lo, hi - 1));
    }
}

/// Appending `b[0..g)` to `all` adds its sums.
pub proof fn lemma_psum_append(sv: StoresView, ps: Seq<Literal>, all: Seq<Partial>, b: Seq<Partial>, g: int, k: Row, w: int)
    requires 0 <= g <= b.len(),
    ensures
        psum(sv, ps, all + b.subrange(0, g), 0, all.len() + g, k, w)
            == psum(sv, ps, all, 0, all.len() as int, k, w) + psum(sv, ps, b, 0, g, k, w),
{
    let c = all + b.subrange(0, g);
    lemma_isum_split(0, all.len() as int, all.len() + g, |t: int| pterm(sv, ps, c[t], k, w));
    lemma_isum_ext(0, all.len() as int, |t: int| pterm(sv, ps, c[t], k, w), |t: int| pterm(sv, ps, all[t], k, w));
    lemma_isum_shift(all.len() as int, g, |t: int| pterm(sv, ps, c[t], k, w), |t: int| pterm(sv, ps, b[t], k, w));
}

/// One more group in the best list: the list, the others and all groups stay related.
proof fn lemma_top_step(old_top: Seq<Partial>, new_top: Seq<Partial>, tl: int, tl2: int, tm: int, rest: Seq<Partial>,
    all: Seq<Partial>, x: Partial, e: Option<Partial>)
    requires
        top_ok(old_top, tl, rest, all), min_ok(old_top, tl, tm), new_top.len() == TOP,
        e is None ==> tl < TOP && tl2 == tl + 1 && new_top.subrange(0, tl2) == old_top.subrange(0, tl).push(x),
        e matches Some(ev) ==> tl == TOP && tl2 == TOP
            && new_top.to_multiset().insert(ev) == old_top.to_multiset().insert(x)
            && (forall|t: int| 0 <= t < TOP ==> old_top[tm].sum <= #[trigger] new_top[t].sum)
            && (forall|t: int| 0 <= t < TOP ==> ev.sum <= #[trigger] new_top[t].sum),
    ensures
        top_ok(new_top, tl2, if let Some(ev) = e { rest.push(ev) } else { rest }, all.push(x)),
{
    broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms,
        vstd::seq_lib::to_multiset_build};
    match e {
        None => {
            assert(all.push(x).to_multiset() =~= new_top.subrange(0, tl2).to_multiset().add(rest.to_multiset()));
        },
        Some(ev) => {
            assert(old_top.subrange(0, TOP as int) =~= old_top);
            assert(new_top.subrange(0, TOP as int) =~= new_top);
            let rest2 = rest.push(ev);
            let a = all.to_multiset();
            assert(a == old_top.to_multiset().add(rest.to_multiset()));
            assert(all.push(x).to_multiset() =~= a.insert(x));
            assert(rest2.to_multiset() =~= rest.to_multiset().insert(ev));
            assert(new_top.to_multiset().add(rest2.to_multiset()) =~= new_top.to_multiset().insert(ev).add(rest.to_multiset()));
            assert(old_top.to_multiset().insert(x).add(rest.to_multiset()) =~= a.insert(x));
            assert(all.push(x).to_multiset() =~= new_top.to_multiset().add(rest2.to_multiset()));
            assert forall|r: int, q: int| 0 <= r < rest2.len() && 0 <= q < TOP implies
                #[trigger] rest2[r].sum <= #[trigger] new_top[q].sum by {
                if r < rest.len() {
                    assert(rest[r].sum <= old_top[tm].sum);
                    assert(rest2[r] == rest[r]);
                } else {
                    assert(rest2[r] == ev);
                }
            }
        },
    }
}

/// The empty best list.
proof fn lemma_state_init(top: Seq<Partial>, st: TopState)
    requires top.len() == TOP, st.tl == 0, st.tm == 0, !st.cnt_over, !st.mass_over, st.all@ == Seq::<Partial>::empty(),
        st.rest@ == Seq::<Partial>::empty(),
    ensures state_ok(top, st),
{
    broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};
    assert(top.subrange(0, 0) =~= Seq::<Partial>::empty());
    assert(Seq::<Partial>::empty().to_multiset() =~= vstd::multiset::Multiset::<Partial>::empty());
    assert(Seq::<Partial>::empty().to_multiset().add(Seq::<Partial>::empty().to_multiset()) =~= Seq::<Partial>::empty().to_multiset());
}

/// The flag "some group's count exceeds int8" over the groups.
pub open spec fn any_cnt_over(all: Seq<Partial>) -> bool {
    exists|x: int| 0 <= x < all.len() && (#[trigger] all[x]).cnt == CNT_OVER
}

pub open spec fn any_mass_over(all: Seq<Partial>) -> bool {
    exists|x: int| 0 <= x < all.len() && (#[trigger] all[x]).mass == MASS_OVER
}

proof fn lemma_flags_push(all: Seq<Partial>, x: Partial)
    ensures
        any_cnt_over(all.push(x)) == (any_cnt_over(all) || x.cnt == CNT_OVER),
        any_mass_over(all.push(x)) == (any_mass_over(all) || x.mass == MASS_OVER),
{
    let a2 = all.push(x);
    if any_cnt_over(all) {
        let y = choose|y: int| 0 <= y < all.len() && (#[trigger] all[y]).cnt == CNT_OVER;
        assert(a2[y] == all[y]);
    }
    if any_cnt_over(a2) {
        let y = choose|y: int| 0 <= y < a2.len() && (#[trigger] a2[y]).cnt == CNT_OVER;
        if y < all.len() { assert(all[y] == a2[y]); }
    }
    if x.cnt == CNT_OVER { assert(a2[all.len() as int] == x); }
    if any_mass_over(all) {
        let y = choose|y: int| 0 <= y < all.len() && (#[trigger] all[y]).mass == MASS_OVER;
        assert(a2[y] == all[y]);
    }
    if any_mass_over(a2) {
        let y = choose|y: int| 0 <= y < a2.len() && (#[trigger] a2[y]).mass == MASS_OVER;
        if y < all.len() { assert(all[y] == a2[y]); }
    }
    if x.mass == MASS_OVER { assert(a2[all.len() as int] == x); }
}

/// The best list's state: length, least position, flags, and as ghosts all groups so far and the unlisted ones.
pub struct TopState {
    pub tl: usize,
    pub tm: usize,
    pub cnt_over: bool,
    pub mass_over: bool,
    pub all: Ghost<Seq<Partial>>,
    pub rest: Ghost<Seq<Partial>>,
}

pub open spec fn state_ok(top: Seq<Partial>, st: TopState) -> bool {
    &&& top_ok(top, st.tl as int, st.rest@, st.all@)
    &&& min_ok(top, st.tl as int, st.tm as int)
    &&& st.cnt_over == any_cnt_over(st.all@)
    &&& st.mass_over == any_mass_over(st.all@)
}

impl JoinTask {
    /// The partials of the filings of one name from `fi0` on: `(fi, len, true)` with the filings `[fi0, fi)` (all
    /// of the name of filing `fi0`, `fi` the first of another name or the end) in `parts[0..len)`, or `false` when
    /// the buffer is full.
    fn segment(&mut self, fi0: usize) -> (r: (usize, usize, bool))
        requires jinputs_ok(*old(self)), fi0 < old(self).nf,
        ensures
            jinputs_ok(*final(self)),
            final(self).filings@ == old(self).filings@, final(self).nf == old(self).nf,
            final(self).sv == old(self).sv, final(self).ps == old(self).ps, final(self).cap == old(self).cap,
            final(self).dicts == old(self).dicts, final(self).top@ == old(self).top@,
            r.2 ==> fi0 < r.0 <= old(self).nf && r.1 <= old(self).cap,
            r.2 ==> forall|x: int| fi0 <= x < r.0 ==> (#[trigger] old(self).filings@[x]).nm == old(self).filings@[fi0 as int].nm,
            r.2 ==> (r.0 < old(self).nf ==> old(self).filings@[r.0 as int].nm != old(self).filings@[fi0 as int].nm),
            r.2 ==> forall|x: int| 0 <= x < r.1 ==> exact_ok(#[trigger] final(self).parts@[x]) && codes_ok(old(self).sv@, final(self).parts@[x])
                && final(self).parts@[x].nm == old(self).filings@[fi0 as int].nm,
            r.2 ==> forall|k: Row, w: int| #[trigger] psum(old(self).sv@, old(self).ps@, final(self).parts@, 0, r.1 as int, k, w)
                == isum(fi0 as int, r.0 as int, |x: int| fsum(old(self).sv@, old(self).ps@, old(self).filings@[x], k, w)),
            !r.2 ==> old(self).cap < rows_sum(old(self).filings@, 0, old(self).nf as int),
        no_unwind
    {
        let ghost sv = self.sv@;
        let ghost ps = self.ps@;
        let ghost fl = self.filings@;
        let nm = self.filings[fi0].nm;
        let mut fi = fi0;
        let mut len: usize = 0;
        while fi < self.nf && self.filings[fi].nm == nm
            invariant
                jinputs_ok(*self), self.sv@ == sv, self.ps@ == ps, self.filings@ == fl, fl == old(self).filings@,
                self.nf == old(self).nf, self.sv == old(self).sv, self.ps == old(self).ps, self.cap == old(self).cap,
                self.dicts == old(self).dicts, self.top@ == old(self).top@,
                fi0 <= fi <= self.nf, fi0 < self.nf, fl[fi0 as int].nm == nm, len <= self.cap,
                forall|x: int| fi0 <= x < fi ==> (#[trigger] fl[x]).nm == nm,
                forall|x: int| 0 <= x < len ==> exact_ok(#[trigger] self.parts@[x]) && codes_ok(sv, self.parts@[x])
                    && self.parts@[x].nm == nm,
                forall|k: Row, w: int| #[trigger] psum(sv, ps, self.parts@, 0, len as int, k, w)
                    == isum(fi0 as int, fi as int, |x: int| fsum(sv, ps, fl[x], k, w)),
                len <= rows_sum(fl, fi0 as int, fi as int),
            decreases self.nf - fi,
        {
            let ghost before = self.parts@;
            let ghost len_b = len as int;
            let (l2, ok) = self.join_filing(fi, len);
            proof {
                let r = |x: int| fl[x].rows as int;
                assert(isum(fi0 as int, fi + 1, r) == isum(fi0 as int, fi as int, r) + r(fi as int));
                lemma_rows_sum_mono(fl, 0, fi0 as int, fi + 1, self.nf as int);
            }
            if !ok {
                return (fi, len, false);
            }
            proof {
                assert forall|k: Row, w: int| #[trigger] psum(sv, ps, self.parts@, 0, l2 as int, k, w)
                    == isum(fi0 as int, fi + 1, |x: int| fsum(sv, ps, fl[x], k, w)) by {
                    lemma_seg_step(sv, ps, self.parts@, before, len_b, l2 as int, fl, fi0 as int, fi as int, k, w);
                }
            }
            len = l2;
            fi = fi + 1;
        }
        (fi, len, true)
    }

    /// Sort `parts[0..len)` by key codes and merge equal keys into groups `parts[0..g)`.
    fn group_segment(&mut self, len: usize, Ghost(nm): Ghost<u64>) -> (g: usize)
        requires
            jinputs_ok(*old(self)), len <= old(self).cap,
            forall|x: int| 0 <= x < len ==> exact_ok(#[trigger] old(self).parts@[x]) && codes_ok(old(self).sv@, old(self).parts@[x])
                && old(self).parts@[x].nm == nm,
        ensures
            jinputs_ok(*final(self)),
            final(self).filings@ == old(self).filings@, final(self).nf == old(self).nf,
            final(self).sv == old(self).sv, final(self).ps == old(self).ps, final(self).cap == old(self).cap,
            final(self).dicts == old(self).dicts, final(self).top@ == old(self).top@,
            g <= len,
            forall|x: int| 0 <= x < g ==> exact_ok(#[trigger] final(self).parts@[x]) && codes_ok(final(self).sv@, final(self).parts@[x])
                && final(self).parts@[x].nm == nm,
            forall|x: int, y: int| 0 <= x < y < g ==> key_lt(#[trigger] final(self).parts@[x], #[trigger] final(self).parts@[y]),
            forall|k: Row, w: int| #[trigger] psum(old(self).sv@, old(self).ps@, final(self).parts@, 0, g as int, k, w)
                == psum(old(self).sv@, old(self).ps@, old(self).parts@, 0, len as int, k, w),
        no_unwind
    {
        let ghost sv = self.sv@;
        let ghost ps = self.ps@;
        let ghost unsorted = self.parts@;
        let o = KeyOrder {};
        proof {
            assert forall|q: int| 0 <= q < len implies o.ok(#[trigger] self.parts@.subrange(0, len as int)[q]) by {}
        }
        sort_range(&o, &mut self.parts, &mut self.tmp, 0, len);
        proof {
            lemma_sorted_facts(sv, ps, self.parts@, unsorted, len as int, nm);
        }
        self.aggregate(len, Ghost(nm))
    }

    /// Offer the groups `parts[0..g)` to the best list.
    fn offer_all(&mut self, g: usize, st: TopState) -> (r: TopState)
        requires
            jinputs_ok(*old(self)), g <= old(self).cap, state_ok(old(self).top@, st),
        ensures
            jinputs_ok(*final(self)),
            final(self).filings@ == old(self).filings@, final(self).nf == old(self).nf,
            final(self).sv == old(self).sv, final(self).ps == old(self).ps, final(self).cap == old(self).cap,
            final(self).dicts == old(self).dicts, final(self).parts@ == old(self).parts@,
            state_ok(final(self).top@, r),
            r.all@ == st.all@ + old(self).parts@.subrange(0, g as int),
        no_unwind
    {
        let mut st = st;
        let ghost all0 = st.all@;
        let mut i: usize = 0;
        while i < g
            invariant
                jinputs_ok(*self), self.filings@ == old(self).filings@, self.nf == old(self).nf,
                self.sv == old(self).sv, self.ps == old(self).ps, self.cap == old(self).cap,
                self.dicts == old(self).dicts, self.parts@ == old(self).parts@,
                i <= g, g <= self.cap, state_ok(self.top@, st),
                st.all@ == all0 + self.parts@.subrange(0, i as int),
            decreases g - i,
        {
            let x = self.parts[i];
            let ghost old_top = self.top@;
            let (a, b, e) = self.offer(x, st.tl, st.tm);
            proof {
                lemma_top_step(old_top, self.top@, st.tl as int, a as int, st.tm as int, st.rest@, st.all@, x, e@);
                lemma_flags_push(st.all@, x);
                assert(all0 + self.parts@.subrange(0, i + 1) =~= st.all@.push(x));
            }
            st = TopState {
                tl: a,
                tm: b,
                cnt_over: st.cnt_over || x.cnt == CNT_OVER,
                mass_over: st.mass_over || x.mass == MASS_OVER,
                all: Ghost(st.all@.push(x)),
                rest: Ghost(if let Some(ev) = e@ { st.rest@.push(ev) } else { st.rest@ }),
            };
            i = i + 1;
        }
        st
    }
}

/// One more filing in a segment.
proof fn lemma_seg_step(sv: StoresView, ps: Seq<Literal>, a: Seq<Partial>, before: Seq<Partial>, len_b: int, len: int,
    fl: Seq<Filing>, fi0: int, fi: int, k: Row, w: int)
    requires
        0 <= len_b <= len, fi0 <= fi,
        forall|x: int| 0 <= x < len_b ==> a[x] == before[x],
        psum(sv, ps, before, 0, len_b, k, w) == isum(fi0, fi, |x: int| fsum(sv, ps, fl[x], k, w)),
        psum(sv, ps, a, len_b, len, k, w) == fsum(sv, ps, fl[fi], k, w),
    ensures psum(sv, ps, a, 0, len, k, w) == isum(fi0, fi + 1, |x: int| fsum(sv, ps, fl[x], k, w)),
{
    lemma_psum_frame(sv, ps, a, before, 0, len_b, k, w);
    lemma_isum_split(0, len_b, len, |x: int| pterm(sv, ps, a[x], k, w));
    let ff = |x: int| fsum(sv, ps, fl[x], k, w);
    assert(isum(fi0, fi + 1, ff) == isum(fi0, fi, ff) + ff(fi));
}

/// After sorting: the same sums, the same element facts, sorted by key codes.
proof fn lemma_sorted_facts(sv: StoresView, ps: Seq<Literal>, so: Seq<Partial>, unsorted: Seq<Partial>, len: int, nm: u64)
    requires
        0 <= len <= so.len(), len <= unsorted.len(),
        so.subrange(0, len).to_multiset() == unsorted.subrange(0, len).to_multiset(),
        crate::agent::common::sort::sorted_by(KeyOrder {}, so.subrange(0, len)),
        forall|x: int| 0 <= x < len ==> exact_ok(#[trigger] unsorted[x]) && codes_ok(sv, unsorted[x]) && unsorted[x].nm == nm,
    ensures
        forall|k: Row, w: int| #[trigger] psum(sv, ps, so, 0, len, k, w) == psum(sv, ps, unsorted, 0, len, k, w),
        forall|x: int| 0 <= x < len ==> exact_ok(#[trigger] so[x]) && codes_ok(sv, so[x]) && so[x].nm == nm,
        forall|x: int, y: int| 0 <= x < y < len ==> key_le(#[trigger] so[x], #[trigger] so[y]),
{
    broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};
    assert forall|k: Row, w: int| #[trigger] psum(sv, ps, so, 0, len, k, w) == psum(sv, ps, unsorted, 0, len, k, w) by {
        lemma_psum_tsum(sv, ps, so, 0, len, k, w);
        lemma_psum_tsum(sv, ps, unsorted, 0, len, k, w);
        lemma_tsum_perm(so.subrange(0, len), unsorted.subrange(0, len), |x: Partial| pterm(sv, ps, x, k, w));
    }
    let ss = so.subrange(0, len);
    let us = unsorted.subrange(0, len);
    assert forall|x: int| 0 <= x < len implies exact_ok(#[trigger] so[x]) && codes_ok(sv, so[x]) && so[x].nm == nm by {
        let v = ss[x];
        assert(ss.contains(v));
        assert(ss.to_multiset().count(v) > 0);
        assert(us.to_multiset().count(v) > 0);
        assert(us.contains(v));
        let y = choose|y: int| 0 <= y < us.len() && us[y] == v;
        assert(unsorted[y] == v);
    }
    assert forall|x: int, y: int| 0 <= x < y < len implies key_le(#[trigger] so[x], #[trigger] so[y]) by {
        assert(ss[x] == so[x] && ss[y] == so[y]);
        assert((KeyOrder {}).le(ss[x], ss[y]));
    }
}

impl WorkerTask for JoinTask {
    type Output = JoinOut;

    open spec fn pre(&self) -> bool {
        jinputs_ok(*self)
    }

    open spec fn post(&self, out: JoinOut) -> bool {
        &&& out.top@.len() == TOP
        &&& out.filings@ == self.filings@
        &&& !out.overflow ==> groups_ok(self.sv@, self.ps@, self.filings@, self.nf as int, out)
        &&& out.overflow ==> self.cap < rows_sum(self.filings@, 0, self.nf as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (0, self.nf as u64)
    }

    fn run(self) -> (out: JoinOut) {
        let mut t = self;
        let ghost sv = t.sv@;
        let ghost ps = t.ps@;
        let ghost fl = t.filings@;
        let ghost nf = t.nf as int;
        // one-worker path: answer the task's own pair codes first (phases B and C are skipped)
        if t.need.len() > 0 && t.need.len() == t.dicts.npp && t.lmap.len() == t.dicts.npp {
            let mut fi: usize = 0;
            while fi < t.nf
                invariant
                    jinputs_ok(t), t.sv@ == sv, t.ps@ == ps, t.filings@ == fl, t.nf == nf, fl == self.filings@,
                    nf == self.nf, sv == self.sv@, ps == self.ps@, t.cap == self.cap, t.top == self.top,
                    t.sv == self.sv, t.ps == self.ps, t.need@.len() == t.dicts.npp, t.lmap@.len() == t.dicts.npp,
                decreases nf - fi,
            {
                t.mark_filing(fi);
                fi = fi + 1;
            }
            let dicts = t.dicts;
            answer_needed(dicts, Ghost(sv), &mut t.need, &mut t.lmap);
        }
        // several-worker path: list, sort and answer the task's own pair codes first
        if t.codes.len() > 0 && t.ncodes == 0 && t.codes.len() == t.cans.len() && t.counts.len() == RADIX_BUCKETS {
            let mut n: usize = 0;
            let mut fi: usize = 0;
            while fi < t.nf
                invariant
                    jinputs_ok(t), t.sv@ == sv, t.ps@ == ps, t.filings@ == fl, t.nf == nf, fl == self.filings@,
                    nf == self.nf, sv == self.sv@, ps == self.ps@, t.cap == self.cap, t.top == self.top,
                    t.sv == self.sv, t.ps == self.ps, t.ncodes == 0, n <= t.codes@.len(), t.codes@.len() == t.cans@.len(),
                    t.counts@.len() == RADIX_BUCKETS,
                decreases nf - fi,
            {
                n = t.list_filing(fi, n);
                fi = fi + 1;
            }
            // increasing codes (all below 2^RADIX_BITS for this data) make equal codes neighbours and let
            // `answer_list` gallop forward; the order is not needed for correctness
            radix_sort_low(&mut t.codes, &mut t.cans, &mut t.counts, n);
            let dicts = t.dicts;
            dicts.answer_list(Ghost(sv), &t.codes, n, &mut t.cans);
            t.ncodes = n;
            proof {
                reveal(own_ok);
                assert(pd_ok(t.dicts, sv));
            }
        }
        let mut st = TopState { tl: 0, tm: 0, cnt_over: false, mass_over: false, all: Ghost(Seq::empty()), rest: Ghost(Seq::empty()) };
        proof {
            lemma_state_init(t.top@, st);
        }
        let mut fi: usize = 0;
        while fi < t.nf
            invariant
                jinputs_ok(t), t.sv@ == sv, t.ps@ == ps, t.filings@ == fl, t.nf == nf, fl == self.filings@,
                nf == self.nf, sv == self.sv@, ps == self.ps@,
                fi <= nf, state_ok(t.top@, st), t.cap == self.cap,
                forall|k: Row, w: int| #[trigger] psum(sv, ps, st.all@, 0, st.all@.len() as int, k, w)
                    == isum(0, fi as int, |x: int| fsum(sv, ps, fl[x], k, w)),
                forall|x: int| 0 <= x < st.all@.len() ==> exact_ok(#[trigger] st.all@[x]) && codes_ok(sv, st.all@[x])
                    && exists|y: int| 0 <= y < fi && st.all@[x].nm == #[trigger] fl[y].nm,
                forall|x: int, y: int| 0 <= x < y < st.all@.len() ==> !same_code(#[trigger] st.all@[x], #[trigger] st.all@[y]),
                fi < nf ==> forall|x: int| 0 <= x < st.all@.len() ==> (#[trigger] st.all@[x]).nm < fl[fi as int].nm,
            decreases nf - fi,
        {
            let fi0 = fi;
            let ghost nm = fl[fi0 as int].nm;
            let (fi2, len, ok) = t.segment(fi0);
            if !ok {
                return JoinOut { filings: t.filings, top: t.top, len: st.tl, cnt_over: st.cnt_over, mass_over: st.mass_over, overflow: true,
                    groups: st.all, rest: st.rest };
            }
            fi = fi2;
            let g = t.group_segment(len, Ghost(nm));
            let ghost all0 = st.all@;
            let ghost grp = t.parts@;
            st = t.offer_all(g, st);
            proof {
                lemma_run_step(sv, ps, fl, nf, all0, grp, g as int, st.all@, fi0 as int, fi as int, len as int, nm);
            }
        }
        JoinOut { filings: t.filings, top: t.top, len: st.tl, cnt_over: st.cnt_over, mass_over: st.mass_over, overflow: false,
            groups: st.all, rest: st.rest }
    }
}

/// One segment's groups appended to all groups keep the run's invariant.
proof fn lemma_run_step(sv: StoresView, ps: Seq<Literal>, fl: Seq<Filing>, nf: int, all0: Seq<Partial>, grp: Seq<Partial>,
    g: int, all: Seq<Partial>, fi0: int, fi: int, len: int, nm: u64)
    requires
        0 <= fi0 < fi <= nf, 0 <= g <= grp.len(), all == all0 + grp.subrange(0, g),
        fl[fi0].nm == nm,
        fi < nf ==> fl[fi].nm != nm,
        forall|x: int, y: int| 0 <= x < y < nf ==> (#[trigger] fl[x]).nm <= (#[trigger] fl[y]).nm,
        forall|k: Row, w: int| #[trigger] psum(sv, ps, all0, 0, all0.len() as int, k, w)
            == isum(0, fi0, |x: int| fsum(sv, ps, fl[x], k, w)),
        forall|k: Row, w: int| #[trigger] psum(sv, ps, grp, 0, g, k, w) == isum(fi0, fi, |x: int| fsum(sv, ps, fl[x], k, w)),
        forall|x: int| 0 <= x < all0.len() ==> exact_ok(#[trigger] all0[x]) && codes_ok(sv, all0[x])
            && exists|y: int| 0 <= y < fi0 && all0[x].nm == #[trigger] fl[y].nm,
        forall|x: int, y: int| 0 <= x < y < all0.len() ==> !same_code(#[trigger] all0[x], #[trigger] all0[y]),
        forall|x: int| 0 <= x < all0.len() ==> (#[trigger] all0[x]).nm < nm,
        forall|x: int| 0 <= x < g ==> exact_ok(#[trigger] grp[x]) && codes_ok(sv, grp[x]) && grp[x].nm == nm,
        forall|x: int, y: int| 0 <= x < y < g ==> key_lt(#[trigger] grp[x], #[trigger] grp[y]),
    ensures
        forall|k: Row, w: int| #[trigger] psum(sv, ps, all, 0, all.len() as int, k, w)
            == isum(0, fi, |x: int| fsum(sv, ps, fl[x], k, w)),
        forall|x: int| 0 <= x < all.len() ==> exact_ok(#[trigger] all[x]) && codes_ok(sv, all[x])
            && exists|y: int| 0 <= y < fi && all[x].nm == #[trigger] fl[y].nm,
        forall|x: int, y: int| 0 <= x < y < all.len() ==> !same_code(#[trigger] all[x], #[trigger] all[y]),
        fi < nf ==> forall|x: int| 0 <= x < all.len() ==> (#[trigger] all[x]).nm < fl[fi].nm,
{
    assert forall|k: Row, w: int| #[trigger] psum(sv, ps, all, 0, all.len() as int, k, w)
        == isum(0, fi, |x: int| fsum(sv, ps, fl[x], k, w)) by {
        lemma_psum_append(sv, ps, all0, grp, g, k, w);
        lemma_isum_split(0, fi0, fi, |x: int| fsum(sv, ps, fl[x], k, w));
    }
    assert forall|x: int| 0 <= x < all.len() implies exact_ok(#[trigger] all[x]) && codes_ok(sv, all[x])
        && exists|y: int| 0 <= y < fi && all[x].nm == #[trigger] fl[y].nm by {
        if x >= all0.len() {
            assert(all[x] == grp[x - all0.len()]);
            assert(fl[fi0].nm == all[x].nm);
        } else {
            assert(all[x] == all0[x]);
        }
    }
    assert forall|x: int, y: int| 0 <= x < y < all.len() implies !same_code(#[trigger] all[x], #[trigger] all[y]) by {
        if x >= all0.len() {
            assert(all[x] == grp[x - all0.len()] && all[y] == grp[y - all0.len()]);
            assert(key_lt(grp[x - all0.len()], grp[y - all0.len()]));
        } else if y >= all0.len() {
            assert(all[y] == grp[y - all0.len()] && all[x] == all0[x]);
        } else {
            assert(all[x] == all0[x] && all[y] == all0[y]);
        }
    }
    if fi < nf {
        assert(nm <= fl[fi].nm);
        assert forall|x: int| 0 <= x < all.len() implies (#[trigger] all[x]).nm < fl[fi].nm by {
            if x >= all0.len() {
                assert(all[x] == grp[x - all0.len()]);
            } else {
                assert(all[x] == all0[x]);
            }
        }
    }
}

} // verus!
