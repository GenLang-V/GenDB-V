//! Phase A: the qualifying filings of one range of name codes `[n_lo, n_hi)`. A filing (`fspec::filing_ok`) is a
//! `sub` row `j` with `fy = $3` whose `adsh` has a `num` run of uom `$1` (stored rows `[rs, re)`) and a `pre` adsh
//! code (sub-runs `[sa, sb)`), with at least one selected row (stmt `$2`). Every other `sub` row of the range has no
//! qualifying triple (`zero_j`). The task sorts its filings by name code (phase D groups them by name). (`count_rows`,
//! the selected rows per bucket of pre pair codes for phase B's routing buffers, is no longer called.)
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::text::lex_cmp;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use crate::stores::num::interface as ni;
use crate::stores::pre::interface as pi;
use crate::stores::sub::interface as si;
use crate::stores::num::interface::common::text as ntext;
use crate::stores::pre::interface::common::text as ptext;
use crate::stores::sub::interface::common::text as stext;
use crate::stores::num::interface::common::text::{find_text, text_entry_of, compare_bytes};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::stores::num::interface::common::runs::pair_lt;
use crate::stores::pre::interface::common::cols::u64s as pu64s;
use crate::agent::meaning::{p_uom, p_stmt, p_fy, ps_ok};
use crate::agent::views::*;
use crate::agent::fspec::*;
use crate::agent::common::sums::*;
use crate::agent::common::sort::{sort_range, NameOrder, SortOrder, sorted_by, all_ok};

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// One qualifying filing: `sub` row `j`, its name code `nm`, the stored `num` rows `[rs, re)` of its run of uom
/// `$1`, the `pre` sub-runs `[sa, sb)` of its adsh, and `rows`, the number of rows of those sub-runs with stmt `$2`.
#[derive(Clone, Copy)]
pub struct Filing {
    pub j: u64,
    pub nm: u64,
    pub rs: u64,
    pub re: u64,
    pub sa: u64,
    pub sb: u64,
    pub rows: u64,
    /// The `num` run of the filing (ghost witness).
    pub gr: Ghost<int>,
    /// The `pre` adsh code of the filing (ghost witness).
    pub gb: Ghost<int>,
}

pub fn empty_filing() -> (f: Filing) {
    Filing { j: 0, nm: 0, rs: 0, re: 0, sa: 0, sb: 0, rows: 0, gr: Ghost(0), gb: Ghost(0) }
}

/// Text lists of the pre and sub storages read through the num text module's functions (identical definitions).
pub proof fn lemma_ptext(off: Seq<u64>, bytes: Seq<u8>, n: int)
    requires ptext::text_parts_wf(off, bytes, n), ptext::text_strictly_sorted(off, bytes, n),
    ensures
        ntext::text_parts_wf(off, bytes, n),
        ntext::text_strictly_sorted(off, bytes, n),
        forall|k: int| #[trigger] ntext::text_entry(off, bytes, k) == ptext::text_entry(off, bytes, k),
{
    assert forall|a: int, b: int| 0 <= a < b < n implies
        lex_cmp(#[trigger] ntext::text_entry(off, bytes, a), #[trigger] ntext::text_entry(off, bytes, b)) < 0 by {
        assert(lex_cmp(ptext::text_entry(off, bytes, a), ptext::text_entry(off, bytes, b)) < 0);
    }
}

pub proof fn lemma_stext(off: Seq<u64>, bytes: Seq<u8>, n: int)
    requires stext::text_parts_wf(off, bytes, n),
    ensures
        ntext::text_parts_wf(off, bytes, n),
        forall|k: int| #[trigger] ntext::text_entry(off, bytes, k) == stext::text_entry(off, bytes, k),
{
}

/// `rank[order[k]] = k` for every position `k` of `order` naming a slot of `rank` (the inverse of a permutation;
/// used only as a search hint, so nothing is promised about the contents).
pub fn fill_rank(rank: &mut Vec<u32>, order: &[u64], n: usize)
    requires n == order@.len(),
    ensures final(rank)@.len() == old(rank)@.len(),
    no_unwind
{
    let m = rank.len();
    let mut k: usize = 0;
    while k < n
        invariant n == order@.len(), k <= n, rank@.len() == m,
        decreases n - k,
    {
        let j = order[k];
        if j < m as u64 {
            put(rank, j as usize, k as u32);
        }
        k = k + 1;
    }
}

/// `find_text` with a guess: positions `h` and `h - 1` are compared first, and the binary search runs only when
/// neither holds `key` (same answer as `find_text`).
pub fn find_text_hint(off: &[u64], bytes: &[u8], count: usize, key: &[u8], key_len: usize, h: usize) -> (r: Option<usize>)
    requires
        ntext::text_parts_wf(off@, bytes@, count as int),
        ntext::text_strictly_sorted(off@, bytes@, count as int),
        key_len == key@.len(),
    ensures
        r matches Some(k) ==> k < count && ntext::text_entry(off@, bytes@, k as int) == key@,
        r is None ==> forall|k: int| 0 <= k < count ==> ntext::text_entry(off@, bytes@, k) != key@,
    no_unwind
{
    if h < count {
        let (e, el) = text_entry_of(off, bytes, count, h);
        if el == key_len && compare_bytes(e, el, key, key_len) == 0 {
            proof { lemma_lex_cmp_zero(e@, key@); }
            return Some(h);
        }
    }
    if h >= 1 && h - 1 < count {
        let (e, el) = text_entry_of(off, bytes, count, h - 1);
        if el == key_len && compare_bytes(e, el, key, key_len) == 0 {
            proof { lemma_lex_cmp_zero(e@, key@); }
            return Some(h - 1);
        }
    }
    find_text(off, bytes, count, key, key_len)
}

/// The run of `[0, nruns)` whose adsh code is `a` (strictly increasing codes), by binary search.
pub fn find_run(run_adsh: &[u64], nruns: usize, a: u64) -> (r: Option<usize>)
    requires
        nruns <= run_adsh@.len(),
        forall|x: int, y: int| 0 <= x < y < nruns ==> #[trigger] run_adsh@[x] < #[trigger] run_adsh@[y],
    ensures
        r matches Some(k) ==> k < nruns && run_adsh@[k as int] == a,
        r is None ==> forall|k: int| 0 <= k < nruns ==> #[trigger] run_adsh@[k] != a,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = nruns;
    while lo < hi
        invariant
            lo <= hi <= nruns <= run_adsh@.len(),
            forall|x: int, y: int| 0 <= x < y < nruns ==> #[trigger] run_adsh@[x] < #[trigger] run_adsh@[y],
            forall|k: int| 0 <= k < lo ==> #[trigger] run_adsh@[k] < a,
            forall|k: int| hi <= k < nruns ==> #[trigger] run_adsh@[k] > a,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let x = run_adsh[mid];
        if x == a {
            return Some(mid);
        } else if x < a {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    None
}

/// The bucket of pair code `c`: the last `v < nb` with `cuts[v] <= c` (0 when none). Performance only.
pub fn bucket_of(cuts: &Vec<u64>, nb: usize, c: u64) -> (v: usize)
    requires 1 <= nb, nb + 1 == cuts@.len(),
    ensures v < nb,
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = nb;
    while hi - lo > 1
        invariant lo < hi <= nb, nb + 1 == cuts@.len(),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if cuts[mid] <= c {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    lo
}

/// Inputs and buffers of a phase-A task (slices of stored parts, moved into the task).
pub struct FilingTask {
    pub fy: &'static [i32],
    pub fy_valid: &'static [u8],
    pub name_codes: &'static [u64],
    pub sadsh_off: &'static [u64],
    pub sadsh_bytes: &'static [u8],
    pub ns: usize,
    /// `sub` rows in adsh order and its length; `rank` (empty, or one slot per `sub` row) is filled by the task with
    /// its inverse (search hints only).
    pub adsh_order: &'static [u64],
    pub norder: usize,
    pub rank: Vec<u32>,
    pub fy_param: i64,
    pub n_lo: u64,
    pub n_hi: u64,
    pub nadsh_off: &'static [u64],
    pub nadsh_bytes: &'static [u8],
    pub nadsh_count: usize,
    pub run_adsh: &'static [u64],
    pub run_start: &'static [u64],
    pub nruns: usize,
    pub padsh_off: &'static [u64],
    pub padsh_bytes: &'static [u8],
    pub padsh_count: usize,
    pub adsh_subs: &'static [u64],
    pub sub_start: &'static [u64],
    pub sub_group: &'static [u64],
    pub nsubs: usize,
    pub group_stmt: &'static [u64],
    pub stmt_key: u64,
    pub pre_tv: &'static [u64],
    pub npre: usize,
    pub cuts: Vec<u64>,
    pub nbuckets: usize,
    pub out: Vec<Filing>,
    pub tmp: Vec<Filing>,
    pub cap: usize,
    pub counts: Vec<u64>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
    /// The uom code of `$1` and its first run (ghost).
    pub u: Ghost<int>,
    pub ur_lo: Ghost<int>,
}

/// `stmt_key` selects exactly the (stmt, rfile) groups whose stmt is `$2`.
pub open spec fn stmt_key_ok(sv: StoresView, ps: Seq<Literal>, key: u64) -> bool {
    forall|g: int| 0 <= g < pi::group_count(sv.pre)
        ==> ((#[trigger] pu64s(sv.pre, pi::P_GROUP_STMT)[g] == key) == (pi::group_stmt_of(sv.pre, g) == Val::Text(p_stmt(ps))))
}

/// The task's slices are the storages' parts, and its parameters decode `$1`, `$2`, `$3`.
pub open spec fn inputs_ok(t: FilingTask) -> bool {
    let sv = t.sv@;
    let ps = t.ps@;
    let np = sv.num;
    let pp = sv.pre;
    let sp = sv.sub;
    let u = t.u@;
    let ur_lo = t.ur_lo@;
    &&& layouts(sv) && adsh_unique(sv) && ps_ok(ps)
    &&& t.fy@ == crate::stores::sub::interface::common::cols::i32_part(sp[si::P_FY as int])
    &&& t.fy_valid@ == stext::u8_part(sp[si::P_FY_VALID as int])
    &&& t.name_codes@ == stext::u64_part(sp[si::P_NAME_CODES as int])
    &&& t.sadsh_off@ == stext::u64_part(sp[si::P_ADSH_OFF as int])
    &&& t.sadsh_bytes@ == stext::u8_part(sp[si::P_ADSH_BYTES as int])
    &&& t.ns == s_count(sv)
    &&& t.fy_param == p_fy(ps)
    &&& t.n_lo <= t.n_hi
    &&& t.nadsh_off@ == ntext::u64_part(np[ni::P_ADSH_OFF as int])
    &&& t.nadsh_bytes@ == ntext::u8_part(np[ni::P_ADSH_BYTES as int])
    &&& t.nadsh_count == ni::adsh_count(np)
    &&& 0 <= u < ni::uom_count(np) && ni::dict_entry(np, ni::P_UOM_OFF, u) == p_uom(ps)
    &&& ur_lo == ni::u64s(np, ni::P_UOM_RUNS)[u]
    &&& ur_lo + t.nruns == ni::u64s(np, ni::P_UOM_RUNS)[u + 1]
    &&& t.run_adsh@ == ni::u64s(np, ni::P_RUN_ADSH).subrange(ur_lo, ur_lo + t.nruns)
    &&& t.run_start@ == n_start(sv).subrange(ur_lo, ur_lo + t.nruns + 1)
    &&& t.padsh_off@ == ptext::u64_part(pp[pi::P_ADSH_OFF as int])
    &&& t.padsh_bytes@ == ptext::u8_part(pp[pi::P_ADSH_BYTES as int])
    &&& t.padsh_count == pi::adsh_count(pp)
    &&& t.adsh_subs@ == pu64s(pp, pi::P_ADSH_SUBS)
    &&& t.sub_start@ == p_start(sv)
    &&& t.sub_group@ == pu64s(pp, pi::P_SUB_GROUP)
    &&& t.nsubs == pi::sub_count(pp)
    &&& t.npre == p_count(sv)
    &&& t.group_stmt@ == pu64s(pp, pi::P_GROUP_STMT)
    &&& stmt_key_ok(sv, ps, t.stmt_key)
    &&& t.pre_tv@ == pu64s(pp, pi::P_TV)
    &&& t.nbuckets >= 1 && t.cuts@.len() == t.nbuckets + 1 && t.counts@.len() == t.nbuckets
    &&& t.out@.len() == t.cap && t.tmp@.len() == t.cap
    &&& t.adsh_order@.len() == t.norder
}

/// The facts of the inputs the searches need.
proof fn lemma_inputs(t: FilingTask)
    requires inputs_ok(t),
    ensures
        ntext::text_parts_wf(t.sadsh_off@, t.sadsh_bytes@, t.ns as int),
        forall|j: int| #[trigger] ntext::text_entry(t.sadsh_off@, t.sadsh_bytes@, j) == s_adsh(t.sv@, j),
        ntext::text_parts_wf(t.nadsh_off@, t.nadsh_bytes@, t.nadsh_count as int),
        ntext::text_strictly_sorted(t.nadsh_off@, t.nadsh_bytes@, t.nadsh_count as int),
        ntext::text_parts_wf(t.padsh_off@, t.padsh_bytes@, t.padsh_count as int),
        ntext::text_strictly_sorted(t.padsh_off@, t.padsh_bytes@, t.padsh_count as int),
        forall|b: int| #[trigger] ntext::text_entry(t.padsh_off@, t.padsh_bytes@, b)
            == crate::stores::pre::interface::common::cols::list_entry(t.sv@.pre, pi::P_ADSH_OFF, b),
        t.fy@.len() == t.ns && t.fy_valid@.len() == t.ns && t.name_codes@.len() == t.ns,
        t.adsh_subs@.len() == t.padsh_count + 1,
        t.run_adsh@.len() == t.nruns && t.run_start@.len() == t.nruns + 1,
        t.sub_start@.len() == pi::sub_count(t.sv@.pre) + 1,
        t.pre_tv@.len() == p_count(t.sv@),
        layouts(t.sv@), pi::pre_layout_ok(t.sv@.pre), ni::num_layout_ok(t.sv@.num), si::sub_layout_ok(t.sv@.sub),
        crate::stores::pre::interface::common::runs::runs_partition_ok(p_start(t.sv@), pi::sub_count(t.sv@.pre), p_count(t.sv@)),
        t.sub_group@.len() == pi::sub_count(t.sv@.pre),
        t.group_stmt@.len() == pi::group_count(t.sv@.pre),
        forall|s: int| 0 <= s < pi::sub_count(t.sv@.pre) ==> #[trigger] t.sub_group@[s] < pi::group_count(t.sv@.pre),
        0 <= t.ur_lo@ <= t.ur_lo@ + t.nruns <= ni::run_count(t.sv@.num),
{
    let sv = t.sv@;
    let sp = sv.sub;
    let pp = sv.pre;
    let np = sv.num;
    assert(si::sub_layout_ok(sp));
    assert(pi::pre_layout_ok(pp));
    assert(ni::num_layout_ok(np));
    lemma_stext(t.sadsh_off@, t.sadsh_bytes@, t.ns as int);
    lemma_ptext(t.padsh_off@, t.padsh_bytes@, t.padsh_count as int);
    ni::lemma_uom_runs(np, t.u@);
    assert(pi::sub_count(pp) == pu64s(pp, pi::P_SUB_GROUP).len());
    assert forall|s: int| 0 <= s < pi::sub_count(pp) implies #[trigger] t.sub_group@[s] < pi::group_count(pp) by {
        assert(pu64s(pp, pi::P_SUB_ADSH)[s] < pi::adsh_count(pp) && pu64s(pp, pi::P_SUB_GROUP)[s] < pi::group_count(pp));
    }
}

// ------------------------------------------------------------------------------------------------ rows without filing

/// No `num` dictionary adsh is the row's adsh: no run, so no qualifying triple.
proof fn lemma_zero_no_num(sv: StoresView, ps: Seq<Literal>, j: int)
    requires
        layouts(sv),
        forall|a: int| 0 <= a < ni::adsh_count(sv.num) ==> #[trigger] ni::dict_entry(sv.num, ni::P_ADSH_OFF, a) != s_adsh(sv, j),
    ensures zero_j(sv, ps, j),
{
    assert forall|i: int, l: int| 0 <= i < n_count(sv) && 0 <= l < p_count(sv) implies !#[trigger] pq(sv, ps, i, j, l) by {
        crate::stores::num::interface::common::runs::lemma_run_of(n_start(sv), ni::run_count(sv.num), n_count(sv), i);
        lemma_run_codes(sv.num, n_run(sv, i));
    }
}

/// The row's adsh has no run of uom `$1`: no qualifying triple.
proof fn lemma_zero_no_run(sv: StoresView, ps: Seq<Literal>, j: int, u: int, a: int)
    requires
        layouts(sv),
        0 <= u < ni::uom_count(sv.num), ni::dict_entry(sv.num, ni::P_UOM_OFF, u) == p_uom(ps),
        0 <= a < ni::adsh_count(sv.num), ni::dict_entry(sv.num, ni::P_ADSH_OFF, a) == s_adsh(sv, j),
        forall|r: int| ni::u64s(sv.num, ni::P_UOM_RUNS)[u] <= r < ni::u64s(sv.num, ni::P_UOM_RUNS)[u + 1]
            ==> #[trigger] ni::u64s(sv.num, ni::P_RUN_ADSH)[r] != a,
    ensures zero_j(sv, ps, j),
{
    let np = sv.num;
    ni::lemma_uom_runs(np, u);
    assert forall|i: int, l: int| 0 <= i < n_count(sv) && 0 <= l < p_count(sv) implies !#[trigger] pq(sv, ps, i, j, l) by {
        crate::stores::num::interface::common::runs::lemma_run_of(n_start(sv), ni::run_count(np), n_count(sv), i);
        let r = n_run(sv, i);
        lemma_run_codes(np, r);
        ntext::lemma_dict_codes(ntext::u64_part(np[ni::P_UOM_OFF as int]), ntext::u8_part(np[ni::P_UOM_OFF + 1]),
            ni::uom_count(np), ni::u64s(np, ni::P_RUN_UOM)[r] as int, u);
        ntext::lemma_dict_codes(ntext::u64_part(np[ni::P_ADSH_OFF as int]), ntext::u8_part(np[ni::P_ADSH_OFF + 1]),
            ni::adsh_count(np), ni::u64s(np, ni::P_RUN_ADSH)[r] as int, a);
    }
}

/// No `pre` dictionary adsh is the row's adsh: no qualifying triple.
proof fn lemma_zero_no_pre(sv: StoresView, ps: Seq<Literal>, j: int)
    requires
        layouts(sv),
        forall|b: int| 0 <= b < pi::adsh_count(sv.pre)
            ==> #[trigger] crate::stores::pre::interface::common::cols::list_entry(sv.pre, pi::P_ADSH_OFF, b) != s_adsh(sv, j),
    ensures zero_j(sv, ps, j),
{
    let pp = sv.pre;
    assert forall|i: int, l: int| 0 <= i < n_count(sv) && 0 <= l < p_count(sv) implies !#[trigger] pq(sv, ps, i, j, l) by {
        crate::stores::pre::interface::common::runs::lemma_run_of(p_start(sv), pi::sub_count(pp), p_count(sv), l);
        let s = p_sub(sv, l);
        assert(pi::pre_layout_ok(pp));
        assert(pu64s(pp, pi::P_SUB_ADSH)[s] < pi::adsh_count(pp) && pu64s(pp, pi::P_SUB_GROUP)[s] < pi::group_count(pp));
    }
}

/// The row's pre sub-runs have no selected row: no qualifying triple.
proof fn lemma_zero_no_rows(sv: StoresView, ps: Seq<Literal>, j: int, b: int)
    requires
        layouts(sv), 0 <= b < pi::adsh_count(sv.pre),
        crate::stores::pre::interface::common::cols::list_entry(sv.pre, pi::P_ADSH_OFF, b) == s_adsh(sv, j),
        sel_rows(sv, ps, pu64s(sv.pre, pi::P_ADSH_SUBS)[b] as int, pu64s(sv.pre, pi::P_ADSH_SUBS)[b + 1] as int) == 0,
    ensures zero_j(sv, ps, j),
{
    let pp = sv.pre;
    let g = pu64s(pp, pi::P_ADSH_SUBS);
    let st = p_start(sv);
    lemma_subs_bounds(sv, b);
    let (sa, sb) = (g[b] as int, g[b + 1] as int);
    assert forall|s: int| sa <= s < sb implies #[trigger] sel_len(sv, ps, s) >= 0 by {
        assert(crate::stores::pre::interface::common::runs::runs_partition_ok(st, pi::sub_count(pp), p_count(sv)));
        assert(st[s] < st[s + 1]);
    }
    assert forall|i: int, l: int| 0 <= i < n_count(sv) && 0 <= l < p_count(sv) implies !#[trigger] pq(sv, ps, i, j, l) by {
        if pq(sv, ps, i, j, l) {
            if !(st[sa] <= l < st[sb]) {
                lemma_outside_adsh(sv, b, l);
            }
            crate::stores::pre::interface::common::runs::lemma_run_of(st, pi::sub_count(pp), p_count(sv), l);
            let s = p_sub(sv, l);
            // the sub-run of l lies in [sa, sb)
            if s < sa {
                assert(st[s + 1] <= st[sa]) by {
                    if s + 1 < sa { assert(crate::stores::pre::interface::common::runs::runs_partition_ok(st, pi::sub_count(pp), p_count(sv))); assert(st[s + 1] < st[sa]); }
                }
            } else if s >= sb {
                assert(st[sb] <= st[s]) by {
                    if sb < s { assert(crate::stores::pre::interface::common::runs::runs_partition_ok(st, pi::sub_count(pp), p_count(sv))); assert(st[sb] < st[s]); }
                }
            }
            lemma_isum_zero_terms(sa, sb, |x: int| sel_len(sv, ps, x), s);
            assert(crate::stores::pre::interface::common::runs::runs_partition_ok(st, pi::sub_count(pp), p_count(sv)));
            assert(st[s] < st[s + 1]);
        }
    }
}

impl FilingTask {
    /// The filing of `sub` row `j` (with `fy = $3`), or `None` when the row has no qualifying triple.
    fn visit(&self, j: usize) -> (r: Option<Filing>)
        requires inputs_ok(*self), j < self.ns, s_fy(self.sv@, j as int) == Val::Int(p_fy(self.ps@)),
        ensures
            r matches Some(f) ==> filing_ok(self.sv@, self.ps@, f) && f.j == j,
            r is None ==> zero_j(self.sv@, self.ps@, j as int),
        no_unwind
    {
        let ghost sv = self.sv@;
        let ghost ps = self.ps@;
        let ghost np = sv.num;
        let ghost pp = sv.pre;
        proof { lemma_inputs(*self); }
        let (key, key_len) = text_entry_of(self.sadsh_off, self.sadsh_bytes, self.ns, j);
        let hint: usize = if j < self.rank.len() { self.rank[j] as usize } else { 0 };
        let a = match find_text_hint(self.nadsh_off, self.nadsh_bytes, self.nadsh_count, key, key_len, hint) {
            Some(a) => a,
            None => {
                proof {
                    assert(key@ == s_adsh(sv, j as int));
                    assert forall|aa: int| 0 <= aa < ni::adsh_count(sv.num) implies
                        #[trigger] ni::dict_entry(sv.num, ni::P_ADSH_OFF, aa) != s_adsh(sv, j as int) by {
                        assert(ntext::text_entry(self.nadsh_off@, self.nadsh_bytes@, aa) != key@);
                    }
                    lemma_zero_no_num(sv, ps, j as int);
                }
                return None;
            },
        };
        let ghost u = self.u@;
        let ghost ur_lo = self.ur_lo@;
        proof {
            ni::lemma_uom_runs(np, u);
            let ra = ni::u64s(np, ni::P_RUN_ADSH);
            let ru = ni::u64s(np, ni::P_RUN_UOM);
            assert forall|x: int, y: int| 0 <= x < y < self.nruns implies #[trigger] self.run_adsh@[x] < #[trigger] self.run_adsh@[y] by {
                assert(ru[ur_lo + x] == u && ru[ur_lo + y] == u);
                assert(pair_lt(ru[ur_lo + x], ra[ur_lo + x], ru[ur_lo + y], ra[ur_lo + y]));
            }
        }
        let r = match find_run(self.run_adsh, self.nruns, a as u64) {
            Some(r) => r,
            None => {
                proof {
                    assert forall|rr: int| ni::u64s(np, ni::P_UOM_RUNS)[u] <= rr < ni::u64s(np, ni::P_UOM_RUNS)[u + 1]
                        implies #[trigger] ni::u64s(np, ni::P_RUN_ADSH)[rr] != a as int by {
                        assert(self.run_adsh@[rr - ur_lo] == ni::u64s(np, ni::P_RUN_ADSH)[rr]);
                    }
                    lemma_zero_no_run(sv, ps, j as int, u, a as int);
                }
                return None;
            },
        };
        let b = match find_text_hint(self.padsh_off, self.padsh_bytes, self.padsh_count, key, key_len, a) {
            Some(b) => b,
            None => {
                proof {
                    assert(key@ == s_adsh(sv, j as int));
                    assert forall|bb: int| 0 <= bb < pi::adsh_count(sv.pre) implies
                        #[trigger] crate::stores::pre::interface::common::cols::list_entry(sv.pre, pi::P_ADSH_OFF, bb) != s_adsh(sv, j as int) by {
                        assert(ntext::text_entry(self.padsh_off@, self.padsh_bytes@, bb) != key@);
                    }
                    lemma_zero_no_pre(sv, ps, j as int);
                }
                return None;
            },
        };
        let ghost gr = ur_lo + r;
        proof {
            assert(key@ == s_adsh(sv, j as int));
            pi::lemma_adsh_subs(pp, b as int);
            lemma_subs_bounds(sv, b as int);
            ni::lemma_uom_runs(np, u);
            assert(ni::u64s(np, ni::P_RUN_UOM)[gr] == u);
        }
        let sa = self.adsh_subs[b];
        let sb = self.adsh_subs[b + 1];
        assert(sb <= self.nsubs);
        let mut rows: u64 = 0;
        let mut s = sa as usize;
        while s < sb as usize
            invariant
                inputs_ok(*self), sa <= s <= sb <= pi::sub_count(pp), sb <= self.nsubs,
                sv == self.sv@, ps == self.ps@, pp == sv.pre,
                layouts(sv), pi::pre_layout_ok(pp),
                sa == pu64s(pp, pi::P_ADSH_SUBS)[b as int], sb == pu64s(pp, pi::P_ADSH_SUBS)[b + 1],
                b < pi::adsh_count(pp),
                rows == sel_rows(sv, ps, sa as int, s as int),
                rows <= p_start(sv)[s as int] - p_start(sv)[sa as int],
            decreases sb - s,
        {
            proof {
                lemma_inputs(*self);
                lemma_sub_step(sv, s as int);
                assert(sub_stmt(sv, s as int) == pi::group_stmt_of(pp, self.sub_group@[s as int] as int));
                assert(self.sub_group@[s as int] < pi::group_count(pp));
                assert(sel_rows(sv, ps, sa as int, s + 1) == sel_rows(sv, ps, sa as int, s as int) + sel_len(sv, ps, s as int));
            }
            if self.group_stmt[self.sub_group[s] as usize] == self.stmt_key {
                let q0 = self.sub_start[s];
                let q1 = self.sub_start[s + 1];
                rows = rows + (q1 - q0);
            }
            s = s + 1;
        }
        if rows == 0 {
            proof { lemma_zero_no_rows(sv, ps, j as int, b as int); }
            return None;
        }
        Some(Filing {
            j: j as u64,
            nm: self.name_codes[j],
            rs: self.run_start[r],
            re: self.run_start[r + 1],
            sa,
            sb,
            rows,
            gr: Ghost(gr),
            gb: Ghost(b as int),
        })
    }

    /// Selected rows of filing `f` per bucket, added to `counts` (performance only).
    fn count_rows(&mut self, f: Filing)
        requires inputs_ok(*old(self)), filing_ok(old(self).sv@, old(self).ps@, f),
        ensures inputs_ok(*final(self)), final(self).out@ == old(self).out@, final(self).sv == old(self).sv,
            final(self).ps == old(self).ps, final(self).cap == old(self).cap, final(self).n_lo == old(self).n_lo,
            final(self).n_hi == old(self).n_hi, final(self).ns == old(self).ns,
        no_unwind
    {
        // one bucket: its count is the filing's selected rows (no walk over the rows)
        if self.nbuckets == 1 {
            let c = self.counts[0];
            put(&mut self.counts, 0, if c <= u64::MAX - f.rows { c + f.rows } else { u64::MAX });
            return;
        }
        let ghost sv = self.sv@;
        proof {
            lemma_inputs(*self);
            lemma_subs_bounds(sv, f.gb@);
        }
        assert(f.sb <= self.nsubs);
        let mut s = f.sa as usize;
        while s < f.sb as usize
            invariant
                inputs_ok(*self), self.out@ == old(self).out@, self.sv == old(self).sv, self.ps == old(self).ps,
                self.cap == old(self).cap, self.n_lo == old(self).n_lo, self.n_hi == old(self).n_hi, self.ns == old(self).ns,
                f.sa <= s <= f.sb <= pi::sub_count(sv.pre), sv == self.sv@,
            decreases f.sb - s,
        {
            proof {
                lemma_inputs(*self);
                assert(p_start(sv)[s as int] < p_start(sv)[s + 1]);
                assert(p_start(sv)[s + 1] <= p_count(sv)) by {
                    if s + 1 < pi::sub_count(sv.pre) { assert(p_start(sv)[s + 1] < p_start(sv)[pi::sub_count(sv.pre)]); }
                }
            }
            if self.group_stmt[self.sub_group[s] as usize] == self.stmt_key {
                assert(self.sub_start[s + 1] <= self.npre);
                let q0 = self.sub_start[s] as usize;
                let q1 = self.sub_start[s + 1] as usize;
                let mut q = q0;
                while q < q1
                    invariant
                        inputs_ok(*self), self.out@ == old(self).out@, self.sv == old(self).sv, self.ps == old(self).ps,
                        self.cap == old(self).cap, self.n_lo == old(self).n_lo, self.n_hi == old(self).n_hi,
                        self.ns == old(self).ns, q1 <= p_count(sv), q0 <= q <= q1, sv == self.sv@,
                        self.pre_tv@.len() == p_count(sv),
                    decreases q1 - q,
                {
                    let v = bucket_of(&self.cuts, self.nbuckets, self.pre_tv[q]);
                    let c = self.counts[v];
                    if c < u64::MAX {
                        put(&mut self.counts, v, c + 1);
                    }
                    q = q + 1;
                }
            }
            s = s + 1;
        }
    }
}

/// Output of a phase-A task: filings `filings[0..len)` sorted by name code (a permutation of the ghost list
/// `pushed`, in `sub` row order), selected rows per bucket, rows of its largest name, and whether its buffer
/// overflowed (then the filings are incomplete and the task is run again with a larger buffer).
pub struct FilingOut {
    pub filings: Vec<Filing>,
    pub len: usize,
    pub counts: Vec<u64>,
    pub max_seg: u64,
    pub overflow: bool,
    pub pushed: Ghost<Seq<Filing>>,
}

/// The facts of a phase-A output for `sub` rows with name codes in `[n_lo, n_hi)`.
pub open spec fn filings_ok(sv: StoresView, ps: Seq<Literal>, n_lo: int, n_hi: int, out: FilingOut) -> bool {
    let p = out.pushed@;
    let fl = out.filings@.subrange(0, out.len as int);
    &&& out.len <= out.filings@.len()
    &&& fl.to_multiset() == p.to_multiset()
    &&& forall|x: int, y: int| 0 <= x < y < out.len ==> (#[trigger] out.filings@[x]).nm <= (#[trigger] out.filings@[y]).nm
    &&& forall|t: int| 0 <= t < p.len() ==> filing_ok(sv, ps, #[trigger] p[t]) && n_lo <= p[t].nm < n_hi
    &&& forall|x: int, y: int| 0 <= x < y < p.len() ==> (#[trigger] p[x]).j < (#[trigger] p[y]).j
    &&& !out.overflow ==> forall|j: int| 0 <= j < s_count(sv) && n_lo <= #[trigger] stext::u64_part(sv.sub[si::P_NAME_CODES as int])[j] < n_hi
        ==> (zero_j(sv, ps, j) || exists|t: int| 0 <= t < p.len() && p[t].j == j)
    &&& 0 <= tsum(p, |f: Filing| rows_of(f)) <= p_count(sv)
}

impl WorkerTask for FilingTask {
    type Output = FilingOut;

    open spec fn pre(&self) -> bool {
        inputs_ok(*self)
    }

    open spec fn post(&self, out: FilingOut) -> bool {
        &&& filings_ok(self.sv@, self.ps@, self.n_lo as int, self.n_hi as int, out)
        &&& out.filings@.len() == self.cap
        &&& out.overflow ==> self.cap < self.ns
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.n_lo, self.n_hi)
    }

    fn run(self) -> (out: FilingOut) {
        let mut t = self;
        let ghost sv = t.sv@;
        let ghost ps = t.ps@;
        let ghost mut p: Seq<Filing> = Seq::empty();
        let mut len: usize = 0;
        let mut overflow = false;
        // search hints: rank[j] = position of sub row j in adsh order, the position of its adsh in the num and pre
        // adsh dictionaries when those hold every sub adsh (checked by `find_text_hint`)
        fill_rank(&mut t.rank, t.adsh_order, t.norder);
        let mut j: usize = 0;
        proof { lemma_inputs(t); }
        while j < t.ns
            invariant
                inputs_ok(t), t.sv@ == sv, t.ps@ == ps, j <= t.ns, len <= t.cap, t.out@.len() == t.cap,
                t.n_lo == self.n_lo, t.n_hi == self.n_hi, t.ns == self.ns, t.cap == self.cap,
                t.fy@.len() == t.ns && t.fy_valid@.len() == t.ns && t.name_codes@.len() == t.ns,
                p.len() == len, len <= j, overflow ==> t.cap < t.ns,
                forall|x: int| 0 <= x < len ==> t.out@[x] == p[x],
                forall|x: int| 0 <= x < p.len() ==> filing_ok(sv, ps, #[trigger] p[x]) && t.n_lo <= p[x].nm < t.n_hi
                    && p[x].j < j,
                forall|x: int, y: int| 0 <= x < y < p.len() ==> (#[trigger] p[x]).j < (#[trigger] p[y]).j,
                !overflow ==> forall|j2: int| 0 <= j2 < j && t.n_lo <= #[trigger] t.name_codes@[j2] < t.n_hi
                    ==> (zero_j(sv, ps, j2) || exists|x: int| 0 <= x < p.len() && p[x].j == j2),
            decreases t.ns - j,
        {
            let nm = t.name_codes[j];
            let ghost before = p;
            let ghost of = overflow;
            if t.n_lo <= nm && nm < t.n_hi {
                if t.fy_valid[j] != 0 && t.fy[j] as i64 == t.fy_param {
                    proof {
                        assert(s_fy(sv, j as int) == Val::Int(p_fy(ps)));
                    }
                    match t.visit(j) {
                        Some(f) => {
                            if len < t.cap {
                                put(&mut t.out, len, f);
                                proof { p = p.push(f); }
                                len = len + 1;
                            } else {
                                overflow = true;
                            }
                        },
                        None => {},
                    }
                } else {
                    proof {
                        assert(s_fy(sv, j as int) != Val::Int(p_fy(ps)));
                        assert forall|i: int, l: int| 0 <= i < n_count(sv) && 0 <= l < p_count(sv)
                            implies !#[trigger] pq(sv, ps, i, j as int, l) by {}
                    }
                }
            }
            proof {
                assert forall|x: int, y: int| 0 <= x < y < p.len() implies (#[trigger] p[x]).j < (#[trigger] p[y]).j by {
                    if y == p.len() - 1 && p.len() > before.len() {
                        assert(p[x] == before[x]);
                    }
                }
                if !overflow {
                    assert forall|j2: int| 0 <= j2 < j + 1 && t.n_lo <= #[trigger] t.name_codes@[j2] < t.n_hi
                        implies (zero_j(sv, ps, j2) || exists|x: int| 0 <= x < p.len() && p[x].j == j2) by {
                        if j2 < j {
                            if !zero_j(sv, ps, j2) {
                                let x = choose|x: int| 0 <= x < before.len() && before[x].j == j2;
                                assert(p[x] == before[x]);
                            }
                        } else if p.len() > before.len() {
                            assert(p[p.len() - 1].j == j);
                        }
                    }
                }
            }
            j = j + 1;
        }
        proof { lemma_rows_le_np(sv, ps, p); }
        let ghost unsorted = t.out@;
        proof {
            assert(unsorted.subrange(0, len as int) =~= p);
        }
        let o = NameOrder {};
        proof {
            assert forall|q: int| 0 <= q < len implies o.ok(#[trigger] t.out@.subrange(0, len as int)[q]) by {}
        }
        sort_range(&o, &mut t.out, &mut t.tmp, 0, len);
        let ghost so = t.out@;
        proof {
            assert(so.subrange(0, len as int).to_multiset() == p.to_multiset());
            assert forall|x: int, y: int| 0 <= x < y < len implies (#[trigger] so[x]).nm <= (#[trigger] so[y]).nm by {
                assert(so.subrange(0, len as int)[x] == so[x] && so.subrange(0, len as int)[y] == so[y]);
                assert(o.le(so.subrange(0, len as int)[x], so.subrange(0, len as int)[y]));
            }
            assert forall|x: int| 0 <= x < len implies filing_ok(sv, ps, #[trigger] so[x]) by {
                let v = so.subrange(0, len as int)[x];
                assert(so.subrange(0, len as int).contains(v));
                assert(p.to_multiset().count(v) > 0);
                assert(p.contains(v));
            }
        }
        // performance information: selected rows per bucket and of the largest name
        let mut max_seg: u64 = 0;
        let mut i: usize = 0;
        while i < len
            invariant
                inputs_ok(t), t.sv@ == sv, t.ps@ == ps, i <= len <= t.cap, t.out@ == so, so.len() == t.cap,
                forall|x: int| 0 <= x < len ==> filing_ok(sv, ps, #[trigger] so[x]),
            decreases len - i,
        {
            let nm = t.out[i].nm;
            let mut seg: u64 = 0;
            let ghost i0 = i;
            while i < len && t.out[i].nm == nm
                invariant
                    inputs_ok(t), t.sv@ == sv, t.ps@ == ps, i0 <= i <= len <= t.cap, t.out@ == so, so.len() == t.cap,
                    forall|x: int| 0 <= x < len ==> filing_ok(sv, ps, #[trigger] so[x]),
                    i0 < len, so[i0 as int].nm == nm,
                decreases len - i,
            {
                let f = t.out[i];
                if seg <= u64::MAX - f.rows {
                    seg = seg + f.rows;
                }
                i = i + 1;
            }
            if seg > max_seg {
                max_seg = seg;
            }
        }
        FilingOut { filings: t.out, len, counts: t.counts, max_seg, overflow, pushed: Ghost(p) }
    }
}

} // verus!
