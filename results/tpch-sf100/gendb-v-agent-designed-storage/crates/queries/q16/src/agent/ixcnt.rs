//! Counting kernel of the index plan: per directory entry of `part_btsidx` (one (brand, type, size) group), the
//! number of distinct supplier rows the subquery keeps among the partsupp rows of the entry's part rows.
//!
//! A task (`CntTask`) takes a range of flat group numbers `[q0, q1)` with their entries (`ents`, `NOENT` for a group
//! that cannot have a row). Per group it walks the entry's index positions; for part row `j` there, the partsupp
//! rows of `j`'s key (`kernel::ps_rows_of`: psrun's key runs, a checked guess or a search) give supplier rows by
//! position (`kernel::supp_of`). A row the subquery excludes (bitmap `excl`, `excl_bitmap`) is skipped; the others
//! are marked in the task's bitmap `seen` (`common::marks`), counting first sightings. The fresh rows are listed in
//! `undo` (room for `ucap`), so afterwards only their words are cleared (all words when the list overflowed): the
//! bitmap is empty again for the next group. Proof: the ghost set of marked rows is exactly the kept supplier rows
//! of the positions walked so far (`cur_ok`), so a group's count is `gset::pos_set`'s size.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use super::tables::*;
use super::model::*;
use super::kernel::*;
use crate::stores::psrun::interface as pri;
use super::supp::{cc_row, comm_ok, SuppTask, SuppOut, supp_out_ok};
use super::common::marks::{bit_at, holds, mark_new, lemma_zero_holds};
use super::common::basemarks::{holds_over, copy_base, mark_over, restore_word, restore_all};
use super::split::{cuts, split_range};
use super::xidx::*;
use super::gset::*;

verus! {

/// "No entry": the group has no part row.
pub const NOENT: u32 = 0xFFFF_FFFF;

/// Room of a task's list of fresh supplier rows.
pub const UCAP: usize = 0x1000;

// ------------------------------------------------------------------------------------------------ the subquery

/// The supplier rows `[lo, hi)` task, with room for all of them.
fn supp_task(s: &SCols, lo: usize, hi: usize) -> (st: SuppTask)
    requires comm_ok(*s), lo <= hi <= s.n,
    ensures st.pre(), st.s == *s, st.lo == lo, st.hi == hi, st.cap >= hi - lo,
{
    let cap = hi - lo;
    SuppTask { s: *s, lo, hi, cap, out: vec![0usize; cap] }
}

/// The bitmap of the supplier rows the subquery excludes (`s_comment LIKE '%Customer%Complaints%'`), the byte test
/// run by at most `workers` tasks over consecutive supplier ranges.
pub fn excl_bitmap(s: &SCols, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<u64>, QueryError>)
    requires comm_ok(*s), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(m) ==> s.n <= 64 * m@.len() && forall|j: int| 0 <= j < s.n ==> #[trigger] bit_at(m@, j) == cc_row(*s, j),
{
    let sb = split_range(s.n, workers, 1);
    let nk = sb.len() - 1;
    let mut tasks: Vec<SuppTask> = Vec::new();
    let mut k: usize = 0;
    while k < nk
        invariant
            comm_ok(*s), cuts(sb@, s.n as int), nk == sb@.len() - 1, k <= nk, tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].s == *s
                && tasks@[i].lo == sb@[i] && tasks@[i].hi == sb@[i + 1] && tasks@[i].cap >= tasks@[i].hi - tasks@[i].lo,
        decreases nk - k,
    {
        proof {
            assert(sb@[k as int] <= sb@[k + 1]);
            super::round::lemma_cuts_mono(sb@, s.n as int, k as int + 1, nk as int);
        }
        let st = supp_task(s, sb[k], sb[k + 1]);
        tasks.push(st);
        k = k + 1;
    }
    let ghost ts = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => {
            return Err(QueryError::WorkerFailed(e));
        },
    };
    proof {
        assert forall|i: int| 0 <= i < nk implies supp_out_ok(*s, sb@[i] as int, sb@[i + 1] as int, #[trigger] outs@[i]) by {
            assert(ts[i].post(outs@[i]));
        }
    }
    Ok(excl_merge(s, &sb, &outs))
}

/// The bitmap of the supplier rows listed by the outputs of consecutive supplier ranges `sb` (each the exact list of
/// its range's excluded rows).
pub fn excl_merge(s: &SCols, sb: &Vec<usize>, outs: &Vec<SuppOut>) -> (excl: Vec<u64>)
    requires
        comm_ok(*s), cuts(sb@, s.n as int), outs@.len() == sb@.len() - 1,
        forall|i: int| 0 <= i < outs@.len() ==> supp_out_ok(*s, sb@[i] as int, sb@[i + 1] as int, #[trigger] outs@[i]),
    ensures
        s.n <= 64 * excl@.len(),
        forall|j: int| 0 <= j < s.n ==> #[trigger] bit_at(excl@, j) == cc_row(*s, j),
{
    let nk = outs.len();
    let mut excl: Vec<u64> = vec![0u64; s.n / 64 + 1];
    proof {
        lemma_zero_holds(excl@);
        assert(s.n <= 64 * (s.n / 64 + 1)) by (nonlinear_arith)
            requires s.n == 64 * (s.n / 64) + s.n % 64, s.n % 64 < 64;
    }
    let ghost mut set: Set<int> = Set::empty();
    let mut t: usize = 0;
    while t < nk
        invariant
            comm_ok(*s), nk == outs@.len(), nk == sb@.len() - 1,
            cuts(sb@, s.n as int),
            forall|i: int| 0 <= i < nk ==> supp_out_ok(*s, sb@[i] as int, sb@[i + 1] as int, #[trigger] outs@[i]),
            t <= nk,
            s.n <= 64 * excl@.len(),
            holds(excl@, set),
            forall|j: int| #[trigger] set.contains(j) ==> 0 <= j < s.n && cc_row(*s, j),
            forall|j: int| 0 <= j < sb@[t as int] && #[trigger] cc_row(*s, j) ==> set.contains(j),
        decreases nk - t,
    {
        let o = &outs[t];
        let lo = sb[t];
        let hi = sb[t + 1];
        proof {
            assert(supp_out_ok(*s, lo as int, hi as int, *o));
            super::round::lemma_cuts_mono(sb@, s.n as int, t as int + 1, nk as int);
        }
        let mut q: usize = 0;
        while q < o.len
            invariant
                supp_out_ok(*s, lo as int, hi as int, *o),
                lo <= hi <= s.n,
                q <= o.len,
                s.n <= 64 * excl@.len(),
                holds(excl@, set),
                forall|j: int| #[trigger] set.contains(j) ==> 0 <= j < s.n && cc_row(*s, j),
                forall|j: int| 0 <= j < lo && #[trigger] cc_row(*s, j) ==> set.contains(j),
                forall|q2: int| 0 <= q2 < q ==> #[trigger] set.contains(o.rows@[q2] as int),
            decreases o.len - q,
        {
            let j = o.rows[q];
            assert(lo <= o.rows@[q as int] < hi && cc_row(*s, o.rows@[q as int] as int));
            let _ = mark_new(&mut excl, j, Ghost(set));
            proof {
                set = set.insert(j as int);
            }
            q = q + 1;
        }
        proof {
            assert forall|j: int| 0 <= j < hi && #[trigger] cc_row(*s, j) implies set.contains(j) by {
                if j >= lo {
                    let q2 = choose|q2: int| 0 <= q2 < o.len && o.rows@[q2] == j;
                    assert(set.contains(o.rows@[q2] as int));
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < s.n implies #[trigger] bit_at(excl@, j) == cc_row(*s, j) by {
            assert(bit_at(excl@, j) == set.contains(j));
        }
    }
    excl
}

// ------------------------------------------------------------------------------------------------ specs

/// A partsupp row of `[a, i)` links part row `j` and supplier row `x`.
pub open spec fn part_upto(c: Cols, j: int, a: int, i: int, x: int) -> bool {
    exists|i2: int| a <= i2 < i && #[trigger] ps_link(c, i2, j, x)
}

/// A part row at positions `[lo, p)` has supplier row `x`.
pub open spec fn pos_hit(c: Cols, xi: XIdx, lo: int, p: int, x: int) -> bool {
    exists|p2: int| lo <= p2 < p && #[trigger] part_hit(c, xi.perm@[p2] as int, x)
}

/// `s` is the set of kept supplier rows of positions `[lo, p)`.
pub open spec fn pos_ok(c: Cols, xi: XIdx, lo: int, p: int, s: Set<int>) -> bool {
    forall|x: int| #[trigger] s.contains(x) <==> (0 <= x < c.s.n && !cc_row(c.s, x) && pos_hit(c, xi, lo, p, x))
}

/// `s` is the set of kept supplier rows of positions `[lo, p)` and of partsupp rows `[a, i)` of part row `j`.
pub open spec fn cur_ok(c: Cols, xi: XIdx, lo: int, p: int, j: int, a: int, i: int, s: Set<int>) -> bool {
    forall|x: int| #[trigger] s.contains(x) <==> (0 <= x < c.s.n && !cc_row(c.s, x)
        && (pos_hit(c, xi, lo, p, x) || part_upto(c, j, a, i, x)))
}

/// The count a task owes for entry `e`.
pub open spec fn want(c: Cols, xi: XIdx, e: u32) -> int {
    if e == NOENT { 0 } else { pos_set(c, xi, xi.offs@[e as int] as int, xi.offs@[e as int + 1] as int).len() as int }
}

/// Partsupp is one arithmetic key run: row `i` has key `pfirst + i / ratio`, and part row `j` has key `pfirst + j`.
pub open spec fn glob_ok(e: PairEnv) -> bool {
    &&& e.ratio > 0
    &&& e.pdense
    &&& forall|i: int| 0 <= i < e.c.ps.n ==> #[trigger] pskey(e.c.ps, i) == e.pfirst + i / (e.ratio as int)
}

/// Row `i = B * 65536 + d` of a block whose run starts at `pfirst + B * rper` has key `pfirst + i / r`.
proof fn lemma_glob_row(pfirst: int, r: int, rper: int, bk: int, i: int)
    requires r >= 1, rper * r == 65536, bk >= 0, bk * 65536 <= i < bk * 65536 + 65536,
    ensures pfirst + bk * rper + (i - bk * 65536) / r == pfirst + i / r,
{
    let d = i - bk * 65536;
    let q = d / r;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(d, r);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(d, r);
    assert(i == (bk * rper + q) * r + d % r) by (nonlinear_arith)
        requires d == r * q + d % r, rper * r == 65536, i == bk * 65536 + d;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i, r, bk * rper + q, d % r);
}

/// Whether every psrun block is the run `pfirst + B * rper` (then `glob_ok`).
pub fn glob_runs(e: &PairEnv) -> (g: bool)
    requires env_ok(*e, 0),
    ensures g ==> glob_ok(*e),
{
    if e.rper == 0 || !e.pdense || e.c.ps.kind != 1 {
        return false;
    }
    let nb = e.c.ps.runs.len() - 1;
    proof {
        assert(e.rper <= 65536) by (nonlinear_arith) requires e.rper * e.ratio == 65536, e.ratio >= 1;
    }
    let mut b: usize = 0;
    while b < nb
        invariant
            env_ok(*e, 0), e.rper > 0, e.rper <= 65536, nb == e.c.ps.runs@.len() - 1,
            nb == pri::run_blocks(e.c.ps.n as int), b <= nb,
            forall|b2: int| 0 <= b2 < b ==> #[trigger] e.c.ps.runs@[b2 + 1] == e.pfirst + b2 * e.rper
                && e.c.ps.runs@[b2 + 1] != pri::NO_RUN,
        decreases nb - b,
    {
        proof {
            assert((b as int) * (e.rper as int) <= 0x1_0000_0000_0000_0000int * 65536) by (nonlinear_arith)
                requires b < 0x1_0000_0000_0000_0000int, e.rper <= 65536;
        }
        let kk = e.c.ps.runs[b + 1];
        if kk == pri::NO_RUN || kk as i128 != e.pfirst as i128 + (b as i128) * (e.rper as i128) {
            return false;
        }
        b = b + 1;
    }
    proof {
        let r = e.ratio as int;
        assert(e.c.ps.runs@[0] == r);
        assert forall|i: int| 0 <= i < e.c.ps.n implies #[trigger] pskey(e.c.ps, i) == e.pfirst + i / r by {
            let bk = i / 65536;
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, 65536);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(i, 65536);
            vstd::arithmetic::div_mod::lemma_div_pos_is_pos(i, 65536);
            vstd::arithmetic::div_mod::lemma_div_is_ordered(i, e.c.ps.n + 65535, 65536);
            assert(bk < nb);
            assert(e.c.ps.runs@[bk + 1] == e.pfirst + bk * e.rper && e.c.ps.runs@[bk + 1] != pri::NO_RUN);
            assert(bk * pri::RUN_ROWS <= i < bk * pri::RUN_ROWS + pri::RUN_ROWS);
            assert(fv32(e.c.ps.key_c@, e.c.ps.key_b@, e.c.ps.bs as int, i) == e.c.ps.runs@[bk + 1] + (i - bk * pri::RUN_ROWS) / r);
            lemma_glob_row(e.pfirst as int, r, e.rper as int, bk, i);
        }
    }
    true
}

/// Under `glob_ok`, the partsupp rows of part row `j` are `[j * ratio, (j + 1) * ratio)`.
proof fn lemma_glob_rows(e: PairEnv, j: int)
    requires env_ok(e, 0), glob_ok(e), 0 <= j < e.jmax, j < e.c.p.n,
    ensures
        j * e.ratio + e.ratio <= e.c.ps.n,
        rows_of(e, pkey(e.c.p, j), j * e.ratio, j * e.ratio + e.ratio, true),
{
    let r = e.ratio as int;
    assert(j * r + r <= e.jmax * r) by (nonlinear_arith) requires j < e.jmax, r > 0;
    assert(pkey(e.c.p, j) == e.pfirst + j);
    assert forall|i: int| 0 <= i < e.c.ps.n && #[trigger] pskey(e.c.ps, i) == pkey(e.c.p, j) implies j * r <= i < j * r + r by {
        assert(i / r == j);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(i, r);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(i, r);
        assert(j * r <= i < j * r + r) by (nonlinear_arith) requires i == r * j + i % r, 0 <= i % r < r;
    }
    assert forall|i: int| j * r <= i < j * r + r implies #[trigger] pskey(e.c.ps, i) == pkey(e.c.p, j) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(i, r, j, i - j * r);
    }
}

/// What every counting task reads.
pub struct CntEnv {
    pub e: PairEnv,
    /// `glob_ok(e)` holds: a part row's partsupp rows follow by arithmetic.
    pub glob: bool,
    pub xi: XIdx,
    pub excl: Arc<Vec<u64>>,
    pub ents: Arc<Vec<u32>>,
}

pub open spec fn cenv_ok(v: CntEnv) -> bool {
    &&& env_ok(v.e, 0)
    &&& v.glob ==> glob_ok(v.e)
    &&& xidx_ok(v.e.c, v.xi)
    &&& v.e.c.s.n <= 64 * v.excl@.len()
    &&& forall|r: int| 0 <= r < v.e.c.s.n ==> #[trigger] bit_at(v.excl@, r) == cc_row(v.e.c.s, r)
    &&& forall|q: int| 0 <= q < v.ents@.len() ==> (#[trigger] v.ents@[q]) == NOENT || v.ents@[q] < v.xi.nk
    &&& forall|x1: int, x2: int| 0 <= x1 < v.e.c.s.n && 0 <= x2 < v.e.c.s.n
        && #[trigger] skey(v.e.c.s, x1) == #[trigger] skey(v.e.c.s, x2) ==> x1 == x2
}

// ------------------------------------------------------------------------------------------------ step lemmas

proof fn lemma_set_bound(s: Set<int>, sn: int)
    requires sn >= 0, forall|x: int| #[trigger] s.contains(x) ==> 0 <= x < sn,
    ensures s.finite(), s.len() <= sn,
{
    vstd::set_lib::lemma_int_range(0, sn);
    assert(s.subset_of(Set::range(0int, sn)));
    vstd::set_lib::lemma_len_subset(s, Set::range(0int, sn));
}

/// The start of a part row's partsupp rows.
proof fn lemma_cur_start(c: Cols, xi: XIdx, lo: int, p: int, j: int, a: int, s: Set<int>)
    requires pos_ok(c, xi, lo, p, s),
    ensures cur_ok(c, xi, lo, p, j, a, a, s),
{
    assert forall|x: int| #[trigger] s.contains(x) <==> (0 <= x < c.s.n && !cc_row(c.s, x)
        && (pos_hit(c, xi, lo, p, x) || part_upto(c, j, a, a, x))) by {
        if part_upto(c, j, a, a, x) {
            let i2 = choose|i2: int| a <= i2 < a && #[trigger] ps_link(c, i2, j, x);
        }
    }
}

/// Partsupp row `i` linking part row `j` to supplier row `x` only.
proof fn lemma_cur_add(c: Cols, xi: XIdx, lo: int, p: int, j: int, a: int, i: int, s: Set<int>, x: int)
    requires
        cur_ok(c, xi, lo, p, j, a, i, s),
        a <= i,
        0 <= x < c.s.n,
        ps_link(c, i, j, x),
        forall|y: int| #[trigger] ps_link(c, i, j, y) && 0 <= y < c.s.n ==> y == x,
    ensures cur_ok(c, xi, lo, p, j, a, i + 1, if cc_row(c.s, x) { s } else { s.insert(x) }),
{
    let s2 = if cc_row(c.s, x) { s } else { s.insert(x) };
    assert forall|y: int| #[trigger] s2.contains(y) <==> (0 <= y < c.s.n && !cc_row(c.s, y)
        && (pos_hit(c, xi, lo, p, y) || part_upto(c, j, a, i + 1, y))) by {
        if part_upto(c, j, a, i + 1, y) && 0 <= y < c.s.n {
            let i2 = choose|i2: int| a <= i2 < i + 1 && #[trigger] ps_link(c, i2, j, y);
            if i2 < i {
                assert(part_upto(c, j, a, i, y));
            } else {
                assert(y == x);
            }
        }
        if part_upto(c, j, a, i, y) {
            let i2 = choose|i2: int| a <= i2 < i && #[trigger] ps_link(c, i2, j, y);
            assert(part_upto(c, j, a, i + 1, y));
        }
        if y == x {
            assert(part_upto(c, j, a, i + 1, y));
        }
    }
}

/// Partsupp row `i` linking part row `j` to no supplier row.
proof fn lemma_cur_none(c: Cols, xi: XIdx, lo: int, p: int, j: int, a: int, i: int, s: Set<int>)
    requires
        cur_ok(c, xi, lo, p, j, a, i, s),
        forall|y: int| 0 <= y < c.s.n ==> !(#[trigger] ps_link(c, i, j, y)),
    ensures cur_ok(c, xi, lo, p, j, a, i + 1, s),
{
    assert forall|y: int| #[trigger] s.contains(y) <==> (0 <= y < c.s.n && !cc_row(c.s, y)
        && (pos_hit(c, xi, lo, p, y) || part_upto(c, j, a, i + 1, y))) by {
        if part_upto(c, j, a, i + 1, y) && 0 <= y < c.s.n {
            let i2 = choose|i2: int| a <= i2 < i + 1 && #[trigger] ps_link(c, i2, j, y);
            assert(i2 < i);
            assert(part_upto(c, j, a, i, y));
        }
        if part_upto(c, j, a, i, y) {
            let i2 = choose|i2: int| a <= i2 < i && #[trigger] ps_link(c, i2, j, y);
            assert(part_upto(c, j, a, i + 1, y));
        }
    }
}

/// Every partsupp row of part row `j`'s key walked: the position is done.
proof fn lemma_pos_next(c: Cols, xi: XIdx, lo: int, p: int, a: int, b: int, s: Set<int>)
    requires
        lo <= p,
        cur_ok(c, xi, lo, p, xi.perm@[p] as int, a, b, s),
        forall|i: int| 0 <= i < c.ps.n && #[trigger] pskey(c.ps, i) == pkey(c.p, xi.perm@[p] as int) ==> a <= i < b,
    ensures pos_ok(c, xi, lo, p + 1, s),
{
    let j = xi.perm@[p] as int;
    assert forall|x: int| #[trigger] s.contains(x) <==> (0 <= x < c.s.n && !cc_row(c.s, x) && pos_hit(c, xi, lo, p + 1, x)) by {
        if pos_hit(c, xi, lo, p + 1, x) {
            let p2 = choose|p2: int| lo <= p2 < p + 1 && #[trigger] part_hit(c, xi.perm@[p2] as int, x);
            if p2 < p {
                assert(pos_hit(c, xi, lo, p, x));
            } else {
                let i = choose|i: int| #[trigger] ps_link(c, i, j, x);
                assert(part_upto(c, j, a, b, x));
            }
        }
        if pos_hit(c, xi, lo, p, x) {
            let p2 = choose|p2: int| lo <= p2 < p && #[trigger] part_hit(c, xi.perm@[p2] as int, x);
            assert(pos_hit(c, xi, lo, p + 1, x));
        }
        if part_upto(c, j, a, b, x) {
            let i2 = choose|i2: int| a <= i2 < b && #[trigger] ps_link(c, i2, j, x);
            assert(part_hit(c, xi.perm@[p] as int, x));
            assert(pos_hit(c, xi, lo, p + 1, x));
        }
    }
}

/// The set of all positions is `pos_set`.
proof fn lemma_pos_all(c: Cols, xi: XIdx, lo: int, hi: int, s: Set<int>)
    requires pos_ok(c, xi, lo, hi, s),
    ensures s == pos_set(c, xi, lo, hi),
{
    assert(s =~= pos_set(c, xi, lo, hi));
}

// ------------------------------------------------------------------------------------------------ one group

/// Key of part row `j`.
#[inline(always)]
fn part_key(e: &PairEnv, j: usize) -> (k: i64)
    requires env_ok(*e, 0), j < e.c.p.n,
    ensures k == pkey(e.c.p, j as int),
    no_unwind
{
    if e.pdense {
        proof {
            assert(pkey(e.c.p, j as int) == e.pfirst + j);
            assert(i64r(pkey(e.c.p, j as int)));
        }
        (e.pfirst as i128 + j as i128) as i64
    } else {
        proof {
            lemma_grp_bound(e.c.p.n as int, e.c.p.bs as int, e.c.p.ng as int, j as int);
            assert(i64r(pkey(e.c.p, j as int)));
        }
        e.c.p.key_b[j / e.c.p.bs] + e.c.p.key_c[j] as i64
    }
}

/// The listed fresh supplier rows: each is a supplier row, and while there was room (`cnt <= UCAP`) every row of
/// `s` is among the first `cnt` entries.
pub open spec fn list_ok(u: Seq<usize>, cnt: int, s: Set<int>, sn: int) -> bool {
    &&& u.len() == UCAP
    &&& forall|q: int| 0 <= q < cnt && q < UCAP ==> (#[trigger] u[q]) < sn
    &&& cnt <= UCAP ==> forall|y: int| #[trigger] s.contains(y) ==> exists|q: int| 0 <= q < cnt && u[q] as int == y
}

/// `s` after supplier row `x`: unchanged when the subquery excludes `x` (bit set in `ex`), else with `x`.
pub open spec fn kept_ins(ex: Seq<u64>, s: Set<int>, x: int) -> Set<int> {
    if bit_at(ex, x) { s } else { s.insert(x) }
}

/// The counting state of a group: `seen` is the exclusion bitmap `ex` with `s` marked as well, `cnt` is the size of
/// `s` and `undo` lists it (`list_ok`).
pub open spec fn st_ok(sn: int, ex: Seq<u64>, seen: Seq<u64>, undo: Seq<usize>, cnt: int, s: Set<int>) -> bool {
    &&& sn <= 64 * seen.len()
    &&& holds_over(seen, ex, s)
    &&& s.finite()
    &&& cnt == s.len()
    &&& forall|y: int| #[trigger] s.contains(y) ==> 0 <= y < sn
    &&& list_ok(undo, cnt, s, sn)
}

/// Supplier row `x` of a walked partsupp row: when the subquery keeps it and it is new, mark it, list it (room
/// permitting) and count it.
#[inline(always)]
fn add_supp(seen: &mut Vec<u64>, undo: &mut Vec<usize>, cnt: u64, x: usize,
    Ghost(ex): Ghost<Seq<u64>>, Ghost(s): Ghost<Set<int>>, Ghost(sn): Ghost<int>) -> (r: u64)
    requires
        x < sn, sn <= u64::MAX,
        st_ok(sn, ex, old(seen)@, old(undo)@, cnt as int, s),
    ensures
        final(seen)@.len() == old(seen)@.len(),
        st_ok(sn, ex, final(seen)@, final(undo)@, r as int, kept_ins(ex, s, x as int)),
    no_unwind
{
    // One bit test: set for an excluded row (the base `ex`) and for a row already counted.
    let fresh = mark_over(seen, x, Ghost(ex), Ghost(s));
    if !fresh {
        proof {
            if !bit_at(ex, x as int) {
                assert(s.insert(x as int) =~= s);
            }
        }
        return cnt;
    }
    proof {
        vstd::set::lemma_set_insert_len(s, x as int);
        lemma_set_bound(s.insert(x as int), sn);
    }
    let ghost u0 = undo@;
    if cnt < UCAP as u64 {
        undo[cnt as usize] = x;
    }
    proof {
        assert(s.insert(x as int).len() <= sn);
    }
    let r = cnt + 1;
    proof {
        let s2 = s.insert(x as int);
        assert forall|q: int| 0 <= q < r && q < UCAP implies (#[trigger] undo@[q]) < sn by {
            if q < cnt { assert(undo@[q] == u0[q]); }
        }
        if r <= UCAP {
            assert forall|y: int| #[trigger] s2.contains(y) implies exists|q: int| 0 <= q < r && undo@[q] as int == y by {
                if y == x as int {
                    assert(undo@[cnt as int] as int == y);
                } else {
                    let q = choose|q: int| 0 <= q < cnt && u0[q] as int == y;
                    assert(undo@[q] == u0[q]);
                }
            }
        }
    }
    r
}

/// Part row `perm[p]` by the general route: its partsupp rows by arithmetic (`glob`) or `ps_rows_of`, each row's
/// supplier row by `supp_of`.
#[inline(never)]
fn part_general(v: &CntEnv, ex: &Vec<u64>, lo: usize, p: usize, seen: &mut Vec<u64>, undo: &mut Vec<usize>,
    cnt: u64, Ghost(s): Ghost<Set<int>>) -> (r: (u64, Ghost<Set<int>>))
    requires
        cenv_ok(*v), ex@ == v.excl@,
        lo <= p < v.e.c.p.n,
        st_ok(v.e.c.s.n as int, ex@, old(seen)@, old(undo)@, cnt as int, s),
        pos_ok(v.e.c, v.xi, lo as int, p as int, s),
    ensures
        final(seen)@.len() == old(seen)@.len(),
        st_ok(v.e.c.s.n as int, ex@, final(seen)@, final(undo)@, r.0 as int, r.1@),
        pos_ok(v.e.c, v.xi, lo as int, p + 1, r.1@),
    no_unwind
{
    let ghost c = v.e.c;
    let ghost sn = c.s.n as int;
    let e = &v.e;
    let xi = &v.xi;
    let ghost mut s = s;
    let mut cnt = cnt;
    let j = xi.perm[p] as usize;
    proof {
        assert(xi.perm@[p as int] < c.p.n);
    }
    let k = part_key(e, j);
    let (a, b, exact) = if v.glob && j < e.jmax {
        proof {
            lemma_glob_rows(*e, j as int);
        }
        (j * e.ratio, j * e.ratio + e.ratio, true)
    } else {
        ps_rows_of(e, j, k, Ghost(0))
    };
    proof {
        lemma_cur_start(c, *xi, lo as int, p as int, j as int, a as int, s);
    }
    let mut i = a;
    while i < b
        invariant
            cenv_ok(*v), ex@ == v.excl@, c == v.e.c, sn == c.s.n, *e == v.e, *xi == v.xi,
            lo <= p < c.p.n,
            j as int == xi.perm@[p as int], j < c.p.n, k as int == pkey(c.p, j as int),
            rows_of(*e, k as int, a as int, b as int, exact),
            a <= i <= b,
            seen@.len() == old(seen)@.len(),
            st_ok(sn, ex@, seen@, undo@, cnt as int, s),
            cur_ok(c, *xi, lo as int, p as int, j as int, a as int, i as int, s),
        decreases b - i,
    {
        let mut hit = false;
        let mut x: usize = 0;
        if exact || ps_key(e, i, Ghost(0)) == k {
            let sk = ps_supp(e, i, Ghost(0));
            match supp_of(e, sk, Ghost(0)) {
                Some(y) => {
                    hit = true;
                    x = y;
                },
                None => {},
            }
        }
        if hit {
            proof {
                assert(ps_link(c, i as int, j as int, x as int));
                assert forall|y: int| #[trigger] ps_link(c, i as int, j as int, y) && 0 <= y < c.s.n implies y == x by {}
                lemma_cur_add(c, *xi, lo as int, p as int, j as int, a as int, i as int, s, x as int);
                assert(bit_at(ex@, x as int) == cc_row(c.s, x as int));
            }
            cnt = add_supp(seen, undo, cnt, x, Ghost(ex@), Ghost(s), Ghost(sn));
            proof {
                s = kept_ins(ex@, s, x as int);
            }
        } else {
            proof {
                lemma_cur_none(c, *xi, lo as int, p as int, j as int, a as int, i as int, s);
            }
        }
        i = i + 1;
    }
    proof {
        lemma_pos_next(c, *xi, lo as int, p as int, a as int, b as int, s);
    }
    (cnt, Ghost(s))
}

/// Partsupp row `i` of part row `j = perm[p]` on the fast route (dense supplier keys, the rows' block base less the
/// first supplier key `base2`): supplier row `base2 + code` when it exists.
#[inline(always)]
fn row_fast(v: &CntEnv, lo: usize, p: usize, j: usize, a: usize, b: usize, i: usize, base2: i64, sn_i: i64,
    seen: &mut Vec<u64>, undo: &mut Vec<usize>, cnt: u64, Ghost(s): Ghost<Set<int>>) -> (r: (u64, Ghost<Set<int>>))
    requires
        cenv_ok(*v), v.e.sdense, sn_i == v.e.c.s.n,
        lo <= p < v.e.c.p.n,
        j as int == v.xi.perm@[p as int], j < v.e.c.p.n,
        rows_of(v.e, pkey(v.e.c.p, j as int), a as int, b as int, true),
        -0x1_0000_0000_0000 <= base2 <= 0x1_0000_0000_0000,
        forall|i2: int| a <= i2 < b ==> #[trigger] pssupp(v.e.c.ps, i2) == v.e.sfirst + base2 + v.e.c.ps.supp_c@[i2],
        a <= i < b,
        st_ok(v.e.c.s.n as int, v.excl@, old(seen)@, old(undo)@, cnt as int, s),
        cur_ok(v.e.c, v.xi, lo as int, p as int, j as int, a as int, i as int, s),
    ensures
        final(seen)@.len() == old(seen)@.len(),
        st_ok(v.e.c.s.n as int, v.excl@, final(seen)@, final(undo)@, r.0 as int, r.1@),
        cur_ok(v.e.c, v.xi, lo as int, p as int, j as int, a as int, i + 1, r.1@),
    no_unwind
{
    let ghost c = v.e.c;
    let ghost sn = c.s.n as int;
    let e = &v.e;
    let d = base2 + e.c.ps.supp_c[i] as i64;
    proof {
        assert(pssupp(c.ps, i as int) == e.sfirst + d);
    }
    if 0 <= d && d < sn_i {
        let x = d as usize;
        proof {
            assert(skey(c.s, x as int) == e.sfirst + x);
            assert(ps_link(c, i as int, j as int, x as int));
            assert forall|y: int| #[trigger] ps_link(c, i as int, j as int, y) && 0 <= y < c.s.n implies y == x by {
                assert(skey(c.s, y) == e.sfirst + y);
            }
            lemma_cur_add(c, v.xi, lo as int, p as int, j as int, a as int, i as int, s, x as int);
            assert(bit_at(v.excl@, x as int) == cc_row(c.s, x as int));
        }
        let c2 = add_supp(seen, undo, cnt, x, Ghost(v.excl@), Ghost(s), Ghost(sn));
        (c2, Ghost(kept_ins(v.excl@, s, x as int)))
    } else {
        proof {
            assert forall|y: int| 0 <= y < c.s.n implies !(#[trigger] ps_link(c, i as int, j as int, y)) by {
                assert(skey(c.s, y) == e.sfirst + y);
            }
            lemma_cur_none(c, v.xi, lo as int, p as int, j as int, a as int, i as int, s);
        }
        (cnt, Ghost(s))
    }
}

/// The kept distinct supplier rows of the part rows at positions `[lo, hi)`; `seen` is the exclusion bitmap before and after.
fn count_group(v: &CntEnv, ex: &Vec<u64>, lo: usize, hi: usize, seen: &mut Vec<u64>, undo: &mut Vec<usize>) -> (r: (u64, u32))
    requires
        cenv_ok(*v), ex@ == v.excl@,
        lo <= hi <= v.e.c.p.n,
        holds_over(old(seen)@, ex@, Set::empty()),
        old(undo)@.len() == UCAP,
    ensures
        final(seen)@.len() == old(seen)@.len(),
        holds_over(final(seen)@, ex@, Set::empty()),
        final(undo)@.len() == UCAP,
        r.0 as int == pos_set(v.e.c, v.xi, lo as int, hi as int).len(),
    no_unwind
{
    let ghost c = v.e.c;
    let ghost sn = c.s.n as int;
    let e = &v.e;
    let xi = &v.xi;
    let mut cnt: u64 = 0;
    let ghost mut s: Set<int> = Set::empty();
    proof {
        assert forall|x: int| #[trigger] s.contains(x) <==> (0 <= x < c.s.n && !cc_row(c.s, x)
            && pos_hit(c, *xi, lo as int, lo as int, x)) by {
            if pos_hit(c, *xi, lo as int, lo as int, x) {
                let p2 = choose|p2: int| lo <= p2 < lo && #[trigger] part_hit(c, xi.perm@[p2] as int, x);
            }
        }
    }
    // Touch the suppkey line of each part row's guessed partsupp rows first: these loads are independent, so their
    // cache misses overlap; the counting loop below then reads cached lines.
    let mut sink: u32 = 0;
    if e.ratio > 0 {
        let mut p = lo;
        while p < hi
            invariant
                cenv_ok(*v), c == v.e.c, *e == v.e, *xi == v.xi, e.ratio > 0,
                lo <= p <= hi <= c.p.n,
            decreases hi - p,
        {
            let j = xi.perm[p] as usize;
            if j < e.jmax {
                proof {
                    assert(j * e.ratio < e.jmax * e.ratio) by (nonlinear_arith) requires j < e.jmax, e.ratio > 0;
                }
                sink = sink ^ e.c.ps.supp_c[j * e.ratio];
            }
            p = p + 1;
        }
    }
    // Fast route: one global key run (`glob`), dense supplier keys, partsupp blocks of `2^ps_shift` rows and
    // supplier rows that fit an `i64`. A part row's rows `[j * ratio, (j + 1) * ratio)` in one block give supplier
    // row `base + code` with the block base (less the first supplier key) read once; any other part row takes
    // `part_general`.
    let fast = v.glob && e.sdense && e.ps_shift < 32 && e.c.s.n <= 0x7fff_ffff && e.ratio > 0;
    let sn_i: i64 = if fast { e.c.s.n as i64 } else { 0 };
    let sh: usize = if fast { e.ps_shift as usize } else { 0 };
    let r = e.ratio;
    let jmax = e.jmax;
    let mut p = lo;
    while p < hi
        invariant
            cenv_ok(*v), ex@ == v.excl@, c == v.e.c, sn == c.s.n, *e == v.e, *xi == v.xi,
            fast ==> v.glob && e.sdense && e.ps_shift < 32 && sn <= 0x7fff_ffff && e.ratio > 0
                && sn_i == sn && sh == e.ps_shift,
            r == e.ratio, jmax == e.jmax,
            lo <= p <= hi <= c.p.n,
            seen@.len() == old(seen)@.len(),
            st_ok(sn, ex@, seen@, undo@, cnt as int, s),
            pos_ok(c, *xi, lo as int, p as int, s),
        decreases hi - p,
    {
        let mut done = false;
        if fast {
            let j = xi.perm[p] as usize;
            proof {
                assert(xi.perm@[p as int] < c.p.n);
            }
            if j < jmax {
                proof {
                    lemma_glob_rows(*e, j as int);
                }
                let a = j * r;
                let b = a + r;
                let g = a >> sh;
                let g2 = (b - 1) >> sh;
                proof {
                    vstd::bits::lemma_usize_shr_is_div(a, sh);
                    vstd::bits::lemma_usize_shr_is_div((b - 1) as usize, sh);
                    lemma_grp_bound(c.ps.n as int, c.ps.bs as int, c.ps.ng as int, a as int);
                }
                if g == g2 {
                    let base128: i128 = e.c.ps.supp_b[g] as i128 - e.sfirst as i128;
                    if -0x1_0000_0000_0000i128 <= base128 && base128 <= 0x1_0000_0000_0000i128 {
                        let base2 = base128 as i64;
                        proof {
                            assert forall|i2: int| a <= i2 < b implies #[trigger] pssupp(c.ps, i2) == e.sfirst + base2 + c.ps.supp_c@[i2] by {
                                vstd::arithmetic::div_mod::lemma_div_is_ordered(a as int, i2, c.ps.bs as int);
                                vstd::arithmetic::div_mod::lemma_div_is_ordered(i2, b - 1, c.ps.bs as int);
                            }
                            lemma_cur_start(c, *xi, lo as int, p as int, j as int, a as int, s);
                        }
                        if r == 4 {
                            // The usual ratio: the part row's four rows, unrolled.
                            let (c1, Ghost(s1)) = row_fast(v, lo, p, j, a, b, a, base2, sn_i, seen, undo, cnt, Ghost(s));
                            let (c2, Ghost(s2)) = row_fast(v, lo, p, j, a, b, a + 1, base2, sn_i, seen, undo, c1, Ghost(s1));
                            let (c3, Ghost(s3)) = row_fast(v, lo, p, j, a, b, a + 2, base2, sn_i, seen, undo, c2, Ghost(s2));
                            let (c4, Ghost(s4)) = row_fast(v, lo, p, j, a, b, a + 3, base2, sn_i, seen, undo, c3, Ghost(s3));
                            cnt = c4;
                            proof {
                                s = s4;
                            }
                        } else {
                            let mut i = a;
                            while i < b
                                invariant
                                    cenv_ok(*v), ex@ == v.excl@, c == v.e.c, sn == c.s.n, *e == v.e, *xi == v.xi,
                                    e.sdense, sn_i == sn,
                                    lo <= p < hi <= c.p.n,
                                    j as int == xi.perm@[p as int], j < c.p.n,
                                    rows_of(*e, pkey(c.p, j as int), a as int, b as int, true),
                                    -0x1_0000_0000_0000 <= base2 <= 0x1_0000_0000_0000,
                                    forall|i2: int| a <= i2 < b ==> #[trigger] pssupp(c.ps, i2) == e.sfirst + base2 + c.ps.supp_c@[i2],
                                    a <= i <= b,
                                    seen@.len() == old(seen)@.len(),
                                    st_ok(sn, ex@, seen@, undo@, cnt as int, s),
                                    cur_ok(c, *xi, lo as int, p as int, j as int, a as int, i as int, s),
                                decreases b - i,
                            {
                                let (c1, Ghost(s1)) = row_fast(v, lo, p, j, a, b, i, base2, sn_i, seen, undo, cnt, Ghost(s));
                                cnt = c1;
                                proof {
                                    s = s1;
                                }
                                i = i + 1;
                            }
                        }
                        proof {
                            lemma_pos_next(c, *xi, lo as int, p as int, a as int, b as int, s);
                        }
                        done = true;
                    }
                }
            }
        }
        if !done {
            let (c2, Ghost(s2)) = part_general(v, ex, lo, p, seen, undo, cnt, Ghost(s));
            cnt = c2;
            proof {
                s = s2;
            }
        }
        p = p + 1;
    }
    proof {
        lemma_pos_all(c, *xi, lo as int, hi as int, s);
    }
    // Restore the bitmap to the exclusion bitmap: the words of the listed rows, or every word after an overflow.
    if cnt > UCAP as u64 {
        restore_all(seen, ex);
    } else {
        let ulen = cnt as usize;
        let ghost mut left: Set<int> = s;
        let mut q: usize = 0;
        while q < ulen
            invariant
                ulen <= UCAP, undo@.len() == UCAP, q <= ulen,
                seen@.len() == old(seen)@.len(),
                sn <= 64 * seen@.len(),
                holds_over(seen@, ex@, left),
                forall|q2: int| 0 <= q2 < ulen ==> (#[trigger] undo@[q2]) < sn,
                forall|y: int| #[trigger] s.contains(y) ==> exists|q2: int| 0 <= q2 < ulen && undo@[q2] as int == y,
                forall|y: int| #[trigger] left.contains(y) ==> s.contains(y)
                    && forall|q2: int| 0 <= q2 < q ==> y / 64 != (#[trigger] undo@[q2]) / 64,
            decreases ulen - q,
        {
            let x = undo[q];
            restore_word(seen, ex, x, Ghost(left));
            proof {
                let l2 = left.filter(|y: int| y / 64 != (x as int) / 64);
                assert forall|y: int| #[trigger] l2.contains(y) implies s.contains(y)
                    && forall|q2: int| 0 <= q2 < q + 1 ==> y / 64 != (#[trigger] undo@[q2]) / 64 by {
                    assert(left.contains(y));
                }
                left = l2;
            }
            q = q + 1;
        }
        proof {
            assert(left =~= Set::empty()) by {
                assert forall|y: int| !left.contains(y) by {
                    if left.contains(y) {
                        let q2 = choose|q2: int| 0 <= q2 < ulen && undo@[q2] as int == y;
                        assert(y / 64 != (undo@[q2]) / 64);
                    }
                }
            }
        }
    }
    (cnt, sink)
}

// ------------------------------------------------------------------------------------------------ tasks

/// Flat groups `[q0, q1)`: the count of each.
pub struct CntTask {
    pub v: Arc<CntEnv>,
    pub q0: usize,
    pub q1: usize,
    /// One bit per supplier row, all clear.
    pub seen: Vec<u64>,
    /// Room for `UCAP` fresh supplier rows.
    pub undo: Vec<usize>,
    /// Output: one count per group (`q1 - q0` entries).
    pub counts: Vec<u64>,
}

/// A task's counts, and the xor of the touched suppkey codes (kept so the touching loads stay).
pub struct CntOut {
    pub counts: Vec<u64>,
    pub sink: u32,
}

impl WorkerTask for CntTask {
    type Output = CntOut;

    open spec fn pre(&self) -> bool {
        &&& cenv_ok(*self.v)
        &&& self.q0 <= self.q1 <= self.v.ents@.len()
        &&& holds_over(self.seen@, self.v.excl@, Set::empty())
        &&& self.undo@.len() == UCAP
        &&& self.counts@.len() == self.q1 - self.q0
    }

    open spec fn post(&self, out: CntOut) -> bool {
        &&& out.counts@.len() == self.q1 - self.q0
        &&& forall|q: int| self.q0 <= q < self.q1 ==>
            #[trigger] out.counts@[q - self.q0] as int == want(self.v.e.c, self.v.xi, self.v.ents@[q])
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.q0 as u64, self.q1 as u64)
    }

    fn run(self) -> (out: CntOut) {
        let CntTask { v, q0, q1, seen, undo, counts } = self;
        let mut seen = seen;
        let mut undo = undo;
        let mut counts = counts;
        let vr: &CntEnv = &*v;
        let ex: &Vec<u64> = &*vr.excl;
        let ents: &Vec<u32> = &*vr.ents;
        let mut sink: u32 = 0;
        let mut q = q0;
        while q < q1
            invariant
                cenv_ok(*vr), *vr == *self.v, ex@ == vr.excl@, ents@ == vr.ents@,
                q0 == self.q0, q1 == self.q1,
                q0 <= q <= q1 <= ents@.len(),
                holds_over(seen@, ex@, Set::empty()),
                undo@.len() == UCAP,
                counts@.len() == q1 - q0,
                forall|h: int| q0 <= h < q ==> #[trigger] counts@[h - q0] as int == want(vr.e.c, vr.xi, ents@[h]),
            decreases q1 - q,
        {
            let en = ents[q];
            if en == NOENT {
                counts[q - q0] = 0;
            } else {
                let lo = vr.xi.offs[en as usize] as usize;
                let hi = vr.xi.offs[en as usize + 1] as usize;
                proof {
                    lemma_offs_mono(vr.e.c, vr.xi, en as int, en as int + 1);
                    lemma_offs_mono(vr.e.c, vr.xi, en as int + 1, vr.xi.nk as int);
                }
                let (cnt, sk) = count_group(vr, ex, lo, hi, &mut seen, &mut undo);
                counts[q - q0] = cnt;
                sink = sink ^ sk;
            }
            q = q + 1;
        }
        CntOut { counts, sink }
    }
}

} // verus!
