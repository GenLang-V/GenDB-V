//! The answer's groups as a list of entries built from the scan tasks' cells. A group is a nation name and an order
//! year; its entry (`Ent`) holds the first nation row of that name (`nrep_ok`), the year and the group's cell (count,
//! exact sum, absolute sum of the amounts). `val` is a group's cell (zero without an entry). `keys_on(.., pos)`:
//! every group's cell is its sums over the lineitem rows `[0, pos)` (`tc`, `ts`, `ta`). A task's cells over
//! `[pos, stop)` are merged slot by slot (`merge_out`): inside slot `k` the nation rows below `n` are merged
//! (`slot_part`, the group terms `g*_f` restricted to nation rows below `nb`), and a merged slot's year is through
//! `stop` (`slots_done`). When an absolute sum would leave `i128`, the merge stops with the group as a witness
//! that the SUM is outside its capacity condition (`kabs > i128::MAX`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::expr::i128_max;
use super::common::isum::*;
use super::model::*;
use super::qspec::*;
use super::cells::*;
use super::scan::ScanOut;
use super::sqlsum::jkey;
use super::answer::{kcnt_f, ksum_f, kabs_f, kcnt, ksum, kabs};

verus! {

// ------------------------------------------------------------------------------------------------ group terms

/// Lineitem row `j` joins and falls in the group (nation name `name`, year `y`) through a nation row below `nb`.
pub open spec fn ghit(m: M, p: QP, name: Seq<u8>, y: int, nb: int, j: int) -> bool {
    jok(m, p, j) && nname(m, jn(m, j)) == name && jyear(m, j) == y && jn(m, j) < nb
}

pub open spec fn gc_f(m: M, p: QP, name: Seq<u8>, y: int, nb: int) -> spec_fn(int) -> int {
    |j: int| if ghit(m, p, name, y, nb, j) { 1int } else { 0int }
}

pub open spec fn gs_f(m: M, p: QP, name: Seq<u8>, y: int, nb: int) -> spec_fn(int) -> int {
    |j: int| if ghit(m, p, name, y, nb, j) { jamt(m, j) } else { 0int }
}

pub open spec fn ga_f(m: M, p: QP, name: Seq<u8>, y: int, nb: int) -> spec_fn(int) -> int {
    |j: int| if ghit(m, p, name, y, nb, j) { abs(jamt(m, j)) } else { 0int }
}

/// The merged count of a group: the rows `[0, pos)` through every nation row, then `[pos, hi)` through the nation
/// rows below `nb`; likewise the sum and the absolute sum.
pub open spec fn tc(m: M, p: QP, name: Seq<u8>, y: int, pos: int, nb: int, hi: int) -> int {
    dsum(gc_f(m, p, name, y, m.n_n), 0, pos) + dsum(gc_f(m, p, name, y, nb), pos, hi)
}

pub open spec fn ts(m: M, p: QP, name: Seq<u8>, y: int, pos: int, nb: int, hi: int) -> int {
    dsum(gs_f(m, p, name, y, m.n_n), 0, pos) + dsum(gs_f(m, p, name, y, nb), pos, hi)
}

pub open spec fn ta(m: M, p: QP, name: Seq<u8>, y: int, pos: int, nb: int, hi: int) -> int {
    dsum(ga_f(m, p, name, y, m.n_n), 0, pos) + dsum(ga_f(m, p, name, y, nb), pos, hi)
}

/// The group key of the statement for a name and a year.
pub open spec fn gkey(name: Seq<u8>, y: int) -> Row {
    seq![Val::Text(name), Val::Num { coeff: y, scale: 0 }]
}

// ------------------------------------------------------------------------------------------------ entries

/// A group entry: the first nation row `r` of the group's name, the year and the cell.
#[derive(Clone, Copy)]
pub struct Ent {
    pub r: u64,
    pub y: i64,
    pub cell: Cell,
}

pub open spec fn ename(m: M, e: Ent) -> Seq<u8> {
    nname(m, e.r as int)
}

/// `nrep[n]` is the first nation row with the name of row `n`.
pub open spec fn nrep_ok(m: M, nrep: Seq<u64>) -> bool {
    &&& nrep.len() == m.n_n
    &&& forall|n: int| 0 <= n < m.n_n ==> {
        &&& #[trigger] nrep[n] <= n
        &&& nname(m, nrep[n] as int) == nname(m, n)
        &&& forall|x: int| 0 <= x < nrep[n] ==> nname(m, x) != nname(m, n)
    }
}

/// Entries hold first nation rows and distinct (row, year) pairs.
pub open spec fn ents_wf(m: M, nrep: Seq<u64>, es: Seq<Ent>) -> bool {
    &&& forall|i: int| 0 <= i < es.len() ==> (#[trigger] es[i]).r < m.n_n && nrep[es[i].r as int] == es[i].r
    &&& forall|i: int, k: int| 0 <= i < es.len() && 0 <= k < es.len() && i != k ==>
            !((#[trigger] es[i]).r == (#[trigger] es[k]).r && es[i].y == es[k].y)
}

/// Entry `i` is the group (name, y).
pub open spec fn is_at(m: M, es: Seq<Ent>, name: Seq<u8>, y: int, i: int) -> bool {
    0 <= i < es.len() && ename(m, es[i]) == name && es[i].y as int == y
}

pub open spec fn has_key(m: M, es: Seq<Ent>, name: Seq<u8>, y: int) -> bool {
    exists|i: int| #[trigger] is_at(m, es, name, y, i)
}

/// The cell of group (name, y): its entry's, or zero.
pub open spec fn val(m: M, es: Seq<Ent>, name: Seq<u8>, y: int) -> Cell {
    if has_key(m, es, name, y) {
        es[choose|i: int| #[trigger] is_at(m, es, name, y, i)].cell
    } else {
        zero_cell()
    }
}

/// Group (name, y) is merged as (`pos`, `nb`, `hi`).
pub open spec fn key_is(m: M, p: QP, es: Seq<Ent>, name: Seq<u8>, y: int, pos: int, nb: int, hi: int) -> bool {
    let x = val(m, es, name, y);
    &&& x.cnt as int == tc(m, p, name, y, pos, nb, hi)
    &&& x.sum as int == ts(m, p, name, y, pos, nb, hi)
    &&& x.ab as int == ta(m, p, name, y, pos, nb, hi)
    &&& x.ab as int <= i128_max()
}

/// Every group is merged through the rows `[0, pos)`.
pub open spec fn keys_on(m: M, p: QP, es: Seq<Ent>, pos: int) -> bool {
    forall|name: Seq<u8>, y: int| #[trigger] key_is(m, p, es, name, y, pos, m.n_n, pos)
}

/// Some slot before `k` holds year `y`.
pub open spec fn in_first(years: Seq<i64>, k: int, y: int) -> bool {
    exists|t: int| 0 <= t < k && #[trigger] years[t] as int == y
}

/// The end of the merged rows of year `y` once the slots before `k` are merged.
pub open spec fn hi_done(years: Seq<i64>, k: int, y: int, pos: int, stop: int) -> int {
    if in_first(years, k, y) { stop } else { pos }
}

/// The slots before `k` of a task over `[pos, stop)` are merged.
pub open spec fn slots_done(m: M, p: QP, es: Seq<Ent>, years: Seq<i64>, k: int, pos: int, stop: int) -> bool {
    forall|name: Seq<u8>, y: int| #[trigger] key_is(m, p, es, name, y, pos, m.n_n, hi_done(years, k, y, pos, stop))
}

/// The nation row bound of year `y` while slot `k` is merged through the nation rows below `n`.
pub open spec fn nb_part(m: M, years: Seq<i64>, k: int, n: int, y: int) -> int {
    if y == years[k] as int { n } else { m.n_n }
}

/// The end of the merged rows of year `y` while slot `k` is merged.
pub open spec fn hi_part(years: Seq<i64>, k: int, y: int, pos: int, stop: int) -> int {
    if y == years[k] as int || in_first(years, k, y) { stop } else { pos }
}

/// The slots before `k` and the nation rows below `n` of slot `k` are merged.
pub open spec fn slot_part(m: M, p: QP, es: Seq<Ent>, years: Seq<i64>, k: int, n: int, pos: int, stop: int) -> bool {
    forall|name: Seq<u8>, y: int| #[trigger] key_is(m, p, es, name, y, pos, nb_part(m, years, k, n, y), hi_part(years, k, y, pos, stop))
}

// ------------------------------------------------------------------------------------------------ sums

/// Equal terms give equal sums.
pub proof fn lemma_dsum_ext(f: spec_fn(int) -> int, g: spec_fn(int) -> int, a: int, b: int)
    requires a <= b, forall|j: int| a <= j < b ==> #[trigger] f(j) == g(j),
    ensures dsum(f, a, b) == dsum(g, a, b),
    decreases b - a,
{
    if a < b && b >= 1 {
        lemma_dsum_ext(f, g, a, b - 1);
        lemma_dsum_step(f, a, b - 1);
        lemma_dsum_step(g, a, b - 1);
    }
}

/// Termwise addition.
pub proof fn lemma_dsum_add(f: spec_fn(int) -> int, g: spec_fn(int) -> int, h: spec_fn(int) -> int, a: int, b: int)
    requires 0 <= a <= b, forall|j: int| a <= j < b ==> #[trigger] h(j) == f(j) + g(j),
    ensures dsum(h, a, b) == dsum(f, a, b) + dsum(g, a, b),
    decreases b - a,
{
    if a < b {
        lemma_dsum_add(f, g, h, a, b - 1);
        lemma_dsum_step(f, a, b - 1);
        lemma_dsum_step(g, a, b - 1);
        lemma_dsum_step(h, a, b - 1);
    }
}

/// Termwise order.
pub proof fn lemma_dsum_mono(f: spec_fn(int) -> int, g: spec_fn(int) -> int, a: int, b: int)
    requires 0 <= a <= b, forall|j: int| a <= j < b ==> #[trigger] f(j) <= g(j),
    ensures dsum(f, a, b) <= dsum(g, a, b),
    decreases b - a,
{
    if a < b {
        lemma_dsum_mono(f, g, a, b - 1);
        lemma_dsum_step(f, a, b - 1);
        lemma_dsum_step(g, a, b - 1);
    }
}

/// Bounds of a group's sums over `[a, b)`.
pub proof fn lemma_g_bounds(m: M, p: QP, name: Seq<u8>, y: int, nb: int, a: int, b: int)
    requires 0 <= a <= b,
    ensures
        0 <= dsum(gc_f(m, p, name, y, nb), a, b) <= b - a,
        0 <= dsum(ga_f(m, p, name, y, nb), a, b),
        -dsum(ga_f(m, p, name, y, nb), a, b) <= dsum(gs_f(m, p, name, y, nb), a, b) <= dsum(ga_f(m, p, name, y, nb), a, b),
    decreases b - a,
{
    if a < b {
        lemma_g_bounds(m, p, name, y, nb, a, b - 1);
        lemma_dsum_step(gc_f(m, p, name, y, nb), a, b - 1);
        lemma_dsum_step(gs_f(m, p, name, y, nb), a, b - 1);
        lemma_dsum_step(ga_f(m, p, name, y, nb), a, b - 1);
    }
}

/// The terms through the nation rows below `n + 1` are those below `n` plus nation row `n`'s cell terms.
proof fn lemma_g_next(m: M, p: QP, y: int, n: int, j: int)
    requires model_ok(m), 0 <= n < m.n_n,
    ensures
        gc_f(m, p, nname(m, n), y, n + 1)(j) == gc_f(m, p, nname(m, n), y, n)(j) + cnt_f(m, p, n, y)(j),
        gs_f(m, p, nname(m, n), y, n + 1)(j) == gs_f(m, p, nname(m, n), y, n)(j) + sum_f(m, p, n, y)(j),
        ga_f(m, p, nname(m, n), y, n + 1)(j) == ga_f(m, p, nname(m, n), y, n)(j) + abs_f(m, p, n, y)(j),
{
    lemma_terms_at(m, p, n, y, j);
    super::lookups::lemma_npos(m, snk(m, ls(m, j)), 0);
}

/// Groups of another name gain nothing from nation row `n`.
proof fn lemma_g_other(m: M, p: QP, name: Seq<u8>, y: int, n: int, j: int)
    requires model_ok(m), 0 <= n < m.n_n, name != nname(m, n),
    ensures
        gc_f(m, p, name, y, n + 1)(j) == gc_f(m, p, name, y, n)(j),
        gs_f(m, p, name, y, n + 1)(j) == gs_f(m, p, name, y, n)(j),
        ga_f(m, p, name, y, n + 1)(j) == ga_f(m, p, name, y, n)(j),
{
    super::lookups::lemma_npos(m, snk(m, ls(m, j)), 0);
}

/// Through no nation row, a group has no terms.
proof fn lemma_g_none(m: M, p: QP, name: Seq<u8>, y: int, a: int, b: int)
    requires model_ok(m), 0 <= a <= b,
    ensures
        dsum(gc_f(m, p, name, y, 0), a, b) == 0,
        dsum(gs_f(m, p, name, y, 0), a, b) == 0,
        dsum(ga_f(m, p, name, y, 0), a, b) == 0,
{
    assert forall|j: int| a <= j < b implies #[trigger] gc_f(m, p, name, y, 0)(j) == 0 by {
        super::lookups::lemma_npos(m, snk(m, ls(m, j)), 0);
    }
    assert forall|j: int| a <= j < b implies #[trigger] gs_f(m, p, name, y, 0)(j) == 0 by {
        super::lookups::lemma_npos(m, snk(m, ls(m, j)), 0);
    }
    assert forall|j: int| a <= j < b implies #[trigger] ga_f(m, p, name, y, 0)(j) == 0 by {
        super::lookups::lemma_npos(m, snk(m, ls(m, j)), 0);
    }
    lemma_dsum_zero(gc_f(m, p, name, y, 0), a, b);
    lemma_dsum_zero(gs_f(m, p, name, y, 0), a, b);
    lemma_dsum_zero(ga_f(m, p, name, y, 0), a, b);
}

/// The group terms through every nation row are the statement's group terms.
pub proof fn lemma_g_k(m: M, p: QP, name: Seq<u8>, y: int, j: int)
    ensures
        gc_f(m, p, name, y, m.n_n)(j) == kcnt_f(m, p, gkey(name, y))(j),
        gs_f(m, p, name, y, m.n_n)(j) == ksum_f(m, p, gkey(name, y))(j),
        ga_f(m, p, name, y, m.n_n)(j) == kabs_f(m, p, gkey(name, y))(j),
{
    let k = gkey(name, y);
    if jok(m, p, j) {
        let jk = jkey(m, j);
        if nname(m, jn(m, j)) == name && jyear(m, j) == y {
            assert(jk =~= k);
        }
        if jk == k {
            assert(jk[0] == k[0] && jk[1] == k[1]);
        }
    }
}

/// A group's sums over `[0, l_n)` are the statement's group accumulators.
pub proof fn lemma_g_total(m: M, p: QP, name: Seq<u8>, y: int)
    requires m.l_n >= 0,
    ensures
        dsum(gc_f(m, p, name, y, m.n_n), 0, m.l_n) == kcnt(m, p, gkey(name, y)),
        dsum(gs_f(m, p, name, y, m.n_n), 0, m.l_n) == ksum(m, p, gkey(name, y)),
        dsum(ga_f(m, p, name, y, m.n_n), 0, m.l_n) == kabs(m, p, gkey(name, y)),
{
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] gc_f(m, p, name, y, m.n_n)(j) == kcnt_f(m, p, gkey(name, y))(j) by {
        lemma_g_k(m, p, name, y, j);
    }
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] gs_f(m, p, name, y, m.n_n)(j) == ksum_f(m, p, gkey(name, y))(j) by {
        lemma_g_k(m, p, name, y, j);
    }
    assert forall|j: int| 0 <= j < m.l_n implies #[trigger] ga_f(m, p, name, y, m.n_n)(j) == kabs_f(m, p, gkey(name, y))(j) by {
        lemma_g_k(m, p, name, y, j);
    }
    lemma_isum_ext(m.l_n, gc_f(m, p, name, y, m.n_n), kcnt_f(m, p, gkey(name, y)));
    lemma_isum_ext(m.l_n, gs_f(m, p, name, y, m.n_n), ksum_f(m, p, gkey(name, y)));
    lemma_isum_ext(m.l_n, ga_f(m, p, name, y, m.n_n), kabs_f(m, p, gkey(name, y)));
}

/// A merged absolute sum is at most the group's whole absolute mass.
pub proof fn lemma_ta_le(m: M, p: QP, name: Seq<u8>, y: int, pos: int, nb: int, hi: int)
    requires 0 <= pos <= hi <= m.l_n, nb <= m.n_n,
    ensures ta(m, p, name, y, pos, nb, hi) <= kabs(m, p, gkey(name, y)),
{
    let f = ga_f(m, p, name, y, m.n_n);
    assert forall|j: int| pos <= j < hi implies #[trigger] ga_f(m, p, name, y, nb)(j) <= f(j) by {}
    lemma_dsum_mono(ga_f(m, p, name, y, nb), f, pos, hi);
    lemma_dsum_split(f, 0, pos, hi);
    lemma_g_bounds(m, p, name, y, m.n_n, hi, m.l_n);
    lemma_dsum_split(f, 0, hi, m.l_n);
    lemma_g_total(m, p, name, y);
}

/// A task's overflowing cell: its group's absolute mass is beyond `i128::MAX`.
pub proof fn lemma_cell_ovf(m: M, p: QP, n: int, y: int, lo: int, hi: int)
    requires
        model_ok(m), 0 <= lo <= hi <= m.l_n, 0 <= n < m.n_n,
        dsum(abs_f(m, p, n, y), lo, hi) > i128_max(),
    ensures kabs(m, p, gkey(nname(m, n), y)) > i128_max(),
{
    let name = nname(m, n);
    assert forall|j: int| lo <= j < hi implies #[trigger] abs_f(m, p, n, y)(j) <= ga_f(m, p, name, y, m.n_n)(j) by {
        lemma_terms_at(m, p, n, y, j);
    }
    lemma_dsum_mono(abs_f(m, p, n, y), ga_f(m, p, name, y, m.n_n), lo, hi);
    lemma_g_bounds(m, p, name, y, m.n_n, 0, lo);
    lemma_dsum_split(ga_f(m, p, name, y, m.n_n), 0, lo, hi);
    lemma_ta_le(m, p, name, y, hi, m.n_n, hi);
}

// ------------------------------------------------------------------------------------------------ entries

/// Rows of the same name have the same first row.
proof fn lemma_nrep_same(m: M, nrep: Seq<u64>, a: int, b: int)
    requires nrep_ok(m, nrep), 0 <= a < m.n_n, 0 <= b < m.n_n,
    ensures (nname(m, a) == nname(m, b)) == (nrep[a] == nrep[b]),
{
    if nname(m, a) == nname(m, b) {
        if nrep[a] < nrep[b] {
            assert(nname(m, nrep[a] as int) != nname(m, b));
        } else if nrep[b] < nrep[a] {
            assert(nname(m, nrep[b] as int) != nname(m, a));
        }
    }
}

/// A first row is its own first row.
proof fn lemma_nrep_first(m: M, nrep: Seq<u64>, n: int)
    requires nrep_ok(m, nrep), 0 <= n < m.n_n,
    ensures nrep[nrep[n] as int] == nrep[n],
{
    let r = nrep[n] as int;
    assert(nrep[r] <= r);
    if nrep[r] < r {
        assert(nname(m, nrep[r] as int) == nname(m, r));
        assert(nname(m, r) == nname(m, n));
    }
}

/// An entry of the group is the entry `val` reads.
pub proof fn lemma_val_at(m: M, nrep: Seq<u64>, es: Seq<Ent>, name: Seq<u8>, y: int, i: int)
    requires nrep_ok(m, nrep), ents_wf(m, nrep, es), is_at(m, es, name, y, i),
    ensures has_key(m, es, name, y), val(m, es, name, y) == es[i].cell,
{
    let k = choose|k: int| #[trigger] is_at(m, es, name, y, k);
    if k != i {
        lemma_nrep_same(m, nrep, es[i].r as int, es[k].r as int);
    }
}

/// The entry for nation row `n`'s name and year `y` is found by its first row.
proof fn lemma_match(m: M, nrep: Seq<u64>, es: Seq<Ent>, n: int, y: int, i: int)
    requires nrep_ok(m, nrep), ents_wf(m, nrep, es), 0 <= n < m.n_n, 0 <= i < es.len(),
    ensures is_at(m, es, nname(m, n), y, i) == (es[i].r == nrep[n] && es[i].y as int == y),
{
    lemma_nrep_same(m, nrep, es[i].r as int, n);
}

/// The entry update of the group of nation row `n` and year `y`.
pub open spec fn plus(x: Cell, d: Cell) -> Cell {
    Cell { cnt: (x.cnt + d.cnt) as u64, sum: (x.sum + d.sum) as i128, ab: (x.ab + d.ab) as u128 }
}

/// Add cell `d` to the group (nation row `n`'s name, year `y`): `false` when its absolute sum would leave `i128`
/// (nothing changed).
fn add_cell(es: &mut Vec<Ent>, nrep: &Vec<u64>, n: usize, y: i64, d: Cell, Ghost(m): Ghost<M>) -> (ok: bool)
    requires
        nrep_ok(m, nrep@), ents_wf(m, nrep@, old(es)@), n < m.n_n,
        d.ab <= i128_max(), -(d.ab as int) <= d.sum <= d.ab,
        val(m, old(es)@, nname(m, n as int), y as int).ab <= i128_max(),
        -(val(m, old(es)@, nname(m, n as int), y as int).ab as int) <= val(m, old(es)@, nname(m, n as int), y as int).sum
            <= val(m, old(es)@, nname(m, n as int), y as int).ab,
        val(m, old(es)@, nname(m, n as int), y as int).cnt + d.cnt <= u64::MAX,
    ensures
        ents_wf(m, nrep@, final(es)@),
        ok ==> forall|name: Seq<u8>, y2: int| #[trigger] val(m, final(es)@, name, y2) ==
            if name == nname(m, n as int) && y2 == y as int { plus(val(m, old(es)@, name, y2), d) } else { val(m, old(es)@, name, y2) },
        ok ==> val(m, old(es)@, nname(m, n as int), y as int).ab + d.ab <= i128_max(),
        !ok ==> final(es)@ == old(es)@
            && val(m, old(es)@, nname(m, n as int), y as int).ab + d.ab > i128_max(),
{
    let ghost e0 = es@;
    let ghost name0 = nname(m, n as int);
    let r = nrep[n];
    let mut i: usize = 0;
    while i < es.len()
        invariant
            nrep_ok(m, nrep@), ents_wf(m, nrep@, e0), es@ == e0, e0 == old(es)@, n < m.n_n, r == nrep@[n as int],
            name0 == nname(m, n as int),
            d.ab <= i128_max(), -(d.ab as int) <= d.sum <= d.ab,
            val(m, e0, name0, y as int).ab <= i128_max(),
            -(val(m, e0, name0, y as int).ab as int) <= val(m, e0, name0, y as int).sum <= val(m, e0, name0, y as int).ab,
            val(m, e0, name0, y as int).cnt + d.cnt <= u64::MAX,
            i <= es@.len(),
            forall|k: int| 0 <= k < i ==> !is_at(m, e0, name0, y as int, k),
        decreases es@.len() - i,
    {
        proof { lemma_match(m, nrep@, e0, n as int, y as int, i as int); }
        let ei = es[i];
        if ei.r == r && ei.y == y {
            let old_cell = ei.cell;
            proof {
                assert(ei == e0[i as int]);
                assert(is_at(m, e0, name0, y as int, i as int));
                lemma_val_at(m, nrep@, e0, name0, y as int, i as int);
                assert(d.ab <= 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128);
            }
            if old_cell.ab > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 - d.ab {
                proof {
                    assert(es@ == old(es)@);
                    assert(val(m, e0, name0, y as int) == old_cell);
                    assert(old_cell.ab + d.ab > i128_max());
                }
                return false;
            }
            let x = Cell { cnt: old_cell.cnt + d.cnt, sum: old_cell.sum + d.sum, ab: old_cell.ab + d.ab };
            let e = Ent { r, y, cell: x };
            es.set(i, e);
            proof {
                let e1 = es@;
                assert forall|a: int| 0 <= a < e1.len() implies (#[trigger] e1[a]).r < m.n_n && nrep@[e1[a].r as int] == e1[a].r by {
                    assert(e0[a].r == e1[a].r);
                }
                assert forall|a: int, b: int| 0 <= a < e1.len() && 0 <= b < e1.len() && a != b implies
                    !((#[trigger] e1[a]).r == (#[trigger] e1[b]).r && e1[a].y == e1[b].y) by {
                    assert(e0[a].r == e1[a].r && e0[a].y == e1[a].y);
                    assert(e0[b].r == e1[b].r && e0[b].y == e1[b].y);
                }
                assert forall|name: Seq<u8>, y2: int| #[trigger] val(m, e1, name, y2) ==
                    if name == name0 && y2 == y as int { plus(val(m, e0, name, y2), d) } else { val(m, e0, name, y2) } by {
                    assert forall|a: int| #[trigger] is_at(m, e1, name, y2, a) == is_at(m, e0, name, y2, a) by {
                        if 0 <= a < e1.len() { assert(e0[a].r == e1[a].r && e0[a].y == e1[a].y); }
                    }
                    if has_key(m, e0, name, y2) {
                        let a = choose|a: int| #[trigger] is_at(m, e0, name, y2, a);
                        lemma_val_at(m, nrep@, e0, name, y2, a);
                        lemma_val_at(m, nrep@, e1, name, y2, a);
                        if a == i as int {
                            assert(name == name0 && y2 == y as int);
                        } else {
                            assert(!(name == name0 && y2 == y as int)) by {
                                if name == name0 && y2 == y as int {
                                    lemma_nrep_same(m, nrep@, e0[a].r as int, e0[i as int].r as int);
                                }
                            }
                        }
                    } else {
                        assert(!has_key(m, e1, name, y2));
                    }
                }
            }
            return true;
        }
        i = i + 1;
    }
    // no entry: a new one when `d` is not zero
    if d.cnt == 0 && d.sum == 0 && d.ab == 0 {
        proof {
            assert(!has_key(m, e0, name0, y as int));
            assert forall|name: Seq<u8>, y2: int| #[trigger] val(m, es@, name, y2) ==
                if name == name0 && y2 == y as int { plus(val(m, e0, name, y2), d) } else { val(m, e0, name, y2) } by {
                if name == name0 && y2 == y as int {
                    assert(plus(zero_cell(), d) == zero_cell());
                }
            }
        }
        return true;
    }
    proof { lemma_nrep_first(m, nrep@, n as int); }
    es.push(Ent { r, y, cell: d });
    proof {
        let e1 = es@;
        let last = e0.len() as int;
        assert(e1[last].r == r && e1[last].y == y && e1[last].cell == d);
        assert forall|a: int| 0 <= a < e1.len() implies (#[trigger] e1[a]).r < m.n_n && nrep@[e1[a].r as int] == e1[a].r by {
            if a < last { assert(e1[a] == e0[a]); }
        }
        assert forall|a: int, b: int| 0 <= a < e1.len() && 0 <= b < e1.len() && a != b implies
            !((#[trigger] e1[a]).r == (#[trigger] e1[b]).r && e1[a].y == e1[b].y) by {
            if a < last && b < last {
                assert(e1[a] == e0[a] && e1[b] == e0[b]);
            } else if a == last {
                assert(e1[b] == e0[b]);
                lemma_match(m, nrep@, e0, n as int, y as int, b);
            } else {
                assert(e1[a] == e0[a]);
                lemma_match(m, nrep@, e0, n as int, y as int, a);
            }
        }
        assert(is_at(m, e1, name0, y as int, last));
        assert forall|name: Seq<u8>, y2: int| #[trigger] val(m, e1, name, y2) ==
            if name == name0 && y2 == y as int { plus(val(m, e0, name, y2), d) } else { val(m, e0, name, y2) } by {
            if name == name0 && y2 == y as int {
                lemma_val_at(m, nrep@, e1, name, y2, last);
                assert(!has_key(m, e0, name, y2));
                assert(plus(zero_cell(), d) == d);
            } else {
                assert forall|a: int| #[trigger] is_at(m, e1, name, y2, a) == is_at(m, e0, name, y2, a) by {
                    if 0 <= a < last { assert(e1[a] == e0[a]); }
                }
                if has_key(m, e0, name, y2) {
                    let a = choose|a: int| #[trigger] is_at(m, e0, name, y2, a);
                    lemma_val_at(m, nrep@, e0, name, y2, a);
                    lemma_val_at(m, nrep@, e1, name, y2, a);
                } else {
                    assert(!has_key(m, e1, name, y2));
                }
            }
        }
    }
    true
}

// ------------------------------------------------------------------------------------------------ merging a task

/// Merged slots before `k`, nothing of slot `k` yet.
proof fn lemma_part_start(m: M, p: QP, es: Seq<Ent>, years: Seq<i64>, ny: int, k: int, pos: int, stop: int)
    requires
        model_ok(m), 0 <= pos <= stop, 0 <= k < ny, years_ok(years, ny),
        slots_done(m, p, es, years, k, pos, stop),
    ensures slot_part(m, p, es, years, k, 0, pos, stop),
{
    assert forall|name: Seq<u8>, y: int| #[trigger] key_is(m, p, es, name, y, pos, nb_part(m, years, k, 0, y), hi_part(years, k, y, pos, stop)) by {
        assert(key_is(m, p, es, name, y, pos, m.n_n, hi_done(years, k, y, pos, stop)));
        if y == years[k] as int {
            assert(!in_first(years, k, y)) by {
                if in_first(years, k, y) {
                    let t = choose|t: int| 0 <= t < k && #[trigger] years[t] as int == y;
                    assert(years[t] != years[k]);
                }
            }
            lemma_g_none(m, p, name, y, pos, stop);
            lemma_dsum_empty(gc_f(m, p, name, y, m.n_n), pos);
            lemma_dsum_empty(gs_f(m, p, name, y, m.n_n), pos);
            lemma_dsum_empty(ga_f(m, p, name, y, m.n_n), pos);
        }
    }
}

/// Every nation row of slot `k` merged: the slots before `k + 1` are merged.
proof fn lemma_part_end(m: M, p: QP, es: Seq<Ent>, years: Seq<i64>, k: int, pos: int, stop: int)
    requires 0 <= k, slot_part(m, p, es, years, k, m.n_n, pos, stop),
    ensures slots_done(m, p, es, years, k + 1, pos, stop),
{
    assert forall|name: Seq<u8>, y: int| #[trigger] key_is(m, p, es, name, y, pos, m.n_n, hi_done(years, k + 1, y, pos, stop)) by {
        assert(key_is(m, p, es, name, y, pos, nb_part(m, years, k, m.n_n, y), hi_part(years, k, y, pos, stop)));
        if y == years[k] as int {
            assert(years[k] as int == y);
            assert(in_first(years, k + 1, y));
        } else {
            assert(in_first(years, k + 1, y) == in_first(years, k, y)) by {
                if in_first(years, k + 1, y) {
                    let t = choose|t: int| 0 <= t < k + 1 && #[trigger] years[t] as int == y;
                    assert(t < k);
                }
            }
        }
    }
}

/// Every slot merged: every group is merged through `[0, stop)` (rows of other years do not join).
proof fn lemma_done_all(m: M, p: QP, es: Seq<Ent>, cells: Seq<Cell>, years: Seq<i64>, ny: int, cap: int, nn: int, pos: int, stop: int)
    requires
        cells_inv(m, p, cells, years, ny, cap, nn, pos, stop),
        slots_done(m, p, es, years, ny, pos, stop),
    ensures keys_on(m, p, es, stop),
{
    assert forall|name: Seq<u8>, y: int| #[trigger] key_is(m, p, es, name, y, stop, m.n_n, stop) by {
        assert(key_is(m, p, es, name, y, pos, m.n_n, hi_done(years, ny, y, pos, stop)));
        lemma_dsum_empty(gc_f(m, p, name, y, m.n_n), stop);
        lemma_dsum_empty(gs_f(m, p, name, y, m.n_n), stop);
        lemma_dsum_empty(ga_f(m, p, name, y, m.n_n), stop);
        lemma_dsum_split(gc_f(m, p, name, y, m.n_n), 0, pos, stop);
        lemma_dsum_split(gs_f(m, p, name, y, m.n_n), 0, pos, stop);
        lemma_dsum_split(ga_f(m, p, name, y, m.n_n), 0, pos, stop);
        if !in_first(years, ny, y) {
            assert forall|j: int| pos <= j < stop implies #[trigger] gc_f(m, p, name, y, m.n_n)(j) == 0 by {
                if ghit(m, p, name, y, m.n_n, j) {
                    let t = choose|t: int| 0 <= t < ny && years[t] as int == jyear(m, j);
                    assert(years[t] as int == y);
                }
            }
            assert forall|j: int| pos <= j < stop implies #[trigger] gs_f(m, p, name, y, m.n_n)(j) == 0 by {
                if ghit(m, p, name, y, m.n_n, j) {
                    let t = choose|t: int| 0 <= t < ny && years[t] as int == jyear(m, j);
                    assert(years[t] as int == y);
                }
            }
            assert forall|j: int| pos <= j < stop implies #[trigger] ga_f(m, p, name, y, m.n_n)(j) == 0 by {
                if ghit(m, p, name, y, m.n_n, j) {
                    let t = choose|t: int| 0 <= t < ny && years[t] as int == jyear(m, j);
                    assert(years[t] as int == y);
                }
            }
            lemma_dsum_zero(gc_f(m, p, name, y, m.n_n), pos, stop);
            lemma_dsum_zero(gs_f(m, p, name, y, m.n_n), pos, stop);
            lemma_dsum_zero(ga_f(m, p, name, y, m.n_n), pos, stop);
            lemma_dsum_empty(gc_f(m, p, name, y, m.n_n), pos);
            lemma_dsum_empty(gs_f(m, p, name, y, m.n_n), pos);
            lemma_dsum_empty(ga_f(m, p, name, y, m.n_n), pos);
        }
    }
}

/// Nation row `n`'s cell `x` of slot `k` added to its group: the nation rows below `n + 1` are merged.
proof fn lemma_part_step(m: M, p: QP, e0: Seq<Ent>, e1: Seq<Ent>, years: Seq<i64>, k: int, n: int, pos: int, stop: int, x: Cell)
    requires
        model_ok(m), 0 <= pos <= stop, 0 <= n < m.n_n,
        slot_part(m, p, e0, years, k, n, pos, stop),
        cell_is(m, p, x, n, years[k] as int, pos, stop),
        forall|name: Seq<u8>, y2: int| #[trigger] val(m, e1, name, y2) ==
            if name == nname(m, n) && y2 == years[k] as int { plus(val(m, e0, name, y2), x) } else { val(m, e0, name, y2) },
        val(m, e0, nname(m, n), years[k] as int).cnt + x.cnt <= u64::MAX,
        val(m, e0, nname(m, n), years[k] as int).ab + x.ab <= i128_max(),
        -(val(m, e0, nname(m, n), years[k] as int).ab as int) <= val(m, e0, nname(m, n), years[k] as int).sum
            <= val(m, e0, nname(m, n), years[k] as int).ab,
        -(x.ab as int) <= x.sum <= x.ab,
    ensures slot_part(m, p, e1, years, k, n + 1, pos, stop),
{
    let yk = years[k] as int;
    assert forall|name: Seq<u8>, y: int| #[trigger] key_is(m, p, e1, name, y, pos, nb_part(m, years, k, n + 1, y), hi_part(years, k, y, pos, stop)) by {
        assert(key_is(m, p, e0, name, y, pos, nb_part(m, years, k, n, y), hi_part(years, k, y, pos, stop)));
        assert(val(m, e1, name, y) == if name == nname(m, n) && y == yk { plus(val(m, e0, name, y), x) } else { val(m, e0, name, y) });
        if y == yk {
            if name == nname(m, n) {
                assert forall|j: int| pos <= j < stop implies #[trigger] gc_f(m, p, name, y, n + 1)(j) == gc_f(m, p, name, y, n)(j) + cnt_f(m, p, n, y)(j) by {
                    lemma_g_next(m, p, y, n, j);
                }
                assert forall|j: int| pos <= j < stop implies #[trigger] gs_f(m, p, name, y, n + 1)(j) == gs_f(m, p, name, y, n)(j) + sum_f(m, p, n, y)(j) by {
                    lemma_g_next(m, p, y, n, j);
                }
                assert forall|j: int| pos <= j < stop implies #[trigger] ga_f(m, p, name, y, n + 1)(j) == ga_f(m, p, name, y, n)(j) + abs_f(m, p, n, y)(j) by {
                    lemma_g_next(m, p, y, n, j);
                }
                lemma_dsum_add(gc_f(m, p, name, y, n), cnt_f(m, p, n, y), gc_f(m, p, name, y, n + 1), pos, stop);
                lemma_dsum_add(gs_f(m, p, name, y, n), sum_f(m, p, n, y), gs_f(m, p, name, y, n + 1), pos, stop);
                lemma_dsum_add(ga_f(m, p, name, y, n), abs_f(m, p, n, y), ga_f(m, p, name, y, n + 1), pos, stop);
            } else {
                assert forall|j: int| pos <= j < stop implies #[trigger] gc_f(m, p, name, y, n + 1)(j) == gc_f(m, p, name, y, n)(j) by {
                    lemma_g_other(m, p, name, y, n, j);
                }
                assert forall|j: int| pos <= j < stop implies #[trigger] gs_f(m, p, name, y, n + 1)(j) == gs_f(m, p, name, y, n)(j) by {
                    lemma_g_other(m, p, name, y, n, j);
                }
                assert forall|j: int| pos <= j < stop implies #[trigger] ga_f(m, p, name, y, n + 1)(j) == ga_f(m, p, name, y, n)(j) by {
                    lemma_g_other(m, p, name, y, n, j);
                }
                lemma_dsum_ext(gc_f(m, p, name, y, n + 1), gc_f(m, p, name, y, n), pos, stop);
                lemma_dsum_ext(gs_f(m, p, name, y, n + 1), gs_f(m, p, name, y, n), pos, stop);
                lemma_dsum_ext(ga_f(m, p, name, y, n + 1), ga_f(m, p, name, y, n), pos, stop);
            }
        }
    }
}

/// Merge slot `k` of a task's cells over `[pos, stop)`: `None` when merged, else a group (nation row, year) whose
/// absolute mass is beyond `i128::MAX`.
fn merge_slot(es: &mut Vec<Ent>, out: &ScanOut, nrep: &Vec<u64>, nn: usize, k: usize,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(pos): Ghost<int>, Ghost(cap): Ghost<int>) -> (r: Option<(usize, i64)>)
    requires
        model_ok(m), nrep_ok(m, nrep@), ents_wf(m, nrep@, old(es)@),
        nn == m.n_n, 0 <= pos <= out.stop <= m.l_n,
        cells_inv(m, p, out.cells@, out.years@, out.ny as int, cap, nn as int, pos, out.stop as int),
        k < out.ny,
        slots_done(m, p, old(es)@, out.years@, k as int, pos, out.stop as int),
    ensures
        ents_wf(m, nrep@, final(es)@),
        r is None ==> slots_done(m, p, final(es)@, out.years@, k + 1, pos, out.stop as int),
        r matches Some((n, y)) ==> n < m.n_n && kabs(m, p, gkey(nname(m, n as int), y as int)) > i128_max(),
{
    let ghost stop = out.stop as int;
    let ghost years = out.years@;
    let y = out.years[k];
    proof { lemma_part_start(m, p, es@, years, out.ny as int, k as int, pos, stop); }
    let mut n: usize = 0;
    while n < nn
        invariant
            model_ok(m), nrep_ok(m, nrep@), ents_wf(m, nrep@, es@),
            nn == m.n_n, 0 <= pos <= stop <= m.l_n, stop == out.stop, years == out.years@, y == years[k as int],
            cells_inv(m, p, out.cells@, years, out.ny as int, cap, nn as int, pos, stop),
            k < out.ny,
            n <= nn,
            slot_part(m, p, es@, years, k as int, n as int, pos, stop),
        decreases nn - n,
    {
        let len = out.cells.len();
        proof {
            lemma_cell_bound(nn as int, cap, k as int, n as int);
            assert(k * nn <= k * nn + n) by (nonlinear_arith) requires n >= 0;
        }
        let x = out.cells[k * nn + n];
        let ghost name = nname(m, n as int);
        proof {
            assert(cell_is(m, p, out.cells@[k * nn + n], n as int, years[k as int] as int, pos, stop));
            super::scan::lemma_dsum_le(m, p, n as int, y as int, pos, stop);
            assert(key_is(m, p, es@, name, y as int, pos, nb_part(m, years, k as int, n as int, y as int), hi_part(years, k as int, y as int, pos, stop)));
            lemma_g_bounds(m, p, name, y as int, m.n_n, 0, pos);
            lemma_g_bounds(m, p, name, y as int, n as int, pos, stop);
            // the merged count after this row stays below the rows
            assert forall|j: int| pos <= j < stop implies #[trigger] gc_f(m, p, name, y as int, n as int + 1)(j)
                == gc_f(m, p, name, y as int, n as int)(j) + cnt_f(m, p, n as int, y as int)(j) by {
                lemma_g_next(m, p, y as int, n as int, j);
            }
            lemma_dsum_add(gc_f(m, p, name, y as int, n as int), cnt_f(m, p, n as int, y as int), gc_f(m, p, name, y as int, n as int + 1), pos, stop);
            lemma_g_bounds(m, p, name, y as int, n as int + 1, pos, stop);
            assert(m.l_n <= u64::MAX) by { assert(frame_ok(m.l_n, m.l_bs, m.l_nb)); }
        }
        let ghost e0 = es@;
        if !add_cell(es, nrep, n, y, x, Ghost(m)) {
            proof {
                assert forall|j: int| pos <= j < stop implies #[trigger] ga_f(m, p, name, y as int, n as int + 1)(j)
                    == ga_f(m, p, name, y as int, n as int)(j) + abs_f(m, p, n as int, y as int)(j) by {
                    lemma_g_next(m, p, y as int, n as int, j);
                }
                lemma_dsum_add(ga_f(m, p, name, y as int, n as int), abs_f(m, p, n as int, y as int), ga_f(m, p, name, y as int, n as int + 1), pos, stop);
                lemma_ta_le(m, p, name, y as int, pos, n as int + 1, stop);
            }
            return Some((n, y));
        }
        proof {
            lemma_part_step(m, p, e0, es@, years, k as int, n as int, pos, stop, x);
        }
        n = n + 1;
    }
    proof { lemma_part_end(m, p, es@, years, k as int, pos, stop); }
    None
}

/// Merge a task's cells over `[pos, out.stop)` into the entries (every group merged through `[0, pos)`): `None`
/// when every group is merged through `[0, out.stop)`, else a group whose absolute mass is beyond `i128::MAX`.
pub fn merge_out(es: &mut Vec<Ent>, out: &ScanOut, nrep: &Vec<u64>, nn: usize,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(pos): Ghost<int>, Ghost(cap): Ghost<int>) -> (r: Option<(usize, i64)>)
    requires
        model_ok(m), nrep_ok(m, nrep@), ents_wf(m, nrep@, old(es)@),
        nn == m.n_n, 0 <= pos <= out.stop <= m.l_n,
        cells_inv(m, p, out.cells@, out.years@, out.ny as int, cap, nn as int, pos, out.stop as int),
        keys_on(m, p, old(es)@, pos),
    ensures
        ents_wf(m, nrep@, final(es)@),
        r is None ==> keys_on(m, p, final(es)@, out.stop as int),
        r matches Some((n, y)) ==> n < m.n_n && kabs(m, p, gkey(nname(m, n as int), y as int)) > i128_max(),
{
    proof {
        assert forall|name: Seq<u8>, y: int| #[trigger] key_is(m, p, es@, name, y, pos, m.n_n, hi_done(out.years@, 0, y, pos, out.stop as int)) by {
            assert(key_is(m, p, es@, name, y, pos, m.n_n, pos));
        }
    }
    let mut k: usize = 0;
    while k < out.ny
        invariant
            model_ok(m), nrep_ok(m, nrep@), ents_wf(m, nrep@, es@),
            nn == m.n_n, 0 <= pos <= out.stop <= m.l_n,
            cells_inv(m, p, out.cells@, out.years@, out.ny as int, cap, nn as int, pos, out.stop as int),
            k <= out.ny,
            slots_done(m, p, es@, out.years@, k as int, pos, out.stop as int),
        decreases out.ny - k,
    {
        match merge_slot(es, out, nrep, nn, k, Ghost(m), Ghost(p), Ghost(pos), Ghost(cap)) {
            Some(w) => {
                return Some(w);
            },
            None => {},
        }
        k = k + 1;
    }
    proof { lemma_done_all(m, p, es@, out.cells@, out.years@, out.ny as int, cap, nn as int, pos, out.stop as int); }
    None
}

} // verus!
