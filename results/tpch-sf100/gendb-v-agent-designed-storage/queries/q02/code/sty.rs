//! The index-driven Q2 candidate scan over storage `part_sztyidx`, a composite (p_size, p_type) index of part: the
//! part rows with `p_size = $1` are the directory entries `e0 .. e1` (one per p_type key text), i.e. the positions
//! `offs[e0] .. offs[e1]` of its permutation. `p_type LIKE $2` is decided once per entry, on the entry's first row
//! (`select_entries`: all rows of an entry share their p_type), and a worker reads only the rows of the selected
//! entries inside its positions `j0 .. j1`, a batch at a time: `scan::touch_batch`, `scan::touch_suppliers`, then
//! `scan::emit_part` per row.
//!
//! Candidates come in position order (`pchunk_ok`): chunks over adjacent position ranges concatenate, and since the
//! permutation lists every row exactly once (`pos_of`), candidates at different positions are of different parts.
//! Over all positions of the size they are the statement's candidates (`lemma_pchunk_cands`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use crate::stores::part_sztyidx::interface as sxi;
use super::tables::*;
use super::q2spec::*;
use super::scan::*;

verus! {

// ------------------------------------------------------------------------------------------------ the index

/// Handles of the composite index (directory mode): first p_size `kmin`, number of key texts `nt`, directory
/// offsets (`nk + 1`), permutation (`np` rows), and the key texts and indexed relation (`rel[r]` is
/// `[p_type, p_size]` of part row `r`).
#[derive(Clone, Copy)]
pub struct StyIdx {
    pub kmin: i64,
    pub nt: usize,
    pub nk: usize,
    pub np: usize,
    pub offs: &'static [u32],
    pub perm: &'static [u32],
    pub toffs: Ghost<Seq<u64>>,
    pub tbytes: Ghost<Seq<u8>>,
    pub rel: Ghost<Seq<Row>>,
}

/// The index is a dense composite directory over the part rows `p` (opaque: its quantifiers are revealed only by
/// the lemmas below).
#[verifier::opaque]
pub open spec fn styx_ok(x: StyIdx, p: Seq<Row>) -> bool {
    &&& x.offs@.len() == x.nk + 1
    &&& x.perm@.len() == x.np
    &&& x.nt as int == x.toffs@.len() - 1
    &&& sxi::directory_ok(x.kmin as int, x.nt as int, x.toffs@, x.tbytes@, x.offs@, x.perm@, x.rel@)
    &&& x.rel@.len() == p.len()
    &&& forall|r: int| 0 <= r < p.len() ==> #[trigger] x.rel@[r][0] == p[r][4] && x.rel@[r][1] == p[r][5]
}

/// The lengths and end offsets of the index.
pub proof fn lemma_styx_shape(x: StyIdx, p: Seq<Row>)
    requires styx_ok(x, p),
    ensures
        x.offs@.len() == x.nk + 1, x.perm@.len() == x.np, x.np == p.len(),
        x.offs@[0] == 0, x.offs@[x.nk as int] == x.np,
{
    reveal(styx_ok);
}

/// Directory offsets are nondecreasing: `offs[e1] <= offs[e2]` for `e1 <= e2 <= nk`.
pub proof fn lemma_offs_mono(x: StyIdx, p: Seq<Row>, e1: int, e2: int)
    requires styx_ok(x, p), 0 <= e1 <= e2 <= x.nk,
    ensures x.offs@[e1] <= x.offs@[e2],
{
    reveal(styx_ok);
    lemma_offs_le(x.offs@, e2, e1);
}

/// A position of entry `e` holds a part row.
pub proof fn lemma_entry_pos(x: StyIdx, p: Seq<Row>, e: int, j: int)
    requires styx_ok(x, p), 0 <= e < x.nk, sxi::in_entry(x.offs@, e, j),
    ensures 0 <= j < x.np, x.perm@[j] < p.len(),
{
    reveal(styx_ok);
    lemma_offs_le(x.offs@, x.nk as int, e + 1);
}

/// Nondecreasing adjacent offsets: `offs[e] <= offs[k]` for `e <= k`.
pub proof fn lemma_offs_le(offs: Seq<u32>, k: int, e: int)
    requires 0 <= e <= k < offs.len(), forall|f: int| 0 <= f < k ==> #[trigger] offs[f] <= offs[f + 1],
    ensures offs[e] <= offs[k],
    decreases k - e,
{
    if e < k {
        lemma_offs_le(offs, k, e + 1);
    }
}

/// The position of part row `r` in the permutation.
pub open spec fn pos_of(x: StyIdx, r: int) -> int {
    choose|j: int| 0 <= j < x.perm@.len() && x.perm@[j] == r
}

/// The row at position `j` has position `j` (the permutation lists every row once).
pub proof fn lemma_pos_of(x: StyIdx, p: Seq<Row>, j: int)
    requires styx_ok(x, p), 0 <= j < x.np,
    ensures pos_of(x, x.perm@[j] as int) == j,
{
    reveal(styx_ok);
    let r = x.perm@[j] as int;
    assert(exists|j2: int| 0 <= j2 < x.perm@.len() && x.perm@[j2] == r) by {
        assert(x.perm@[j] == r);
    }
    let j2 = pos_of(x, r);
    if j2 != j {
        assert(x.perm@[j2] != x.perm@[j]);
    }
}

/// Every part row of `p_size = v` is at a position of the entries `e0 .. e1`, and every row there has p_size `v`.
pub open spec fn size_range_ok(x: StyIdx, p: Seq<Row>, v: int, e0: int, e1: int) -> bool {
    &&& 0 <= e0 <= e1 <= x.nk
    &&& forall|e: int, j: int| e0 <= e < e1 && #[trigger] sxi::in_entry(x.offs@, e, j)
            ==> x.perm@[j] < p.len() && p[x.perm@[j] as int][5] == Val::Int(v)
    &&& forall|r: int| 0 <= r < p.len() && #[trigger] p[r][5] == Val::Int(v)
            ==> exists|j: int| x.offs@[e0] <= j < x.offs@[e1] && x.perm@[j] == r
}

/// The row at position `j` lies in an entry `e < nk`, has that entry's p_size, and `e`'s p_size number is
/// `e / nt` with `e / nt <= nk / nt`.
proof fn lemma_row_entry(x: StyIdx, p: Seq<Row>, j: int) -> (e: int)
    requires styx_ok(x, p), 0 <= j < x.np,
    ensures
        0 <= e < x.nk, sxi::in_entry(x.offs@, e, j), x.nt >= 1,
        x.perm@[j] < p.len(),
        p[x.perm@[j] as int][5] == Val::Int(x.kmin + e / (x.nt as int)),
        0 <= e / (x.nt as int) <= (x.nk as int) / (x.nt as int),
{
    reveal(styx_ok);
    let e = sxi::lemma_find_entry(x.offs@, x.nk as int, j);
    let r = x.perm@[j] as int;
    assert(sxi::has_key(x.rel@[r], x.kmin as int, x.nt as int, x.toffs@, x.tbytes@, e));
    assert(x.rel@[r][1] == p[r][5]);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(e, x.nt as int);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(e, x.nk as int, x.nt as int);
    e
}

/// Every row of the entries `e0 .. e1` (`e0 = du * nt`, `e1 <= e0 + nt`) has p_size `kmin + du`.
proof fn lemma_size_rows(x: StyIdx, p: Seq<Row>, du: int, e0: int, e1: int)
    requires styx_ok(x, p), x.nt >= 1, du >= 0, e0 == du * x.nt, e0 <= e1 <= e0 + x.nt, e1 <= x.nk,
    ensures
        forall|e: int, j: int| e0 <= e < e1 && #[trigger] sxi::in_entry(x.offs@, e, j)
            ==> x.perm@[j] < p.len() && p[x.perm@[j] as int][5] == Val::Int(x.kmin + du),
{
    reveal(styx_ok);
    let (offs, perm, nt) = (x.offs@, x.perm@, x.nt as int);
    assert forall|e: int, j: int| e0 <= e < e1 && #[trigger] sxi::in_entry(offs, e, j)
        implies perm[j] < p.len() && p[perm[j] as int][5] == Val::Int(x.kmin + du) by {
        assert(sxi::has_key(x.rel@[perm[j] as int], x.kmin as int, nt, x.toffs@, x.tbytes@, e));
        assert(x.rel@[perm[j] as int][1] == p[perm[j] as int][5]);
        sxi::lemma_key_split(e, nt, du);
    }
}

/// Every part row is at some position of the permutation.
proof fn lemma_row_pos(x: StyIdx, p: Seq<Row>, r: int) -> (j: int)
    requires styx_ok(x, p), 0 <= r < p.len(),
    ensures 0 <= j < x.np, x.perm@[j] == r,
{
    reveal(styx_ok);
    assert(sxi::listed(x.perm@, r));
    choose|j: int| 0 <= j < x.perm@.len() && x.perm@[j] == r
}

/// Every row of p_size `kmin + du` lies at a position of the entries `e0 .. e1`.
proof fn lemma_size_listed(x: StyIdx, p: Seq<Row>, du: int, e0: int, e1: int)
    requires
        styx_ok(x, p), x.nt >= 1, du >= 0,
        e0 == du * x.nt, e0 <= x.nk,
        e1 == (if x.nk - e0 > x.nt { e0 + x.nt } else { x.nk as int }),
    ensures
        forall|r: int| 0 <= r < p.len() && #[trigger] p[r][5] == Val::Int(x.kmin + du)
            ==> exists|j: int| x.offs@[e0] <= j < x.offs@[e1] && x.perm@[j] == r,
{
    let nt = x.nt as int;
    assert forall|r: int| 0 <= r < p.len() && #[trigger] p[r][5] == Val::Int(x.kmin + du)
        implies exists|j: int| x.offs@[e0] <= j < x.offs@[e1] && x.perm@[j] == r by {
        let j = lemma_row_pos(x, p, r);
        let e = lemma_row_entry(x, p, j);
        sxi::lemma_key_split(e, nt, du);
        lemma_offs_mono(x, p, e0, e);
        lemma_offs_mono(x, p, e + 1, e1);
    }
}

/// The entries `du * nt .. e1` (`e1 = min(du * nt + nt, nk)`) are those of p_size `kmin + du`.
proof fn lemma_size_in(x: StyIdx, p: Seq<Row>, du: int, e0: int, e1: int)
    requires
        styx_ok(x, p), x.nt >= 1, du >= 0,
        e0 == du * x.nt, e0 <= x.nk,
        e1 == (if x.nk - e0 > x.nt { e0 + x.nt } else { x.nk as int }),
    ensures size_range_ok(x, p, x.kmin + du, e0, e1),
{
    lemma_size_rows(x, p, du, e0, e1);
    lemma_size_listed(x, p, du, e0, e1);
}

/// A p_size `kmin + d` outside `0 <= d <= nk / nt` has no row.
proof fn lemma_size_out(x: StyIdx, p: Seq<Row>, d: int)
    requires styx_ok(x, p), !(x.nt >= 1 && 0 <= d <= (x.nk as int) / (x.nt as int)),
    ensures size_range_ok(x, p, x.kmin + d, 0, 0),
{
    lemma_styx_shape(x, p);
    assert forall|r: int| 0 <= r < p.len() && #[trigger] p[r][5] == Val::Int(x.kmin + d)
        implies exists|j: int| x.offs@[0] <= j < x.offs@[0] && x.perm@[j] == r by {
        let j = lemma_row_pos(x, p, r);
        let e = lemma_row_entry(x, p, j);
    }
}

/// The entries `e0 .. e1` of p_size `v` (an empty range when no row has it).
pub fn size_range(x: &StyIdx, v: i64, Ghost(p): Ghost<Seq<Row>>) -> (r: (usize, usize))
    requires styx_ok(*x, p),
    ensures size_range_ok(*x, p, v as int, r.0 as int, r.1 as int),
{
    let nk = x.nk;
    let nt = x.nt;
    let d: i128 = v as i128 - x.kmin as i128;
    if nt >= 1 && d >= 0 && d <= (nk / nt) as i128 {
        let du = d as usize;
        proof { lemma_mul_le_div(du as int, nt as int, nk as int); }
        let e0 = du * nt;
        let e1 = if nk - e0 > nt { e0 + nt } else { nk };
        proof { lemma_size_in(*x, p, du as int, e0 as int, e1 as int); }
        (e0, e1)
    } else {
        proof { lemma_size_out(*x, p, d as int); }
        (0, 0)
    }
}

// ------------------------------------------------------------------------------------------------ selection

/// `sel[e - e0]` tells, for every row of entry `e`, whether it passes the statement's part filter.
pub open spec fn sel_ok(x: StyIdx, t: Tabs, m: Prm, e0: int, e1: int, sel: Seq<bool>) -> bool {
    &&& sel.len() == e1 - e0
    &&& forall|e: int, j: int| e0 <= e < e1 && #[trigger] sxi::in_entry(x.offs@, e, j)
            ==> (sel[e - e0] <==> part_sel(t, m, x.perm@[j] as int))
}

/// Two rows of one entry have the same p_type.
proof fn lemma_same_type(x: StyIdx, p: Seq<Row>, e: int, j1: int, j2: int)
    requires styx_ok(x, p), 0 <= e < x.nk, sxi::in_entry(x.offs@, e, j1), sxi::in_entry(x.offs@, e, j2),
    ensures
        x.perm@[j1] < p.len(), x.perm@[j2] < p.len(),
        p[x.perm@[j1] as int][4] == p[x.perm@[j2] as int][4],
{
    reveal(styx_ok);
    let (r1, r2) = (x.perm@[j1] as int, x.perm@[j2] as int);
    assert(sxi::has_key(x.rel@[r1], x.kmin as int, x.nt as int, x.toffs@, x.tbytes@, e));
    assert(sxi::has_key(x.rel@[r2], x.kmin as int, x.nt as int, x.toffs@, x.tbytes@, e));
    assert(x.rel@[r1][0] == p[r1][4]);
    assert(x.rel@[r2][0] == p[r2][4]);
}

/// Entry `e` (of p_size `$1`) with first position `a` holding a row of p_type dictionary entry `te`: its rows pass
/// the part filter iff LIKE holds on `te`.
proof fn lemma_entry_sel(c: Cols, lk: Lookups, x: StyIdx, t: Tabs, m: Prm, e0: int, e1: int, e: int, a: int, te: int)
    requires
        cols_ok(c, t), lookups_ok(lk, c, t, m), styx_ok(x, t.p),
        size_range_ok(x, t.p, m.size, e0, e1), e0 <= e < e1,
        sxi::in_entry(x.offs@, e, a),
        x.perm@[a] < t.p.len(),
        t.p[x.perm@[a] as int][4] == Val::Text(txt(c.p.type_o@, c.p.type_y@, te)),
        0 <= te < lk.like_ok@.len(),
    ensures
        forall|j: int| #[trigger] sxi::in_entry(x.offs@, e, j) ==> (lk.like_ok@[te] <==> part_sel(t, m, x.perm@[j] as int)),
{
    assert(lk.like_ok@[te] == like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, te)), m.pat));
    assert forall|j: int| #[trigger] sxi::in_entry(x.offs@, e, j) implies (lk.like_ok@[te] <==> part_sel(t, m, x.perm@[j] as int)) by {
        lemma_same_type(x, t.p, e, a, j);
    }
}

/// The selection of entry `e` of p_size `$1`: LIKE of its first row (false for an empty entry).
fn entry_sel(c: &Cols, lk: &Lookups, x: &StyIdx, e0: usize, e1: usize, e: usize, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    -> (s: bool)
    requires
        cols_ok(*c, t), lookups_ok(*lk, *c, t, m), styx_ok(*x, t.p),
        size_range_ok(*x, t.p, m.size, e0 as int, e1 as int), e0 <= e < e1,
    ensures
        forall|j: int| #[trigger] sxi::in_entry(x.offs@, e as int, j) ==> (s <==> part_sel(t, m, x.perm@[j] as int)),
{
    proof { lemma_styx_shape(*x, t.p); }
    let a = x.offs[e] as usize;
    let b = x.offs[e + 1] as usize;
    if a < b {
        assert(sxi::in_entry(x.offs@, e as int, a as int));
        proof { lemma_entry_pos(*x, t.p, e as int, a as int); }
        let rep = x.perm[a] as usize;
        assert(rep < t.p.len());
        assert(part_row_ok(c.p, t.p[rep as int], rep as int));
        proof { lemma_grp_bound(c.p.n as int, c.p.bs as int, c.p.ng as int, rep as int); }
        let te = (c.p.type_b[grp(rep, c.p.bs)] + c.p.type_c[rep] as u64) as usize;
        let s = lk.like_ok[te];
        proof { lemma_entry_sel(*c, *lk, *x, t, m, e0 as int, e1 as int, e as int, a as int, te as int); }
        s
    } else {
        false
    }
}

/// The selection of the entries `e0 .. e1` of p_size `$1`.
pub fn select_entries(c: &Cols, lk: &Lookups, x: &StyIdx, e0: usize, e1: usize, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    -> (sel: Vec<bool>)
    requires
        cols_ok(*c, t), lookups_ok(*lk, *c, t, m), styx_ok(*x, t.p),
        size_range_ok(*x, t.p, m.size, e0 as int, e1 as int),
    ensures sel_ok(*x, t, m, e0 as int, e1 as int, sel@),
{
    let mut sel: Vec<bool> = Vec::with_capacity(e1 - e0);
    let mut e = e0;
    while e < e1
        invariant
            cols_ok(*c, t), lookups_ok(*lk, *c, t, m), styx_ok(*x, t.p),
            size_range_ok(*x, t.p, m.size, e0 as int, e1 as int),
            e0 <= e <= e1, sel@.len() == e - e0,
            forall|f: int, j: int| e0 <= f < e && #[trigger] sxi::in_entry(x.offs@, f, j)
                ==> (sel@[f - e0] <==> part_sel(t, m, x.perm@[j] as int)),
        decreases e1 - e,
    {
        let s = entry_sel(c, lk, x, e0, e1, e, Ghost(t), Ghost(m));
        let ghost before = sel@;
        sel.push(s);
        proof {
            assert forall|f: int, j: int| e0 <= f < e + 1 && #[trigger] sxi::in_entry(x.offs@, f, j)
                implies (sel@[f - e0] <==> part_sel(t, m, x.perm@[j] as int)) by {
                if f < e {
                    assert(sel@[f - e0] == before[f - e0]);
                }
            }
        }
        e = e + 1;
    }
    sel
}

// ------------------------------------------------------------------------------------------------ position chunks

/// Candidates in increasing (position of the part, partsupp) order.
pub open spec fn pcand_lt(x: StyIdx, a: Cand, b: Cand) -> bool {
    pos_of(x, a.part as int) < pos_of(x, b.part as int) || (a.part == b.part && a.ps < b.ps)
}

/// The candidates of the part rows at positions `[a, b)`, exactly and in position order.
pub open spec fn pchunk_ok(t: Tabs, m: Prm, x: StyIdx, cs: Seq<Cand>, a: int, b: int) -> bool {
    &&& a <= b
    &&& forall|i: int| 0 <= i < cs.len() ==> #[trigger] cand_ok(t, m, cs[i])
    &&& forall|i: int, k: int| 0 <= i < k < cs.len() ==> #[trigger] pcand_lt(x, cs[i], cs[k])
    &&& forall|i: int| 0 <= i < cs.len() ==> a <= #[trigger] pos_of(x, cs[i].part as int) < b
    &&& forall|j: int, k: int| a <= j < b && #[trigger] part_sel(t, m, x.perm@[j] as int)
            && #[trigger] is_min(t, m, t.p[x.perm@[j] as int][0], k) ==> has_pair(cs, x.perm@[j] as int, k)
}

pub proof fn lemma_pchunk_empty(t: Tabs, m: Prm, x: StyIdx, a: int)
    ensures pchunk_ok(t, m, x, Seq::<Cand>::empty(), a, a),
{
}

/// Positions without a selected part add no candidates.
pub proof fn lemma_pchunk_extend(t: Tabs, m: Prm, x: StyIdx, cs: Seq<Cand>, a: int, b: int, b2: int)
    requires
        pchunk_ok(t, m, x, cs, a, b), b <= b2,
        forall|j: int| b <= j < b2 ==> !#[trigger] part_sel(t, m, x.perm@[j] as int),
    ensures pchunk_ok(t, m, x, cs, a, b2),
{
}

/// Adjacent position chunks concatenate.
pub proof fn lemma_pchunk_append(t: Tabs, m: Prm, x: StyIdx, c1: Seq<Cand>, c2: Seq<Cand>, a: int, b: int, c: int)
    requires pchunk_ok(t, m, x, c1, a, b), pchunk_ok(t, m, x, c2, b, c),
    ensures pchunk_ok(t, m, x, c1 + c2, a, c),
{
    let cs = c1 + c2;
    assert forall|i: int| 0 <= i < cs.len() implies #[trigger] cand_ok(t, m, cs[i]) by {
        if i < c1.len() { assert(cs[i] == c1[i]); } else { assert(cs[i] == c2[i - c1.len()]); }
    }
    assert forall|i: int, k: int| 0 <= i < k < cs.len() implies #[trigger] pcand_lt(x, cs[i], cs[k]) by {
        if k < c1.len() {
            assert(cs[i] == c1[i] && cs[k] == c1[k]);
        } else if i >= c1.len() {
            assert(cs[i] == c2[i - c1.len()] && cs[k] == c2[k - c1.len()]);
        } else {
            assert(cs[i] == c1[i] && cs[k] == c2[k - c1.len()]);
            assert(pos_of(x, c1[i].part as int) < b);
            assert(b <= pos_of(x, c2[k - c1.len()].part as int));
        }
    }
    assert forall|i: int| 0 <= i < cs.len() implies a <= #[trigger] pos_of(x, cs[i].part as int) < c by {
        if i < c1.len() { assert(cs[i] == c1[i]); } else { assert(cs[i] == c2[i - c1.len()]); }
    }
    assert forall|j: int, k: int| a <= j < c && #[trigger] part_sel(t, m, x.perm@[j] as int)
        && #[trigger] is_min(t, m, t.p[x.perm@[j] as int][0], k) implies has_pair(cs, x.perm@[j] as int, k) by {
        let r = x.perm@[j] as int;
        if j < b {
            let y = choose|y: int| 0 <= y < c1.len() && #[trigger] c1[y].part == r && c1[y].ps == k;
            assert(cs[y] == c1[y]);
        } else {
            let y = choose|y: int| 0 <= y < c2.len() && #[trigger] c2[y].part == r && c2[y].ps == k;
            assert(cs[y + c1.len()] == c2[y]);
        }
    }
}

/// The candidates of the part row at position `j`.
pub proof fn lemma_pchunk_part(t: Tabs, m: Prm, x: StyIdx, cs: Seq<Cand>, seg: Seq<Cand>, a: int, j: int)
    requires
        styx_ok(x, t.p),
        pchunk_ok(t, m, x, cs, a, j),
        0 <= j < x.np,
        forall|y: int| 0 <= y < seg.len() ==> #[trigger] cand_ok(t, m, seg[y]),
        forall|y: int| 0 <= y < seg.len() ==> #[trigger] seg[y].part == x.perm@[j],
        forall|y: int, z: int| 0 <= y < z < seg.len() ==> #[trigger] seg[y].ps < #[trigger] seg[z].ps,
        forall|k: int| #[trigger] is_min(t, m, t.p[x.perm@[j] as int][0], k) ==> has_pair(seg, x.perm@[j] as int, k),
    ensures pchunk_ok(t, m, x, cs + seg, a, j + 1),
{
    lemma_pos_of(x, t.p, j);
    let r = x.perm@[j] as int;
    assert forall|y: int| 0 <= y < seg.len() implies j <= #[trigger] pos_of(x, seg[y].part as int) < j + 1 by {
        assert(seg[y].part == r);
    }
    assert forall|y: int, z: int| 0 <= y < z < seg.len() implies #[trigger] pcand_lt(x, seg[y], seg[z]) by {
        assert(seg[y].ps < seg[z].ps);
        assert(seg[y].part == r && seg[z].part == r);
    }
    assert forall|jj: int, k: int| j <= jj < j + 1 && #[trigger] part_sel(t, m, x.perm@[jj] as int)
        && #[trigger] is_min(t, m, t.p[x.perm@[jj] as int][0], k) implies has_pair(seg, x.perm@[jj] as int, k) by {
        assert(jj == j);
    }
    assert(pchunk_ok(t, m, x, seg, j, j + 1));
    lemma_pchunk_append(t, m, x, cs, seg, a, j, j + 1);
}

/// The candidates of every position of p_size `$1` are the statement's candidates.
pub proof fn lemma_pchunk_cands(t: Tabs, m: Prm, x: StyIdx, cs: Seq<Cand>, e0: int, e1: int)
    requires
        styx_ok(x, t.p),
        size_range_ok(x, t.p, m.size, e0, e1),
        pchunk_ok(t, m, x, cs, x.offs@[e0] as int, x.offs@[e1] as int),
    ensures cands_ok(t, m, cs),
{
    assert forall|i: int, k: int| 0 <= i < cs.len() && 0 <= k < cs.len() && i != k implies pair_ne(#[trigger] cs[i], #[trigger] cs[k]) by {
        if i < k { assert(pcand_lt(x, cs[i], cs[k])); } else { assert(pcand_lt(x, cs[k], cs[i])); }
    }
    assert forall|i: int, k: int| 0 <= i < t.p.len() && #[trigger] part_sel(t, m, i) && #[trigger] is_min(t, m, t.p[i][0], k)
        implies has_pair(cs, i, k) by {
        assert(t.p[i][5] == Val::Int(m.size));
        let j = choose|j: int| x.offs@[e0] <= j < x.offs@[e1] && x.perm@[j] == i;
        assert(part_sel(t, m, x.perm@[j] as int));
    }
}

// ------------------------------------------------------------------------------------------------ the scan

/// `v` clamped into `[j0, j1]`.
pub open spec fn clampv(v: int, j0: int, j1: int) -> int {
    if v < j0 { j0 } else if v > j1 { j1 } else { v }
}

fn clamp_exec(v: usize, j0: usize, j1: usize) -> (r: usize)
    requires j0 <= j1,
    ensures r as int == clampv(v as int, j0 as int, j1 as int),
    no_unwind
{
    if v < j0 { j0 } else if v > j1 { j1 } else { v }
}

/// Everything the entry scan relies on.
pub open spec fn sty_env(c: Cols, lk: Lookups, a: ScanArgs, x: StyIdx, t: Tabs, m: Prm, e0: int, e1: int, sel: Seq<bool>) -> bool {
    &&& scan_env(c, lk, a, t, m)
    &&& styx_ok(x, t.p)
    &&& size_range_ok(x, t.p, m.size, e0, e1)
    &&& sel_ok(x, t, m, e0, e1, sel)
}

/// Scans the positions `[s, u)` of the selected entry `e` (every row there passes the part filter) after the chunk
/// `[j0, s)` in `st.buf`, a batch at a time. Returns `u`, or the position it stopped at when the next part's
/// candidates might not fit.
fn scan_run(c: &Cols, lk: &Lookups, a: ScanArgs, x: &StyIdx, e: usize, s: usize, u: usize, j0: usize,
    st: &mut ScanState, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (next: usize)
    requires
        scan_env(*c, *lk, a, t, m), styx_ok(*x, t.p),
        j0 <= s <= u <= x.np,
        forall|jj: int| s <= jj < u ==> part_sel(t, m, #[trigger] x.perm@[jj] as int),
        old(st).pend@.len() > 0,
        buf_wf(old(st).buf),
        pchunk_ok(t, m, *x, buf_view(old(st).buf), j0 as int, s as int),
    ensures
        buf_wf(final(st).buf),
        final(st).pend@.len() == old(st).pend@.len(),
        s <= next <= u,
        pchunk_ok(t, m, *x, buf_view(final(st).buf), j0 as int, next as int),
    no_unwind
{
    let pcap = st.pend.len();
    let mut j = s;
    while j < u
        invariant
            scan_env(*c, *lk, a, t, m), styx_ok(*x, t.p),
            pcap == st.pend@.len(), pcap > 0, pcap == old(st).pend@.len(),
            j0 <= s <= j <= u, u <= x.np,
            forall|jj: int| s <= jj < u ==> part_sel(t, m, #[trigger] x.perm@[jj] as int),
            buf_wf(st.buf),
            pchunk_ok(t, m, *x, buf_view(st.buf), j0 as int, j as int),
        decreases u - j,
    {
        // Collect a batch of the entry's rows.
        let jb = j;
        let mut np: usize = 0;
        while j < u && np < pcap
            invariant
                styx_ok(*x, t.p), cols_ok(*c, t),
                pcap == st.pend@.len(), pcap == old(st).pend@.len(),
                s <= jb <= j <= u, u <= x.np,
                np == j - jb, np <= pcap,
                forall|y: int| 0 <= y < np ==> #[trigger] st.pend@[y] == x.perm@[jb + y] as int,
                forall|y: int| 0 <= y < np ==> #[trigger] st.pend@[y] < c.p.n,
            decreases u - j,
        {
            proof { lemma_row_entry(*x, t.p, j as int); lemma_styx_shape(*x, t.p); }
            let r = x.perm[j] as usize;
            let ghost p0 = st.pend@;
            put(&mut st.pend, np, r);
            proof {
                assert forall|y: int| 0 <= y < np + 1 implies #[trigger] st.pend@[y] == x.perm@[jb + y] as int by {
                    if y < np { assert(st.pend@[y] == p0[y]); }
                }
                assert forall|y: int| 0 <= y < np + 1 implies #[trigger] st.pend@[y] < c.p.n by {
                    if y < np { assert(st.pend@[y] == p0[y]); }
                }
            }
            np = np + 1;
            j = j + 1;
        }
        touch_batch(c, a, &st.pend, np, &mut st.sink, Ghost(t), Ghost(m));
        touch_suppliers(c, a, &st.pend, np, &mut st.sink, Ghost(t), Ghost(m));
        // Process the batch in position order.
        let mut q: usize = 0;
        while q < np
            invariant
                scan_env(*c, *lk, a, t, m), styx_ok(*x, t.p),
                pcap == st.pend@.len(), pcap > 0, pcap == old(st).pend@.len(),
                j0 <= s <= jb <= j <= u, u <= x.np,
                np == j - jb, q <= np, np <= pcap,
                forall|y: int| 0 <= y < np ==> #[trigger] st.pend@[y] == x.perm@[jb + y] as int,
                forall|jj: int| s <= jj < u ==> part_sel(t, m, #[trigger] x.perm@[jj] as int),
                buf_wf(st.buf),
                pchunk_ok(t, m, *x, buf_view(st.buf), j0 as int, jb + q),
            decreases np - q,
        {
            let r = st.pend[q];
            let ghost jq = jb + q;
            proof {
                assert(st.pend@[q as int] == x.perm@[jq] as int);
                assert(part_sel(t, m, x.perm@[jq] as int));
            }
            let pk = part_key(c, a, r, Ghost(t), Ghost(m));
            let (plo, phi) = ps_range(c, a, pk, Ghost(t));
            if st.buf.v.len() - st.buf.len < phi - plo {
                return jb + q;
            }
            let ghost before = buf_view(st.buf);
            let ghost blen = st.buf.len;
            emit_part(c, lk, a, r, pk, plo, phi, &mut st.buf, Ghost(t), Ghost(m));
            proof {
                let seg = buf_view(st.buf).subrange(blen as int, st.buf.len as int);
                lemma_pchunk_part(t, m, *x, before, seg, j0 as int, jq);
            }
            q = q + 1;
        }
    }
    u
}

/// The positions `[s, u)` of entry `e` (`e0 <= e < e1`) pass the part filter iff the entry is selected.
proof fn lemma_run_sel(x: StyIdx, t: Tabs, m: Prm, e0: int, e1: int, sel: Seq<bool>, e: int, s: int, u: int)
    requires
        sel_ok(x, t, m, e0, e1, sel), e0 <= e < e1,
        s >= u || (x.offs@[e] <= s && u <= x.offs@[e + 1]),
    ensures
        forall|jj: int| s <= jj < u ==> (part_sel(t, m, #[trigger] x.perm@[jj] as int) <==> sel[e - e0]),
{
    assert forall|jj: int| s <= jj < u implies (part_sel(t, m, #[trigger] x.perm@[jj] as int) <==> sel[e - e0]) by {
        assert(sxi::in_entry(x.offs@, e, jj));
    }
}

/// Scans the positions `[j0, j1)` (inside the entries `e0 .. e1` of p_size `$1`) into `st.buf` (empty on entry):
/// the rows of the selected entries only, a batch at a time; stops early, returning the position it stopped at,
/// when the next part's candidates might not fit. Returns `j1` when complete.
pub fn scan_sel(c: &Cols, lk: &Lookups, a: ScanArgs, x: &StyIdx, e0: usize, e1: usize, sel: &Vec<bool>, j0: usize, j1: usize,
    st: &mut ScanState, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (next: usize)
    requires
        sty_env(*c, *lk, a, *x, t, m, e0 as int, e1 as int, sel@),
        x.offs@[e0 as int] <= j0 <= j1 <= x.offs@[e1 as int],
        buf_wf(old(st).buf),
        old(st).buf.len == 0,
    ensures
        buf_wf(final(st).buf),
        j0 <= next <= j1,
        pchunk_ok(t, m, *x, buf_view(final(st).buf), j0 as int, next as int),
    no_unwind
{
    let pcap = st.pend.len();
    proof {
        lemma_pchunk_empty(t, m, *x, j0 as int);
        assert(buf_view(st.buf) =~= Seq::<Cand>::empty());
        lemma_styx_shape(*x, t.p);
        lemma_offs_mono(*x, t.p, e1 as int, x.nk as int);
    }
    if pcap == 0 {
        return j0;
    }
    let mut e = e0;
    let mut cur = j0;
    while e < e1
        invariant
            sty_env(*c, *lk, a, *x, t, m, e0 as int, e1 as int, sel@),
            x.offs@[e0 as int] <= j0 <= j1 <= x.offs@[e1 as int],
            x.offs@[x.nk as int] == x.np,
            x.offs@[e1 as int] <= x.np,
            pcap == st.pend@.len(), pcap > 0,
            e0 <= e <= e1,
            cur as int == clampv(x.offs@[e as int] as int, j0 as int, j1 as int),
            buf_wf(st.buf),
            pchunk_ok(t, m, *x, buf_view(st.buf), j0 as int, cur as int),
        decreases e1 - e,
    {
        proof {
            lemma_styx_shape(*x, t.p);
            lemma_offs_mono(*x, t.p, e as int, e + 1);
        }
        let ea = x.offs[e] as usize;
        let eb = x.offs[e + 1] as usize;
        let s = clamp_exec(ea, j0, j1);
        let u = clamp_exec(eb, j0, j1);
        assert(s == cur);
        proof { lemma_run_sel(*x, t, m, e0 as int, e1 as int, sel@, e as int, s as int, u as int); }
        if sel[e - e0] && s < u {
            let next = scan_run(c, lk, a, x, e, s, u, j0, st, Ghost(t), Ghost(m));
            if next < u {
                return next;
            }
        } else {
            proof { lemma_pchunk_extend(t, m, *x, buf_view(st.buf), j0 as int, s as int, u as int); }
        }
        cur = u;
        e = e + 1;
    }
    j1
}

/// Serial continuation over the positions `[from, to)`: one row at a time (p_size and LIKE checked on the row),
/// each part with a buffer of its own; appends the candidates of those positions to `out`.
pub fn scan_pos_serial(c: &Cols, lk: &Lookups, a: ScanArgs, x: &StyIdx, from: usize, to: usize, out: &mut Vec<Cand>,
    Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    requires scan_env(*c, *lk, a, t, m), styx_ok(*x, t.p), from <= to <= x.np,
    ensures exists|seg: Seq<Cand>| final(out)@ == old(out)@ + seg && pchunk_ok(t, m, *x, seg, from as int, to as int),
{
    let bs = c.p.bs;
    let ghost o0 = out@;
    let ghost mut seg = Seq::<Cand>::empty();
    proof {
        lemma_pchunk_empty(t, m, *x, from as int);
        assert(out@ =~= o0 + seg);
    }
    let mut j = from;
    while j < to
        invariant
            scan_env(*c, *lk, a, t, m), styx_ok(*x, t.p), bs == c.p.bs, from <= j <= to <= x.np,
            out@ == o0 + seg,
            pchunk_ok(t, m, *x, seg, from as int, j as int),
        decreases to - j,
    {
        proof { lemma_row_entry(*x, t.p, j as int); lemma_styx_shape(*x, t.p); }
        let i = x.perm[j] as usize;
        assert(part_row_ok(c.p, t.p[i as int], i as int));
        proof { lemma_grp_bound(c.p.n as int, c.p.bs as int, c.p.ng as int, i as int); }
        let g = grp(i, bs);
        let sz: i64 = c.p.size_b[g] + c.p.size_c[i] as i64;
        if sz == a.size {
            let te = (c.p.type_b[g] + c.p.type_c[i] as u64) as usize;
            assert(lk.like_ok@[te as int] == like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, te as int)), m.pat));
            if lk.like_ok[te] {
                assert(part_sel(t, m, i as int));
                let pk = part_key(c, a, i, Ghost(t), Ghost(m));
                let (lo, hi) = ps_range(c, a, pk, Ghost(t));
                let mut buf = CandBuf { v: vec![Cand { part: 0, ps: 0, supp: 0, nation: 0, acct: 0 }; hi - lo], len: 0 };
                proof { assert(buf_view(buf) =~= Seq::<Cand>::empty()); }
                emit_part(c, lk, a, i, pk, lo, hi, &mut buf, Ghost(t), Ghost(m));
                let ghost part = buf_view(buf);
                proof {
                    assert(part =~= buf_view(buf).subrange(0, buf.len as int));
                    lemma_pchunk_part(t, m, *x, seg, part, from as int, j as int);
                }
                let blen = buf.len;
                let mut v = buf.v;
                v.truncate(blen);
                out.append(&mut v);
                proof {
                    seg = seg + part;
                    assert(out@ =~= o0 + seg);
                }
            } else {
                proof { lemma_pchunk_extend(t, m, *x, seg, from as int, j as int, j + 1); }
            }
        } else {
            proof { lemma_pchunk_extend(t, m, *x, seg, from as int, j as int, j + 1); }
        }
        j = j + 1;
    }
}

// ------------------------------------------------------------------------------------------------ tasks

/// One worker: the positions `[j0, j1)` of the entries `e0 .. e1` of p_size `$1`, into its preallocated state.
pub struct StyTask {
    pub c: Cols,
    pub lk: Lookups,
    pub a: ScanArgs,
    pub x: StyIdx,
    pub e0: usize,
    pub e1: usize,
    pub sel: Vec<bool>,
    pub j0: usize,
    pub j1: usize,
    pub st: ScanState,
    pub t: Ghost<Tabs>,
    pub m: Ghost<Prm>,
}

impl WorkerTask for StyTask {
    type Output = (ScanState, usize);

    open spec fn pre(&self) -> bool {
        &&& sty_env(self.c, self.lk, self.a, self.x, self.t@, self.m@, self.e0 as int, self.e1 as int, self.sel@)
        &&& self.x.offs@[self.e0 as int] <= self.j0 <= self.j1 <= self.x.offs@[self.e1 as int]
        &&& buf_wf(self.st.buf)
        &&& self.st.buf.len == 0
    }

    open spec fn post(&self, out: (ScanState, usize)) -> bool {
        &&& buf_wf(out.0.buf)
        &&& self.j0 <= out.1 <= self.j1
        &&& pchunk_ok(self.t@, self.m@, self.x, buf_view(out.0.buf), self.j0 as int, out.1 as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.j0 as u64, self.j1 as u64)
    }

    fn run(self) -> (out: (ScanState, usize)) {
        let StyTask { c, lk, a, x, e0, e1, sel, j0, j1, st, t, m } = self;
        let mut st = st;
        let next = scan_sel(&c, &lk, a, &x, e0, e1, &sel, j0, j1, &mut st, t, m);
        (st, next)
    }
}

} // verus!
