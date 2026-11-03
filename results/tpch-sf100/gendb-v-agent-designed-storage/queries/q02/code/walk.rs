//! The supplier-driven Q2 plan over storage `suppliers_rank`: only the candidates with the largest s_acctbal can
//! reach the output, so the suppliers are walked in descending balance order (`SBAL`); for each supplier in region
//! `$3`, its partsupp rows come from the ps_suppkey directory, each row's part (row `k / ratio` under the run layout
//! of `suppliers_psrun`, dense part keys) is checked against `p_size = $1 AND p_type LIKE $2`, and for a selected
//! part the row is a candidate when its cost is the least among the part's partsupp rows in the region
//! (`part_best`). The walk stops once at least 100 candidates are found and the next supplier's balance is below
//! the last one's: every candidate reaching that balance (`thr`) is then found. It gives up (`None`) after
//! `VISIT_BUDGET` partsupp rows, and the caller scans instead.
//!
//! Proof: the walk keeps its candidates sound, pairwise distinct (`sel_ok`) and complete for every supplier position
//! walked (`walked`). The statement's candidates below `thr` are enumerated in ghost code (`low_cands`); the
//! candidates found followed by them are all candidates (`lemma_picked`), of which the found ones are exactly those
//! reaching `thr` — the pick `picked_ok` the output proof takes.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::stores::suppliers_rank::interface as rki;
use super::tables::*;
use super::q2spec::*;
use super::scan::*;
use super::output::ge_f;
use super::common::relops::select;

verus! {

// ------------------------------------------------------------------------------------------------ the index

/// Handles of storage suppliers_rank's indexes: supplier rows by descending balance, and the ps_suppkey directory
/// (`kmin`, offsets, permutation of the partsupp rows).
#[derive(Clone, Copy)]
pub struct RankIdx {
    pub sbal: &'static [u32],
    pub kmin: i64,
    pub offs: &'static [u32],
    pub perm: &'static [u32],
}

/// The directory header the handles stand for.
pub open spec fn rmeta(x: RankIdx) -> Seq<i64> {
    seq![rki::MODE_DIRECTORY, x.kmin]
}

/// Both indexes are present over the tables `t`.
pub open spec fn rank_ok(x: RankIdx, t: Tabs) -> bool {
    &&& x.sbal@.len() == t.s.len()
    &&& x.sbal@.len() > 0
    &&& rki::sbal_ok(x.sbal@, t.s)
    &&& rki::psdir_ok(rmeta(x), x.offs@, x.perm@, t.ps)
}

// ------------------------------------------------------------------------------------------------ specification

/// The supplier row of partsupp row `k` (the one with its suppkey).
pub open spec fn supp_of(t: Tabs, k: int) -> int {
    choose|j: int| smatch(t, k, j)
}

/// The SBAL position of partsupp row `k`'s supplier.
pub open spec fn spos(t: Tabs, x: RankIdx, k: int) -> int {
    choose|i: int| 0 <= i < x.sbal@.len() && x.sbal@[i] as int == supp_of(t, k)
}

/// (part row `i`, partsupp row `k`) is a candidate pair of the statement.
pub open spec fn cpair(t: Tabs, m: Prm, i: int, k: int) -> bool {
    part_sel(t, m, i) && is_min(t, m, t.p[i][0], k)
}

/// Candidates found: sound, of suppliers at SBAL positions below `i`, pairwise distinct.
pub open spec fn sel_ok(t: Tabs, m: Prm, x: RankIdx, cs: Seq<Cand>, i: int) -> bool {
    &&& forall|y: int| 0 <= y < cs.len() ==> #[trigger] cand_ok(t, m, cs[y])
    &&& forall|y: int| 0 <= y < cs.len() ==> spos(t, x, (#[trigger] cs[y]).ps as int) < i
    &&& forall|y: int, z: int| 0 <= y < cs.len() && 0 <= z < cs.len() && y != z ==> pair_ne(#[trigger] cs[y], #[trigger] cs[z])
}

/// Every candidate pair whose supplier sits at an SBAL position below `i` is in `cs`.
pub open spec fn walked(t: Tabs, m: Prm, x: RankIdx, cs: Seq<Cand>, i: int) -> bool {
    forall|pi: int, k: int| #[trigger] cpair(t, m, pi, k) && spos(t, x, k) < i ==> has_pair(cs, pi, k)
}

// ------------------------------------------------------------------------------------------------ key lemmas

/// A partsupp row has one supplier row.
proof fn lemma_supp_unique(t: Tabs, k: int, j1: int, j2: int)
    requires keys_unique(t), smatch(t, k, j1), smatch(t, k, j2),
    ensures j1 == j2,
{
}

/// The supplier of a partsupp row with one, and its SBAL position.
proof fn lemma_spos_of(t: Tabs, x: RankIdx, k: int, j: int)
    requires keys_unique(t), rank_ok(x, t), smatch(t, k, j),
    ensures
        supp_of(t, k) == j,
        0 <= spos(t, x, k) < x.sbal@.len(),
        x.sbal@[spos(t, x, k)] as int == j,
{
    let j2 = supp_of(t, k);
    lemma_supp_unique(t, k, j, j2);
    assert(rki::listed(x.sbal@, j));
}

/// Partsupp row `k` of the supplier at position `i` has SBAL position `i`.
proof fn lemma_spos(t: Tabs, x: RankIdx, k: int, i: int)
    requires keys_unique(t), rank_ok(x, t), 0 <= i < x.sbal@.len(), smatch(t, k, x.sbal@[i] as int),
    ensures spos(t, x, k) == i,
{
    lemma_spos_of(t, x, k, x.sbal@[i] as int);
    let p = spos(t, x, k);
    if p != i {
        assert(x.sbal@[p] != x.sbal@[i]);
    }
}

/// A candidate's supplier is its partsupp row's supplier, and its balance is that supplier's.
proof fn lemma_cand_supp(t: Tabs, m: Prm, x: RankIdx, cd: Cand)
    requires keys_unique(t), rank_ok(x, t), cand_ok(t, m, cd),
    ensures
        supp_of(t, cd.ps as int) == cd.supp,
        x.sbal@[spos(t, x, cd.ps as int)] as int == cd.supp,
        0 <= spos(t, x, cd.ps as int) < x.sbal@.len(),
        rki::bal(t.s, cd.supp as int) == cd.acct,
{
    lemma_spos_of(t, x, cd.ps as int, cd.supp as int);
}

/// The part rows with partsupp row `k`'s partkey: only `k / ratio` (run layout, dense part keys).
proof fn lemma_part_of(t: Tabs, m: Prm, a: ScanArgs, k: int, pi2: int)
    requires args_ok(a, t, m), a.psrun, a.p_dense, 0 <= k < t.ps.len(), 0 <= pi2 < t.p.len(), t.p[pi2][0] == t.ps[k][0],
    ensures pi2 == k / (a.ratio as int),
{
    assert(t.ps[k][0] == Val::Int(a.p_first + k / (a.ratio as int)));
    assert(t.p[pi2][0] == Val::Int(a.p_first + pi2));
}

/// A partsupp row whose supplier's nation has no region named `$3` does not qualify.
proof fn lemma_not_inreg(t: Tabs, m: Prm, k: int, j: int)
    requires keys_unique(t), smatch(t, k, j), forall|n: int, r: int| nmatch(t, j, n) ==> !#[trigger] rmatch(t, m, n, r),
    ensures !inreg(t, m, k),
{
    assert forall|j2: int, n: int, r: int| #![trigger smatch(t, k, j2), nmatch(t, j2, n), rmatch(t, m, n, r)]
        smatch(t, k, j2) && nmatch(t, j2, n) implies !rmatch(t, m, n, r) by {
        lemma_supp_unique(t, k, j, j2);
    }
}

// ------------------------------------------------------------------------------------------------ one part

/// Whether a partsupp row of key `pk` qualifies, and then the least cost among them (`[lo, hi)` holds every row of
/// `pk`).
fn part_best(c: &Cols, lk: &Lookups, a: ScanArgs, pk: i64, lo: usize, hi: usize, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    -> (r: (bool, i64))
    requires
        scan_env(*c, *lk, a, t, m),
        lo <= hi <= c.ps.n,
        forall|k: int| 0 <= k < c.ps.n && #[trigger] t.ps[k][0] == Val::Int(pk as int) ==> lo <= k < hi,
        a.psrun ==> forall|k: int| lo <= k < hi ==> #[trigger] t.ps[k][0] == Val::Int(pk as int),
    ensures
        r.0 ==> exists|k0: int| qual(t, m, Val::Int(pk as int), k0) && cost(t, k0) == r.1,
        r.0 ==> forall|k2: int| #[trigger] qual(t, m, Val::Int(pk as int), k2) ==> r.1 <= cost(t, k2),
        !r.0 ==> forall|k2: int| !#[trigger] qual(t, m, Val::Int(pk as int), k2),
{
    let ghost pkv = Val::Int(pk as int);
    let mut best: i64 = 0;
    let mut found = false;
    let mut k = lo;
    while k < hi
        invariant
            scan_env(*c, *lk, a, t, m),
            pkv == Val::Int(pk as int),
            lo <= k <= hi <= c.ps.n,
            a.psrun ==> forall|k2: int| lo <= k2 < hi ==> #[trigger] t.ps[k2][0] == Val::Int(pk as int),
            found ==> exists|k0: int| lo <= k0 < k && qual(t, m, pkv, k0) && cost(t, k0) == best,
            found ==> forall|k2: int| lo <= k2 < k && #[trigger] qual(t, m, pkv, k2) ==> best <= cost(t, k2),
            !found ==> forall|k2: int| lo <= k2 < k ==> !#[trigger] qual(t, m, pkv, k2),
        decreases hi - k,
    {
        let key_ok: bool = if a.psrun { true } else { ps_key(c, k, Ghost(t)) == pk };
        assert(key_ok <==> t.ps[k as int][0] == pkv);
        if key_ok {
            match supp_region(c, lk, a, k, Ghost(t), Ghost(m)) {
                Some((_j, _n, _r)) => {
                    assert(ps_row_ok(c.ps, t.ps[k as int], k as int));
                    proof { lemma_grp_bound(c.ps.n as int, c.ps.bs as int, c.ps.ng as int, k as int); }
                    let cst = c.ps.cost_b[grp(k, c.ps.bs)] + c.ps.cost_c[k] as i64;
                    assert(qual(t, m, pkv, k as int));
                    assert(cost(t, k as int) == cst as int);
                    if !found || cst < best {
                        best = cst;
                        found = true;
                        assert(lo <= k < k + 1 && qual(t, m, pkv, k as int) && cost(t, k as int) == best);
                    }
                },
                None => {},
            }
        }
        k = k + 1;
    }
    proof {
        assert forall|k2: int| #[trigger] qual(t, m, pkv, k2) implies lo <= k2 < hi by {
            assert(t.ps[k2][0] == Val::Int(pk as int));
        }
    }
    (found, best)
}

// ------------------------------------------------------------------------------------------------ one supplier

/// Walks the partsupp rows `[lo, hi)` of directory entry `e`, those of supplier row `j` (SBAL position `i`, nation
/// row `n` in region `$3`, balance `bj`): appends the candidates among them.
fn walk_entry(c: &Cols, lk: &Lookups, a: ScanArgs, x: &RankIdx, i: usize, j: usize, n: usize, bj: i64,
    e: usize, lo: usize, hi: usize, sel: &mut Vec<Cand>, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    requires
        scan_env(*c, *lk, a, t, m), rank_ok(*x, t), a.psrun, a.p_dense,
        i < x.sbal@.len(), j == x.sbal@[i as int],
        nmatch(t, j as int, n as int), exists|r: int| #[trigger] rmatch(t, m, n as int, r),
        t.s[j as int][5] == (Val::Num { coeff: bj as int, scale: 2 }),
        e + 1 < x.offs@.len(), lo == x.offs@[e as int], hi == x.offs@[e + 1],
        t.s[j as int][0] == Val::Int(x.kmin + e),
        sel_ok(t, m, *x, old(sel)@, i as int),
    ensures
        old(sel)@.len() <= final(sel)@.len(),
        final(sel)@.subrange(0, old(sel)@.len() as int) == old(sel)@,
        sel_ok(t, m, *x, final(sel)@, i + 1),
        forall|pi: int, k: int| #[trigger] cpair(t, m, pi, k) && spos(t, *x, k) == i ==> has_pair(final(sel)@, pi, k),
{
    let ghost s0 = sel@;
    let ghost meta = rmeta(*x);
    let np = c.p.n;
    let ratio = a.ratio;
    proof {
        rki::lemma_offs_mono(meta, x.offs@, x.perm@, t.ps, e as int, e + 1);
        rki::lemma_offs_mono(meta, x.offs@, x.perm@, t.ps, e + 1, x.offs@.len() - 1);
    }
    let ghost mut qs = Seq::<int>::empty();
    let mut p = lo;
    while p < hi
        invariant
            scan_env(*c, *lk, a, t, m), rank_ok(*x, t), a.psrun, a.p_dense,
            meta == rmeta(*x), np == c.p.n, ratio == a.ratio, ratio >= 1,
            i < x.sbal@.len(), j == x.sbal@[i as int],
            nmatch(t, j as int, n as int), exists|r: int| #[trigger] rmatch(t, m, n as int, r),
            t.s[j as int][5] == (Val::Num { coeff: bj as int, scale: 2 }),
            e + 1 < x.offs@.len(), lo == x.offs@[e as int], hi == x.offs@[e + 1], hi <= t.ps.len(),
            t.s[j as int][0] == Val::Int(x.kmin + e),
            lo <= p <= hi,
            s0.len() <= sel@.len(),
            sel@.subrange(0, s0.len() as int) == s0,
            sel_ok(t, m, *x, s0, i as int),
            forall|y: int| 0 <= y < sel@.len() ==> #[trigger] cand_ok(t, m, sel@[y]),
            forall|y: int| 0 <= y < s0.len() ==> spos(t, *x, (#[trigger] sel@[y]).ps as int) < i,
            qs.len() + s0.len() == sel@.len(),
            forall|y: int| 0 <= y < qs.len() ==> lo <= #[trigger] qs[y] < p && x.perm@[qs[y]] == sel@[s0.len() + y].ps,
            forall|y: int, z: int| 0 <= y < sel@.len() && 0 <= z < sel@.len() && y != z ==> pair_ne(#[trigger] sel@[y], #[trigger] sel@[z]),
            forall|q: int, pi: int| lo <= q < p && #[trigger] cpair(t, m, pi, x.perm@[q] as int) ==> has_pair(sel@, pi, x.perm@[q] as int),
        decreases hi - p,
    {
        assert(rki::in_entry(x.offs@, e as int, p as int));
        let k = x.perm[p] as usize;
        let ghost kk = k as int;
        proof {
            assert(t.ps[kk][1] == Val::Int(meta[1] + e));
            assert(smatch(t, kk, j as int));
            lemma_spos(t, *x, kk, i as int);
        }
        let ghost before = sel@;
        let pi = if ratio == 4 { k / 4 } else { k / ratio };
        if pi < np {
            assert(part_row_ok(c.p, t.p[pi as int], pi as int));
            proof { lemma_grp_bound(c.p.n as int, c.p.bs as int, c.p.ng as int, pi as int); }
            let pg = grp(pi, c.p.bs);
            let sz: i64 = c.p.size_b[pg] + c.p.size_c[pi] as i64;
            let te = (c.p.type_b[pg] + c.p.type_c[pi] as u64) as usize;
            assert(lk.like_ok@[te as int] == like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, te as int)), m.pat));
            if sz == a.size && lk.like_ok[te] {
                assert(part_sel(t, m, pi as int));
                let pk = part_key(c, a, pi, Ghost(t), Ghost(m));
                let (plo, phi) = ps_range(c, a, pk, Ghost(t));
                let (found, best) = part_best(c, lk, a, pk, plo, phi, Ghost(t), Ghost(m));
                assert(ps_row_ok(c.ps, t.ps[kk], kk));
                proof { lemma_grp_bound(c.ps.n as int, c.ps.bs as int, c.ps.ng as int, kk); }
                let cst = c.ps.cost_b[grp(k, c.ps.bs)] + c.ps.cost_c[k] as i64;
                proof {
                    assert(t.ps[kk][0] == Val::Int(a.p_first + kk / (ratio as int)));
                    assert(t.p[pi as int][0] == Val::Int(a.p_first + pi));
                }
                if found && cst == best {
                    let cd = Cand { part: pi, ps: k, supp: j, nation: n, acct: bj };
                    sel.push(cd);
                    proof {
                        let pkv = Val::Int(pk as int);
                        let r = choose|r: int| #[trigger] rmatch(t, m, n as int, r);
                        assert(inreg(t, m, kk)) by {
                            assert(smatch(t, kk, j as int) && nmatch(t, j as int, n as int) && rmatch(t, m, n as int, r));
                        }
                        assert(qual(t, m, pkv, kk));
                        assert(is_min(t, m, pkv, kk));
                        assert(cand_ok(t, m, cd));
                        assert(sel@ == before.push(cd));
                        assert forall|y: int| 0 <= y < sel@.len() implies #[trigger] cand_ok(t, m, sel@[y]) by {
                            if y < before.len() { assert(sel@[y] == before[y]); }
                        }
                        assert forall|y: int| 0 <= y < s0.len() implies spos(t, *x, (#[trigger] sel@[y]).ps as int) < i by {
                            assert(sel@[y] == before[y]);
                        }
                        let q0 = qs;
                        qs = qs.push(p as int);
                        assert forall|y: int| 0 <= y < qs.len() implies lo <= #[trigger] qs[y] < p + 1 && x.perm@[qs[y]] == sel@[s0.len() + y].ps by {
                            if y < q0.len() {
                                assert(qs[y] == q0[y]);
                                assert(sel@[s0.len() + y] == before[s0.len() + y]);
                            }
                        }
                        assert forall|y: int, z: int| 0 <= y < sel@.len() && 0 <= z < sel@.len() && y != z
                            implies pair_ne(#[trigger] sel@[y], #[trigger] sel@[z]) by {
                            if y < before.len() && z < before.len() {
                                assert(sel@[y] == before[y] && sel@[z] == before[z]);
                            } else {
                                let w = if y < before.len() { y } else { z };
                                assert(w < before.len());
                                assert(sel@[w] == before[w]);
                                lemma_new_ne(t, m, *x, s0, before, q0, cd, w, i as int, lo as int, p as int);
                            }
                        }
                        assert forall|q: int, pi2: int| lo <= q < p + 1 && #[trigger] cpair(t, m, pi2, x.perm@[q] as int)
                            implies has_pair(sel@, pi2, x.perm@[q] as int) by {
                            if q < p {
                                let y = choose|y: int| 0 <= y < before.len() && #[trigger] before[y].part == pi2 && before[y].ps == x.perm@[q] as int;
                                assert(sel@[y] == before[y]);
                            } else {
                                lemma_part_of(t, m, a, kk, pi2);
                                assert(sel@[before.len() as int] == cd);
                            }
                        }
                        assert(sel@.subrange(0, s0.len() as int) =~= before.subrange(0, s0.len() as int));
                    }
                } else {
                    proof {
                        assert forall|q: int, pi2: int| lo <= q < p + 1 && #[trigger] cpair(t, m, pi2, x.perm@[q] as int)
                            implies has_pair(sel@, pi2, x.perm@[q] as int) by {
                            if q == p {
                                lemma_part_of(t, m, a, kk, pi2);
                                let pkv = Val::Int(pk as int);
                                assert(qual(t, m, pkv, kk));
                                if found {
                                    let k0 = choose|k0: int| qual(t, m, pkv, k0) && cost(t, k0) == best;
                                    assert(cost(t, kk) <= cost(t, k0));
                                }
                            }
                        }
                    }
                }
            } else {
                proof {
                    assert forall|q: int, pi2: int| lo <= q < p + 1 && #[trigger] cpair(t, m, pi2, x.perm@[q] as int)
                        implies has_pair(sel@, pi2, x.perm@[q] as int) by {
                        if q == p {
                            lemma_part_of(t, m, a, kk, pi2);
                        }
                    }
                }
            }
        } else {
            proof {
                assert forall|q: int, pi2: int| lo <= q < p + 1 && #[trigger] cpair(t, m, pi2, x.perm@[q] as int)
                    implies has_pair(sel@, pi2, x.perm@[q] as int) by {
                    if q == p {
                        lemma_part_of(t, m, a, kk, pi2);
                    }
                }
            }
        }
        p = p + 1;
    }
    proof {
        // Every new candidate's supplier is at position `i`; every candidate pair of supplier `j` was visited.
        assert forall|y: int| 0 <= y < sel@.len() implies spos(t, *x, (#[trigger] sel@[y]).ps as int) < i + 1 by {
            if y >= s0.len() {
                let q = qs[y - s0.len()];
                assert(lo <= q < hi && x.perm@[q] == sel@[y].ps);
                assert(rki::in_entry(x.offs@, e as int, q));
                assert(t.ps[x.perm@[q] as int][1] == Val::Int(meta[1] + e));
                assert(smatch(t, x.perm@[q] as int, j as int));
                lemma_spos(t, *x, x.perm@[q] as int, i as int);
            }
        }
        assert forall|pi: int, k: int| #[trigger] cpair(t, m, pi, k) && spos(t, *x, k) == i implies has_pair(sel@, pi, k) by {
            // `k` qualifies, so it has a supplier: the one at position `i`, `j`.
            let pkv = t.p[pi][0];
            assert(qual(t, m, pkv, k));
            let (j0, n0, r0) = choose|j0: int, n0: int, r0: int| #![trigger smatch(t, k, j0), nmatch(t, j0, n0), rmatch(t, m, n0, r0)]
                smatch(t, k, j0) && nmatch(t, j0, n0) && rmatch(t, m, n0, r0);
            lemma_spos_of(t, *x, k, j0);
            assert(j0 == j);
            rki::lemma_key_rows(meta, x.offs@, x.perm@, t.ps, x.kmin + e, k);
            let q = choose|q: int| #[trigger] rki::in_entry(x.offs@, e as int, q) && x.perm@[q] == k;
        }
    }
}

/// A new candidate (at position `p` of the entry, supplier position `i`) differs from an earlier one `w`: those of
/// earlier suppliers by their supplier position, those of this supplier by their entry position (`qs`).
proof fn lemma_new_ne(t: Tabs, m: Prm, x: RankIdx, s0: Seq<Cand>, before: Seq<Cand>, qs: Seq<int>, cd: Cand, w: int, i: int, lo: int, p: int)
    requires
        keys_unique(t), rank_ok(x, t),
        0 <= w < before.len(), s0.len() <= before.len(), qs.len() + s0.len() == before.len(),
        forall|y: int| 0 <= y < s0.len() ==> spos(t, x, (#[trigger] before[y]).ps as int) < i,
        forall|y: int| 0 <= y < qs.len() ==> lo <= #[trigger] qs[y] < p && x.perm@[qs[y]] == before[s0.len() + y].ps,
        0 <= lo <= p < x.perm@.len(), cd.ps == x.perm@[p], spos(t, x, cd.ps as int) == i,
    ensures pair_ne(before[w], cd), pair_ne(cd, before[w]),
{
    if w < s0.len() {
        assert(spos(t, x, before[w].ps as int) < i);
    } else {
        let q = qs[w - s0.len()];
        assert(x.perm@[q] != x.perm@[p as int]);
    }
}

// ------------------------------------------------------------------------------------------------ the candidates below thr

/// Partsupp row `k` is the partsupp row of some candidate pair.
pub open spec fn has_cand(t: Tabs, m: Prm, k: int) -> bool {
    exists|i: int| cpair(t, m, i, k)
}

/// The candidate of partsupp row `k` (when it has one): its part, supplier and nation rows, and its balance.
pub open spec fn cand_of(t: Tabs, m: Prm, k: int) -> Cand {
    let i = choose|i: int| cpair(t, m, i, k);
    let j = supp_of(t, k);
    let n = choose|n: int| nmatch(t, j, n);
    Cand { part: i as usize, ps: k as usize, supp: j as usize, nation: n as usize, acct: rki::bal(t.s, j) as i64 }
}

/// The candidates of the partsupp rows below `k` whose supplier's balance is below `thr`, in row order.
pub open spec fn low_cands(t: Tabs, m: Prm, thr: int, k: int) -> Seq<Cand>
    decreases k,
{
    if k <= 0 {
        Seq::empty()
    } else if has_cand(t, m, k - 1) && rki::bal(t.s, supp_of(t, k - 1)) < thr {
        low_cands(t, m, thr, k - 1).push(cand_of(t, m, k - 1))
    } else {
        low_cands(t, m, thr, k - 1)
    }
}

/// The candidate of a partsupp row with one is a candidate, of its part.
proof fn lemma_cand_of(c: Cols, t: Tabs, m: Prm, k: int)
    requires cols_ok(c, t), keys_unique(t), has_cand(t, m, k),
    ensures
        cand_ok(t, m, cand_of(t, m, k)),
        cand_of(t, m, k).ps == k,
        cand_of(t, m, k).supp == supp_of(t, k),
        cand_of(t, m, k).acct == rki::bal(t.s, supp_of(t, k)),
        forall|i: int| #[trigger] cpair(t, m, i, k) ==> cand_of(t, m, k).part == i,
{
    let i = choose|i: int| cpair(t, m, i, k);
    let pkv = t.p[i][0];
    assert(qual(t, m, pkv, k));
    let (j0, n0, r0) = choose|j0: int, n0: int, r0: int| #![trigger smatch(t, k, j0), nmatch(t, j0, n0), rmatch(t, m, n0, r0)]
        smatch(t, k, j0) && nmatch(t, j0, n0) && rmatch(t, m, n0, r0);
    let j = supp_of(t, k);
    lemma_supp_unique(t, k, j0, j);
    let n = choose|n: int| nmatch(t, j, n);
    assert(nmatch(t, j, n0));
    assert(t.n[n][0] == t.n[n0][0]);
    assert(n == n0);
    assert(supp_row_ok(c.s, t.s[j], j));
    let cd = cand_of(t, m, k);
    assert(rki::bal(t.s, j) == fv32(c.s.acct_c@, c.s.acct_b@, c.s.bs as int, j));
    assert(rmatch(t, m, cd.nation as int, r0));
    assert forall|i2: int| #[trigger] cpair(t, m, i2, k) implies cd.part == i2 by {
        assert(qual(t, m, t.p[i2][0], k));
        assert(t.p[i2][0] == t.p[i][0]);
    }
}

/// The candidates below `thr`: sound, below `thr`, in increasing partsupp order, and complete.
proof fn lemma_low(c: Cols, t: Tabs, m: Prm, thr: int, k: int)
    requires cols_ok(c, t), keys_unique(t), 0 <= k <= t.ps.len(),
    ensures ({
        let l = low_cands(t, m, thr, k);
        &&& forall|y: int| 0 <= y < l.len() ==> cand_ok(t, m, #[trigger] l[y]) && l[y].acct < thr && 0 <= l[y].ps < k
        &&& forall|y: int, z: int| 0 <= y < z < l.len() ==> (#[trigger] l[y]).ps < (#[trigger] l[z]).ps
        &&& forall|pi: int, k2: int| 0 <= k2 < k && #[trigger] cpair(t, m, pi, k2) && rki::bal(t.s, supp_of(t, k2)) < thr
                ==> has_pair(l, pi, k2)
    }),
    decreases k,
{
    if k > 0 {
        lemma_low(c, t, m, thr, k - 1);
        let l0 = low_cands(t, m, thr, k - 1);
        let l = low_cands(t, m, thr, k);
        if has_cand(t, m, k - 1) && rki::bal(t.s, supp_of(t, k - 1)) < thr {
            lemma_cand_of(c, t, m, k - 1);
            let cd = cand_of(t, m, k - 1);
            assert(l == l0.push(cd));
            assert forall|y: int| 0 <= y < l.len() implies cand_ok(t, m, #[trigger] l[y]) && l[y].acct < thr && 0 <= l[y].ps < k by {
                if y < l0.len() { assert(l[y] == l0[y]); }
            }
            assert forall|y: int, z: int| 0 <= y < z < l.len() implies (#[trigger] l[y]).ps < (#[trigger] l[z]).ps by {
                assert(l[y] == l0[y]);
                assert(l0[y].ps < k - 1);
                if z < l0.len() { assert(l[z] == l0[z]); } else { assert(l[z] == cd); }
            }
            assert forall|pi: int, k2: int| 0 <= k2 < k && #[trigger] cpair(t, m, pi, k2) && rki::bal(t.s, supp_of(t, k2)) < thr
                implies has_pair(l, pi, k2) by {
                if k2 < k - 1 {
                    let y = choose|y: int| 0 <= y < l0.len() && #[trigger] l0[y].part == pi && l0[y].ps == k2;
                    assert(l[y] == l0[y]);
                } else {
                    assert(l[l0.len() as int] == cd);
                }
            }
        } else {
            assert(l == l0);
            assert forall|pi: int, k2: int| 0 <= k2 < k && #[trigger] cpair(t, m, pi, k2) && rki::bal(t.s, supp_of(t, k2)) < thr
                implies has_pair(l, pi, k2) by {
                if k2 == k - 1 {
                    assert(cpair(t, m, pi, k - 1));
                    assert(has_cand(t, m, k - 1));
                }
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ select lemmas

/// Selecting over a concatenation.
proof fn lemma_select_concat(s: Seq<Cand>, u: Seq<Cand>, f: spec_fn(Cand) -> bool)
    ensures select(s + u, f) == select(s, f) + select(u, f),
    decreases u.len(),
{
    if u.len() == 0 {
        assert(s + u =~= s);
        assert(select(s, f) + select(u, f) =~= select(s, f));
    } else {
        let d = u.drop_last();
        lemma_select_concat(s, d, f);
        assert((s + u).drop_last() =~= s + d);
        assert((s + u).last() == u.last());
        if f(u.last()) {
            assert(select(s, f) + select(d, f).push(u.last()) =~= (select(s, f) + select(d, f)).push(u.last()));
        }
    }
}

/// Selecting keeps every element when all satisfy `f`, and none when none do.
proof fn lemma_select_all(s: Seq<Cand>, f: spec_fn(Cand) -> bool, all: bool)
    requires forall|y: int| 0 <= y < s.len() ==> f(#[trigger] s[y]) == all,
    ensures select(s, f) == (if all { s } else { Seq::<Cand>::empty() }),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|y: int| 0 <= y < d.len() implies f(#[trigger] d[y]) == all by {
            assert(d[y] == s[y]);
        }
        lemma_select_all(d, f, all);
        assert(f(s.last()) == all);
        if all {
            assert(d.push(s.last()) =~= s);
        }
    }
}

// ------------------------------------------------------------------------------------------------ the pick

/// The candidates found and those below `thr` are all candidates, of which the found ones are those reaching `thr`.
proof fn lemma_picked(c: Cols, t: Tabs, m: Prm, x: RankIdx, sel: Seq<Cand>, thr: int, i: int)
    requires
        cols_ok(c, t), keys_unique(t), rank_ok(x, t),
        0 <= i <= x.sbal@.len(),
        sel_ok(t, m, x, sel, i), walked(t, m, x, sel, i),
        forall|y: int| 0 <= y < sel.len() ==> (#[trigger] sel[y]).acct >= thr,
        forall|i2: int| i <= i2 < x.sbal@.len() ==> rki::bal(t.s, #[trigger] x.sbal@[i2] as int) < thr,
        sel.len() >= 100 || thr == i64::MIN,
    ensures super::picked_ok(t, m, sel + low_cands(t, m, thr, t.ps.len() as int), sel, thr),
{
    let low = low_cands(t, m, thr, t.ps.len() as int);
    let all = sel + low;
    lemma_low(c, t, m, thr, t.ps.len() as int);
    assert forall|y: int| 0 <= y < all.len() implies #[trigger] cand_ok(t, m, all[y]) by {
        if y < sel.len() { assert(all[y] == sel[y]); } else { assert(all[y] == low[y - sel.len()]); }
    }
    assert forall|y: int, z: int| 0 <= y < all.len() && 0 <= z < all.len() && y != z implies pair_ne(#[trigger] all[y], #[trigger] all[z]) by {
        if y < sel.len() && z < sel.len() {
            assert(all[y] == sel[y] && all[z] == sel[z]);
        } else if y >= sel.len() && z >= sel.len() {
            assert(all[y] == low[y - sel.len()] && all[z] == low[z - sel.len()]);
            if y < z {
                assert(low[y - sel.len()].ps < low[z - sel.len()].ps);
            } else {
                assert(low[z - sel.len()].ps < low[y - sel.len()].ps);
            }
        } else {
            let (ys, zl) = if y < sel.len() { (y, z - sel.len()) } else { (z, y - sel.len()) };
            assert(all[ys] == sel[ys]);
            assert(all[zl + sel.len()] == low[zl]);
            lemma_cand_supp(t, m, x, sel[ys]);
            lemma_cand_supp(t, m, x, low[zl]);
            assert(cand_ok(t, m, low[zl]) && low[zl].acct < thr);
        }
    }
    assert forall|pi: int, k: int| 0 <= pi < t.p.len() && #[trigger] part_sel(t, m, pi) && #[trigger] is_min(t, m, t.p[pi][0], k)
        implies has_pair(all, pi, k) by {
        assert(cpair(t, m, pi, k));
        let pkv = t.p[pi][0];
        assert(qual(t, m, pkv, k));
        let (j0, n0, r0) = choose|j0: int, n0: int, r0: int| #![trigger smatch(t, k, j0), nmatch(t, j0, n0), rmatch(t, m, n0, r0)]
            smatch(t, k, j0) && nmatch(t, j0, n0) && rmatch(t, m, n0, r0);
        lemma_spos_of(t, x, k, j0);
        if rki::bal(t.s, supp_of(t, k)) < thr {
            let y = choose|y: int| 0 <= y < low.len() && #[trigger] low[y].part == pi && low[y].ps == k;
            assert(all[y + sel.len()] == low[y]);
        } else {
            let i2 = spos(t, x, k);
            if i2 >= i {
                assert(rki::bal(t.s, x.sbal@[i2] as int) < thr);
            }
            let y = choose|y: int| 0 <= y < sel.len() && #[trigger] sel[y].part == pi && sel[y].ps == k;
            assert(all[y] == sel[y]);
        }
    }
    assert(cands_ok(t, m, all));
    lemma_select_concat(sel, low, ge_f(thr));
    lemma_select_all(sel, ge_f(thr), true);
    assert forall|y: int| 0 <= y < low.len() implies ge_f(thr)(#[trigger] low[y]) == false by {
        assert(low[y].acct < thr);
    }
    assert forall|y: int| 0 <= y < sel.len() implies ge_f(thr)(#[trigger] sel[y]) == true by {
        assert(sel[y].acct >= thr);
    }
    lemma_select_all(low, ge_f(thr), false);
    assert(select(all, ge_f(thr)) =~= sel);
    if thr == i64::MIN {
        super::lemma_none_below_min(all);
    }
}

// ------------------------------------------------------------------------------------------------ the walk

/// Partsupp rows visited after which the walk gives up (the caller then scans instead).
pub const VISIT_BUDGET: usize = 4_000_000;

/// Partsupp row `k` whose supplier sits at position `i` outside the region (or without directory entry) has no
/// candidate pair: walking position `i` adds nothing.
proof fn lemma_walked_skip(t: Tabs, m: Prm, x: RankIdx, cs: Seq<Cand>, i: int)
    requires
        keys_unique(t), rank_ok(x, t), 0 <= i < x.sbal@.len(), walked(t, m, x, cs, i),
        forall|k: int| 0 <= k < t.ps.len() && smatch(t, k, x.sbal@[i] as int) ==> !#[trigger] inreg(t, m, k),
    ensures walked(t, m, x, cs, i + 1),
{
    assert forall|pi: int, k: int| #[trigger] cpair(t, m, pi, k) && spos(t, x, k) < i + 1 implies has_pair(cs, pi, k) by {
        assert(qual(t, m, t.p[pi][0], k));
        let (j0, n0, r0) = choose|j0: int, n0: int, r0: int| #![trigger smatch(t, k, j0), nmatch(t, j0, n0), rmatch(t, m, n0, r0)]
            smatch(t, k, j0) && nmatch(t, j0, n0) && rmatch(t, m, n0, r0);
        lemma_spos_of(t, x, k, j0);
        if spos(t, x, k) == i {
            assert(!inreg(t, m, k));
        }
    }
}

/// The supplier-driven candidates and threshold (see the module header), or `None` past the visit budget.
pub fn walk(c: &Cols, lk: &Lookups, a: ScanArgs, x: &RankIdx, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    -> (r: Option<(Vec<Cand>, i64, Ghost<Seq<Cand>>)>)
    requires scan_env(*c, *lk, a, t, m), rank_ok(*x, t), a.psrun, a.p_dense,
    ensures r matches Some(p) ==> super::picked_ok(t, m, p.2@, p.0@, p.1 as int),
{
    let ghost meta = rmeta(*x);
    let ns = x.sbal.len();
    let nk = x.offs.len() - 1;
    let mut sel: Vec<Cand> = Vec::new();
    let mut prev: i64 = 0;
    let mut visited: usize = 0;
    let mut i: usize = 0;
    proof {
        assert forall|pi: int, k: int| #[trigger] cpair(t, m, pi, k) && spos(t, *x, k) < 0 implies has_pair(sel@, pi, k) by {
            assert(qual(t, m, t.p[pi][0], k));
            let (j0, n0, r0) = choose|j0: int, n0: int, r0: int| #![trigger smatch(t, k, j0), nmatch(t, j0, n0), rmatch(t, m, n0, r0)]
                smatch(t, k, j0) && nmatch(t, j0, n0) && rmatch(t, m, n0, r0);
            lemma_spos_of(t, *x, k, j0);
        }
    }
    while i < ns
        invariant
            scan_env(*c, *lk, a, t, m), rank_ok(*x, t), a.psrun, a.p_dense,
            meta == rmeta(*x),
            ns == x.sbal@.len(), ns == t.s.len(), nk + 1 == x.offs@.len(),
            i <= ns, visited <= VISIT_BUDGET,
            sel_ok(t, m, *x, sel@, i as int),
            walked(t, m, *x, sel@, i as int),
            i > 0 ==> prev as int == rki::bal(t.s, x.sbal@[i - 1] as int),
        decreases ns - i,
    {
        let j = x.sbal[i] as usize;
        assert(supp_row_ok(c.s, t.s[j as int], j as int));
        proof { lemma_grp_bound(c.s.n as int, c.s.bs as int, c.s.ng as int, j as int); }
        let g = grp(j, c.s.bs);
        let bj: i64 = c.s.acct_b[g] + c.s.acct_c[j] as i64;
        assert(rki::bal(t.s, j as int) == bj);
        if sel.len() >= 100 && i > 0 && bj < prev {
            proof {
                assert forall|y: int| 0 <= y < sel@.len() implies (#[trigger] sel@[y]).acct >= prev by {
                    lemma_cand_supp(t, m, *x, sel@[y]);
                    rki::lemma_desc(x.sbal@, t.s, spos(t, *x, sel@[y].ps as int), i - 1);
                }
                assert forall|i2: int| i <= i2 < ns implies rki::bal(t.s, #[trigger] x.sbal@[i2] as int) < prev by {
                    rki::lemma_desc(x.sbal@, t.s, i as int, i2);
                }
                lemma_picked(*c, t, m, *x, sel@, prev as int, i as int);
            }
            return Some((sel, prev, Ghost(sel@ + low_cands(t, m, prev as int, t.ps.len() as int))));
        }
        let nv: i64 = c.s.nat_b[g] + c.s.nat_c[j] as i64;
        let rn: Option<usize> = match nation_of(lk, nv, Ghost(*c), Ghost(t), Ghost(m)) {
            Some(n) => {
                assert(nreg_ok(lk.nreg@[n as int], t, m, n as int));
                if lk.nreg[n] > 0 { Some(n) } else { None }
            },
            None => None,
        };
        match rn {
            Some(n) => {
                assert(nmatch(t, j as int, n as int));
                assert(rmatch(t, m, n as int, lk.nreg@[n as int] - 1));
                let v: i64 = c.s.key_b[g] + c.s.key_c[j] as i64;
                let d: i128 = v as i128 - x.kmin as i128;
                if 0 <= d && d < nk as i128 {
                    let e = d as usize;
                    proof { rki::lemma_offs_mono(meta, x.offs@, x.perm@, t.ps, e as int, e + 1); }
                    let lo = x.offs[e] as usize;
                    let hi = x.offs[e + 1] as usize;
                    if hi - lo > VISIT_BUDGET - visited {
                        return None;
                    }
                    visited = visited + (hi - lo);
                    let ghost before = sel@;
                    proof { assert(t.s[j as int][0] == Val::Int(x.kmin + e)); }
                    walk_entry(c, lk, a, x, i, j, n, bj, e, lo, hi, &mut sel, Ghost(t), Ghost(m));
                    proof {
                        assert forall|pi: int, k: int| #[trigger] cpair(t, m, pi, k) && spos(t, *x, k) < i + 1 implies has_pair(sel@, pi, k) by {
                            if spos(t, *x, k) < i {
                                let y = choose|y: int| 0 <= y < before.len() && #[trigger] before[y].part == pi && before[y].ps == k;
                                assert(sel@.subrange(0, before.len() as int)[y] == before[y]);
                                assert(sel@[y] == before[y]);
                            }
                        }
                    }
                } else {
                    proof {
                        assert forall|k: int| 0 <= k < t.ps.len() && smatch(t, k, j as int) implies !#[trigger] inreg(t, m, k) by {
                            rki::lemma_key_rows(meta, x.offs@, x.perm@, t.ps, v as int, k);
                        }
                        lemma_walked_skip(t, m, *x, sel@, i as int);
                    }
                }
            },
            None => {
                proof {
                    assert forall|k: int| 0 <= k < t.ps.len() && smatch(t, k, j as int) implies !#[trigger] inreg(t, m, k) by {
                        assert forall|n: int, r: int| nmatch(t, j as int, n) implies !#[trigger] rmatch(t, m, n, r) by {}
                        lemma_not_inreg(t, m, k, j as int);
                    }
                    lemma_walked_skip(t, m, *x, sel@, i as int);
                }
            },
        }
        prev = bj;
        i = i + 1;
    }
    proof {
        lemma_picked(*c, t, m, *x, sel@, i64::MIN as int, ns as int);
    }
    Some((sel, i64::MIN, Ghost(sel@ + low_cands(t, m, i64::MIN as int, t.ps.len() as int))))
}

} // verus!
