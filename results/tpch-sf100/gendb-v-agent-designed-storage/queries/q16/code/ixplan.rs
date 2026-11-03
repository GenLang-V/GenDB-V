//! The index plan: every (brand, type, size) group read through the directory of `part_btsidx` (`xidx`).
//!
//! The groups are numbered `q = (b * nt + tt) * ns + z` (brand entry `b`, type entry `tt`, size slot `z`; the
//! round numbering `answer::gid` of one round over every entry), so increasing `q` is the answer's (brand, type,
//! size) order. Per group, `ents[q]` is its directory entry when the brand differs from `$1`, the type does not
//! match `$2`, the size lies in the index's key range and the entry has a position, else `NOENT` (`ent_ok`). The
//! subquery's bitmap (`ixcnt::excl_bitmap`) and the counts (`ixcnt::CntTask`, ranges of `q` cut by the entries'
//! position counts) take one fork-join each; the groups with a positive count are then collected in `q` order.
//! A count is the group's COUNT(DISTINCT ps_suppkey) (`lemma_ent_count`: `gset::lemma_pos_grp`,
//! `gset::lemma_grp_card`, `gset::lemma_kc_zero`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use super::tables::*;
use super::model::*;
use super::kernel::*;
use super::sqlq::{Prm, like_true};
use super::answer::*;
use super::output::{Grp, grp_lt, lex_sorted};
use super::split::*;
use super::bind::{keys_unique, fk_supp};
use super::supp::comm_ok;
use super::round::*;
use super::fin::groups_ok;
use super::prep::part_dense;
use super::common::basemarks::copy_base;
use super::xidx::*;
use super::gset::*;
use super::ixcnt::*;
use super::ssig::{SSig, ssig_ok, excl_bitmap_sig};

verus! {

/// The round of every brand, type and size slot.
pub open spec fn rall(nb: int, nt: int, ns: int) -> Rnd {
    Rnd { b0: 0, b1: nb, t0: 0, t1: nt, ns }
}

/// Group `q`'s brand entry, type entry and size slot.
pub open spec fn qb(q: int, nt: int, ns: int) -> int { (q / ns) / nt }
pub open spec fn qt(q: int, nt: int, ns: int) -> int { (q / ns) % nt }
pub open spec fn qz(q: int, ns: int) -> int { q % ns }

/// The group's size lies in the index's key range.
pub open spec fn size_in_range(xi: XIdx, v: int) -> bool {
    xi.smin <= v < xi.smin + xi.ns
}

/// `en` is group (`b`, `tt`, `z`)'s entry, or `NOENT` when the group cannot have a kept row.
pub open spec fn ent_ok(c: Cols, m: Prm, xi: XIdx, bok: Seq<bool>, tlike: Seq<bool>, sizes: Seq<i64>, b: int, tt: int,
    z: int, en: u32) -> bool
{
    let v = sizes[z] as int;
    &&& en != NOENT ==> bok[b] && !tlike[tt] && size_in_range(xi, v) && en as int == ent_of(xi, b, tt, v)
        && xi.offs@[en as int] < xi.offs@[en as int + 1]
    &&& en == NOENT ==> !bok[b] || tlike[tt] || !size_in_range(xi, v)
        || xi.offs@[ent_of(xi, b, tt, v)] >= xi.offs@[ent_of(xi, b, tt, v) + 1]
}

/// The task environment over the column handles.
fn make_env0(c: &Cols, sdense: bool, sfirst: i64, Ghost(t): Ghost<Tabs>) -> (e: PairEnv)
    requires
        cols_ok(*c, t), keys_unique(t),
        sdense ==> forall|x: int| 0 <= x < c.s.n ==> #[trigger] skey(c.s, x) == sfirst + x,
    ensures env_ok(e, 0), e.c == *c,
{
    let pn = c.p.n;
    let psn = c.ps.n;
    let ratio = if pn > 0 { psn / pn } else { 0 };
    let jmax = if ratio > 0 { psn / ratio } else { 0 };
    let ps_shift = pow2_shift(c.ps.bs);
    let tabs = Arc::new(QualTabs { bterm: Vec::new(), tterm: Vec::new(), sizes: Vec::new() });
    proof {
        lemma_shape(*c, t);
        if ratio > 0 {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(psn as int, ratio as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(psn as int, ratio as int);
            assert(jmax * ratio <= psn) by (nonlinear_arith)
                requires psn == ratio * jmax + psn % ratio, psn % ratio >= 0;
        }
        assert forall|j1: int, j2: int| 0 <= j1 < c.p.n && 0 <= j2 < c.p.n
            && #[trigger] pkey(c.p, j1) == #[trigger] pkey(c.p, j2) implies j1 == j2 by {
            assert(part_row_ok(c.p, t.p[j1], j1));
            assert(part_row_ok(c.p, t.p[j2], j2));
            assert(t.p[j1][0] == t.p[j2][0]);
        }
        assert forall|r1: int, r2: int| 0 <= r1 < c.s.n && 0 <= r2 < c.s.n
            && #[trigger] skey(c.s, r1) == #[trigger] skey(c.s, r2) implies r1 == r2 by {
            lemma_skeys_uniq(*c, t, r1, r2);
        }
        assert(tabs.sizes@.no_duplicates());
    }
    let (pfirst, pdense) = part_dense(&c.p, Ghost(c.e32@), Ghost(c.e64@));
    // psrun's key runs apply to the guess when their ratio is the guess's and divides the block size.
    let runs0 = c.ps.runs[0];
    let rper = if ratio > 0 && ratio <= 65536 && runs0 == ratio as i64 && 65536 % ratio == 0 { 65536 / ratio } else { 0 };
    proof {
        if rper > 0 {
            let (ri, pi) = (ratio as int, rper as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(65536, ri);
            assert(pi * ri == 65536) by (nonlinear_arith)
                requires 65536int == ri * (65536int / ri) + 65536int % ri, 65536int % ri == 0, pi == 65536int / ri;
        }
    }
    PairEnv { c: *c, ratio, jmax, ps_shift, sdense, sfirst, pdense, pfirst, tabs, nb: 0, nt: 0, ns: 0, rper }
}

/// The entry of every group, and its position count (the tasks' weights).
fn group_ents(c: &Cols, xi: &XIdx, bok: &Vec<bool>, tlike: &Vec<bool>, sizes: &Vec<i64>, nq: usize,
    Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (r: (Vec<u32>, Vec<u64>))
    requires
        cols_ok(*c, t),
        inputs_ok(*c, m, bok@, tlike@, sizes@),
        xidx_ok(*c, *xi),
        xi.nk < NOENT as usize,
        nq == bok@.len() * tlike@.len() * sizes@.len(),
        bok@.len() >= 1, tlike@.len() >= 1,
    ensures
        r.0@.len() == nq, r.1@.len() == nq,
        forall|q: int| 0 <= q < nq ==> (#[trigger] r.0@[q] == NOENT || r.0@[q] < xi.nk)
            && ent_ok(*c, m, *xi, bok@, tlike@, sizes@, qb(q, tlike@.len() as int, sizes@.len() as int),
                qt(q, tlike@.len() as int, sizes@.len() as int), qz(q, sizes@.len() as int), r.0@[q]),
{
    let nb = bok.len();
    let nt = tlike.len();
    let ns = sizes.len();
    let ghost rr = rall(nb as int, nt as int, ns as int);
    let mut ents: Vec<u32> = Vec::with_capacity(nq);
    let mut ws: Vec<u64> = Vec::with_capacity(nq);
    let mut q: usize = 0;
    while q < nq
        invariant
            cols_ok(*c, t), inputs_ok(*c, m, bok@, tlike@, sizes@), xidx_ok(*c, *xi), xi.nk < NOENT as usize,
            nb == bok@.len(), nt == tlike@.len(), ns == sizes@.len(), nb >= 1, nt >= 1, 1 <= ns <= 8,
            nq == nb * nt * ns, rr == rall(nb as int, nt as int, ns as int),
            q <= nq, ents@.len() == q, ws@.len() == q,
            forall|h: int| 0 <= h < q ==> (#[trigger] ents@[h] == NOENT || ents@[h] < xi.nk)
                && ent_ok(*c, m, *xi, bok@, tlike@, sizes@, qb(h, nt as int, ns as int), qt(h, nt as int, ns as int),
                    qz(h, ns as int), ents@[h]),
        decreases nq - q,
    {
        proof {
            assert(rng(rr) == nq);
            lemma_decode(rr, q as int);
        }
        let z = q % ns;
        let tt = (q / ns) % nt;
        let b = (q / ns) / nt;
        let v = sizes[z];
        let mut en: u32 = NOENT;
        let mut w: u64 = 0;
        if bok[b] && !tlike[tt] && xi.smin as i128 <= v as i128 && (v as i128) < xi.smin as i128 + xi.ns as i128 {
            let ghost e = ent_of(*xi, b as int, tt as int, v as int);
            proof {
                lemma_comp_bound(b as int, tt as int, v - xi.smin, nb as int, nt as int, xi.ns as int);
                assert(e < xi.nk);
                assert(b * nt + tt < nb * nt) by (nonlinear_arith) requires b < nb, tt < nt;
                assert(xi.nk == nb * nt * xi.ns);
                assert(nb * nt <= nb * nt * xi.ns) by (nonlinear_arith) requires xi.ns >= 1, nb >= 1, nt >= 1;
                assert((b * nt + tt) * xi.ns <= (b * nt + tt) * xi.ns + (v - xi.smin)) by (nonlinear_arith)
                    requires v - xi.smin >= 0;
                assert((b * nt + tt) * xi.ns + (v - xi.smin) == e);
                assert(b * nt <= b * nt + tt);
            }
            let ei = (b * nt + tt) * xi.ns + (v - xi.smin) as usize;
            let lo = xi.offs[ei];
            let hi = xi.offs[ei + 1];
            if lo < hi {
                en = ei as u32;
                w = (hi - lo) as u64;
            }
        }
        ents.push(en);
        ws.push(w);
        q = q + 1;
    }
    (ents, ws)
}

/// Group `q`'s count is its COUNT(DISTINCT ps_suppkey).
proof fn lemma_ent_count(c: Cols, t: Tabs, m: Prm, xi: XIdx, bok: Seq<bool>, tlike: Seq<bool>, sizes: Seq<i64>,
    b: int, tt: int, z: int, en: u32)
    requires
        cols_ok(c, t), keys_unique(t), fk_supp(t),
        inputs_ok(c, m, bok, tlike, sizes),
        xidx_ok(c, xi),
        0 <= b < bok.len(), 0 <= tt < tlike.len(), 0 <= z < sizes.len(),
        en == NOENT || en < xi.nk,
        ent_ok(c, m, xi, bok, tlike, sizes, b, tt, z, en),
    ensures want(c, xi, en) == kc(c, t, m, sizes, b, tt, z),
{
    let v = sizes[z] as int;
    assert(listed(sizes, v));
    assert(m.sizes.contains(v));
    if !bok[b] || tlike[tt] {
        lemma_kc_zero(c, t, m, sizes, b, tt, z);
    } else {
        lemma_grp_card(c, t, m, sizes, b, tt, z);
        if !size_in_range(xi, v) {
            assert forall|j: int| 0 <= j < c.p.n implies !(#[trigger] in_grp(c, j, b, tt, v)) by {}
            lemma_grp_empty(c, b, tt, v);
        } else {
            lemma_pos_grp(c, t, xi, b, tt, v);
            let e = ent_of(xi, b, tt, v);
            if en == NOENT {
                assert(pos_set(c, xi, xi.offs@[e] as int, xi.offs@[e + 1] as int) =~= Set::empty());
            }
        }
    }
}

/// Every group of the index plan, as `all_rounds` delivers them.
pub fn ix_groups(c: &Cols, xi: XIdx, sg: SSig, bok: &Vec<bool>, tlike: &Vec<bool>, sizes: &Vec<i64>, sdense: bool,
    sfirst: i64, workers: usize, dispatch: &mut Dispatch, res: &mut Vec<Grp>, Ghost(t): Ghost<Tabs>,
    Ghost(m): Ghost<Prm>) -> (r: Result<bool, QueryError>)
    requires
        ssig_ok(c.s, sg),
        world_ok(*c, t, m, sdense, sfirst),
        inputs_ok(*c, m, bok@, tlike@, sizes@),
        xidx_ok(*c, xi),
        xi.nk < NOENT as usize,
        bok@.len() <= 0x1000, tlike@.len() <= 0x1000,
        1 <= workers <= MAX_WORKERS,
        old(res)@.len() == 0,
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(false) ==> exists|b: int, tt: int, z: int| 0 <= b < bok@.len() && 0 <= tt < tlike@.len()
            && 0 <= z < sizes@.len() && #[trigger] kc(*c, t, m, sizes@, b, tt, z) > i64::MAX,
        r matches Ok(true) ==> groups_ok(*c, t, m, sizes@, final(res)@),
{
    let nb = bok.len();
    let nt = tlike.len();
    let ns = sizes.len();
    if nb == 0 || nt == 0 {
        return Ok(true);
    }
    proof {
        assert(nb * nt <= 0x100_0000) by (nonlinear_arith) requires nb <= 0x1000, nt <= 0x1000;
        assert(nb * nt * ns <= 0x800_0000) by (nonlinear_arith) requires nb * nt <= 0x100_0000, ns <= 8;
    }
    let nq = nb * nt * ns;
    let ghost rr = rall(nb as int, nt as int, ns as int);
    // The subquery's excluded supplier rows, through the s_comment signatures.
    let excl = match excl_bitmap_sig(&c.s, sg, workers, dispatch) {
        Ok(x) => x,
        Err(e) => {
            return Err(e);
        },
    };
    let (ents, ws) = group_ents(c, &xi, bok, tlike, sizes, nq, Ghost(t), Ghost(m));
    let bnd = weight_cuts(&ws, workers);
    let ntk = bnd.len() - 1;
    let sn = c.s.n;
    let env = make_env0(c, sdense, sfirst, Ghost(t));
    let glob = glob_runs(&env);
    let v = Arc::new(CntEnv { e: env, glob, xi, excl: Arc::new(excl), ents: Arc::new(ents) });
    proof {
        assert(cenv_ok(*v));
    }
    let mut tasks: Vec<CntTask> = Vec::new();
    let mut k: usize = 0;
    while k < ntk
        invariant
            cenv_ok(*v), v.e.c == *c, v.xi == xi, v.ents@.len() == nq, sn == c.s.n,
            cuts(bnd@, nq as int), ntk == bnd@.len() - 1, ntk <= workers, k <= ntk, tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].v == v
                && tasks@[i].q0 == bnd@[i] && tasks@[i].q1 == bnd@[i + 1],
        decreases ntk - k,
    {
        proof {
            assert(bnd@[k as int] <= bnd@[k + 1]);
            lemma_cuts_mono(bnd@, nq as int, k as int + 1, ntk as int);
        }
        let q0 = bnd[k];
        let q1 = bnd[k + 1];
        // The task's bitmap starts as the exclusion bitmap (`common::basemarks`).
        let ex: &Vec<u64> = &*v.excl;
        let seen: Vec<u64> = copy_base(ex);
        let tk = CntTask { v: v.clone(), q0, q1, seen, undo: vec![0usize; UCAP], counts: vec![0u64; q1 - q0] };
        tasks.push(tk);
        k = k + 1;
    }
    let ghost ts = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => {
            return Err(QueryError::WorkerFailed(e));
        },
    };
    // The groups with a positive count, in `q` order.
    let mut k: usize = 0;
    while k < ntk
        invariant
            cenv_ok(*v), v.e.c == *c, v.xi == xi, v.ents@.len() == nq,
            world_ok(*c, t, m, sdense, sfirst), inputs_ok(*c, m, bok@, tlike@, sizes@), xidx_ok(*c, xi),
            nb == bok@.len(), nt == tlike@.len(), ns == sizes@.len(), nb >= 1, nt >= 1, 1 <= ns <= 8,
            nq == nb * nt * ns, rr == rall(nb as int, nt as int, ns as int),
            cuts(bnd@, nq as int), ntk == bnd@.len() - 1, k <= ntk,
            outs@.len() == ntk, ts.len() == ntk,
            forall|i: int| 0 <= i < ntk ==> (#[trigger] ts[i]).post(outs@[i]) && ts[i].v == v
                && ts[i].q0 == bnd@[i] && ts[i].q1 == bnd@[i + 1],
            forall|h: int| 0 <= h < nq ==> (#[trigger] v.ents@[h] == NOENT || v.ents@[h] < xi.nk)
                && ent_ok(*c, m, xi, bok@, tlike@, sizes@, qb(h, nt as int, ns as int), qt(h, nt as int, ns as int),
                    qz(h, ns as int), v.ents@[h]),
            lex_sorted(res@),
            forall|i: int| 0 <= i < res@.len() ==> grp_ok(*c, t, m, sizes@, #[trigger] res@[i])
                && in_round(rr, res@[i].b as int, res@[i].t as int, res@[i].z as int)
                && gid(rr, res@[i].b as int, res@[i].t as int, res@[i].z as int) < bnd@[k as int],
            forall|b: int, tt: int, z: int| in_round(rr, b, tt, z) && gid(rr, b, tt, z) < bnd@[k as int]
                && #[trigger] kc(*c, t, m, sizes@, b, tt, z) > 0
                ==> exists|i: int| 0 <= i < res@.len() && at(#[trigger] res@[i], b, tt, z),
        decreases ntk - k,
    {
        let o = &outs[k].counts;
        let q0 = bnd[k];
        let q1 = bnd[k + 1];
        proof {
            assert(ts[k as int].post(outs@[k as int]));
            lemma_cuts_mono(bnd@, nq as int, k as int + 1, ntk as int);
        }
        let mut q = q0;
        while q < q1
            invariant
                cenv_ok(*v), v.e.c == *c, v.xi == xi, v.ents@.len() == nq,
                world_ok(*c, t, m, sdense, sfirst), inputs_ok(*c, m, bok@, tlike@, sizes@), xidx_ok(*c, xi),
                nb == bok@.len(), nt == tlike@.len(), ns == sizes@.len(), nb >= 1, nt >= 1, 1 <= ns <= 8,
                nq == nb * nt * ns, rr == rall(nb as int, nt as int, ns as int),
                q0 <= q <= q1 <= nq,
                o@.len() == q1 - q0,
                forall|h: int| q0 <= h < q1 ==> #[trigger] o@[h - q0] as int == want(*c, xi, v.ents@[h]),
                forall|h: int| 0 <= h < nq ==> (#[trigger] v.ents@[h] == NOENT || v.ents@[h] < xi.nk)
                    && ent_ok(*c, m, xi, bok@, tlike@, sizes@, qb(h, nt as int, ns as int), qt(h, nt as int, ns as int),
                        qz(h, ns as int), v.ents@[h]),
                lex_sorted(res@),
                forall|i: int| 0 <= i < res@.len() ==> grp_ok(*c, t, m, sizes@, #[trigger] res@[i])
                    && in_round(rr, res@[i].b as int, res@[i].t as int, res@[i].z as int)
                    && gid(rr, res@[i].b as int, res@[i].t as int, res@[i].z as int) < q,
                forall|b: int, tt: int, z: int| in_round(rr, b, tt, z) && gid(rr, b, tt, z) < q
                    && #[trigger] kc(*c, t, m, sizes@, b, tt, z) > 0
                    ==> exists|i: int| 0 <= i < res@.len() && at(#[trigger] res@[i], b, tt, z),
            decreases q1 - q,
        {
            proof {
                assert(rng(rr) == nq);
                lemma_decode(rr, q as int);
            }
            let z = q % ns;
            let tt = (q / ns) % nt;
            let b = (q / ns) / nt;
            let cnt = o[q - q0];
            let ghost en = v.ents@[q as int];
            proof {
                assert(ent_ok(*c, m, xi, bok@, tlike@, sizes@, b as int, tt as int, z as int, en));
                lemma_ent_count(*c, t, m, xi, bok@, tlike@, sizes@, b as int, tt as int, z as int, en);
                assert(cnt as int == kc(*c, t, m, sizes@, b as int, tt as int, z as int));
            }
            if cnt > (i64::MAX as u64) {
                return Ok(false);
            }
            let ghost r0 = res@;
            if cnt > 0 {
                res.push(Grp { b, t: tt, z, cnt });
                proof {
                    assert forall|x: int, y: int| 0 <= x < y < res@.len() implies #[trigger] grp_lt(res@[x], res@[y])
                        && grp_lt(res@[x], res@[y]) by {
                        if y == res@.len() - 1 {
                            assert(res@[x] == r0[x]);
                            lemma_gid_lt(rr, res@[x].b as int, res@[x].t as int, res@[x].z as int, b as int, tt as int, z as int);
                        } else {
                            assert(res@[x] == r0[x] && res@[y] == r0[y]);
                        }
                    }
                }
            }
            proof {
                assert forall|i: int| 0 <= i < res@.len() implies grp_ok(*c, t, m, sizes@, #[trigger] res@[i])
                    && in_round(rr, res@[i].b as int, res@[i].t as int, res@[i].z as int)
                    && gid(rr, res@[i].b as int, res@[i].t as int, res@[i].z as int) < q + 1 by {
                    if i < r0.len() {
                        assert(res@[i] == r0[i]);
                    }
                }
                assert forall|b2: int, t2: int, z2: int| in_round(rr, b2, t2, z2) && gid(rr, b2, t2, z2) < q + 1
                    && #[trigger] kc(*c, t, m, sizes@, b2, t2, z2) > 0
                    implies exists|i: int| 0 <= i < res@.len() && at(#[trigger] res@[i], b2, t2, z2) by {
                    if gid(rr, b2, t2, z2) < q {
                        let i = choose|i: int| 0 <= i < r0.len() && at(#[trigger] r0[i], b2, t2, z2);
                        assert(res@[i] == r0[i]);
                    } else {
                        lemma_gid_inj(rr, b2, t2, z2, b as int, tt as int, z as int);
                        assert(at(res@[res@.len() - 1], b2, t2, z2));
                    }
                }
            }
            q = q + 1;
        }
        k = k + 1;
    }
    proof {
        assert forall|b2: int, tt2: int, z2: int| 0 <= b2 < c.p.brand_o@.len() - 1 && 0 <= tt2 < c.p.type_o@.len() - 1
            && 0 <= z2 < sizes@.len() && #[trigger] kc(*c, t, m, sizes@, b2, tt2, z2) > 0
            implies exists|i: int| 0 <= i < res@.len() && at(#[trigger] res@[i], b2, tt2, z2) by {
            assert(in_round(rr, b2, tt2, z2));
            lemma_gid_bound(rr, b2, tt2, z2);
        }
    }
    Ok(true)
}

} // verus!
