//! GROUP BY of the kept rows (calling thread): one group per `(tag, version)` key in first-occurrence order, with
//! its COUNT(*), SUM(value) coefficient and absolute coefficient sum, exactly the `link::query` accumulators
//! `gkeys` / `gcount` / `gsum` / `gabs` of the normal form `sem::nf` over the projected kept rows (`groups_ok`).
//!
//! A row finds its group by a linear search over the groups (exact text comparison with the group's representative
//! row): the kept rows are few for the statement's bindings. The absolute sums are checked; a group whose absolute
//! sum leaves `i128` makes the statement leave the capacity domain (`Over`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::link::expr::i128_max;
use crate::stores::flat_num::interface as ni;
use crate::agent::spec::*;
use crate::agent::sem::*;
use crate::agent::txt::*;
use crate::agent::scan::kept;

verus! {

/// The projected rows of a sequence of row numbers.
pub open spec fn xr(c: Ctx, u: Seq<usize>) -> Seq<Row> {
    u.map_values(|i: usize| xrow(c, i as int))
}

/// The groups `reps/cnts/sums/masses` are the accumulators of the projected rows `xs`.
#[verifier::opaque]
pub open spec fn groups_ok(c: Ctx, xs: Seq<Row>, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>, masses: Seq<u128>) -> bool {
    let g = nf(c);
    let ks = gkeys(g, xs);
    &&& reps.len() == ks.len() && cnts.len() == ks.len() && sums.len() == ks.len() && masses.len() == ks.len()
    &&& forall|t: int| #![trigger reps[t]] 0 <= t < ks.len() ==> {
        &&& (reps[t] as int) < c.n
        &&& ks[t] == nf_key(xrow(c, reps[t] as int))
        &&& cnts[t] as int == gcount(g, xs, ks[t])
        &&& sums[t] as int == gsum(g, xs, ks[t], 1)
        &&& masses[t] as int == gabs(g, xs, ks[t], 1)
        &&& gabs(g, xs, ks[t], 1) <= i128_max()
    }
}

/// The facts of `groups_ok` for the representatives, and for one group `t`.
pub proof fn lemma_groups_reps(c: Ctx, xs: Seq<Row>, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>, masses: Seq<u128>)
    requires groups_ok(c, xs, reps, cnts, sums, masses),
    ensures
        gkeys(nf(c), xs).len() == reps.len(),
        reps.len() == cnts.len() && reps.len() == sums.len() && reps.len() == masses.len(),
        forall|t: int| #![trigger reps[t]] 0 <= t < reps.len() ==>
            (reps[t] as int) < c.n && gkeys(nf(c), xs)[t] == nf_key(xrow(c, reps[t] as int)),
{
    reveal(groups_ok);
}

pub proof fn lemma_groups_at(c: Ctx, xs: Seq<Row>, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>, masses: Seq<u128>, t: int)
    requires groups_ok(c, xs, reps, cnts, sums, masses), 0 <= t < reps.len(),
    ensures ({
        let k = gkeys(nf(c), xs)[t];
        &&& cnts[t] as int == gcount(nf(c), xs, k)
        &&& sums[t] as int == gsum(nf(c), xs, k, 1)
        &&& masses[t] as int == gabs(nf(c), xs, k, 1)
    }),
{
    reveal(groups_ok);
    let r = reps[t];
    assert((r as int) < c.n);
}

/// The key of a projected row.
pub proof fn lemma_xrow_key(c: Ctx, i: int)
    ensures nf_key(xrow(c, i)) == seq![Val::Text(ntag(c, i)), Val::Text(nver(c, i))],
{
    assert(nf_key(xrow(c, i)) =~= seq![Val::Text(ntag(c, i)), Val::Text(nver(c, i))]);
}

/// A group count is at most the number of rows.
pub proof fn lemma_gcount_le(g: QuerySpec, xs: Seq<Row>, k: Row)
    ensures gcount(g, xs, k) <= xs.len(),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_gcount_le(g, xs.drop_last(), k);
    }
}

/// `|v|` as an unsigned 128-bit integer.
fn abs_u128(v: i128) -> (r: u128)
    ensures r as int == abs(v as int),
{
    if v < 0 {
        let w = -(v + 1);
        (w as u128) + 1
    } else {
        v as u128
    }
}

/// The group of row `i` among the groups with representatives `reps` (keys `ks`).
fn find_group(reps: &Vec<usize>, tag_col: &TextCol, ver_col: &TextCol, i: usize, Ghost(c): Ghost<Ctx>, Ghost(ks): Ghost<Seq<Row>>)
    -> (r: Option<usize>)
    requires
        ctx_ok(c), (i as int) < c.n,
        tag_col@ == ntag_v(c), ver_col@ == nver_v(c), text_wf(tag_col@, c.n), text_wf(ver_col@, c.n),
        ks.len() == reps@.len(),
        forall|t: int| #![trigger reps@[t]] 0 <= t < ks.len() ==> (reps@[t] as int) < c.n && ks[t] == nf_key(xrow(c, reps@[t] as int)),
    ensures
        r matches Some(t) ==> t < reps@.len() && ks[t as int] == nf_key(xrow(c, i as int)),
        r is None ==> !ks.contains(nf_key(xrow(c, i as int))),
{
    let ghost key = nf_key(xrow(c, i as int));
    proof {
        lemma_xrow_key(c, i as int);
    }
    let ng = reps.len();
    let mut t: usize = 0;
    while t < ng
        invariant
            t <= ng, ng == reps@.len(), ks.len() == ng, ctx_ok(c), (i as int) < c.n,
            tag_col@ == ntag_v(c), ver_col@ == nver_v(c), text_wf(tag_col@, c.n), text_wf(ver_col@, c.n),
            forall|t2: int| #![trigger reps@[t2]] 0 <= t2 < ks.len() ==> (reps@[t2] as int) < c.n && ks[t2] == nf_key(xrow(c, reps@[t2] as int)),
            key == seq![Val::Text(ntag(c, i as int)), Val::Text(nver(c, i as int))],
            forall|t2: int| 0 <= t2 < t ==> #[trigger] ks[t2] != key,
        decreases ng - t,
    {
        let rep = reps[t];
        proof {
            assert((reps@[t as int] as int) < c.n && ks[t as int] == nf_key(xrow(c, reps@[t as int] as int)));
            lemma_xrow_key(c, rep as int);
        }
        if text_same(tag_col, rep, Ghost(c.n), tag_col, i, Ghost(c.n)) && text_same(ver_col, rep, Ghost(c.n), ver_col, i, Ghost(c.n)) {
            return Some(t);
        }
        proof {
            if ks[t as int] == key {
                assert(ks[t as int][0] == key[0] && ks[t as int][1] == key[1]);
            }
        }
        t = t + 1;
    }
    proof {
        if ks.contains(key) {
            let t2 = choose|t2: int| 0 <= t2 < ks.len() && ks[t2] == key;
            assert(ks[t2] != key);
        }
    }
    None
}

/// One more row of an existing group `t`.
proof fn lemma_found_step(c: Ctx, xs: Seq<Row>, i: int, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>, masses: Seq<u128>,
    t: int, cnt: u64, sum: i128, mass: u128)
    requires
        groups_ok(c, xs, reps, cnts, sums, masses), 0 <= i < c.n, nf_qual(c.pv, c.dlo, c.dhi, xrow(c, i)),
        0 <= t < reps.len(), gkeys(nf(c), xs)[t] == nf_key(xrow(c, i)),
        cnt as int == cnts[t] + 1, sum as int == sums[t] + coeff(c, i), mass as int == masses[t] + abs(coeff(c, i)),
        mass as int <= i128_max(),
    ensures
        groups_ok(c, xs.push(xrow(c, i)), reps, cnts.update(t, cnt), sums.update(t, sum), masses.update(t, mass)),
{
    reveal(groups_ok);
    let g = nf(c);
    let x = xrow(c, i);
    let ks = gkeys(g, xs);
    let key = nf_key(x);
    lemma_gkeys(g, xs);
    assert(ks.contains(key));
    let xs2 = xs.push(x);
    assert(xs2.drop_last() =~= xs);
    assert(gkeys(g, xs2) == ks);
    let (cnts2, sums2, masses2) = (cnts.update(t, cnt), sums.update(t, sum), masses.update(t, mass));
    assert forall|t2: int| #![trigger reps[t2]] 0 <= t2 < ks.len() implies {
        &&& (reps[t2] as int) < c.n
        &&& ks[t2] == nf_key(xrow(c, reps[t2] as int))
        &&& cnts2[t2] as int == gcount(g, xs2, ks[t2])
        &&& sums2[t2] as int == gsum(g, xs2, ks[t2], 1)
        &&& masses2[t2] as int == gabs(g, xs2, ks[t2], 1)
        &&& gabs(g, xs2, ks[t2], 1) <= i128_max()
    } by {
        lemma_push(g, xs, x, ks[t2], 1);
        if t2 != t {
            assert(ks[t2] != key) by {
                assert(ks.no_duplicates());
            }
        }
    }
}

/// A new group for row `i`.
proof fn lemma_new_step(c: Ctx, xs: Seq<Row>, i: int, reps: Seq<usize>, cnts: Seq<u64>, sums: Seq<i128>, masses: Seq<u128>,
    v: i128, av: u128)
    requires
        groups_ok(c, xs, reps, cnts, sums, masses), 0 <= i < c.n, c.n <= usize::MAX, nf_qual(c.pv, c.dlo, c.dhi, xrow(c, i)),
        !gkeys(nf(c), xs).contains(nf_key(xrow(c, i))),
        v as int == coeff(c, i), av as int == abs(coeff(c, i)), av as int <= i128_max(),
    ensures
        groups_ok(c, xs.push(xrow(c, i)), reps.push(i as usize), cnts.push(1), sums.push(v), masses.push(av)),
{
    reveal(groups_ok);
    let g = nf(c);
    let x = xrow(c, i);
    let ks = gkeys(g, xs);
    let key = nf_key(x);
    lemma_gkeys(g, xs);
    assert(gcount(g, xs, key) == 0);
    lemma_zero_count(g, xs, key, 1);
    let xs2 = xs.push(x);
    assert(xs2.drop_last() =~= xs);
    assert(gkeys(g, xs2) == ks.push(key));
    let ks2 = ks.push(key);
    let (reps2, cnts2, sums2, masses2) = (reps.push(i as usize), cnts.push(1), sums.push(v), masses.push(av));
    assert forall|t2: int| #![trigger reps2[t2]] 0 <= t2 < ks2.len() implies {
        &&& (reps2[t2] as int) < c.n
        &&& ks2[t2] == nf_key(xrow(c, reps2[t2] as int))
        &&& cnts2[t2] as int == gcount(g, xs2, ks2[t2])
        &&& sums2[t2] as int == gsum(g, xs2, ks2[t2], 1)
        &&& masses2[t2] as int == gabs(g, xs2, ks2[t2], 1)
        &&& gabs(g, xs2, ks2[t2], 1) <= i128_max()
    } by {
        lemma_push(g, xs, x, ks2[t2], 1);
        if t2 < ks.len() {
            assert(reps2[t2] == reps[t2]);
            assert(ks[t2] != key);
        }
    }
}

/// The groups of the kept rows `u`, or `Err(k)` with a key whose absolute sum leaves `i128`.
#[verifier::spinoff_prover]
pub fn group_rows(u: &Vec<usize>, tag_col: &TextCol, ver_col: &TextCol, value: &'static [i128], Ghost(c): Ghost<Ctx>)
    -> (r: Result<(Vec<usize>, Vec<u64>, Vec<i128>, Vec<u128>), Ghost<Row>>)
    requires
        ctx_ok(c), c.n <= usize::MAX,
        tag_col@ == ntag_v(c), ver_col@ == nver_v(c),
        value@ == ni::i128s(c.np[ni::VALUE as int]),
        forall|q: int| 0 <= q < u@.len() ==> (#[trigger] u@[q] as int) < c.n && keep(c, u@[q] as int),
    ensures
        r matches Ok(gr) ==> groups_ok(c, xr(c, u@), gr.0@, gr.1@, gr.2@, gr.3@),
        r matches Err(k) ==> gabs(nf(c), xr(c, u@), k@, 1) > i128_max(),
{
    let ghost g = nf(c);
    proof {
        lemma_text_cols_wf(c);
    }
    let mut reps: Vec<usize> = Vec::new();
    let mut cnts: Vec<u64> = Vec::new();
    let mut sums: Vec<i128> = Vec::new();
    let mut masses: Vec<u128> = Vec::new();
    let len = u.len();
    let mut q: usize = 0;
    proof {
        assert(xr(c, u@.take(0)) =~= Seq::<Row>::empty());
        reveal(groups_ok);
    }
    while q < len
        invariant
            q <= len, len == u@.len(), ctx_ok(c), c.n <= usize::MAX, g == nf(c),
            tag_col@ == ntag_v(c), ver_col@ == nver_v(c), text_wf(tag_col@, c.n), text_wf(ver_col@, c.n),
            value@ == ni::i128s(c.np[ni::VALUE as int]), value@.len() == c.n,
            forall|q2: int| 0 <= q2 < u@.len() ==> (#[trigger] u@[q2] as int) < c.n && keep(c, u@[q2] as int),
            groups_ok(c, xr(c, u@.take(q as int)), reps@, cnts@, sums@, masses@),
        decreases len - q,
    {
        let i = u[q];
        let ghost xs = xr(c, u@.take(q as int));
        let ghost x = xrow(c, i as int);
        let ghost key = nf_key(x);
        proof {
            assert(xr(c, u@.take(q + 1)) =~= xs.push(x));
            assert((u@[q as int] as int) < c.n && keep(c, u@[q as int] as int));
            lemma_xrow_qual(c, i as int);
            lemma_gkeys(g, xs);
            lemma_gcount_le(g, xs, key);
            lemma_push(g, xs, x, key, 1);
            lemma_abs_bound(g, xs.push(x), key, 1);
            lemma_groups_reps(c, xs, reps@, cnts@, sums@, masses@);
        }
        let v = value[i];
        let av = abs_u128(v);
        match find_group(&reps, tag_col, ver_col, i, Ghost(c), Ghost(gkeys(g, xs))) {
            Some(t) => {
                let m0 = masses[t];
                proof {
                    lemma_groups_at(c, xs, reps@, cnts@, sums@, masses@, t as int);
                    assert(m0 as int == gabs(g, xs, key, 1));
                    assert(cnts@[t as int] as int == gcount(g, xs, key));
                }
                let m1 = match m0.checked_add(av) {
                    Some(m1) => m1,
                    None => {
                        proof {
                            lemma_over_prefix(c, u@, q as int + 1, key);
                        }
                        return Err(Ghost(key));
                    },
                };
                if m1 > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 {
                    proof {
                        lemma_over_prefix(c, u@, q as int + 1, key);
                    }
                    return Err(Ghost(key));
                }
                let cnt = cnts[t] + 1;
                let sum = sums[t] + v;
                proof {
                    lemma_found_step(c, xs, i as int, reps@, cnts@, sums@, masses@, t as int, cnt, sum, m1);
                }
                cnts.set(t, cnt);
                sums.set(t, sum);
                masses.set(t, m1);
            },
            None => {
                if av > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 {
                    proof {
                        lemma_zero_count(g, xs, key, 1);
                        lemma_over_prefix(c, u@, q as int + 1, key);
                    }
                    return Err(Ghost(key));
                }
                proof {
                    lemma_new_step(c, xs, i as int, reps@, cnts@, sums@, masses@, v, av);
                }
                reps.push(i);
                cnts.push(1);
                sums.push(v);
                masses.push(av);
            },
        }
        q = q + 1;
    }
    proof {
        assert(u@.take(len as int) =~= u@);
    }
    Ok((reps, cnts, sums, masses))
}

/// A key whose absolute sum over a prefix leaves `i128` leaves it over all rows (absolute sums only grow).
pub proof fn lemma_over_prefix(c: Ctx, u: Seq<usize>, q: int, k: Row)
    requires 0 <= q <= u.len(), gabs(nf(c), xr(c, u.take(q)), k, 1) > i128_max(),
    ensures gabs(nf(c), xr(c, u), k, 1) > i128_max(),
{
    let g = nf(c);
    assert(xr(c, u) =~= xr(c, u.take(q)) + xr(c, u.skip(q)));
    lemma_append(g, xr(c, u.take(q)), xr(c, u.skip(q)), k, 1);
    lemma_abs_bound(g, xr(c, u.skip(q)), k, 1);
}

} // verus!
