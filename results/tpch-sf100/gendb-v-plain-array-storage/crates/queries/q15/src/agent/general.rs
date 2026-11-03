//! The general path, for every database (the fast path declined): serial and simple, quadratic in the number of
//! groups. It builds the normal form's groups exactly as `gkeys` lists them (first-occurrence order), each with an
//! exact `i128` SUM and saturating absolute mass (`common::accum`, `build_groups`); answers `Capacity` with the
//! group whose mass leaves `i128`; otherwise takes the largest SUM (`max_of_groups`) and picks the supplier rows
//! whose key is a group key with that SUM (`general_picks`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::agent::common::selection::*;
use crate::agent::common::accum::*;
use crate::agent::common::max_num::*;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::bounds::*;
use crate::agent::scan::{p_ship, rev, lemma_rev_bound};
use crate::agent::fastspec::g_of;
use crate::agent::groups::*;
use crate::agent::answer::{pick_of, idxs_ok};

verus! {

/// The group list over the first `i` rows: `keys[j]` is the key of group `j` of `gkeys` and `accs[j]` its SUM,
/// absolute mass and count.
pub open spec fn groups_ok(keys: Seq<i64>, accs: Seq<Acc>, c: Cols, w: DayWindow, i: int) -> bool {
    let g = g_of(w);
    let rows = crows(c).take(i);
    let gk = gkeys(g, rows);
    &&& keys.len() == gk.len()
    &&& accs.len() == gk.len()
    &&& forall|j: int| 0 <= j < gk.len() ==> #[trigger] gk[j] == seq![Val::Int(keys[j] as int)]
    &&& forall|j: int| 0 <= j < gk.len() ==> acc_ok(#[trigger] accs[j], gsum(g, rows, gk[j], 0), gabs(g, rows, gk[j], 0),
            gcount(g, rows, gk[j]) as int)
}

/// The position of `key` in `keys`, or `keys.len()` when absent.
pub fn find_key(keys: &Vec<i64>, key: i64) -> (j: usize)
    ensures
        j <= keys@.len(),
        j < keys@.len() ==> keys@[j as int] == key,
        j == keys@.len() ==> forall|u: int| 0 <= u < keys@.len() ==> #[trigger] keys@[u] != key,
{
    let mut j: usize = 0;
    while j < keys.len()
        invariant j <= keys@.len(), forall|u: int| 0 <= u < j ==> #[trigger] keys@[u] != key,
        decreases keys@.len() - j,
    {
        if keys[j] == key {
            return j;
        }
        j = j + 1;
    }
    j
}

/// Row `i` of the normal form: qualifies exactly when its shipdate is in the window; its key and argument.
pub proof fn lemma_crow(c: Cols, w: DayWindow, i: int)
    requires 0 <= i < c.n,
    ensures ({
        let g = g_of(w);
        let x = crows(c)[i];
        &&& x == crow(c, i)
        &&& (g.qual)(x) == p_ship(c, w)(i)
        &&& (g.key)(x) == seq![Val::Int(c.supp@[i] as int)]
        &&& (g.arg)(0, x) == rev(c, i)
    }),
{
}

/// The groups of all rows, built row by row.
pub fn build_groups(c: &Cols, w: DayWindow) -> (r: (Vec<i64>, Vec<Acc>))
    requires cols_wf(*c),
    ensures groups_ok(r.0@, r.1@, *c, w, c.n as int),
{
    let ghost g = g_of(w);
    let ghost xs = crows(*c);
    let mut keys: Vec<i64> = Vec::new();
    let mut accs: Vec<Acc> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(xs.take(0) =~= Seq::<Row>::empty());
    }
    while i < c.n
        invariant
            cols_wf(*c),
            i <= c.n,
            g == g_of(w),
            xs == crows(*c),
            groups_ok(keys@, accs@, *c, w, i as int),
        decreases c.n - i,
    {
        let ghost rows = xs.take(i as int);
        let ghost gk = gkeys(g, rows);
        let ghost x = xs[i as int];
        proof {
            assert(xs.take(i + 1) =~= rows.push(x));
            assert(rows.push(x).drop_last() =~= rows);
            lemma_crow(*c, w, i as int);
            lemma_gkeys(g, rows);
        }
        let d = c.ship[i];
        if w.lo <= d && d < w.hi {
            let key = c.supp[i];
            proof {
                lemma_rev_bound(*c, i as int);
            }
            let t = c.price[i] * (100 - c.disc[i]);
            let ghost kx = seq![Val::Int(key as int)];
            let j = find_key(&keys, key);
            if j < keys.len() {
                let ghost old_accs = accs@;
                let mut a = accs[j];
                let ghost gj = gk[j as int];
                acc_add(&mut a, t, Ghost(gsum(g, rows, gj, 0)), Ghost(gabs(g, rows, gj, 0)), Ghost(gcount(g, rows, gj) as int));
                accs.set(j, a);
                proof {
                    assert(gj == kx);
                    assert(gk.contains(kx));
                    assert(gkeys(g, xs.take(i + 1)) == gk);
                    assert forall|u: int| 0 <= u < gk.len() implies acc_ok(#[trigger] accs@[u], gsum(g, xs.take(i + 1), gk[u], 0),
                        gabs(g, xs.take(i + 1), gk[u], 0), gcount(g, xs.take(i + 1), gk[u]) as int) by {
                        lemma_push(g, rows, x, gk[u], 0);
                        if u != j {
                            assert(gk[u] != gk[j as int]);
                            assert(!hit(g, x, gk[u]));
                            assert(accs@[u] == old_accs[u]);
                        }
                    }
                }
            } else {
                let mut a = acc_new();
                acc_add(&mut a, t, Ghost(0), Ghost(0), Ghost(0));
                keys.push(key);
                accs.push(a);
                proof {
                    assert(!gk.contains(kx)) by {
                        if gk.contains(kx) {
                            let u = choose|u: int| 0 <= u < gk.len() && gk[u] == kx;
                            assert(gk[u] == seq![Val::Int(keys@[u] as int)]);
                            assert(gk[u][0] == kx[0]);
                        }
                    }
                    let gk2 = gkeys(g, xs.take(i + 1));
                    assert(gk2 == gk.push(kx));
                    assert(gcount(g, rows, kx) == 0);
                    lemma_zero_count(g, rows, kx, 0);
                    assert forall|u: int| 0 <= u < gk2.len() implies #[trigger] gk2[u] == seq![Val::Int(keys@[u] as int)] by {
                        if u < gk.len() {
                            assert(gk2[u] == gk[u]);
                        }
                    }
                    assert forall|u: int| 0 <= u < gk2.len() implies acc_ok(#[trigger] accs@[u], gsum(g, xs.take(i + 1), gk2[u], 0),
                        gabs(g, xs.take(i + 1), gk2[u], 0), gcount(g, xs.take(i + 1), gk2[u]) as int) by {
                        lemma_push(g, rows, x, gk2[u], 0);
                        if u < gk.len() {
                            assert(gk2[u] == gk[u]);
                            assert(gk[u] != kx) by {
                                assert(gk.contains(gk[u]));
                            }
                            assert(!hit(g, x, gk[u]));
                        }
                    }
                }
            }
        } else {
            proof {
                assert(gkeys(g, xs.take(i + 1)) == gk);
                assert forall|u: int| 0 <= u < gk.len() implies acc_ok(#[trigger] accs@[u], gsum(g, xs.take(i + 1), gk[u], 0),
                    gabs(g, xs.take(i + 1), gk[u], 0), gcount(g, xs.take(i + 1), gk[u]) as int) by {
                    lemma_push(g, rows, x, gk[u], 0);
                }
            }
        }
        i = i + 1;
    }
    (keys, accs)
}

/// The general path's outcome.
pub enum GeneralOut {
    /// The picked supplier rows and the largest SUM.
    Picks { idxs: Vec<usize>, best: i128 },
    /// The group of this key leaves the capacity domain.
    Capacity { key: Ghost<Row> },
}

/// A group whose mass saturated, or none (then every group is inside `group_caps`).
pub fn find_saturated(keys: &Vec<i64>, accs: &Vec<Acc>, Ghost(c): Ghost<Cols>, Ghost(w): Ghost<DayWindow>) -> (r: Option<usize>)
    requires groups_ok(keys@, accs@, c, w, c.n as int),
    ensures
        r matches Some(j) ==> j < keys@.len() && gabs(g_of(w), crows(c), seq![Val::Int(keys@[j as int] as int)], 0) > i128_max(),
        r is None ==> group_caps(g_of(w), crows(c)),
{
    let ghost g = g_of(w);
    let ghost xs = crows(c);
    proof {
        assert(xs.take(c.n as int) =~= xs);
    }
    let mut j: usize = 0;
    while j < accs.len()
        invariant
            groups_ok(keys@, accs@, c, w, c.n as int),
            xs.take(c.n as int) == xs,
            g == g_of(w),
            xs == crows(c),
            j <= accs@.len(),
            forall|u: int| 0 <= u < j ==> (#[trigger] accs@[u]).mass < MASS_CAP,
        decreases accs@.len() - j,
    {
        if accs[j].mass == MASS_CAP {
            proof {
                let gk = gkeys(g, xs);
                assert(acc_ok(accs@[j as int], gsum(g, xs, gk[j as int], 0), gabs(g, xs, gk[j as int], 0), gcount(g, xs, gk[j as int]) as int));
            }
            return Some(j);
        }
        j = j + 1;
    }
    proof {
        let gk = gkeys(g, xs);
        lemma_gkeys(g, xs);
        assert forall|k: Row, a: int| 0 <= a < g.aggs.len() && !(g.aggs[a] is Count) implies #[trigger] gabs(g, xs, k, a) <= i128_max() by {
            assert(a == 0);
            if gk.contains(k) {
                let u = choose|u: int| 0 <= u < gk.len() && gk[u] == k;
                assert(acc_ok(accs@[u], gsum(g, xs, gk[u], 0), gabs(g, xs, gk[u], 0), gcount(g, xs, gk[u]) as int));
            } else {
                lemma_zero_count(g, xs, k, 0);
            }
        }
    }
    None
}

/// The largest group SUM (0 without groups), when every group is inside `group_caps`.
pub fn max_of_groups(keys: &Vec<i64>, accs: &Vec<Acc>, Ghost(c): Ghost<Cols>, Ghost(w): Ghost<DayWindow>) -> (best: i128)
    requires
        groups_ok(keys@, accs@, c, w, c.n as int),
        group_caps(g_of(w), crows(c)),
    ensures best as int == max_sum(g_of(w), crows(c)),
{
    let ghost g = g_of(w);
    let ghost xs = crows(c);
    let ghost gk = gkeys(g, xs);
    let ghost vs = sum_vals(g, xs);
    proof {
        assert(xs.take(c.n as int) =~= xs);
        lemma_gkeys(g, xs);
        // every group's accumulator holds its exact SUM: the mass is inside `i128`
        assert forall|u: int| 0 <= u < gk.len() implies (#[trigger] accs@[u]).sum as int == gsum(g, xs, gk[u], 0) by {
            assert(acc_ok(accs@[u], gsum(g, xs, gk[u], 0), gabs(g, xs, gk[u], 0), gcount(g, xs, gk[u]) as int));
            assert(gabs(g, xs, gk[u], 0) <= i128_max());
        }
    }
    if accs.len() == 0 {
        proof {
            assert(vs =~= Seq::<Val>::empty());
        }
        return 0;
    }
    let mut best: i128 = accs[0].sum;
    let mut j: usize = 1;
    proof {
        assert(vs[0]->Num_coeff == accs@[0].sum);
    }
    while j < accs.len()
        invariant
            groups_ok(keys@, accs@, c, w, c.n as int),
            gk == gkeys(g_of(w), crows(c)),
            vs == sum_vals(g_of(w), crows(c)),
            g == g_of(w),
            xs == crows(c),
            1 <= j <= accs@.len(),
            accs@.len() == gk.len(),
            forall|u: int| 0 <= u < gk.len() ==> (#[trigger] accs@[u]).sum as int == gsum(g, xs, gk[u], 0),
            forall|u: int| 0 <= u < j ==> (#[trigger] vs[u])->Num_coeff <= best,
            exists|u: int| 0 <= u < j && (#[trigger] vs[u])->Num_coeff == best,
        decreases accs@.len() - j,
    {
        if accs[j].sum > best {
            best = accs[j].sum;
        }
        proof {
            assert(vs[j as int]->Num_coeff == accs@[j as int].sum);
        }
        j = j + 1;
    }
    proof {
        assert(is_max_of(vs, best as int));
        assert forall|u: int| 0 <= u < vs.len() implies (#[trigger] vs[u]) is Num && vs[u]->Num_scale == 4 by {}
        lemma_max_value_num(vs, 4);
        lemma_max_unique(vs, best as int, coeff_max(vs));
    }
    best
}

/// The supplier rows whose key is a group key with the SUM `best`, in row order.
pub fn general_picks(k: &SuppKeys, keys: &Vec<i64>, accs: &Vec<Acc>, best: i128, Ghost(c): Ghost<Cols>,
    Ghost(w): Ghost<DayWindow>, Ghost(srows): Ghost<Seq<Row>>) -> (idxs: Vec<usize>)
    requires
        groups_ok(keys@, accs@, c, w, c.n as int),
        group_caps(g_of(w), crows(c)),
        keys_match(*k, srows),
    ensures idxs_ok(idxs@, range_filter(0, k.ns as int, pick_of(g_of(w), crows(c), srows, best as int)), k.ns),
{
    let ghost g = g_of(w);
    let ghost xs = crows(c);
    let ghost gk = gkeys(g, xs);
    let ghost p = pick_of(g, xs, srows, best as int);
    proof {
        assert(xs.take(c.n as int) =~= xs);
        lemma_gkeys(g, xs);
        assert forall|u: int| 0 <= u < gk.len() implies (#[trigger] accs@[u]).sum as int == gsum(g, xs, gk[u], 0) by {
            assert(acc_ok(accs@[u], gsum(g, xs, gk[u], 0), gabs(g, xs, gk[u], 0), gcount(g, xs, gk[u]) as int));
            assert(gabs(g, xs, gk[u], 0) <= i128_max());
        }
    }
    let mut idxs: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < k.ns
        invariant
            groups_ok(keys@, accs@, c, w, c.n as int),
            keys_match(*k, srows),
            g == g_of(w),
            xs == crows(c),
            gk == gkeys(g, xs),
            p == pick_of(g, xs, srows, best as int),
            keys@.len() == gk.len(),
            forall|u: int| 0 <= u < gk.len() ==> #[trigger] gk[u] == seq![Val::Int(keys@[u] as int)],
            forall|u: int| 0 <= u < gk.len() ==> (#[trigger] accs@[u]).sum as int == gsum(g, xs, gk[u], 0),
            i <= k.ns,
            idxs_ok(idxs@, range_filter(0, i as int, p), k.ns),
        decreases k.ns - i,
    {
        let key = k.keys[i];
        let ghost kx = seq![Val::Int(key as int)];
        let mut found = false;
        let mut j: usize = 0;
        while j < keys.len()
            invariant
                keys@.len() == gk.len(),
                accs@.len() == gk.len(),
                forall|u: int| 0 <= u < gk.len() ==> #[trigger] gk[u] == seq![Val::Int(keys@[u] as int)],
                forall|u: int| 0 <= u < gk.len() ==> (#[trigger] accs@[u]).sum as int == gsum(g, xs, gk[u], 0),
                j <= keys@.len(),
                found == exists|u: int| 0 <= u < j && #[trigger] keys@[u] == key && accs@[u].sum == best,
            decreases keys@.len() - j,
        {
            if keys[j] == key && accs[j].sum == best {
                found = true;
            }
            j = j + 1;
        }
        proof {
            lemma_range_filter_step(0, i as int, p);
            assert(srows[i as int][0] == Val::Int(key as int));
            assert(seq![srows[i as int][0]] == kx);
            if found {
                let u = choose|u: int| 0 <= u < gk.len() && #[trigger] keys@[u] == key && accs@[u].sum == best;
                assert(gk[u] == kx);
                assert(gk.contains(kx));
            }
            if p(i as int) {
                let u = choose|u: int| 0 <= u < gk.len() && gk[u] == kx;
                assert(gk[u] == seq![Val::Int(keys@[u] as int)]);
                assert(gk[u][0] == kx[0]);
                assert(keys@[u] == key);
            }
            assert(found == p(i as int));
        }
        if found {
            let ghost old_idxs = idxs@;
            idxs.push(i);
            proof {
                let sel = range_filter(0, i as int, p);
                assert forall|u: int| 0 <= u < sel.len() + 1 implies (#[trigger] idxs@[u]) as int == sel.push(i as int)[u]
                    && sel.push(i as int)[u] < k.ns by {
                    if u < sel.len() {
                        assert(idxs@[u] == old_idxs[u]);
                    }
                }
            }
        }
        i = i + 1;
    }
    idxs
}

/// The general path: `Capacity` with a group outside the capacity domain, or the picked supplier rows and the largest
/// SUM inside `group_caps`.
pub fn general_path(c: &Cols, k: &SuppKeys, w: DayWindow, Ghost(srows): Ghost<Seq<Row>>) -> (r: GeneralOut)
    requires cols_wf(*c), keys_match(*k, srows),
    ensures
        r matches GeneralOut::Capacity { key } ==> gabs(g_of(w), crows(*c), key@, 0) > i128_max(),
        r matches GeneralOut::Picks { idxs, best } ==> {
            &&& group_caps(g_of(w), crows(*c))
            &&& best as int == max_sum(g_of(w), crows(*c))
            &&& idxs_ok(idxs@, range_filter(0, k.ns as int, pick_of(g_of(w), crows(*c), srows, best as int)), k.ns)
        },
{
    let (keys, accs) = build_groups(c, w);
    match find_saturated(&keys, &accs, Ghost(*c), Ghost(w)) {
        Some(j) => {
            let ghost key = seq![Val::Int(keys@[j as int] as int)];
            return GeneralOut::Capacity { key: Ghost(key) };
        },
        None => {},
    }
    let best = max_of_groups(&keys, &accs, Ghost(*c), Ghost(w));
    let idxs = general_picks(k, &keys, &accs, best, Ghost(*c), Ghost(w), Ghost(srows));
    GeneralOut::Picks { idxs, best }
}

} // verus!
