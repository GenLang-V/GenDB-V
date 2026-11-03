//! The general path for any data (used when the parallel path cannot run: a range with more than `GCAP` groups,
//! more than 64 groups in all, or an adsh value the dictionary does not find): one pass over the rows with a
//! growable group table and, per group, the rows holding its distinct adsh values found so far (`seen`, searched
//! linearly). Slow on large inputs but exact.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::agent::cols::*;
use crate::agent::spec::*;
use crate::agent::kernel::gkey;
use crate::agent::merge::{Groups, find_global, lemma_bounds_m};
use crate::agent::common::bytes::*;

verus! {

/// The groups of the whole table with their counts, sums and distinct adsh counts.
pub open spec fn final_ok(t: Seq<Row>, nrows: int, n: int, gs: Groups) -> bool {
    let rep = gs.rep@;
    &&& gs.cnt@.len() == rep.len() && gs.sum@.len() == rep.len() && gs.dcnt@.len() == rep.len()
    &&& forall|g: int| 0 <= g < rep.len() ==> #[trigger] rep[g] < nrows && qual(t[rep[g] as int])
    &&& forall|g1: int, g2: int| 0 <= g1 < rep.len() && 0 <= g2 < rep.len() && g1 != g2
        ==> #[trigger] gkey(t, rep, g1) != #[trigger] gkey(t, rep, g2)
    &&& forall|j: int| 0 <= j < n && qual(#[trigger] t[j]) ==> exists|g: int| 0 <= g < rep.len() && key_of(t[j]) == gkey(t, rep, g)
    &&& forall|g: int| 0 <= g < rep.len() ==> #[trigger] gs.cnt@[g] == cnt_r(t, gkey(t, rep, g), 0, n)
    &&& forall|g: int| 0 <= g < rep.len() ==> #[trigger] gs.sum@[g] == sum_r(t, gkey(t, rep, g), 0, n)
    &&& forall|g: int| 0 <= g < rep.len() ==> #[trigger] gs.dcnt@[g] == aset_r(t, gkey(t, rep, g), 0, n).len()
}

/// The serial state after rows `[0, i)`: groups as in `final_ok` over `[0, i)`; `seen` lists (group, row) pairs
/// whose rows hold, per group, one row of each distinct adsh value of the group.
pub open spec fn ser_inv(c: Cols, t: Seq<Row>, i: int, gs: Groups, sg: Seq<usize>, sr: Seq<usize>) -> bool {
    &&& cols_wf(c) && corr(c, t) && 0 <= i <= c.n
    &&& final_ok(t, c.n as int, i, gs)
    &&& sg.len() == sr.len()
    &&& forall|e: int| 0 <= e < sg.len() ==> #[trigger] sg[e] < gs.rep@.len() && sr[e] < i
        && hit(t[sr[e] as int], gkey(t, gs.rep@, sg[e] as int))
    &&& forall|g: int, v: Val| 0 <= g < gs.rep@.len() && #[trigger] aset_r(t, gkey(t, gs.rep@, g), 0, i).contains(v)
        ==> exists|e: int| 0 <= e < sg.len() && sg[e] == g && #[trigger] t[sr[e] as int][0] == v
}

/// Whether some seen row of group `g` has row `i`'s adsh.
fn seen_has(c: &Cols, Ghost(t): Ghost<Seq<Row>>, sg: &Vec<usize>, sr: &Vec<usize>, g: usize, i: usize) -> (r: bool)
    requires
        cols_wf(*c), corr(*c, t), i < c.n, sg@.len() == sr@.len(),
        forall|e: int| 0 <= e < sr@.len() ==> #[trigger] sr@[e] < c.n,
    ensures
        r == exists|e: int| 0 <= e < sg@.len() && sg@[e] == g && #[trigger] t[sr@[e] as int][0] == t[i as int][0],
{
    proof {
        assert(row_corr(*c, t[i as int], i as int));
        assert(0 <= c.adsh_off@[i as int] <= c.adsh_off@[i + 1] <= c.adsh@.len());
    }
    let a0 = c.adsh_off[i] as usize;
    let a1 = c.adsh_off[i + 1] as usize;
    let mut e: usize = 0;
    while e < sg.len()
        invariant
            cols_wf(*c), corr(*c, t), i < c.n, sg@.len() == sr@.len(), e <= sg@.len(),
            forall|e2: int| 0 <= e2 < sr@.len() ==> #[trigger] sr@[e2] < c.n,
            a0 as int == c.adsh_off@[i as int], a1 as int == c.adsh_off@[i + 1], a0 <= a1 <= c.adsh_len,
            t[i as int][0] == Val::Text(c.atext(i as int)),
            forall|e2: int| 0 <= e2 < e && sg@[e2] == g ==> #[trigger] t[sr@[e2] as int][0] != t[i as int][0],
        decreases sg@.len() - e,
    {
        if sg[e] == g {
            let j = sr[e];
            proof {
                assert(row_corr(*c, t[j as int], j as int));
                assert(0 <= c.adsh_off@[j as int] <= c.adsh_off@[j + 1] <= c.adsh@.len());
            }
            let b0 = c.adsh_off[j] as usize;
            let b1 = c.adsh_off[j + 1] as usize;
            if eq_ranges(c.adsh, c.adsh_len, a0, a1, c.adsh, c.adsh_len, b0, b1) {
                return true;
            }
            proof {
                assert(t[j as int][0] == Val::Text(c.atext(j as int)));
                assert(c.atext(j as int) != c.atext(i as int));
            }
        }
        e = e + 1;
    }
    false
}

proof fn lemma_ser_skip(c: Cols, t: Seq<Row>, i: int, gs: Groups, sg: Seq<usize>, sr: Seq<usize>)
    requires ser_inv(c, t, i, gs, sg, sr), i < c.n, !qual(t[i]),
    ensures ser_inv(c, t, i + 1, gs, sg, sr),
{
    let rep = gs.rep@;
    assert forall|k: Row| #![auto] cnt_r(t, k, 0, i + 1) == cnt_r(t, k, 0, i) && sum_r(t, k, 0, i + 1) == sum_r(t, k, 0, i)
        && aset_r(t, k, 0, i + 1) == aset_r(t, k, 0, i) by {
        assert(!hit(t[i], k));
    }
    assert forall|g: int| 0 <= g < rep.len() implies #[trigger] gs.cnt@[g] == cnt_r(t, gkey(t, rep, g), 0, i + 1) by {
        assert(cnt_r(t, gkey(t, rep, g), 0, i + 1) == cnt_r(t, gkey(t, rep, g), 0, i));
    }
    assert forall|g: int| 0 <= g < rep.len() implies #[trigger] gs.sum@[g] == sum_r(t, gkey(t, rep, g), 0, i + 1) by {
        assert(sum_r(t, gkey(t, rep, g), 0, i + 1) == sum_r(t, gkey(t, rep, g), 0, i));
    }
    assert forall|g: int| 0 <= g < rep.len() implies #[trigger] gs.dcnt@[g] == aset_r(t, gkey(t, rep, g), 0, i + 1).len() by {
        assert(aset_r(t, gkey(t, rep, g), 0, i + 1) == aset_r(t, gkey(t, rep, g), 0, i));
    }
    assert forall|j: int| 0 <= j < i + 1 && qual(#[trigger] t[j]) implies exists|g: int| 0 <= g < rep.len() && key_of(t[j]) == gkey(t, rep, g) by {
        assert(j < i);
    }
    assert forall|g: int, v: Val| 0 <= g < rep.len() && #[trigger] aset_r(t, gkey(t, rep, g), 0, i + 1).contains(v)
        implies exists|e: int| 0 <= e < sg.len() && sg[e] == g && #[trigger] t[sr[e] as int][0] == v by {
        assert(aset_r(t, gkey(t, rep, g), 0, i + 1) == aset_r(t, gkey(t, rep, g), 0, i));
    }
}

/// Adding a group for row `i` (whose key no group has) keeps the state at `i`.
proof fn lemma_ser_new(c: Cols, t: Seq<Row>, i: int, gs: Groups, sg: Seq<usize>, sr: Seq<usize>, gs2: Groups)
    requires
        ser_inv(c, t, i, gs, sg, sr), i < c.n, qual(t[i]),
        forall|g: int| 0 <= g < gs.rep@.len() ==> #[trigger] gkey(t, gs.rep@, g) != key_of(t[i]),
        gs2.rep@ == gs.rep@.push(i as usize), gs2.cnt@ == gs.cnt@.push(0), gs2.sum@ == gs.sum@.push(0),
        gs2.dcnt@ == gs.dcnt@.push(0),
    ensures
        ser_inv(c, t, i, gs2, sg, sr),
        gkey(t, gs2.rep@, gs.rep@.len() as int) == key_of(t[i]),
{
    let rep = gs.rep@;
    let rep2 = gs2.rep@;
    let ng = rep.len() as int;
    let key = key_of(t[i]);
    assert forall|g: int| 0 <= g < ng implies #[trigger] gkey(t, rep2, g) == gkey(t, rep, g) by {
        assert(rep2[g] == rep[g]);
    }
    assert(gkey(t, rep2, ng) == key);
    assert forall|j: int| 0 <= j < i implies !#[trigger] hit(t[j], key) by {
        if hit(t[j], key) {
            let g2 = choose|g2: int| 0 <= g2 < ng && key_of(t[j]) == gkey(t, rep, g2);
            assert(gkey(t, rep, g2) != key);
        }
    }
    lemma_no_hit(t, key, 0, i);
    assert forall|g1: int, g2: int| 0 <= g1 < ng + 1 && 0 <= g2 < ng + 1 && g1 != g2
        implies #[trigger] gkey(t, rep2, g1) != #[trigger] gkey(t, rep2, g2) by {
        if g1 < ng && g2 < ng {
            assert(gkey(t, rep, g1) != gkey(t, rep, g2));
        }
    }
    assert forall|j: int| 0 <= j < i && qual(#[trigger] t[j]) implies exists|g3: int| 0 <= g3 < ng + 1 && key_of(t[j]) == gkey(t, rep2, g3) by {
        let g3 = choose|g3: int| 0 <= g3 < ng && key_of(t[j]) == gkey(t, rep, g3);
        assert(gkey(t, rep2, g3) == gkey(t, rep, g3));
    }
    assert forall|g: int| 0 <= g < ng + 1 implies #[trigger] gs2.cnt@[g] == cnt_r(t, gkey(t, rep2, g), 0, i) by {
        if g < ng {
            assert(gs.cnt@[g] == cnt_r(t, gkey(t, rep, g), 0, i));
        }
    }
    assert forall|g: int| 0 <= g < ng + 1 implies #[trigger] gs2.sum@[g] == sum_r(t, gkey(t, rep2, g), 0, i) by {
        if g < ng {
            assert(gs.sum@[g] == sum_r(t, gkey(t, rep, g), 0, i));
        }
    }
    assert forall|g: int| 0 <= g < ng + 1 implies #[trigger] gs2.dcnt@[g] == aset_r(t, gkey(t, rep2, g), 0, i).len() by {
        if g < ng {
            assert(gs.dcnt@[g] == aset_r(t, gkey(t, rep, g), 0, i).len());
        }
    }
    assert forall|e: int| 0 <= e < sg.len() implies #[trigger] sg[e] < rep2.len() && sr[e] < i
        && hit(t[sr[e] as int], gkey(t, rep2, sg[e] as int)) by {
        assert(gkey(t, rep2, sg[e] as int) == gkey(t, rep, sg[e] as int));
    }
    assert forall|g: int, v: Val| 0 <= g < ng + 1 && #[trigger] aset_r(t, gkey(t, rep2, g), 0, i).contains(v)
        implies exists|e: int| 0 <= e < sg.len() && sg[e] == g && #[trigger] t[sr[e] as int][0] == v by {
        if g == ng {
            assert(aset_r(t, key, 0, i) == Set::<Val>::empty());
        } else {
            assert(gkey(t, rep2, g) == gkey(t, rep, g));
        }
    }
}

/// Counting row `i` into group `g` (with `found`: whether a seen row of `g` has its adsh).
proof fn lemma_ser_count(c: Cols, t: Seq<Row>, i: int, gs: Groups, sg: Seq<usize>, sr: Seq<usize>, g: int, found: bool,
    gs2: Groups, sg2: Seq<usize>, sr2: Seq<usize>)
    requires
        ser_inv(c, t, i, gs, sg, sr), i < c.n, qual(t[i]), 0 <= g < gs.rep@.len(), gkey(t, gs.rep@, g) == key_of(t[i]),
        g <= usize::MAX,
        found == exists|e: int| 0 <= e < sg.len() && sg[e] == g && #[trigger] t[sr[e] as int][0] == t[i][0],
        gs2.rep@ == gs.rep@,
        gs2.cnt@ == gs.cnt@.update(g, (gs.cnt@[g] + 1) as u64),
        gs2.sum@ == gs.sum@.update(g, (gs.sum@[g] + line_of(t[i])) as i128),
        gs2.dcnt@ == (if found { gs.dcnt@ } else { gs.dcnt@.update(g, (gs.dcnt@[g] + 1) as u64) }),
        sg2 == (if found { sg } else { sg.push(g as usize) }),
        sr2 == (if found { sr } else { sr.push(i as usize) }),
        gs.cnt@[g] + 1 <= u64::MAX, gs.dcnt@[g] + 1 <= u64::MAX,
        i128::MIN <= gs.sum@[g] + line_of(t[i]) <= i128::MAX,
    ensures
        ser_inv(c, t, i + 1, gs2, sg2, sr2),
{
    let rep = gs.rep@;
    let ng = rep.len() as int;
    let key = key_of(t[i]);
    let v = t[i][0];
    lemma_hit_step_s(t, key, i);
    assert forall|g2: int| 0 <= g2 < ng && g2 != g implies !hit(t[i], #[trigger] gkey(t, rep, g2)) by {
        assert(gkey(t, rep, g2) != gkey(t, rep, g));
    }
    assert forall|g2: int| 0 <= g2 < ng && g2 != g implies
        #[trigger] cnt_r(t, gkey(t, rep, g2), 0, i + 1) == cnt_r(t, gkey(t, rep, g2), 0, i)
        && sum_r(t, gkey(t, rep, g2), 0, i + 1) == sum_r(t, gkey(t, rep, g2), 0, i)
        && aset_r(t, gkey(t, rep, g2), 0, i + 1) == aset_r(t, gkey(t, rep, g2), 0, i) by {
        assert(!hit(t[i], gkey(t, rep, g2)));
    }
    // Was the value already in the group?
    if found {
        let e = choose|e: int| 0 <= e < sg.len() && sg[e] == g && #[trigger] t[sr[e] as int][0] == t[i][0];
        lemma_aset_member(t, key, 0, i, sr[e] as int);
        assert(aset_r(t, key, 0, i).contains(v));
        assert(aset_r(t, key, 0, i).insert(v) =~= aset_r(t, key, 0, i));
    } else {
        assert(!aset_r(t, key, 0, i).contains(v));
    }
    assert forall|g2: int| 0 <= g2 < ng implies #[trigger] gs2.cnt@[g2] == cnt_r(t, gkey(t, rep, g2), 0, i + 1) by {}
    assert forall|g2: int| 0 <= g2 < ng implies #[trigger] gs2.sum@[g2] == sum_r(t, gkey(t, rep, g2), 0, i + 1) by {}
    assert forall|g2: int| 0 <= g2 < ng implies #[trigger] gs2.dcnt@[g2] == aset_r(t, gkey(t, rep, g2), 0, i + 1).len() by {}
    assert forall|j: int| 0 <= j < i + 1 && qual(#[trigger] t[j]) implies exists|g3: int| 0 <= g3 < ng && key_of(t[j]) == gkey(t, rep, g3) by {
        if j == i {
            assert(key_of(t[j]) == gkey(t, rep, g));
        }
    }
    assert forall|e: int| 0 <= e < sg2.len() implies #[trigger] sg2[e] < rep.len() && sr2[e] < i + 1
        && hit(t[sr2[e] as int], gkey(t, rep, sg2[e] as int)) by {
        if found {
            assert(sg2[e] == sg[e] && sr2[e] == sr[e]);
        } else if e < sg.len() {
            assert(sg2[e] == sg[e] && sr2[e] == sr[e]);
        } else {
            assert(sg2[e] == g as usize && sr2[e] == i as usize);
            assert(hit(t[i], gkey(t, rep, g)));
        }
    }
    assert forall|g2: int, w: Val| 0 <= g2 < ng && #[trigger] aset_r(t, gkey(t, rep, g2), 0, i + 1).contains(w)
        implies exists|e: int| 0 <= e < sg2.len() && sg2[e] == g2 && #[trigger] t[sr2[e] as int][0] == w by {
        if g2 == g && w == v && !found {
            assert(sg2[sg.len() as int] == g2 && sr2[sg.len() as int] == i);
        } else {
            assert(aset_r(t, gkey(t, rep, g2), 0, i).contains(w));
            let e = choose|e: int| 0 <= e < sg.len() && sg[e] == g2 && #[trigger] t[sr[e] as int][0] == w;
            assert(sg2[e] == sg[e] && sr2[e] == sr[e]);
        }
    }
}

proof fn lemma_hit_step_s(t: Seq<Row>, k: Row, i: int)
    requires 0 <= i, hit(t[i], k),
    ensures
        cnt_r(t, k, 0, i + 1) == cnt_r(t, k, 0, i) + 1,
        sum_r(t, k, 0, i + 1) == sum_r(t, k, 0, i) + line_of(t[i]),
        aset_r(t, k, 0, i + 1) == aset_r(t, k, 0, i).insert(t[i][0]),
{
}

/// The groups of the whole table, by the serial general path.
pub fn serial_groups(c: &Cols, Ghost(t): Ghost<Seq<Row>>) -> (gs: Groups)
    requires cols_wf(*c), corr(*c, t),
    ensures final_ok(t, c.n as int, c.n as int, gs),
{
    let mut gs = Groups { rep: Vec::new(), cnt: Vec::new(), sum: Vec::new(), dcnt: Vec::new() };
    let mut sg: Vec<usize> = Vec::new();
    let mut sr: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < c.n
        invariant ser_inv(*c, t, i as int, gs, sg@, sr@),
        decreases c.n - i,
    {
        proof { assert(row_corr(*c, t[i as int], i as int)); }
        if c.stmt_valid[i] != 0 {
            let g = match find_global(c, Ghost(t), Ghost(c.n as int), &gs.rep, i) {
                Some(g) => g,
                None => {
                    let ghost gs0 = gs;
                    gs.rep.push(i);
                    gs.cnt.push(0);
                    gs.sum.push(0);
                    gs.dcnt.push(0);
                    proof { lemma_ser_new(*c, t, i as int, gs0, sg@, sr@, gs); }
                    gs.rep.len() - 1
                },
            };
            proof {
                assert forall|e: int| 0 <= e < sr@.len() implies #[trigger] sr@[e] < c.n by {
                    assert(sg@[e] < gs.rep@.len());
                }
            }
            let found = seen_has(c, Ghost(t), &sg, &sr, g, i);
            let ghost gs0 = gs;
            let ghost sg0 = sg@;
            let ghost sr0 = sr@;
            proof {
                let key = gkey(t, gs.rep@, g as int);
                lemma_bounds_m(*c, t, 0, i + 1, key);
                lemma_hit_step_s(t, key, i as int);
                lemma_aset_finite(t, key, 0, i as int + 1);
                assert(gs.cnt@[g as int] == cnt_r(t, key, 0, i as int));
                assert(gs.dcnt@[g as int] == aset_r(t, key, 0, i as int).len());
                lemma_aset_finite(t, key, 0, i as int);
                assert(line_of(t[i as int]) == c.line@[i as int]);
            }
            let nc = gs.cnt[g] + 1;
            gs.cnt.set(g, nc);
            let ns = gs.sum[g] + c.line[i] as i128;
            gs.sum.set(g, ns);
            if !found {
                let nd = gs.dcnt[g] + 1;
                gs.dcnt.set(g, nd);
                sg.push(g);
                sr.push(i);
            }
            proof { lemma_ser_count(*c, t, i as int, gs0, sg0, sr0, g as int, found, gs, sg@, sr@); }
        } else {
            proof { lemma_ser_skip(*c, t, i as int, gs, sg@, sr@); }
        }
        i = i + 1;
    }
    gs
}

} // verus!
