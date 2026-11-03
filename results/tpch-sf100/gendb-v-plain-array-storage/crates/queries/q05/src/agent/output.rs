//! From the group totals to the statement's outcome: `Capacity` when a non-empty group's SUM mass leaves `i128`
//! (`over_group`); otherwise one row `[n_name, revenue]` per non-empty group, ordered by revenue descending
//! (`order_groups`, insertion by revenue), which is an allowed output of the statement (`lemma_answer_rows`: its
//! keys are exactly the normal form's non-empty groups, its values the group sums, and `group_caps` holds).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::order::*;
use crate::exec::value::{EVal, view_row};
use crate::spec::ast::OrderKey;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::work::text_bytes;
use crate::link::query::*;
use crate::link::expr::{lemma_compare_num, lemma_align_same, i128_max};
use crate::agent::model::*;
use crate::agent::sem_ast::*;
use crate::agent::sem_from::*;
use crate::agent::sem_body::*;
use crate::agent::plan::*;
use crate::agent::contrib::*;
use crate::agent::cols::*;
use crate::agent::common::exact_sum::*;

verus! {

/// The output row of group `g` with revenue coefficient `s` (scale 4).
pub open spec fn grow(sv: StoresView, reps: Seq<usize>, g: int, s: int) -> Row {
    seq![Val::Text(n_name(sv, reps[g] as int)), Val::Num { coeff: s, scale: 4 }]
}

/// `ord` lists exactly the non-empty groups, each once, by revenue descending.
pub open spec fn ord_ok(ord: Seq<usize>, totals: Seq<Acc>) -> bool {
    &&& forall|p: int| 0 <= p < ord.len() ==> #[trigger] ord[p] < totals.len() && totals[ord[p] as int].cnt > 0
    &&& forall|p: int, q: int| 0 <= p < q < ord.len() ==> #[trigger] ord[p] != #[trigger] ord[q]
    &&& forall|g: int| 0 <= g < totals.len() && #[trigger] totals[g].cnt > 0 ==> ord.contains(g as usize)
    &&& forall|p: int, q: int| 0 <= p < q < ord.len() ==> totals[#[trigger] ord[p] as int].sum >= totals[#[trigger] ord[q] as int].sum
}

/// `ord_ok` over the groups below `g`.
pub open spec fn ord_prefix(ord: Seq<usize>, totals: Seq<Acc>, g: int) -> bool {
    &&& forall|p: int| 0 <= p < ord.len() ==> #[trigger] ord[p] < g && totals[ord[p] as int].cnt > 0
    &&& forall|p: int, q: int| 0 <= p < q < ord.len() ==> #[trigger] ord[p] != #[trigger] ord[q]
    &&& forall|h: int| 0 <= h < g && #[trigger] totals[h].cnt > 0 ==> ord.contains(h as usize)
    &&& forall|p: int, q: int| 0 <= p < q < ord.len() ==> totals[#[trigger] ord[p] as int].sum >= totals[#[trigger] ord[q] as int].sum
}

/// Positions of a sequence after inserting `g` at `p`.
proof fn lemma_insert_at(o0: Seq<usize>, g: usize, p: int, i: int)
    requires 0 <= p <= o0.len(), 0 <= i <= o0.len(),
    ensures o0.insert(p, g)[i] == if i < p { o0[i] } else if i == p { g } else { o0[i - 1] },
{
}

proof fn lemma_insert_members(o0: Seq<usize>, totals: Seq<Acc>, g: usize, p: int)
    requires
        forall|i: int| 0 <= i < o0.len() ==> #[trigger] o0[i] < g && totals[o0[i] as int].cnt > 0,
        forall|h: int| 0 <= h < g && #[trigger] totals[h].cnt > 0 ==> o0.contains(h as usize),
        g < totals.len(), totals[g as int].cnt > 0, 0 <= p <= o0.len(),
    ensures
        forall|i: int| 0 <= i < o0.insert(p, g).len() ==> #[trigger] o0.insert(p, g)[i] < g + 1 && totals[o0.insert(p, g)[i] as int].cnt > 0,
        forall|h: int| 0 <= h < g + 1 && #[trigger] totals[h].cnt > 0 ==> o0.insert(p, g).contains(h as usize),
{
    let o = o0.insert(p, g);
    assert forall|i: int| 0 <= i < o.len() implies #[trigger] o[i] < g + 1 && totals[o[i] as int].cnt > 0 by {
        lemma_insert_at(o0, g, p, i);
    }
    assert forall|h: int| 0 <= h < g + 1 && #[trigger] totals[h].cnt > 0 implies o.contains(h as usize) by {
        if h < g {
            let i = choose|i: int| 0 <= i < o0.len() && o0[i] == h as usize;
            if i < p { lemma_insert_at(o0, g, p, i); } else { lemma_insert_at(o0, g, p, i + 1); }
        } else {
            lemma_insert_at(o0, g, p, p);
        }
    }
}

proof fn lemma_insert_distinct(o0: Seq<usize>, g: usize, p: int)
    requires
        forall|i: int| 0 <= i < o0.len() ==> #[trigger] o0[i] < g,
        forall|i: int, j: int| 0 <= i < j < o0.len() ==> #[trigger] o0[i] != #[trigger] o0[j],
        0 <= p <= o0.len(),
    ensures forall|i: int, j: int| 0 <= i < j < o0.insert(p, g).len() ==> #[trigger] o0.insert(p, g)[i] != #[trigger] o0.insert(p, g)[j],
{
    let o = o0.insert(p, g);
    assert forall|i: int, j: int| 0 <= i < j < o.len() implies #[trigger] o[i] != #[trigger] o[j] by {
        lemma_insert_at(o0, g, p, i);
        lemma_insert_at(o0, g, p, j);
    }
}

proof fn lemma_insert_sorted(o0: Seq<usize>, totals: Seq<Acc>, g: usize, p: int)
    requires
        forall|i: int| 0 <= i < o0.len() ==> #[trigger] o0[i] < totals.len(),
        forall|i: int, j: int| 0 <= i < j < o0.len() ==> totals[#[trigger] o0[i] as int].sum >= totals[#[trigger] o0[j] as int].sum,
        g < totals.len(), 0 <= p <= o0.len(),
        forall|i: int| 0 <= i < p ==> totals[#[trigger] o0[i] as int].sum >= totals[g as int].sum,
        p < o0.len() ==> !(totals[o0[p] as int].sum >= totals[g as int].sum),
    ensures
        forall|i: int, j: int| 0 <= i < j < o0.insert(p, g).len() ==>
            totals[#[trigger] o0.insert(p, g)[i] as int].sum >= totals[#[trigger] o0.insert(p, g)[j] as int].sum,
{
    let o = o0.insert(p, g);
    assert forall|i: int, j: int| 0 <= i < j < o.len() implies totals[#[trigger] o[i] as int].sum >= totals[#[trigger] o[j] as int].sum by {
        lemma_insert_at(o0, g, p, i);
        lemma_insert_at(o0, g, p, j);
        if i == p && j > p {
            if j - 1 > p {
                assert(totals[o0[p] as int].sum >= totals[o0[j - 1] as int].sum);
            }
        }
        if i < p && j > p {
            assert(totals[o0[i] as int].sum >= totals[g as int].sum);
            if j - 1 > p {
                assert(totals[o0[p] as int].sum >= totals[o0[j - 1] as int].sum);
            }
        }
    }
}

/// Inserting non-empty group `g` at position `p` (after every group with revenue not below `g`'s, before the
/// first one below) keeps the list ordered.
proof fn lemma_insert(o0: Seq<usize>, totals: Seq<Acc>, g: usize, p: int)
    requires
        ord_prefix(o0, totals, g as int), g < totals.len(), totals[g as int].cnt > 0, 0 <= p <= o0.len(),
        forall|i: int| 0 <= i < p ==> totals[#[trigger] o0[i] as int].sum >= totals[g as int].sum,
        p < o0.len() ==> !(totals[o0[p] as int].sum >= totals[g as int].sum),
    ensures ord_prefix(o0.insert(p, g), totals, g as int + 1),
{
    lemma_insert_members(o0, totals, g, p);
    lemma_insert_distinct(o0, g, p);
    lemma_insert_sorted(o0, totals, g, p);
}

/// The non-empty groups by revenue descending (insertion into the ordered list).
pub fn order_groups(totals: &Vec<Acc>) -> (ord: Vec<usize>)
    ensures ord_ok(ord@, totals@),
{
    let ng = totals.len();
    let mut ord: Vec<usize> = Vec::new();
    let mut g: usize = 0;
    while g < ng
        invariant ng == totals@.len(), g <= ng, ord_prefix(ord@, totals@, g as int),
        decreases ng - g,
    {
        if totals[g].cnt > 0 {
            let s = totals[g].sum;
            let n = ord.len();
            let mut p: usize = 0;
            while p < n && totals[ord[p]].sum >= s
                invariant
                    ng == totals@.len(), n == ord@.len(), p <= n, g < ng, ord_prefix(ord@, totals@, g as int),
                    s == totals@[g as int].sum,
                    forall|i: int| 0 <= i < p ==> totals@[#[trigger] ord@[i] as int].sum >= s,
                decreases n - p,
            {
                p = p + 1;
            }
            proof { lemma_insert(ord@, totals@, g, p as int); }
            ord.insert(p, g);
        } else {
            proof {
                assert forall|h: int| 0 <= h < g + 1 && #[trigger] totals@[h].cnt > 0 implies ord@.contains(h as usize) by {}
            }
        }
        g = g + 1;
    }
    ord
}

/// Some non-empty group whose SUM mass leaves `i128`, if any.
pub fn over_group(totals: &Vec<Acc>) -> (r: Option<usize>)
    ensures
        r matches Some(g) ==> g < totals@.len() && totals@[g as int].cnt > 0 && totals@[g as int].over,
        r is None ==> forall|g: int| 0 <= g < totals@.len() ==> !(#[trigger] totals@[g].cnt > 0 && totals@[g].over),
{
    let mut g: usize = 0;
    while g < totals.len()
        invariant g <= totals@.len(), forall|h: int| 0 <= h < g ==> !(#[trigger] totals@[h].cnt > 0 && totals@[h].over),
        decreases totals@.len() - g,
    {
        if totals[g].cnt > 0 && totals[g].over {
            return Some(g);
        }
        g = g + 1;
    }
    None
}

/// The answer rows of the ordered groups.
pub fn build_rows(c: &Cols, reps: &Vec<usize>, totals: &Vec<Acc>, ord: &Vec<usize>, Ghost(sv): Ghost<StoresView>) -> (out: Vec<Vec<EVal>>)
    requires
        cols_ok(*c, sv), stores_wf(sv),
        forall|g: int| 0 <= g < reps@.len() ==> #[trigger] reps@[g] < nn(sv),
        forall|p: int| 0 <= p < ord@.len() ==> #[trigger] ord@[p] < reps@.len() && ord@[p] < totals@.len(),
    ensures
        view_rows(out@) == ord@.map_values(|g: usize| grow(sv, reps@, g as int, totals@[g as int].sum as int)),
{
    assert(crate::link::query::text_wf(c.nname@, c.nn as int));
    let mut out: Vec<Vec<EVal>> = Vec::new();
    let mut p: usize = 0;
    while p < ord.len()
        invariant
            cols_ok(*c, sv), stores_wf(sv), crate::link::query::text_wf(c.nname@, c.nn as int),
            forall|g: int| 0 <= g < reps@.len() ==> #[trigger] reps@[g] < nn(sv),
            forall|q: int| 0 <= q < ord@.len() ==> #[trigger] ord@[q] < reps@.len() && ord@[q] < totals@.len(),
            p <= ord@.len(), out@.len() == p,
            forall|q: int| 0 <= q < p ==> #[trigger] view_row(out@[q]@) == grow(sv, reps@, ord@[q] as int, totals@[ord@[q] as int].sum as int),
        decreases ord@.len() - p,
    {
        let g = ord[p];
        let e = reps[g];
        let name = text_bytes(&c.nname, e);
        let mut bytes: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < name.len()
            invariant i <= name@.len(), bytes@ == name@.subrange(0, i as int),
            decreases name@.len() - i,
        {
            bytes.push(name[i]);
            i = i + 1;
            proof { assert(bytes@ =~= name@.subrange(0, i as int)); }
        }
        proof { assert(bytes@ =~= name@); }
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Text(bytes));
        row.push(EVal::Num { coeff: totals[g].sum, scale: 4 });
        proof {
            assert(view_row(row@) =~= grow(sv, reps@, g as int, totals@[g as int].sum as int));
        }
        out.push(row);
        p = p + 1;
    }
    proof {
        assert(view_rows(out@) =~= ord@.map_values(|g: usize| grow(sv, reps@, g as int, totals@[g as int].sum as int)));
    }
    out
}

// ------------------------------------------------------------------------------------------ the answer's meaning

/// `ORDER BY revenue DESC` on two output rows: the first comes no later exactly when its revenue is not smaller.
pub proof fn lemma_cmp_rows(a: Seq<u8>, b: Seq<u8>, s1: int, s2: int)
    ensures
        (keys_cmp(order_keys(), seq![Val::Text(a), Val::Num { coeff: s1, scale: 4 }], seq![Val::Text(b), Val::Num { coeff: s2, scale: 4 }]) <= 0)
            == (s1 >= s2),
{
    let r1 = seq![Val::Text(a), Val::Num { coeff: s1, scale: 4 }];
    let r2 = seq![Val::Text(b), Val::Num { coeff: s2, scale: 4 }];
    let ks = order_keys();
    lemma_compare_num(s1, 4, s2, 4);
    lemma_align_same(s1, 4);
    lemma_align_same(s2, 4);
    assert(max_nat(4, 4) == 4);
    assert(ks.drop_first() =~= Seq::<OrderKey>::empty());
    assert(keys_cmp(ks.drop_first(), r1, r2) == 0);
    assert(key_cmp(ks[0], r1, r2) == -sign(s1 - s2));
}

/// The group key sums of the normal form: group `g`'s key carries the group sums; other keys are empty.
pub proof fn lemma_key_sums(sv: StoresView, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>)
    requires stores_wf(sv), keys_ok(sv), nation_ok(sv, rp, inregv, gids, reps),
    ensures
        forall|g: int| 0 <= g < reps.len() ==> {
            let k = #[trigger] gkey(sv, reps, g);
            &&& gsum(q5_spec(rp, pd, t), from6(sv), k, 0) == gsum_r(sv, rp, pd, t, gids, g, 0, nl(sv) as int)
            &&& gcount(q5_spec(rp, pd, t), from6(sv), k) as int == gcnt_r(sv, rp, pd, t, gids, g, 0, nl(sv) as int)
            &&& gabs(q5_spec(rp, pd, t), from6(sv), k, 0) == gabs_r(sv, rp, pd, t, gids, g, 0, nl(sv) as int)
        },
        forall|k: Row| (forall|g: int| 0 <= g < reps.len() ==> #[trigger] gkey(sv, reps, g) != k) ==>
            #[trigger] gcount(q5_spec(rp, pd, t), from6(sv), k) == 0 && gabs(q5_spec(rp, pd, t), from6(sv), k, 0) == 0,
{
    let n = nl(sv) as int;
    assert forall|g: int| 0 <= g < reps.len() implies {
        let k = #[trigger] gkey(sv, reps, g);
        &&& gsum(q5_spec(rp, pd, t), from6(sv), k, 0) == gsum_r(sv, rp, pd, t, gids, g, 0, n)
        &&& gcount(q5_spec(rp, pd, t), from6(sv), k) as int == gcnt_r(sv, rp, pd, t, gids, g, 0, n)
        &&& gabs(q5_spec(rp, pd, t), from6(sv), k, 0) == gabs_r(sv, rp, pd, t, gids, g, 0, n)
    } by {
        lemma_group_sums(sv, rp, pd, t, gkey(sv, reps, g));
        lemma_group_key_sums(sv, rp, pd, t, inregv, gids, reps, g, n);
    }
    assert forall|k: Row| (forall|g: int| 0 <= g < reps.len() ==> #[trigger] gkey(sv, reps, g) != k) implies
        #[trigger] gcount(q5_spec(rp, pd, t), from6(sv), k) == 0 && gabs(q5_spec(rp, pd, t), from6(sv), k, 0) == 0 by {
        lemma_group_sums(sv, rp, pd, t, k);
        lemma_other_key(sv, rp, pd, t, inregv, gids, reps, k, n);
    }
}

/// The totals of the groups (one accumulator per group, over all lineitem rows).
pub open spec fn totals_rel(sv: StoresView, rp: Seq<u8>, pd: int, t: int, gids: Seq<usize>, ng: int, totals: Seq<Acc>) -> bool {
    &&& totals.len() == ng
    &&& forall|g: int| 0 <= g < ng ==> acc_ok(#[trigger] totals[g], gsum_r(sv, rp, pd, t, gids, g, 0, nl(sv) as int),
        gabs_r(sv, rp, pd, t, gids, g, 0, nl(sv) as int), gcnt_r(sv, rp, pd, t, gids, g, 0, nl(sv) as int))
}

/// A non-empty group whose accumulator is `over`: the normal form's group of its key is non-empty with mass beyond
/// `i128`.
pub proof fn lemma_over_group(sv: StoresView, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>,
    totals: Seq<Acc>, g: int)
    requires
        stores_wf(sv), keys_ok(sv), nation_ok(sv, rp, inregv, gids, reps),
        totals_rel(sv, rp, pd, t, gids, reps.len() as int, totals),
        0 <= g < reps.len(), totals[g].cnt > 0, totals[g].over,
    ensures
        gcount(q5_spec(rp, pd, t), from6(sv), gkey(sv, reps, g)) > 0,
        gabs(q5_spec(rp, pd, t), from6(sv), gkey(sv, reps, g), 0) > i128_max(),
{
    lemma_key_sums(sv, rp, pd, t, inregv, gids, reps);
    assert(acc_ok(totals[g], gsum_r(sv, rp, pd, t, gids, g, 0, nl(sv) as int),
        gabs_r(sv, rp, pd, t, gids, g, 0, nl(sv) as int), gcnt_r(sv, rp, pd, t, gids, g, 0, nl(sv) as int)));
}

/// The answer facts shared by the lemmas below.
pub open spec fn answer_hyps(sv: StoresView, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>,
    totals: Seq<Acc>, ord: Seq<usize>) -> bool {
    &&& stores_wf(sv)
    &&& keys_ok(sv)
    &&& nation_ok(sv, rp, inregv, gids, reps)
    &&& totals_rel(sv, rp, pd, t, gids, reps.len() as int, totals)
    &&& forall|g: int| 0 <= g < totals.len() ==> !(#[trigger] totals[g].cnt > 0 && totals[g].over)
    &&& ord_ok(ord, totals)
}

/// Group `g`: non-empty exactly when its count is; its mass fits `i128`; its sum is the accumulator's.
proof fn lemma_group_facts(sv: StoresView, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>,
    totals: Seq<Acc>, ord: Seq<usize>, g: int)
    requires answer_hyps(sv, rp, pd, t, inregv, gids, reps, totals, ord), 0 <= g < reps.len(),
    ensures ({
        let k = gkey(sv, reps, g);
        let g5 = q5_spec(rp, pd, t);
        &&& (totals[g].cnt > 0) == (gcount(g5, from6(sv), k) > 0)
        &&& gabs(g5, from6(sv), k, 0) <= i128_max()
        &&& totals[g].cnt > 0 ==> totals[g].sum as int == gsum(g5, from6(sv), k, 0)
    }),
{
    let n = nl(sv) as int;
    lemma_key_sums(sv, rp, pd, t, inregv, gids, reps);
    let k = gkey(sv, reps, g);
    assert(acc_ok(totals[g], gsum_r(sv, rp, pd, t, gids, g, 0, n), gabs_r(sv, rp, pd, t, gids, g, 0, n),
        gcnt_r(sv, rp, pd, t, gids, g, 0, n)));
    lemma_range_bounds(sv, rp, pd, t, gids, g, 0, n);
}

/// The groups lie inside `group_caps`.
proof fn lemma_caps(sv: StoresView, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>,
    totals: Seq<Acc>, ord: Seq<usize>)
    requires answer_hyps(sv, rp, pd, t, inregv, gids, reps, totals, ord),
    ensures group_caps(q5_spec(rp, pd, t), from6(sv)),
{
    let g5 = q5_spec(rp, pd, t);
    let xs = from6(sv);
    lemma_key_sums(sv, rp, pd, t, inregv, gids, reps);
    assert forall|k: Row, j: int| 0 <= j < g5.aggs.len() && !(g5.aggs[j] is Count) implies #[trigger] gabs(g5, xs, k, j) <= i128_max() by {
        assert(j == 0);
        if exists|g: int| 0 <= g < reps.len() && #[trigger] gkey(sv, reps, g) == k {
            let g = choose|g: int| 0 <= g < reps.len() && #[trigger] gkey(sv, reps, g) == k;
            lemma_group_facts(sv, rp, pd, t, inregv, gids, reps, totals, ord, g);
        } else {
            assert forall|g: int| 0 <= g < reps.len() implies #[trigger] gkey(sv, reps, g) != k by {}
            lemma_group_sums(sv, rp, pd, t, k);
            lemma_other_key(sv, rp, pd, t, inregv, gids, reps, k, nl(sv) as int);
        }
    }
}

/// The keys of the ordered groups.
pub open spec fn ord_keys(sv: StoresView, reps: Seq<usize>, ord: Seq<usize>) -> Seq<Row> {
    ord.map_values(|g: usize| gkey(sv, reps, g as int))
}

/// The ordered groups' keys are distinct and are exactly the non-empty groups of the normal form.
proof fn lemma_ord_keys(sv: StoresView, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>,
    totals: Seq<Acc>, ord: Seq<usize>)
    requires answer_hyps(sv, rp, pd, t, inregv, gids, reps, totals, ord),
    ensures
        ord_keys(sv, reps, ord).no_duplicates(),
        forall|k: Row| #[trigger] ord_keys(sv, reps, ord).contains(k) <==> gcount(q5_spec(rp, pd, t), from6(sv), k) > 0,
{
    let g5 = q5_spec(rp, pd, t);
    let xs = from6(sv);
    let ks = ord_keys(sv, reps, ord);
    lemma_key_sums(sv, rp, pd, t, inregv, gids, reps);
    assert forall|p: int, q: int| 0 <= p < ks.len() && 0 <= q < ks.len() && p != q implies ks[p] != ks[q] by {
        let (g1, g2) = (ord[p] as int, ord[q] as int);
        if p < q { assert(ord[p] != ord[q]); } else { assert(ord[q] != ord[p]); }
        if ks[p] == ks[q] {
            let (e1, e2) = (reps[g1] as int, reps[g2] as int);
            assert(gkey(sv, reps, g1)[0] == gkey(sv, reps, g2)[0]);
            assert(n_name(sv, e1) == n_name(sv, e2));
            assert(gids[e1] == g1 && gids[e2] == g2);
        }
    }
    assert forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g5, xs, k) > 0 by {
        if ks.contains(k) {
            let p = choose|p: int| 0 <= p < ks.len() && ks[p] == k;
            lemma_group_facts(sv, rp, pd, t, inregv, gids, reps, totals, ord, ord[p] as int);
        }
        if gcount(g5, xs, k) > 0 {
            if exists|g: int| 0 <= g < reps.len() && #[trigger] gkey(sv, reps, g) == k {
                let g = choose|g: int| 0 <= g < reps.len() && #[trigger] gkey(sv, reps, g) == k;
                lemma_group_facts(sv, rp, pd, t, inregv, gids, reps, totals, ord, g);
                assert(ord.contains(g as usize));
                let p = choose|p: int| 0 <= p < ord.len() && ord[p] == g as usize;
                assert(ks[p] == k);
            }
        }
    }
}

/// Each output row is the normal form's output row of its group's key.
proof fn lemma_out_rows(sv: StoresView, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>,
    totals: Seq<Acc>, ord: Seq<usize>, out: Seq<Row>)
    requires
        answer_hyps(sv, rp, pd, t, inregv, gids, reps, totals, ord),
        out == ord.map_values(|g: usize| grow(sv, reps, g as int, totals[g as int].sum as int)),
    ensures
        out.len() == ord_keys(sv, reps, ord).len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == out_row(q5_spec(rp, pd, t), from6(sv), ord_keys(sv, reps, ord)[i]),
{
    let g5 = q5_spec(rp, pd, t);
    let xs = from6(sv);
    let ks = ord_keys(sv, reps, ord);
    assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i] == out_row(g5, xs, ks[i]) by {
        let g = ord[i] as int;
        let k = gkey(sv, reps, g);
        lemma_group_facts(sv, rp, pd, t, inregv, gids, reps, totals, ord, g);
        let fr = full_row(g5, xs, k);
        assert(agg_outs(g5, xs, k) =~= seq![Val::Num { coeff: gsum(g5, xs, k, 0), scale: 4 }]);
        assert(fr =~= grow(sv, reps, g, totals[g].sum as int));
        lemma_select_identity(fr, q5_outs());
    }
}

/// The output rows are ordered by revenue descending.
proof fn lemma_out_sorted(sv: StoresView, reps: Seq<usize>, totals: Seq<Acc>, ord: Seq<usize>, out: Seq<Row>)
    requires ord_ok(ord, totals), out == ord.map_values(|g: usize| grow(sv, reps, g as int, totals[g as int].sum as int)),
    ensures sorted_by(order_keys(), out),
{
    assert forall|i: int, j: int| 0 <= i < j < out.len() implies keys_cmp(order_keys(), #[trigger] out[i], #[trigger] out[j]) <= 0 by {
        let (g1, g2) = (ord[i] as int, ord[j] as int);
        lemma_cmp_rows(n_name(sv, reps[g1] as int), n_name(sv, reps[g2] as int), totals[g1].sum as int, totals[g2].sum as int);
    }
}

/// Without an `over` non-empty group, the ordered rows are an allowed output and the groups lie inside
/// `group_caps`.
pub proof fn lemma_answer_rows(sv: StoresView, rp: Seq<u8>, pd: int, t: int, inregv: Seq<bool>, gids: Seq<usize>, reps: Seq<usize>,
    totals: Seq<Acc>, ord: Seq<usize>, out: Seq<Row>)
    requires
        answer_hyps(sv, rp, pd, t, inregv, gids, reps, totals, ord),
        out == ord.map_values(|g: usize| grow(sv, reps, g as int, totals[g as int].sum as int)),
    ensures
        group_caps(q5_spec(rp, pd, t), from6(sv)),
        result_ok(q5_spec(rp, pd, t), order_keys(), 0, None, from6(sv), out),
{
    lemma_caps(sv, rp, pd, t, inregv, gids, reps, totals, ord);
    lemma_ord_keys(sv, rp, pd, t, inregv, gids, reps, totals, ord);
    lemma_out_rows(sv, rp, pd, t, inregv, gids, reps, totals, ord, out);
    lemma_out_sorted(sv, reps, totals, ord, out);
    lemma_result_from_keys(q5_spec(rp, pd, t), order_keys(), 0, None, from6(sv), ord_keys(sv, reps, ord), out);
    lemma_slice_all(out);
}

} // verus!
