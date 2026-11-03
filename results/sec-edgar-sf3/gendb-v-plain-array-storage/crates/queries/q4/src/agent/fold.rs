//! P5: the GROUP BY over the contributions, in their order. A record `(num row, entry, value)` has the key row
//! `[sic, tlabel, stmt]` (`krow`) and the argument row `[cik, value, value]` (`arow`) the statement's GroupBy
//! evaluates; its group id is the entry's (`groups::groups_ok`).
//!
//! The fold keeps, for the records seen so far (`fold_inv`): the group ids in first-occurrence order (`order`,
//! whose key rows are `distinct_rows` of the keys), and per group the member count, the exact sum of the values
//! and the number of distinct ciks of `group_members` (a pair id seen for the first time is a new cik of its
//! group). A sum that leaves `i128` stops the fold (`Overflow`): the group's absolute mass is then beyond `i128`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::exec::relational::domain::num_mass_at;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::bridge::equality::*;
use crate::link::query::lemma_row_exact;
use crate::agent::common::chains::NONE;
use crate::agent::common::distinct::*;
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::ents::*;
use crate::agent::groups::*;

verus! {

pub type Rec = (usize, usize, i128);

/// The key row `[sic, tlabel, stmt]` of a record.
pub open spec fn krow(c: Ctx, ents: Seq<(usize, usize, usize)>, r: Rec) -> Row {
    let (l, j, k) = ents[r.1 as int];
    seq![Val::Int(s_sic(c, j as int)), t_label(c, k as int), Val::Text(c.stmt)]
}

/// The argument row `[cik, value, value]` of a record (COUNT(DISTINCT cik), SUM(value), AVG(value)).
pub open spec fn arow(c: Ctx, ents: Seq<(usize, usize, usize)>, r: Rec) -> Row {
    let (l, j, k) = ents[r.1 as int];
    seq![Val::Int(s_cik(c, j as int)), Val::Num { coeff: r.2 as int, scale: 4 }, Val::Num { coeff: r.2 as int, scale: 4 }]
}

/// The key row of group `g` (its representative's).
pub open spec fn grow_row(c: Ctx, reps: Seq<(usize, usize)>, g: int) -> Row {
    seq![Val::Int(s_sic(c, reps[g].0 as int)), t_label(c, reps[g].1 as int), Val::Text(c.stmt)]
}

pub open spec fn keys_of(c: Ctx, ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>) -> Seq<Row> {
    recs.map_values(|r: Rec| krow(c, ents, r))
}

pub open spec fn args_of(c: Ctx, ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>) -> Seq<Row> {
    recs.map_values(|r: Rec| arow(c, ents, r))
}

/// The argument rows of the members of group `g` among `recs` (the statement's `group_members`).
pub open spec fn members(c: Ctx, ents: Seq<(usize, usize, usize)>, reps: Seq<(usize, usize)>, recs: Seq<Rec>, g: int) -> Seq<Row> {
    group_members(keys_of(c, ents, recs), args_of(c, ents, recs), grow_row(c, reps, g))
}

/// A key-shaped row: `[Int, NULL or Text, Text]`.
pub open spec fn key_shaped(r: Row) -> bool {
    r.len() == 3 && r[0] is Int && (r[1] is Null || r[1] is Text) && r[2] is Text
}

/// On key-shaped rows "not distinct" is equality.
pub proof fn lemma_key_exact(a: Row, b: Row)
    requires key_shaped(a), key_shaped(b),
    ensures row_not_distinct(a, b) == (a == b),
{
    assert forall|i: int| 0 <= i < a.len() implies crate::bridge::equality::same_exact_type(#[trigger] a[i], b[i]) by {}
    lemma_row_exact(a, b);
}

/// `has_not_distinct` over key-shaped rows is `contains`.
pub proof fn lemma_has_key(d: Seq<Row>, k: Row)
    requires forall|i: int| 0 <= i < d.len() ==> key_shaped(#[trigger] d[i]), key_shaped(k),
    ensures has_not_distinct(d, k) == d.contains(k),
    decreases d.len(),
{
    if d.len() > 0 {
        let di = d.drop_last();
        assert forall|i: int| 0 <= i < di.len() implies key_shaped(#[trigger] di[i]) by {
            assert(di[i] == d[i]);
        }
        lemma_has_key(di, k);
        assert(d[d.len() - 1] == d.last());
        lemma_key_exact(d.last(), k);
        if di.contains(k) {
            let w = choose|w: int| 0 <= w < di.len() && di[w] == k;
            assert(d[w] == k);
        }
        if d.contains(k) && d.last() != k {
            let w = choose|w: int| 0 <= w < d.len() && d[w] == k;
            assert(di[w] == k);
        }
    }
}

/// The record facts the fold relies on: entries exist, ids come from `groups_ok`.
pub open spec fn recs_ok(ents: Seq<(usize, usize, usize)>, recs: Seq<Rec>) -> bool {
    forall|q: int| 0 <= q < recs.len() ==> ((#[trigger] recs[q]).1 as int) < ents.len()
}

/// The fold state over the records `p`.
pub open spec fn fold_inv(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>,
    order: Seq<usize>, seen: Seq<bool>, cnt: Seq<usize>, sum: Seq<i128>, ovf: Seq<bool>, dcnt: Seq<usize>, pseen: Seq<bool>) -> bool
{
    &&& seen.len() == gr.reps@.len()
    &&& forall|x: int| 0 <= x < order.len() ==> (#[trigger] order[x] as int) < gr.reps@.len()
    &&& forall|g: int| 0 <= g < gr.reps@.len() ==> (#[trigger] seen[g] <==> order.contains(g as usize))
    &&& order.map_values(|g: usize| grow_row(c, gr.reps@, g as int)) == distinct_rows(keys_of(c, ents, p))
    &&& acc_inv(c, ents, gr, p, cnt, sum, ovf)
    &&& dist_inv(c, ents, gr, p, dcnt, pseen)
}


/// A record's key row is its group's key row; group key rows are key-shaped and identify groups.
pub proof fn lemma_rec_key(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, r: Rec)
    requires groups_ok(c, ents, gr), (r.1 as int) < ents.len(),
    ensures
        (gr.gid@[r.1 as int] as int) < gr.reps@.len(),
        krow(c, ents, r) == grow_row(c, gr.reps@, gr.gid@[r.1 as int] as int),
        key_shaped(krow(c, ents, r)),
{
    let e = r.1 as int;
    let g = gr.gid@[e] as int;
    assert(gkey(c, gr.reps@[g].0 as int, gr.reps@[g].1 as int) == gkey(c, ents[e].1 as int, ents[e].2 as int));
    assert(krow(c, ents, r) =~= grow_row(c, gr.reps@, g));
}

pub proof fn lemma_grow_row(c: Ctx, gr: &Groups, ents: Seq<(usize, usize, usize)>, g1: int, g2: int)
    requires groups_ok(c, ents, gr), 0 <= g1 < gr.reps@.len(), 0 <= g2 < gr.reps@.len(),
    ensures
        key_shaped(grow_row(c, gr.reps@, g1)),
        (grow_row(c, gr.reps@, g1) == grow_row(c, gr.reps@, g2)) == (g1 == g2),
        row_not_distinct(grow_row(c, gr.reps@, g1), grow_row(c, gr.reps@, g2)) == (g1 == g2),
{
    let (a, b) = (grow_row(c, gr.reps@, g1), grow_row(c, gr.reps@, g2));
    if a == b && g1 != g2 {
        assert(a[0] == b[0] && a[1] == b[1]);
        assert(gkey(c, gr.reps@[g1].0 as int, gr.reps@[g1].1 as int) == gkey(c, gr.reps@[g2].0 as int, gr.reps@[g2].1 as int));
    }
    lemma_key_exact(a, b);
}

/// One more record: the members of its group get its argument row, the others are unchanged.
pub proof fn lemma_members_push(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, r: Rec, g: int)
    requires groups_ok(c, ents, gr), (r.1 as int) < ents.len(), 0 <= g < gr.reps@.len(),
    ensures members(c, ents, gr.reps@, p.push(r), g) == if gr.gid@[r.1 as int] as int == g {
        members(c, ents, gr.reps@, p, g).push(arow(c, ents, r))
    } else {
        members(c, ents, gr.reps@, p, g)
    },
{
    let ks = keys_of(c, ents, p.push(r));
    let as_ = args_of(c, ents, p.push(r));
    assert(ks.drop_last() =~= keys_of(c, ents, p));
    assert(as_.drop_last() =~= args_of(c, ents, p));
    assert(ks.last() == krow(c, ents, r));
    assert(as_.last() == arow(c, ents, r));
    lemma_rec_key(c, ents, gr, r);
    lemma_grow_row(c, gr, ents, gr.gid@[r.1 as int] as int, g);
}

/// A column of rows with one more row.
pub proof fn lemma_column_push(rows: Seq<Row>, x: Row, j: int)
    ensures column(rows.push(x), j) == column(rows, j).push(x[j]),
{
    assert(column(rows.push(x), j) =~= column(rows, j).push(x[j]));
}

/// Members of a group are at most the records.
pub proof fn lemma_members_len(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, g: int)
    requires groups_ok(c, ents, gr), recs_ok(ents, p), 0 <= g < gr.reps@.len(),
    ensures members(c, ents, gr.reps@, p, g).len() <= p.len(),
    decreases p.len(),
{
    if p.len() > 0 {
        let pi = p.drop_last();
        assert(pi.push(p.last()) =~= p);
        assert(p[p.len() - 1] == p.last());
        assert forall|q: int| 0 <= q < pi.len() implies ((#[trigger] pi[q]).1 as int) < ents.len() by {
            assert(pi[q] == p[q]);
        }
        lemma_members_len(c, ents, gr, pi, g);
        lemma_members_push(c, ents, gr, pi, p.last(), g);
    } else {
        assert(keys_of(c, ents, p) =~= Seq::<Row>::empty());
    }
}

/// `distinct_vals` is no longer than its input.
pub proof fn lemma_distinct_len(vs: Seq<Val>)
    ensures distinct_vals(vs).len() <= vs.len(),
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_distinct_len(vs.drop_last());
    }
}

/// The fold over no records.
pub proof fn lemma_fold_empty(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, seen: Seq<bool>, cnt: Seq<usize>,
    sum: Seq<i128>, ovf: Seq<bool>, dcnt: Seq<usize>, pseen: Seq<bool>)
    requires
        groups_ok(c, ents, gr),
        seen == Seq::new(gr.reps@.len(), |g: int| false), cnt == Seq::new(gr.reps@.len(), |g: int| 0usize),
        sum == Seq::new(gr.reps@.len(), |g: int| 0i128), ovf == Seq::new(gr.reps@.len(), |g: int| false),
        dcnt == Seq::new(gr.reps@.len(), |g: int| 0usize), pseen == Seq::new(gr.preps@.len(), |g: int| false),
    ensures fold_inv(c, ents, gr, Seq::empty(), Seq::empty(), seen, cnt, sum, ovf, dcnt, pseen),
{
    let p = Seq::<Rec>::empty();
    assert(keys_of(c, ents, p) =~= Seq::<Row>::empty());
    assert(args_of(c, ents, p) =~= Seq::<Row>::empty());
    assert(Seq::<usize>::empty().map_values(|g: usize| grow_row(c, gr.reps@, g as int)) =~= Seq::<Row>::empty());
    assert forall|g: int| 0 <= g < gr.reps@.len() implies #[trigger] members(c, ents, gr.reps@, p, g) == Seq::<Row>::empty() by {}
    assert forall|g: int| 0 <= g < gr.reps@.len() implies column(#[trigger] members(c, ents, gr.reps@, p, g), 0) =~= Seq::<Val>::empty() by {}
    assert forall|g: int| 0 <= g < gr.reps@.len() implies column(#[trigger] members(c, ents, gr.reps@, p, g), 1) =~= Seq::<Val>::empty() by {}
}

/// The order part of one fold step: a record of a group seen before leaves the distinct keys unchanged, a new
/// group's key row is appended.
proof fn lemma_step_order(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, r: Rec,
    order: Seq<usize>, seen: Seq<bool>, order2: Seq<usize>, seen2: Seq<bool>)
    requires
        groups_ok(c, ents, gr), (r.1 as int) < ents.len(), gr.reps@.len() < NONE,
        seen.len() == gr.reps@.len(),
        forall|x: int| 0 <= x < order.len() ==> (#[trigger] order[x] as int) < gr.reps@.len(),
        forall|g: int| 0 <= g < gr.reps@.len() ==> (#[trigger] seen[g] <==> order.contains(g as usize)),
        order.map_values(|g: usize| grow_row(c, gr.reps@, g as int)) == distinct_rows(keys_of(c, ents, p)),
        seen2 == seen.update(gr.gid@[r.1 as int] as int, true),
        order2 == if seen[gr.gid@[r.1 as int] as int] { order } else { order.push(gr.gid@[r.1 as int]) },
    ensures
        forall|x: int| 0 <= x < order2.len() ==> (#[trigger] order2[x] as int) < gr.reps@.len(),
        forall|g: int| 0 <= g < gr.reps@.len() ==> (#[trigger] seen2[g] <==> order2.contains(g as usize)),
        order2.map_values(|g: usize| grow_row(c, gr.reps@, g as int)) == distinct_rows(keys_of(c, ents, p.push(r))),
{
    let g = gr.gid@[r.1 as int];
    let f = |g: usize| grow_row(c, gr.reps@, g as int);
    let d = order.map_values(f);
    let ks = keys_of(c, ents, p.push(r));
    assert(ks.drop_last() =~= keys_of(c, ents, p));
    lemma_rec_key(c, ents, gr, r);
    assert(ks.last() == grow_row(c, gr.reps@, g as int));
    assert forall|i: int| 0 <= i < d.len() implies key_shaped(#[trigger] d[i]) by {
        lemma_grow_row(c, gr, ents, order[i] as int, order[i] as int);
    }
    lemma_has_key(d, ks.last());
    // `d` contains the record's key row exactly when its group was seen.
    if d.contains(ks.last()) {
        let w = choose|w: int| 0 <= w < d.len() && d[w] == ks.last();
        lemma_grow_row(c, gr, ents, order[w] as int, g as int);
        assert(order[w] == g);
        assert(seen[g as int]);
    }
    if seen[g as int] {
        let w = choose|w: int| 0 <= w < order.len() && order[w] == g;
        assert(d[w] == ks.last());
    } else {
        assert(order2.map_values(f) =~= d.push(f(g)));
    }
    assert forall|x: int| 0 <= x < order2.len() implies (#[trigger] order2[x] as int) < gr.reps@.len() by {
        if x < order.len() {
            assert(order2[x] == order[x]);
        }
    }
    assert forall|g2: int| 0 <= g2 < gr.reps@.len() implies (#[trigger] seen2[g2] <==> order2.contains(g2 as usize)) by {
        let gu = g2 as usize;
        assert(seen2[g2] == if g2 == g as int { true } else { seen[g2] });
        if order.contains(gu) {
            let w = choose|w: int| 0 <= w < order.len() && order[w] == gu;
            assert(order2[w] == order[w]);
        }
        if order2.contains(gu) && !order.contains(gu) {
            let w = choose|w: int| 0 <= w < order2.len() && order2[w] == gu;
            if w < order.len() {
                assert(order2[w] == order[w]);
            }
            assert(!seen[g as int] && w == order.len() as int && gu == g);
        }
        if g2 == g as int {
            if seen[g as int] {
                assert(order.contains(g));
            } else {
                assert(order2[order.len() as int] == g);
            }
        }
    }
}

/// The counter, sum and cik-column part of the fold state: a group whose sum left `i128` (`ovf`) has an absolute
/// value mass beyond `i128::MAX`; the others have their exact sum.
pub open spec fn acc_inv(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, cnt: Seq<usize>, sum: Seq<i128>,
    ovf: Seq<bool>) -> bool
{
    let ng = gr.reps@.len();
    &&& cnt.len() == ng && sum.len() == ng && ovf.len() == ng
    &&& forall|g: int| 0 <= g < ng ==> #[trigger] cnt[g] as int == members(c, ents, gr.reps@, p, g).len()
    &&& forall|g: int| 0 <= g < ng && !ovf[g] ==> #[trigger] num_sum(column(members(c, ents, gr.reps@, p, g), 1))
        == (sum[g] as int, if cnt[g] == 0 { 0nat } else { 4nat })
    &&& forall|g: int| 0 <= g < ng && ovf[g] ==> #[trigger] num_mass_at(column(members(c, ents, gr.reps@, p, g), 1), 4) > i128::MAX
    &&& forall|g: int| 0 <= g < ng ==> all_num(#[trigger] column(members(c, ents, gr.reps@, p, g), 1), 4)
    &&& forall|g: int| 0 <= g < ng ==> all_int(#[trigger] column(members(c, ents, gr.reps@, p, g), 0))
    &&& forall|g: int, x: int| 0 <= g < ng ==>
        (#[trigger] column(members(c, ents, gr.reps@, p, g), 0).contains(Val::Int(x))
            <==> exists|q: int| 0 <= q < p.len() && gr.gid@[p[q].1 as int] == g && s_cik(c, ents[p[q].1 as int].1 as int) == x)
}

/// The distinct-count part of the fold state.
pub open spec fn dist_inv(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, dcnt: Seq<usize>, pseen: Seq<bool>) -> bool {
    let ng = gr.reps@.len();
    &&& dcnt.len() == ng && pseen.len() == gr.preps@.len()
    &&& forall|g: int| 0 <= g < ng ==> #[trigger] dcnt[g] as int == distinct_vals(column(members(c, ents, gr.reps@, p, g), 0)).len()
    &&& forall|pp: int| 0 <= pp < pseen.len() ==> (#[trigger] pseen[pp] <==> exists|q: int| 0 <= q < p.len() && gr.pid@[p[q].1 as int] == pp)
}


/// The mass of numerics of scale 4 with one more: plus its absolute coefficient.
proof fn lemma_mass_push(vs: Seq<Val>, v: int)
    ensures num_mass_at(vs.push(Val::Num { coeff: v, scale: 4 }), 4) == num_mass_at(vs, 4) + abs(v),
{
    assert(vs.push(Val::Num { coeff: v, scale: 4 }).drop_last() =~= vs);
    assert(((4 - 4) as nat) == 0nat);
    assert(pow10(0) == 1);
}

/// The exact sum of numerics of scale 4 is at most their mass.
proof fn lemma_sum_le_mass(vs: Seq<Val>)
    requires all_num(vs, 4), vs.len() > 0,
    ensures abs(num_sum(vs).0) <= num_mass_at(vs, 4),
{
    crate::link::capacity::lemma_num_sum_bound(vs);
    crate::link::capacity::lemma_num_mass_uniform(vs, 4);
    assert(vs[0] is Num);
}

/// The fold state of group `g2` after one record: count, sum or overflow, numeric and integer columns.
proof fn lemma_step_acc_g(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, r: Rec,
    cnt: Seq<usize>, sum: Seq<i128>, ovf: Seq<bool>, cnt2: Seq<usize>, sum2: Seq<i128>, ovf2: Seq<bool>, g2: int)
    requires
        groups_ok(c, ents, gr), (r.1 as int) < ents.len(), gr.reps@.len() < NONE, 0 <= g2 < gr.reps@.len(),
        acc_inv(c, ents, gr, p, cnt, sum, ovf),
        cnt[gr.gid@[r.1 as int] as int] + 1 <= usize::MAX,
        cnt2 == cnt.update(gr.gid@[r.1 as int] as int, (cnt[gr.gid@[r.1 as int] as int] + 1) as usize),
        ({
            let g = gr.gid@[r.1 as int] as int;
            let t = sum[g] + r.2;
            if ovf[g] || !(i128::MIN <= t <= i128::MAX) {
                sum2 == sum && ovf2 == ovf.update(g, true)
            } else {
                sum2 == sum.update(g, t as i128) && ovf2 == ovf
            }
        }),
    ensures
        cnt2[g2] as int == members(c, ents, gr.reps@, p.push(r), g2).len(),
        !ovf2[g2] ==> num_sum(column(members(c, ents, gr.reps@, p.push(r), g2), 1)) == (sum2[g2] as int, if cnt2[g2] == 0 { 0nat } else { 4nat }),
        ovf2[g2] ==> num_mass_at(column(members(c, ents, gr.reps@, p.push(r), g2), 1), 4) > i128::MAX,
        all_num(column(members(c, ents, gr.reps@, p.push(r), g2), 1), 4),
        all_int(column(members(c, ents, gr.reps@, p.push(r), g2), 0)),
{
    let g = gr.gid@[r.1 as int] as int;
    lemma_rec_key(c, ents, gr, r);
    lemma_members_push(c, ents, gr, p, r, g2);
    let m = members(c, ents, gr.reps@, p, g2);
    assert(cnt[g2] as int == m.len());
    assert(all_num(column(m, 1), 4));
    assert(all_int(column(m, 0)));
    if g2 == g {
        let a = arow(c, ents, r);
        lemma_column_push(m, a, 1);
        lemma_column_push(m, a, 0);
        let c1 = column(m, 1);
        lemma_mass_push(c1, r.2 as int);
        if !ovf[g] {
            if m.len() == 0 {
                assert(c1 =~= Seq::<Val>::empty());
            }
            lemma_num_sum_push(c1, sum[g] as int, r.2 as int, 4);
            let t = sum[g] + r.2;
            if !(i128::MIN <= t <= i128::MAX) {
                let c2 = c1.push(a[1]);
                assert forall|i: int| 0 <= i < c2.len() implies (#[trigger] c2[i] is Num) && c2[i]->Num_scale == 4 by {
                    if i < c1.len() {
                        assert(c2[i] == c1[i]);
                    }
                }
                lemma_sum_le_mass(c2);
            }
        }
        let c0 = column(m, 0).push(a[0]);
        assert forall|i: int| 0 <= i < c0.len() implies #[trigger] c0[i] is Int by {
            if i < column(m, 0).len() {
                assert(c0[i] == column(m, 0)[i]);
            }
        }
        let c2 = c1.push(a[1]);
        assert forall|i: int| 0 <= i < c2.len() implies (#[trigger] c2[i] is Num) && c2[i]->Num_scale == 4 by {
            if i < c1.len() {
                assert(c2[i] == c1[i]);
            }
        }
        if ovf[g] {
            lemma_mass_push(c1, r.2 as int);
        }
    }
}

/// The counters and sums after one record of group `g`.
proof fn lemma_step_acc(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, r: Rec,
    cnt: Seq<usize>, sum: Seq<i128>, ovf: Seq<bool>, cnt2: Seq<usize>, sum2: Seq<i128>, ovf2: Seq<bool>)
    requires
        groups_ok(c, ents, gr), (r.1 as int) < ents.len(), gr.reps@.len() < NONE,
        acc_inv(c, ents, gr, p, cnt, sum, ovf),
        cnt[gr.gid@[r.1 as int] as int] + 1 <= usize::MAX,
        cnt2 == cnt.update(gr.gid@[r.1 as int] as int, (cnt[gr.gid@[r.1 as int] as int] + 1) as usize),
        ({
            let g = gr.gid@[r.1 as int] as int;
            let t = sum[g] + r.2;
            if ovf[g] || !(i128::MIN <= t <= i128::MAX) {
                sum2 == sum && ovf2 == ovf.update(g, true)
            } else {
                sum2 == sum.update(g, t as i128) && ovf2 == ovf
            }
        }),
    ensures acc_inv(c, ents, gr, p.push(r), cnt2, sum2, ovf2),
{
    let g = gr.gid@[r.1 as int] as int;
    let ng = gr.reps@.len();
    let p2 = p.push(r);
    lemma_rec_key(c, ents, gr, r);
    assert forall|g2: int| 0 <= g2 < ng implies #[trigger] cnt2[g2] as int == members(c, ents, gr.reps@, p2, g2).len() by {
        lemma_step_acc_g(c, ents, gr, p, r, cnt, sum, ovf, cnt2, sum2, ovf2, g2);
    }
    assert forall|g2: int| 0 <= g2 < ng && !ovf2[g2] implies #[trigger] num_sum(column(members(c, ents, gr.reps@, p2, g2), 1))
        == (sum2[g2] as int, if cnt2[g2] == 0 { 0nat } else { 4nat }) by {
        lemma_step_acc_g(c, ents, gr, p, r, cnt, sum, ovf, cnt2, sum2, ovf2, g2);
    }
    assert forall|g2: int| 0 <= g2 < ng && ovf2[g2] implies #[trigger] num_mass_at(column(members(c, ents, gr.reps@, p2, g2), 1), 4) > i128::MAX by {
        lemma_step_acc_g(c, ents, gr, p, r, cnt, sum, ovf, cnt2, sum2, ovf2, g2);
    }
    assert forall|g2: int| 0 <= g2 < ng implies all_num(#[trigger] column(members(c, ents, gr.reps@, p2, g2), 1), 4) by {
        lemma_step_acc_g(c, ents, gr, p, r, cnt, sum, ovf, cnt2, sum2, ovf2, g2);
    }
    assert forall|g2: int| 0 <= g2 < ng implies all_int(#[trigger] column(members(c, ents, gr.reps@, p2, g2), 0)) by {
        lemma_step_acc_g(c, ents, gr, p, r, cnt, sum, ovf, cnt2, sum2, ovf2, g2);
    }
    assert forall|g2: int, x: int| 0 <= g2 < ng implies
        (#[trigger] column(members(c, ents, gr.reps@, p2, g2), 0).contains(Val::Int(x))
            <==> exists|q: int| 0 <= q < p2.len() && gr.gid@[p2[q].1 as int] == g2 && s_cik(c, ents[p2[q].1 as int].1 as int) == x) by {
        lemma_members_push(c, ents, gr, p, r, g2);
        let m = members(c, ents, gr.reps@, p, g2);
        let c0 = column(m, 0);
        let ex_old = exists|q: int| 0 <= q < p.len() && gr.gid@[p[q].1 as int] == g2 && s_cik(c, ents[p[q].1 as int].1 as int) == x;
        let ex_new = exists|q: int| 0 <= q < p2.len() && gr.gid@[p2[q].1 as int] == g2 && s_cik(c, ents[p2[q].1 as int].1 as int) == x;
        if ex_old {
            let q = choose|q: int| 0 <= q < p.len() && gr.gid@[p[q].1 as int] == g2 && s_cik(c, ents[p[q].1 as int].1 as int) == x;
            assert(p2[q] == p[q]);
        }
        if ex_new {
            let q = choose|q: int| 0 <= q < p2.len() && gr.gid@[p2[q].1 as int] == g2 && s_cik(c, ents[p2[q].1 as int].1 as int) == x;
            if q < p.len() {
                assert(p2[q] == p[q]);
            }
        }
        assert(p2[p.len() as int] == r);
        if g2 == g {
            let a = arow(c, ents, r);
            lemma_column_push(m, a, 0);
            let c1 = c0.push(a[0]);
            if c1.contains(Val::Int(x)) && !c0.contains(Val::Int(x)) {
                let w = choose|w: int| 0 <= w < c1.len() && c1[w] == Val::Int(x);
                if w < c0.len() {
                    assert(c1[w] == c0[w]);
                }
            }
            if c0.contains(Val::Int(x)) {
                let w = choose|w: int| 0 <= w < c0.len() && c0[w] == Val::Int(x);
                assert(c1[w] == c0[w]);
            }
            if s_cik(c, ents[r.1 as int].1 as int) == x {
                assert(c1[c0.len() as int] == Val::Int(x));
            }
        }
    }
}

/// The distinct counts after one record of group `g` with pair `pp`.
proof fn lemma_step_dist(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, r: Rec,
    cnt: Seq<usize>, sum: Seq<i128>, ovf: Seq<bool>, dcnt: Seq<usize>, pseen: Seq<bool>, dcnt2: Seq<usize>, pseen2: Seq<bool>)
    requires
        groups_ok(c, ents, gr), (r.1 as int) < ents.len(), gr.reps@.len() < NONE, gr.preps@.len() < NONE,
        recs_ok(ents, p),
        acc_inv(c, ents, gr, p, cnt, sum, ovf), dist_inv(c, ents, gr, p, dcnt, pseen),
        dcnt[gr.gid@[r.1 as int] as int] + 1 <= usize::MAX,
        pseen2 == pseen.update(gr.pid@[r.1 as int] as int, true),
        dcnt2 == if pseen[gr.pid@[r.1 as int] as int] { dcnt } else {
            dcnt.update(gr.gid@[r.1 as int] as int, (dcnt[gr.gid@[r.1 as int] as int] + 1) as usize)
        },
    ensures dist_inv(c, ents, gr, p.push(r), dcnt2, pseen2),
{
    let e = r.1 as int;
    let g = gr.gid@[e] as int;
    let pp = gr.pid@[e] as int;
    let ng = gr.reps@.len();
    let p2 = p.push(r);
    let cik = s_cik(c, ents[e].1 as int);
    assert(p2[p.len() as int] == r);
    // The pair of the record was seen exactly when its cik is already among its group's ciks.
    let m = members(c, ents, gr.reps@, p, g);
    assert(pseen[pp] == column(m, 0).contains(Val::Int(cik))) by {
        if pseen[pp] {
            let q = choose|q: int| 0 <= q < p.len() && gr.pid@[p[q].1 as int] == pp;
            let e2 = p[q].1 as int;
            assert(gr.preps@[gr.pid@[e2] as int] == (gr.gid@[e2], s_cik_s(c)[ents[e2].1 as int]));
            assert(gr.preps@[pp] == (gr.gid@[e], s_cik_s(c)[ents[e].1 as int]));
        }
        if column(m, 0).contains(Val::Int(cik)) {
            let q = choose|q: int| 0 <= q < p.len() && gr.gid@[p[q].1 as int] == g && s_cik(c, ents[p[q].1 as int].1 as int) == cik;
            let e2 = p[q].1 as int;
            assert(gr.preps@[gr.pid@[e2] as int] == (gr.gid@[e2], s_cik_s(c)[ents[e2].1 as int]));
            assert(gr.preps@[gr.pid@[e2] as int] == gr.preps@[pp]);
            assert(gr.pid@[e2] as int == pp);
        }
    }
    assert forall|g2: int| 0 <= g2 < ng implies #[trigger] dcnt2[g2] as int == distinct_vals(column(members(c, ents, gr.reps@, p2, g2), 0)).len() by {
        lemma_members_push(c, ents, gr, p, r, g2);
        if g2 == g {
            let a = arow(c, ents, r);
            lemma_column_push(m, a, 0);
            lemma_distinct_push(column(m, 0), a[0]);
        }
    }
    assert forall|p3: int| 0 <= p3 < pseen2.len() implies (#[trigger] pseen2[p3] <==> exists|q: int| 0 <= q < p2.len() && gr.pid@[p2[q].1 as int] == p3) by {
        if exists|q: int| 0 <= q < p.len() && gr.pid@[p[q].1 as int] == p3 {
            let q = choose|q: int| 0 <= q < p.len() && gr.pid@[p[q].1 as int] == p3;
            assert(p2[q] == p[q]);
        }
        if exists|q: int| 0 <= q < p2.len() && gr.pid@[p2[q].1 as int] == p3 {
            let q = choose|q: int| 0 <= q < p2.len() && gr.pid@[p2[q].1 as int] == p3;
            if q < p.len() {
                assert(p2[q] == p[q]);
            }
        }
    }
}

/// The result of the fold (`ovf[g]`: group `g`'s sum left `i128`).
pub struct FoldOut {
    pub order: Vec<usize>,
    pub seen: Vec<bool>,
    pub cnt: Vec<usize>,
    pub sum: Vec<i128>,
    pub ovf: Vec<bool>,
    pub dcnt: Vec<usize>,
    pub pseen: Vec<bool>,
}

/// The records of the segments, concatenated in order.
pub open spec fn flat(segs: Seq<Vec<Rec>>) -> Seq<Rec>
    decreases segs.len(),
{
    if segs.len() == 0 { Seq::empty() } else { flat(segs.drop_last()) + segs.last()@ }
}

/// One segment more.
pub proof fn lemma_flat_push(segs: Seq<Vec<Rec>>, v: Vec<Rec>)
    ensures flat(segs.push(v)) == flat(segs) + v@,
{
    assert(segs.push(v).drop_last() =~= segs);
}

/// The fold state.
pub struct FoldState {
    pub order: Vec<usize>,
    pub seen: Vec<bool>,
    pub cnt: Vec<usize>,
    pub sum: Vec<i128>,
    pub ovf: Vec<bool>,
    pub dcnt: Vec<usize>,
    pub pseen: Vec<bool>,
}

pub open spec fn state_inv(c: Ctx, ents: Seq<(usize, usize, usize)>, gr: &Groups, p: Seq<Rec>, st: &FoldState) -> bool {
    &&& fold_inv(c, ents, gr, p, st.order@, st.seen@, st.cnt@, st.sum@, st.ovf@, st.dcnt@, st.pseen@)
    &&& forall|g: int| 0 <= g < st.seen@.len() && #[trigger] st.seen@[g] ==> st.cnt@[g] > 0
}

/// Fold the records of one segment after the records `p`.
fn fold_seg(st: &mut FoldState, seg: &Vec<Rec>, gr: &Groups, Ghost(c): Ghost<Ctx>, Ghost(ents): Ghost<Seq<(usize, usize, usize)>>,
    Ghost(p): Ghost<Seq<Rec>>)
    requires
        groups_ok(c, ents, gr), recs_ok(ents, p + seg@), gr.reps@.len() < NONE, gr.preps@.len() < NONE,
        p.len() + seg@.len() <= usize::MAX, state_inv(c, ents, gr, p, old(st)),
    ensures state_inv(c, ents, gr, p + seg@, final(st)),
{
    let ng = gr.reps.len();
    let np = gr.preps.len();
    let n = seg.len();
    let mut q: usize = 0;
    proof {
        assert(p + seg@.subrange(0, 0) =~= p);
    }
    while q < n
        invariant
            groups_ok(c, ents, gr), recs_ok(ents, p + seg@), ng == gr.reps@.len(), np == gr.preps@.len(), ng < NONE, np < NONE,
            n == seg@.len(), q <= n, p.len() + seg@.len() <= usize::MAX,
            state_inv(c, ents, gr, p + seg@.subrange(0, q as int), st),
        decreases n - q,
    {
        let r = seg[q];
        let e = r.1;
        let v = r.2;
        let ghost pq = p + seg@.subrange(0, q as int);
        proof {
            let all = p + seg@;
            assert(all[p.len() + q] == r);
            assert(p + seg@.subrange(0, q + 1) =~= pq.push(r));
            assert forall|q2: int| 0 <= q2 < pq.len() implies ((#[trigger] pq[q2]).1 as int) < ents.len() by {
                assert(pq[q2] == all[q2]);
            }
            assert((r.1 as int) < ents.len());
            lemma_rec_key(c, ents, gr, r);
            lemma_members_len(c, ents, gr, pq, gr.gid@[e as int] as int);
            lemma_distinct_len(column(members(c, ents, gr.reps@, pq, gr.gid@[e as int] as int), 0));
            assert(column(members(c, ents, gr.reps@, pq, gr.gid@[e as int] as int), 0).len()
                == members(c, ents, gr.reps@, pq, gr.gid@[e as int] as int).len());
        }
        let g = gr.gid[e];
        let pp = gr.pid[e];
        let ghost order0 = st.order@;
        let ghost seen0 = st.seen@;
        let ghost cnt0 = st.cnt@;
        let ghost sum0 = st.sum@;
        let ghost ovf0 = st.ovf@;
        let ghost dcnt0 = st.dcnt@;
        let ghost pseen0 = st.pseen@;
        if !st.seen[g] {
            st.order.push(g);
        }
        st.seen.set(g, true);
        let c0 = st.cnt[g];
        st.cnt.set(g, c0 + 1);
        if !st.ovf[g] {
            let s0 = st.sum[g];
            match s0.checked_add(v) {
                Some(ns) => st.sum.set(g, ns),
                None => st.ovf.set(g, true),
            }
        } else {
            st.ovf.set(g, true);
        }
        if !st.pseen[pp] {
            let d0 = st.dcnt[g];
            st.dcnt.set(g, d0 + 1);
        }
        st.pseen.set(pp, true);
        proof {
            lemma_step_order(c, ents, gr, pq, r, order0, seen0, st.order@, st.seen@);
            lemma_step_acc(c, ents, gr, pq, r, cnt0, sum0, ovf0, st.cnt@, st.sum@, st.ovf@);
            lemma_step_dist(c, ents, gr, pq, r, cnt0, sum0, ovf0, dcnt0, pseen0, st.dcnt@, st.pseen@);
        }
        q = q + 1;
    }
    proof {
        assert(seg@.subrange(0, n as int) =~= seg@);
    }
}

/// Fold the records of the segments in order.
pub fn fold(segs: &Vec<Vec<Rec>>, gr: &Groups, Ghost(c): Ghost<Ctx>, Ghost(ents): Ghost<Seq<(usize, usize, usize)>>) -> (r: FoldOut)
    requires
        groups_ok(c, ents, gr), recs_ok(ents, flat(segs@)), gr.reps@.len() < NONE, gr.preps@.len() < NONE,
        flat(segs@).len() <= usize::MAX,
    ensures
        fold_inv(c, ents, gr, flat(segs@), r.order@, r.seen@, r.cnt@, r.sum@, r.ovf@, r.dcnt@, r.pseen@),
        forall|g: int| 0 <= g < r.seen@.len() && #[trigger] r.seen@[g] ==> r.cnt@[g] > 0,
{
    let ng = gr.reps.len();
    let np = gr.preps.len();
    let mut st = FoldState {
        order: Vec::new(), seen: vec![false; ng], cnt: vec![0usize; ng], sum: vec![0i128; ng], ovf: vec![false; ng],
        dcnt: vec![0usize; ng], pseen: vec![false; np],
    };
    proof {
        assert(st.seen@ =~= Seq::new(ng as nat, |g: int| false));
        assert(st.cnt@ =~= Seq::new(ng as nat, |g: int| 0usize));
        assert(st.sum@ =~= Seq::new(ng as nat, |g: int| 0i128));
        assert(st.ovf@ =~= Seq::new(ng as nat, |g: int| false));
        assert(st.dcnt@ =~= Seq::new(ng as nat, |g: int| 0usize));
        assert(st.pseen@ =~= Seq::new(np as nat, |g: int| false));
        lemma_fold_empty(c, ents, gr, st.seen@, st.cnt@, st.sum@, st.ovf@, st.dcnt@, st.pseen@);
        assert(st.order@ =~= Seq::<usize>::empty());
        assert(flat(segs@.subrange(0, 0)) =~= Seq::<Rec>::empty());
    }
    let ns = segs.len();
    let mut u: usize = 0;
    while u < ns
        invariant
            groups_ok(c, ents, gr), recs_ok(ents, flat(segs@)), ng == gr.reps@.len(), np == gr.preps@.len(), ng < NONE, np < NONE,
            ns == segs@.len(), u <= ns, flat(segs@).len() <= usize::MAX,
            state_inv(c, ents, gr, flat(segs@.subrange(0, u as int)), &st),
        decreases ns - u,
    {
        let ghost p = flat(segs@.subrange(0, u as int));
        proof {
            assert(segs@.subrange(0, u + 1) =~= segs@.subrange(0, u as int).push(segs@[u as int]));
            lemma_flat_push(segs@.subrange(0, u as int), segs@[u as int]);
            lemma_flat_prefix(segs@, u as int + 1);
            assert forall|q: int| 0 <= q < (p + segs@[u as int]@).len() implies ((#[trigger] (p + segs@[u as int]@)[q]).1 as int) < ents.len() by {
                assert((p + segs@[u as int]@)[q] == flat(segs@)[q]);
            }
            assert(p.len() + segs@[u as int]@.len() <= usize::MAX);
        }
        fold_seg(&mut st, &segs[u], gr, Ghost(c), Ghost(ents), Ghost(p));
        u = u + 1;
    }
    proof {
        assert(segs@.subrange(0, ns as int) =~= segs@);
    }
    FoldOut { order: st.order, seen: st.seen, cnt: st.cnt, sum: st.sum, ovf: st.ovf, dcnt: st.dcnt, pseen: st.pseen }
}

/// The same records with a total count of at most `usize::MAX`: the segments themselves when their lengths add
/// up without overflow, otherwise one vector with all of them (a vector's length is a `usize`).
pub fn bound_segs(segs: Vec<Vec<Rec>>) -> (r: Vec<Vec<Rec>>)
    ensures flat(r@) == flat(segs@), flat(r@).len() <= usize::MAX,
{
    let ns = segs.len();
    let mut tot: usize = 0;
    let mut u: usize = 0;
    let mut ok = true;
    proof {
        assert(flat(segs@.subrange(0, 0)) =~= Seq::<Rec>::empty());
    }
    while u < ns && ok
        invariant
            ns == segs@.len(), u <= ns, ok ==> tot as int == flat(segs@.subrange(0, u as int)).len(),
        decreases ns - u, if ok { 1int } else { 0int },
    {
        match tot.checked_add(segs[u].len()) {
            Some(t) => {
                proof {
                    assert(segs@.subrange(0, u + 1) =~= segs@.subrange(0, u as int).push(segs@[u as int]));
                    lemma_flat_push(segs@.subrange(0, u as int), segs@[u as int]);
                }
                tot = t;
                u = u + 1;
            },
            None => {
                ok = false;
            },
        }
    }
    if ok {
        proof {
            assert(segs@.subrange(0, ns as int) =~= segs@);
        }
        return segs;
    }
    let mut all: Vec<Rec> = Vec::new();
    let mut w: usize = 0;
    proof {
        assert(flat(segs@.subrange(0, 0)) =~= Seq::<Rec>::empty());
    }
    while w < ns
        invariant ns == segs@.len(), w <= ns, all@ == flat(segs@.subrange(0, w as int)),
        decreases ns - w,
    {
        let seg = &segs[w];
        let m = seg.len();
        let mut q: usize = 0;
        let ghost a0 = all@;
        while q < m
            invariant m == seg@.len(), q <= m, all@ == a0 + seg@.subrange(0, q as int),
            decreases m - q,
        {
            all.push(seg[q]);
            proof {
                assert(seg@.subrange(0, q + 1) =~= seg@.subrange(0, q as int).push(seg@[q as int]));
            }
            q = q + 1;
        }
        proof {
            assert(seg@.subrange(0, m as int) =~= seg@);
            assert(segs@.subrange(0, w + 1) =~= segs@.subrange(0, w as int).push(segs@[w as int]));
            lemma_flat_push(segs@.subrange(0, w as int), segs@[w as int]);
        }
        w = w + 1;
    }
    proof {
        assert(segs@.subrange(0, ns as int) =~= segs@);
    }
    let mut r: Vec<Vec<Rec>> = Vec::new();
    let ghost all_v = all@;
    let la = all.len();
    r.push(all);
    proof {
        lemma_flat_push(Seq::<Vec<Rec>>::empty(), r@[0]);
        assert(r@ =~= Seq::<Vec<Rec>>::empty().push(r@[0]));
        assert(flat(Seq::<Vec<Rec>>::empty()) =~= Seq::<Rec>::empty());
        assert(flat(r@) =~= all_v);
        assert(all_v.len() == la as int);
    }
    r
}

/// The records of the first `u` segments are a prefix of all records.
pub proof fn lemma_flat_prefix(segs: Seq<Vec<Rec>>, u: int)
    requires 0 <= u <= segs.len(),
    ensures
        flat(segs.subrange(0, u)).len() <= flat(segs).len(),
        forall|q: int| 0 <= q < flat(segs.subrange(0, u)).len() ==> #[trigger] flat(segs.subrange(0, u))[q] == flat(segs)[q],
    decreases segs.len() - u,
{
    if u < segs.len() {
        lemma_flat_prefix(segs, u + 1);
        assert(segs.subrange(0, u + 1).drop_last() =~= segs.subrange(0, u));
        let a = flat(segs.subrange(0, u));
        let b = flat(segs.subrange(0, u + 1));
        assert(b == a + segs[u]@);
        assert forall|q: int| 0 <= q < a.len() implies #[trigger] a[q] == flat(segs)[q] by {
            assert(b[q] == a[q]);
        }
    } else {
        assert(segs.subrange(0, u) =~= segs);
    }
}

} // verus!
