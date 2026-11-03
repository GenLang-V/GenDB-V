//! From the final group table (the groups of all qualifying orders) to the statement's outcome (`finalize`): the SQL
//! error 22003 when a group counts more than int8 rows, otherwise one row (priority, count) per group, sorted by the
//! priority.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::limits::int8_max;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::exec::value::*;
use crate::exec::ast::EOrderKey;
use crate::exec::relational::order::{sort_rows_exec, view_keys};
use crate::bridge::order::{keys_ok, key_ok, all_keys_ok, lemma_sort_rows};
use crate::link::query::*;
use crate::agent::cols::*;
use crate::agent::lists::*;
use crate::agent::table::*;
use crate::agent::normal::*;

verus! {

/// The final table: the groups of the qualifying orders of all rows.
pub open spec fn final_ok(l: LCols, o: OCols, w: Win, pd: int, t1: int, reps: Seq<usize>, counts: Seq<u64>) -> bool {
    &&& win_of(w, pd, t1)
    &&& reps.len() == counts.len()
    &&& tbl_ok(o, reps, counts, reps.len() as int, q_list(l, o, w, 0, o.no as int))
}

/// The GROUP BY key of a representative row.
pub open spec fn key_row(o: OCols, r: usize) -> Row {
    seq![Val::Text(prio(o, r as int))]
}

/// The group keys of the table, slot by slot.
pub open spec fn table_keys(o: OCols, reps: Seq<usize>) -> Seq<Row> {
    reps.map_values(|r: usize| key_row(o, r))
}

/// The output row of a group.
pub open spec fn group_row(o: OCols, r: usize, n: u64) -> Row {
    seq![Val::Text(prio(o, r as int)), Val::Int(n as int)]
}

/// The final table's slots are the groups of the normal form, with their counts.
pub proof fn lemma_final_table(l: LCols, o: OCols, w: Win, pd: int, t1: int, reps: Seq<usize>, counts: Seq<u64>)
    requires final_ok(l, o, w, pd, t1, reps, counts),
    ensures ({
        let g = q4_spec(l, pd, t1);
        let xs = crows(o);
        let ks = table_keys(o, reps);
        &&& ks.len() == reps.len()
        &&& forall|t: int| 0 <= t < reps.len() ==> #[trigger] ks[t] == key_row(o, reps[t])
        &&& forall|t: int| 0 <= t < reps.len() ==> gcount(g, xs, #[trigger] key_row(o, reps[t])) == counts[t]
        &&& forall|t: int| 0 <= t < reps.len() ==> (#[trigger] reps[t]) < o.no
        &&& ks.no_duplicates()
        &&& forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g, xs, k) > 0
    }),
{
    let g = q4_spec(l, pd, t1);
    let xs = crows(o);
    let ks = table_keys(o, reps);
    let n = reps.len() as int;
    let p = q_list(l, o, w, 0, o.no as int);
    lemma_tbl_facts(o, reps, counts, n, p);
    assert(xs.subrange(0, o.no as int) =~= xs);
    assert forall|t: int| 0 <= t < n implies gcount(g, xs, #[trigger] key_row(o, reps[t])) == counts[t] by {
        lemma_gcount_list(l, o, w, pd, t1, 0, o.no as int, prio(o, reps[t] as int));
    }
    assert forall|a: int, b: int| 0 <= a < ks.len() && 0 <= b < ks.len() && a != b implies ks[a] != ks[b] by {
        assert(tkey(o, reps, a) != tkey(o, reps, b));
        if ks[a] == ks[b] {
            assert(ks[a][0] == ks[b][0]);
        }
    }
    assert forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g, xs, k) > 0 by {
        if ks.contains(k) {
            let t = choose|t: int| 0 <= t < ks.len() && ks[t] == k;
            assert(p.contains(reps[t]));
            let m = choose|m: int| 0 <= m < p.len() && p[m] == reps[t];
            lemma_cnt_pos(o, p, m, prio(o, reps[t] as int));
            lemma_gcount_list(l, o, w, pd, t1, 0, o.no as int, prio(o, reps[t] as int));
        }
        if gcount(g, xs, k) > 0 {
            if !(k.len() == 1 && k[0] is Text) {
                lemma_gcount_other(l, o, pd, t1, 0, o.no as int, k);
            } else {
                let kb = k[0]->Text_0;
                assert(k =~= seq![Val::Text(kb)]);
                lemma_gcount_list(l, o, w, pd, t1, 0, o.no as int, kb);
                lemma_cnt_witness(o, p, kb);
                let m = choose|m: int| 0 <= m < p.len() && prio(o, #[trigger] p[m] as int) == kb;
                assert(in_tbl(o, reps, n, prio(o, p[m] as int)));
                let s = choose|s: int| 0 <= s < n && tkey(o, reps, s) == prio(o, p[m] as int);
                assert(ks[s] == k);
            }
        }
    }
}

/// Within int8 counts the groups are inside `group_caps` (COUNT is the only aggregate).
pub proof fn lemma_group_caps(l: LCols, o: OCols, w: Win, pd: int, t1: int, reps: Seq<usize>, counts: Seq<u64>)
    requires
        final_ok(l, o, w, pd, t1, reps, counts),
        forall|t: int| 0 <= t < counts.len() ==> (#[trigger] counts[t]) <= int8_max(),
    ensures group_caps(q4_spec(l, pd, t1), crows(o)),
{
    let g = q4_spec(l, pd, t1);
    let xs = crows(o);
    let ks = table_keys(o, reps);
    lemma_final_table(l, o, w, pd, t1, reps, counts);
    assert forall|k: Row, j: int| #![trigger gcount(g, xs, k), g.aggs[j]] 0 <= j < g.aggs.len() && g.aggs[j] is Count implies gcount(g, xs, k) <= int8_max() by {
        if gcount(g, xs, k) > 0 {
            assert(ks.contains(k));
            let t = choose|t: int| 0 <= t < ks.len() && ks[t] == k;
            assert(gcount(g, xs, key_row(o, reps[t])) == counts[t]);
        }
    }
}

/// The output rows of the table, sorted by the ORDER BY keys, are an allowed output.
pub proof fn lemma_rows_result(l: LCols, o: OCols, w: Win, pd: int, t1: int, reps: Seq<usize>, counts: Seq<u64>, u: Seq<Row>)
    requires
        final_ok(l, o, w, pd, t1, reps, counts),
        u.len() == reps.len(),
        forall|t: int| 0 <= t < reps.len() ==> #[trigger] u[t] == group_row(o, reps[t], counts[t]),
    ensures result_ok(q4_spec(l, pd, t1), ast_order_keys(), 0, None, crows(o), sort_rows(ast_order_keys(), u)),
{
    let g = q4_spec(l, pd, t1);
    let xs = crows(o);
    let ks = table_keys(o, reps);
    let keys = ast_order_keys();
    let fams = seq![3int];
    lemma_final_table(l, o, w, pd, t1, reps, counts);
    assert forall|t: int| 0 <= t < u.len() implies keys_ok(keys, fams, #[trigger] u[t]) by {
        assert forall|i: int| 0 <= i < keys.len() implies #[trigger] key_ok(keys[i], fams[i], u[t]) by {
            assert(u[t][0] == Val::Text(prio(o, reps[t] as int)));
        }
    }
    lemma_sort_rows(keys, fams, u);
    let p = sort_rows(keys, u);
    lemma_gkeys(g, xs);
    lemma_nodup_same_multiset(ks, gkeys(g, xs));
    let f = |k: Row| out_row(g, xs, k);
    lemma_map_multiset(ks, gkeys(g, xs), f);
    assert forall|t: int| 0 <= t < u.len() implies #[trigger] u[t] == ks.map_values(f)[t] by {
        let k = ks[t];
        assert(k == key_row(o, reps[t]));
        assert(gcount(g, xs, k) == counts[t]);
        let fr = full_row(g, xs, k);
        assert(agg_outs(g, xs, k) =~= seq![Val::Int(counts[t] as int)]);
        lemma_select_identity(fr, seq![0nat, 1nat]);
        assert(fr =~= group_row(o, reps[t], counts[t]));
    }
    assert(u =~= ks.map_values(f));
    assert(result_rows(g, xs) == gkeys(g, xs).map_values(f));
    lemma_result_ok_from(g, keys, 0, None, xs, p);
    lemma_slice_all(p);
}

/// What `finalize` decides.
pub enum Outcome {
    /// The result rows, sorted.
    Rows(Vec<Vec<EVal>>),
    /// Some group counts more than int8 rows.
    CountError,
}

/// The ORDER BY key `o_orderpriority` as an executable key.
fn order_keys() -> (keys: Vec<EOrderKey>)
    ensures view_keys(keys@) == ast_order_keys(),
{
    let mut keys: Vec<EOrderKey> = Vec::new();
    keys.push(EOrderKey { col: 0, desc: false, nulls_first: false });
    proof {
        assert(view_keys(keys@) =~= ast_order_keys());
    }
    keys
}

/// The priority bytes of row `r`, copied.
fn prio_bytes(o: &OCols, r: usize) -> (v: Vec<u8>)
    requires ocols_wf(*o), r < o.no,
    ensures v@ == prio(*o, r as int),
{
    let (a, b) = prio_extent(o, r);
    let mut v: Vec<u8> = Vec::new();
    let mut i = a;
    while i < b
        invariant a <= i <= b <= o.pbytes@.len(), v@ == o.pbytes@.subrange(a as int, i as int),
        decreases b - i,
    {
        v.push(o.pbytes[i]);
        i = i + 1;
        proof {
            assert(v@ =~= o.pbytes@.subrange(a as int, i as int));
        }
    }
    v
}

/// The outcome of the statement from the final table.
pub fn finalize(o: &OCols, reps: &Vec<usize>, counts: &Vec<u64>, Ghost(l): Ghost<LCols>, Ghost(w): Ghost<Win>,
    Ghost(pd): Ghost<int>, Ghost(t1): Ghost<int>) -> (r: Outcome)
    requires
        ocols_wf(*o),
        final_ok(l, *o, w, pd, t1, reps@, counts@),
    ensures
        r matches Outcome::Rows(rows) ==> group_caps(q4_spec(l, pd, t1), crows(*o))
            && result_ok(q4_spec(l, pd, t1), ast_order_keys(), 0, None, crows(*o), view_rows(rows@)),
        r is CountError ==> exists|k: Row| #[trigger] gcount(q4_spec(l, pd, t1), crows(*o), k) > int8_max(),
{
    proof {
        lemma_final_table(l, *o, w, pd, t1, reps@, counts@);
    }
    let n = reps.len();
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut t: usize = 0;
    while t < n
        invariant
            ocols_wf(*o),
            final_ok(l, *o, w, pd, t1, reps@, counts@),
            n == reps@.len(),
            n == counts@.len(),
            forall|x: int| 0 <= x < n ==> (#[trigger] reps@[x]) < o.no,
            forall|x: int| 0 <= x < n ==> gcount(q4_spec(l, pd, t1), crows(*o), #[trigger] key_row(*o, reps@[x])) == counts@[x],
            t <= n,
            rows@.len() == t,
            forall|x: int| 0 <= x < t ==> (#[trigger] counts@[x]) <= int8_max(),
            forall|x: int| 0 <= x < t ==> view_row((#[trigger] rows@[x])@) == group_row(*o, reps@[x], counts@[x]),
        decreases n - t,
    {
        let c = counts[t];
        if c > 0x7fff_ffff_ffff_ffff {
            proof {
                assert(gcount(q4_spec(l, pd, t1), crows(*o), key_row(*o, reps@[t as int])) > int8_max());
            }
            return Outcome::CountError;
        }
        let v = prio_bytes(o, reps[t]);
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Text(v));
        row.push(EVal::Int(c as i64));
        proof {
            assert(view_row(row@) =~= group_row(*o, reps@[t as int], c));
        }
        rows.push(row);
        t = t + 1;
    }
    let keys = order_keys();
    let ghost u = view_rows(rows@);
    let sorted = sort_rows_exec(&keys, rows);
    proof {
        assert forall|x: int| 0 <= x < n implies #[trigger] u[x] == group_row(*o, reps@[x], counts@[x]) by {}
        lemma_rows_result(l, *o, w, pd, t1, reps@, counts@, u);
        lemma_group_caps(l, *o, w, pd, t1, reps@, counts@);
    }
    Outcome::Rows(sorted)
}

} // verus!
