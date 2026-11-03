//! From the groups and the selection to the fixed claim, for every database bound to the stored parts.
//!
//! The executable code establishes, over the stored columns only (`plan_facts`): the selected suppliers are exactly
//! those with a nation named `$1`, their counts are the key counts over all lineitem rows, and the groups list every
//! name with a positive COUNT once, with its COUNT capped at `CAP` (`groups::grp_ok`, `lemma_group_counts`). Then:
//! a group at `CAP` makes the statement's meaning the error 22003 (`lemma_answer_err`); otherwise the body is the
//! normal form's result rows (`denot::lemma_body_ok`), whose rows are exactly the groups' rows (`lemma_all_rows`),
//! and a sorted top-100 of them is a slice of a sorted permutation (`common::topk_spec`), i.e. an allowed output
//! (`lemma_answer_rows`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::limits::int8_max;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::exec::value::{EVal, view_row};
use crate::query::{query_spec_at, param_domain};
use crate::link::query::*;
use crate::bridge::order::all_keys_ok;
use crate::agent::cols::*;
use crate::agent::nf::*;
use crate::agent::denot::*;
use crate::agent::sums::*;
use crate::agent::scan::*;
use crate::agent::plan::sel_exact;
use crate::agent::groups::*;
use crate::agent::topk::*;
use crate::agent::common::topk_spec::{lemma_topk_slice, lemma_nodup_len};

verus! {

/// What the executable code establishes over the stored columns.
pub open spec fn plan_facts(sv: StoresView, p: Seq<u8>, c: Cols, m: SupMap, tot: Seq<u64>, grep: Seq<usize>, gt: Seq<u64>) -> bool {
    &&& cols_ok(c, sv)
    &&& sup_ok(m, sv)
    &&& sel_exact(m, sv, p)
    &&& tot_ok(sv, m, tot)
    &&& grp_ok(sv, m, tot, grep, gt, m.nsel as int)
}

/// The facts, assembled.
pub proof fn lemma_plan_facts(sv: StoresView, p: Seq<u8>, c: Cols, m: SupMap, tot: Seq<u64>, grep: Seq<usize>, gt: Seq<u64>)
    requires cols_ok(c, sv), sup_ok(m, sv), sel_exact(m, sv, p), tot_ok(sv, m, tot), grp_ok(sv, m, tot, grep, gt, m.nsel as int),
    ensures
        plan_facts(sv, p, c, m, tot, grep, gt),
        forall|g: int| 0 <= g < gt.len() ==> #[trigger] gt[g] <= CAP,
        grp_rows_ok(c, m, grep, gt, sv),
{
    assert forall|g: int| 0 <= g < gt.len() implies #[trigger] gt[g] <= CAP by {
        assert(gt[g] as int == capped(csel(sv, m, tot, gname(sv, m, grep[g] as int), m.nsel as int)));
    }
}

/// The first group whose capped COUNT is `CAP`, if any.
pub fn find_over(gt: &Vec<u64>) -> (r: Option<usize>)
    ensures
        r matches Some(g) ==> g < gt@.len() && gt@[g as int] >= CAP,
        r is None ==> forall|h: int| 0 <= h < gt@.len() ==> #[trigger] gt@[h] < CAP,
{
    let mut g: usize = 0;
    while g < gt.len()
        invariant g <= gt@.len(), forall|h: int| 0 <= h < g ==> #[trigger] gt@[h] < CAP,
        decreases gt@.len() - g,
    {
        if gt[g] >= CAP {
            return Some(g);
        }
        g = g + 1;
    }
    None
}

/// The groups in COUNT terms: each group's capped COUNT is positive, and every name with a positive COUNT is a
/// group's.
pub proof fn lemma_group_counts(sv: StoresView, p: Seq<u8>, c: Cols, m: SupMap, tot: Seq<u64>, grep: Seq<usize>, gt: Seq<u64>)
    requires plan_facts(sv, p, c, m, tot, grep, gt),
    ensures
        forall|g: int| 0 <= g < grep.len() ==> #[trigger] gt[g] as int == capped(gc(sv, p, gname(sv, m, grep[g] as int)) as int)
            && gc(sv, p, gname(sv, m, grep[g] as int)) > 0,
        forall|nm: Seq<u8>| #[trigger] gc(sv, p, nm) > 0 ==> exists|g: int| 0 <= g < grep.len() && gname(sv, m, #[trigger] grep[g] as int) == nm,
{
    let k = m.nsel as int;
    assert forall|g: int| 0 <= g < grep.len() implies #[trigger] gt[g] as int == capped(gc(sv, p, gname(sv, m, grep[g] as int)) as int)
        && gc(sv, p, gname(sv, m, grep[g] as int)) > 0 by {
        lemma_gc_sel(sv, p, m, tot, gname(sv, m, grep[g] as int));
    }
    assert forall|nm: Seq<u8>| #[trigger] gc(sv, p, nm) > 0 implies exists|g: int| 0 <= g < grep.len() && gname(sv, m, #[trigger] grep[g] as int) == nm by {
        lemma_gc_sel(sv, p, m, tot, nm);
        lemma_csel_pos(sv, m, tot, nm, k);
        let cj = choose|cj: int| 0 <= cj < k && #[trigger] gname(sv, m, cj) == nm && tot[cj] > 0;
        let g = choose|g: int| 0 <= g < grep.len() && #[trigger] gname(sv, m, grep[g] as int) == gname(sv, m, cj);
        assert(gname(sv, m, grep[g] as int) == nm);
    }
}

/// A group at `CAP`: the statement's meaning is the error 22003 on every bound database.
pub proof fn lemma_answer_err(sv: StoresView, ps: Seq<Literal>, c: Cols, m: SupMap, tot: Seq<u64>, grep: Seq<usize>,
    gt: Seq<u64>, g0: int)
    requires
        param_domain(ps), plan_facts(sv, pb_of(ps), c, m, tot, grep, gt), 0 <= g0 < grep.len(), gt[g0] == CAP,
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==>
            ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
{
    let p = pb_of(ps);
    let nm = gname(sv, m, grep[g0] as int);
    lemma_group_counts(sv, p, c, m, tot, grep, gt);
    assert(gc(sv, p, nm) > int8_max());
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)) by {
        lemma_gcount_gc(sv, db, p, nm);
        lemma_body_count_error(sv, db, ps, seq![Val::Text(nm)]);
    }
}

/// The result row of the group key `[nm]`: the name and its COUNT.
proof fn lemma_out_row(sv: StoresView, db: Database, p: Seq<u8>, nm: Seq<u8>)
    requires bound_db(sv, db),
    ensures out_row(q_spec(sv, p), q_xs(db), seq![Val::Text(nm)]) == seq![Val::Text(nm), Val::Int(gc(sv, p, nm) as int)],
{
    let g = q_spec(sv, p);
    let xs = q_xs(db);
    let k = seq![Val::Text(nm)];
    lemma_gcount_gc(sv, db, p, nm);
    let f = full_row(g, xs, k);
    assert(agg_outs(g, xs, k) =~= seq![Val::Int(gcount(g, xs, k) as int)]);
    assert(f =~= seq![Val::Text(nm), Val::Int(gc(sv, p, nm) as int)]);
    lemma_select_identity(f, seq![0nat, 1nat]);
}

/// Inside the COUNT domain, the result rows are exactly the groups' rows, without duplicates.
proof fn lemma_all_rows(sv: StoresView, db: Database, p: Seq<u8>, c: Cols, m: SupMap, tot: Seq<u64>, grep: Seq<usize>,
    gt: Seq<u64>)
    requires
        bound_db(sv, db), plan_facts(sv, p, c, m, tot, grep, gt),
        forall|g: int| 0 <= g < gt.len() ==> #[trigger] gt[g] < CAP,
    ensures ({
        let all = result_rows(q_spec(sv, p), q_xs(db));
        let rows = grows(sv, m, grep, gt);
        &&& all.no_duplicates()
        &&& rows.no_duplicates()
        &&& forall|x: Row| #[trigger] all.contains(x) <==> rows.contains(x)
        &&& all.len() == rows.len()
        &&& forall|g: int| 0 <= g < rows.len() ==> #[trigger] rows[g] == out_row(q_spec(sv, p), q_xs(db), seq![Val::Text(gname(sv, m, grep[g] as int))])
    }),
{
    let gs = q_spec(sv, p);
    let xs = q_xs(db);
    let gk = gkeys(gs, xs);
    let all = result_rows(gs, xs);
    let rows = grows(sv, m, grep, gt);
    lemma_group_counts(sv, p, c, m, tot, grep, gt);
    lemma_gkeys(gs, xs);
    assert(all == gk.map_values(|k: Row| out_row(gs, xs, k)));
    // each group row is the result row of its name
    assert forall|g: int| 0 <= g < rows.len() implies #[trigger] rows[g] == out_row(gs, xs, seq![Val::Text(gname(sv, m, grep[g] as int))]) by {
        let nm = gname(sv, m, grep[g] as int);
        lemma_out_row(sv, db, p, nm);
        assert(gt[g] as int == gc(sv, p, nm));
    }
    // the result rows are the group rows
    assert forall|x: Row| #[trigger] all.contains(x) implies rows.contains(x) by {
        let i = choose|i: int| 0 <= i < all.len() && all[i] == x;
        let k = gk[i];
        assert(gk.contains(k));
        lemma_gcount_key(sv, db, p, k);
        let nm = k[0]->Text_0;
        lemma_gcount_gc(sv, db, p, nm);
        let g = choose|g: int| 0 <= g < grep.len() && gname(sv, m, #[trigger] grep[g] as int) == nm;
        assert(rows[g] == x);
    }
    assert forall|x: Row| #[trigger] rows.contains(x) implies all.contains(x) by {
        let g = choose|g: int| 0 <= g < rows.len() && rows[g] == x;
        let nm = gname(sv, m, grep[g] as int);
        let k = seq![Val::Text(nm)];
        lemma_gcount_gc(sv, db, p, nm);
        assert(gk.contains(k));
        let i = choose|i: int| 0 <= i < gk.len() && gk[i] == k;
        assert(all[i] == x);
    }
    // no duplicates: different keys give different first columns
    assert(all.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < all.len() && 0 <= j < all.len() && i != j implies all[i] != all[j] by {
            let (ki, kj) = (gk[i], gk[j]);
            assert(gk.contains(ki) && gk.contains(kj));
            lemma_gcount_key(sv, db, p, ki);
            lemma_gcount_key(sv, db, p, kj);
            lemma_out_row(sv, db, p, ki[0]->Text_0);
            lemma_out_row(sv, db, p, kj[0]->Text_0);
            if all[i] == all[j] {
                assert(all[i][0] == all[j][0]);
                assert(ki == kj);
            }
        }
    }
    assert(rows.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && i != j implies rows[i] != rows[j] by {
            assert(gname(sv, m, grep[i] as int) != gname(sv, m, grep[j] as int));
            assert(rows[i][0] != rows[j][0]);
        }
    }
    lemma_nodup_len(all, rows);
}

/// Inside the COUNT domain, the selected group rows are an allowed output on every bound database.
pub proof fn lemma_answer_rows(sv: StoresView, ps: Seq<Literal>, c: Cols, m: SupMap, tot: Seq<u64>, grep: Seq<usize>,
    gt: Seq<u64>, sel: Seq<usize>, out: Seq<Row>)
    requires
        param_domain(ps), plan_facts(sv, pb_of(ps), c, m, tot, grep, gt),
        forall|g: int| 0 <= g < gt.len() ==> #[trigger] gt[g] < CAP,
        top_inv(grows(sv, m, grep, gt), grep.len() as int, sel),
        out == sel.map_values(|g: usize| grows(sv, m, grep, gt)[g as int]),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    let p = pb_of(ps);
    let gs = q_spec(sv, p);
    let rows = grows(sv, m, grep, gt);
    let keys = q_order_keys();
    lemma_group_counts(sv, p, c, m, tot, grep, gt);
    lemma_grows_ok(sv, m, grep, gt);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)) by {
        let xs = q_xs(db);
        let all = result_rows(gs, xs);
        // the COUNT domain
        assert(group_caps(gs, xs)) by {
            assert forall|k: Row, j: int| #![trigger gcount(gs, xs, k), gs.aggs[j]] 0 <= j < gs.aggs.len() && gs.aggs[j] is Count
                implies gcount(gs, xs, k) <= int8_max() by {
                if gcount(gs, xs, k) > 0 {
                    lemma_gcount_key(sv, db, p, k);
                    let nm = k[0]->Text_0;
                    lemma_gcount_gc(sv, db, p, nm);
                    let g = choose|g: int| 0 <= g < grep.len() && gname(sv, m, #[trigger] grep[g] as int) == nm;
                    assert(gt[g] < CAP);
                }
            }
            assert forall|k: Row, j: int| 0 <= j < gs.aggs.len() && !(gs.aggs[j] is Count) implies #[trigger] gabs(gs, xs, k, j) <= crate::link::expr::i128_max() by {
                assert(gs.aggs[0] is Count);
            }
            assert forall|k: Row, j: int| 0 <= j < gs.aggs.len() && gs.aggs[j] is Avg implies
                crate::spec::fns::div::num_div_fits(#[trigger] gsum(gs, xs, k, j), gs.aggs[j]->Avg_scale, gcount(gs, xs, k) as int, 0) by {
                assert(gs.aggs[0] is Count);
            }
        }
        lemma_body_ok(sv, db, ps);
        lemma_all_rows(sv, db, p, c, m, tot, grep, gt);
        lemma_query_shape(ps);
        // the selection as rows
        assert(out.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < out.len() && 0 <= b < out.len() && a != b implies out[a] != out[b] by {
                assert(sel[a] != sel[b]);
                assert((sel[a] as int) < rows.len() && (sel[b] as int) < rows.len());
            }
        }
        assert forall|t: int| 0 <= t < out.len() implies all.contains(#[trigger] out[t]) by {
            assert((sel[t] as int) < rows.len());
            assert(rows.contains(rows[sel[t] as int]));
        }
        assert(all_keys_ok(keys, ofams(), all)) by {
            assert forall|i: int| 0 <= i < all.len() implies crate::bridge::order::keys_ok(keys, ofams(), #[trigger] all[i]) by {
                assert(all.contains(all[i]));
                let g = choose|g: int| 0 <= g < rows.len() && rows[g] == all[i];
            }
        }
        reveal(ccmp);
        assert(sorted_by(keys, out)) by {
            assert forall|a: int, b: int| 0 <= a < b < out.len() implies keys_cmp(keys, #[trigger] out[a], #[trigger] out[b]) <= 0 by {
                assert(ccmp(rows, sel[a] as int, sel[b] as int) <= 0);
            }
        }
        if out.len() > 0 {
            assert forall|x: Row| #[trigger] all.contains(x) && !out.contains(x) implies keys_cmp(keys, out.last(), x) <= 0 by {
                let g = choose|g: int| 0 <= g < rows.len() && rows[g] == x;
                if sel.contains(g as usize) {
                    let t = choose|t: int| 0 <= t < sel.len() && sel[t] == g as usize;
                    assert(out[t] == x);
                }
                let a = sel.len() - 1;
                assert(ccmp(rows, sel[a] as int, g) <= 0);
                assert(out.last() == rows[sel[a] as int]);
            }
        }
        lemma_topk_slice(keys, ofams(), all, out, 100);
        let pm = choose|pm: Seq<Row>| #![trigger sorted_by(keys, pm)]
            pm.to_multiset() == all.to_multiset() && sorted_by(keys, pm) && out == slice_rows(pm, 0, Some(100nat));
        assert(result_ok(gs, keys, 0, Some(100nat), xs, out));
        lemma_ordered_link(db, query_spec_at(ps), gs, xs, out);
    }
}

// ------------------------------------------------------------------------------------------------ output rows

/// The bytes of supplier row `s`'s name.
fn name_bytes(c: &Cols, s: usize, Ghost(sv): Ghost<StoresView>) -> (v: Vec<u8>)
    requires cols_ok(*c, sv), s < c.ns,
    ensures v@ == sname(sv, s as int),
{
    let ghost t = sname_col(sv);
    let a = c.snoff[s];
    let b = c.snoff[s + 1];
    let blen = c.snb.len();
    proof { assert(0 <= t.offsets[s as int] <= t.offsets[s + 1] <= t.bytes.len()); }
    let (au, bu) = (a as usize, b as usize);
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = au;
    while i < bu
        invariant
            cols_ok(*c, sv), t == sname_col(sv), s < c.ns, blen == c.snb@.len(), au == a, bu == b,
            a == t.offsets[s as int], b == t.offsets[s + 1], 0 <= a <= b <= blen, au <= i <= bu,
            v@ == c.snb@.subrange(au as int, i as int),
        decreases bu - i,
    {
        v.push(c.snb[i]);
        proof { assert(v@ =~= c.snb@.subrange(au as int, i + 1)); }
        i = i + 1;
    }
    v
}

/// The output rows of the selected groups.
pub fn out_rows(c: &Cols, m: &SupMap, grep: &Vec<usize>, gt: &Vec<u64>, sel: &Vec<usize>, Ghost(sv): Ghost<StoresView>)
    -> (rows: Vec<Vec<EVal>>)
    requires
        grp_rows_ok(*c, *m, grep@, gt@, sv),
        forall|t: int| 0 <= t < sel@.len() ==> (#[trigger] sel@[t] as int) < grep@.len(),
        forall|g: int| 0 <= g < gt@.len() ==> #[trigger] gt@[g] < CAP,
    ensures
        view_rows(rows@) == sel@.map_values(|g: usize| grows(sv, *m, grep@, gt@)[g as int]),
{
    let ghost want = sel@.map_values(|g: usize| grows(sv, *m, grep@, gt@)[g as int]);
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut t: usize = 0;
    while t < sel.len()
        invariant
            grp_rows_ok(*c, *m, grep@, gt@, sv),
            forall|u: int| 0 <= u < sel@.len() ==> (#[trigger] sel@[u] as int) < grep@.len(),
            forall|g: int| 0 <= g < gt@.len() ==> #[trigger] gt@[g] < CAP,
            want == sel@.map_values(|g: usize| grows(sv, *m, grep@, gt@)[g as int]),
            t <= sel@.len(), rows@.len() == t,
            forall|u: int| 0 <= u < t ==> view_row(#[trigger] rows@[u]@) == want[u],
        decreases sel@.len() - t,
    {
        let g = sel[t];
        let nm = name_bytes(c, m.sel[grep[g]], Ghost(sv));
        let cnt = gt[g];
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Text(nm));
        row.push(EVal::Int(cnt as i64));
        proof {
            assert(view_row(row@) =~= seq![Val::Text(gname(sv, *m, grep@[g as int] as int)), Val::Int(cnt as int)]);
            assert(want[t as int] == grows(sv, *m, grep@, gt@)[g as int]);
        }
        rows.push(row);
        t = t + 1;
    }
    proof {
        assert(view_rows(rows@) =~= want) by {
            assert forall|u: int| 0 <= u < want.len() implies view_rows(rows@)[u] == want[u] by {
                assert(view_rows(rows@)[u] == view_row(rows@[u]@));
            }
        }
    }
    rows
}

} // verus!
