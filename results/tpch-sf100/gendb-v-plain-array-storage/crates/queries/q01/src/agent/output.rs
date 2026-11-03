//! From the merged group table of all rows to the statement's outcome (`finalize`): a COUNT beyond int8 (the SQL
//! error 22003), a group outside the capacity domain (SUM mass beyond `i128` or an AVG division outside its
//! executable domain), or the result rows: one row per group, sorted by (returnflag, linestatus).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::limits::*;
use crate::spec::numeric::abs;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::fns::div::num_div_fits;
use crate::exec::value::*;
use crate::exec::ast::EOrderKey;
use crate::exec::relational::order::{sort_rows_exec, view_keys};
use crate::bridge::order::{keys_ok, key_ok, all_keys_ok, lemma_sort_rows};
use crate::bridge::typing::val_family;
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::gendb_entry::work::text_bytes;
use crate::agent::normal::*;
use crate::agent::columns::*;
use crate::agent::accum::*;
use crate::agent::scan::*;

verus! {

/// The merged table of all rows.
pub open spec fn full_table(pd: int, c: Cols, gt: Seq<Acc>) -> bool {
    table_ok(pd, c, 0, c.n as int, gt, gt.len() as int)
}

/// The group keys of the table, slot by slot.
pub open spec fn table_keys(c: Cols, gt: Seq<Acc>) -> Seq<Row> {
    gt.map_values(|a: Acc| slot_key(c, a))
}

/// Witness of `Capacity` from the groups: every group within int8, and one group's aggregate `j` outside its
/// capacity condition (SUM mass of disc_price / charge beyond `i128`, or an AVG division outside its domain).
pub open spec fn group_capacity(pd: int, xs: Seq<Row>) -> bool {
    &&& forall|k: Row| #[trigger] gcount(q1_spec(pd), xs, k) <= int8_max()
    &&& exists|k: Row, j: int| #[trigger] group_violation(pd, xs, k, j)
}

/// Group `k`'s aggregate `j` leaves its capacity condition.
pub open spec fn group_violation(pd: int, xs: Seq<Row>, k: Row, j: int) -> bool {
    let g = q1_spec(pd);
    &&& 2 <= j <= 6
    &&& gcount(g, xs, k) > 0
    &&& (j == 2 || j == 3) ==> gabs(g, xs, k, j) > i128_max()
    &&& (4 <= j <= 6) ==> !num_div_fits(gsum(g, xs, k, j), 2, gcount(g, xs, k) as int, 0)
}

/// A row of group `k` gives it a positive count.
pub proof fn lemma_hit_count(g: QuerySpec, rows: Seq<Row>, m: int, k: Row)
    requires 0 <= m < rows.len(), hit(g, rows[m], k),
    ensures gcount(g, rows, k) > 0,
    decreases rows.len(),
{
    if m < rows.len() - 1 {
        assert(rows.drop_last()[m] == rows[m]);
        lemma_hit_count(g, rows.drop_last(), m, k);
    }
}

/// The merged table: its slots are the groups of all rows, exactly once each, with their accumulators.
pub proof fn lemma_full_table(pd: int, c: Cols, gt: Seq<Acc>)
    requires full_table(pd, c, gt),
    ensures
        range_rows(c, 0, c.n as int) == crows(c),
        forall|s: int| 0 <= s < gt.len() ==> acc_ok(pd, crows(c), slot_key(c, #[trigger] gt[s]), gt[s]),
        table_keys(c, gt).len() == gt.len(),
        forall|s: int| 0 <= s < gt.len() ==> #[trigger] table_keys(c, gt)[s] == slot_key(c, gt[s]),
        table_keys(c, gt).no_duplicates(),
        forall|k: Row| #[trigger] table_keys(c, gt).contains(k) <==> gcount(q1_spec(pd), crows(c), k) > 0,
        forall|s: int| 0 <= s < gt.len() ==> gcount(q1_spec(pd), crows(c), slot_key(c, #[trigger] gt[s])) > 0,
        forall|s: int| 0 <= s < gt.len() ==> (#[trigger] gt[s]).rep < c.n,
{
    let g = q1_spec(pd);
    let xs = crows(c);
    let ks = table_keys(c, gt);
    lemma_crows(c);
    assert(range_rows(c, 0, c.n as int) =~= crows(c));
    assert forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g, xs, k) > 0 by {
        if ks.contains(k) {
            let s = choose|s: int| 0 <= s < ks.len() && ks[s] == k;
            let r = gt[s].rep as int;
            assert(hit(g, xs[r], k));
            lemma_hit_count(g, xs, r, k);
        }
        if gcount(g, xs, k) > 0 {
            lemma_count_witness(g, xs, k);
            let m = choose|m: int| 0 <= m < xs.len() && #[trigger] hit(g, xs[m], k);
            assert(q1_qual(pd, crow(c, m)));
            let s = choose|s: int| 0 <= s < gt.len() && key_of(c, m) == slot_key(c, #[trigger] gt[s]);
            assert(ks[s] == k);
        }
    }
    assert forall|a: int, b: int| 0 <= a < ks.len() && 0 <= b < ks.len() && a != b implies ks[a] != ks[b] by {
        assert(slot_key(c, gt[a]) != slot_key(c, gt[b]));
    }
    assert forall|s: int| 0 <= s < gt.len() implies gcount(g, xs, slot_key(c, #[trigger] gt[s])) > 0 by {
        assert(ks[s] == slot_key(c, gt[s]));
        assert(ks.contains(ks[s]));
    }
}

/// Groups not in the table have no rows; so the table's counts bound every group's count.
pub proof fn lemma_counts_bounded(pd: int, c: Cols, gt: Seq<Acc>)
    requires
        full_table(pd, c, gt),
        forall|s: int| 0 <= s < gt.len() ==> (#[trigger] gt[s]).cnt <= int8_max(),
    ensures forall|k: Row| #[trigger] gcount(q1_spec(pd), crows(c), k) <= int8_max(),
{
    lemma_full_table(pd, c, gt);
    assert forall|k: Row| #[trigger] gcount(q1_spec(pd), crows(c), k) <= int8_max() by {
        if gcount(q1_spec(pd), crows(c), k) > 0 {
            let ks = table_keys(c, gt);
            assert(ks.contains(k));
            let s = choose|s: int| 0 <= s < ks.len() && ks[s] == k;
            assert(acc_ok(pd, crows(c), slot_key(c, gt[s]), gt[s]));
        }
    }
}

/// Aggregates 4 and 5 (AVG of quantity and price) have the arguments of aggregates 0 and 1.
pub proof fn lemma_gsum_alias(pd: int, xs: Seq<Row>, k: Row)
    ensures
        gsum(q1_spec(pd), xs, k, 4) == gsum(q1_spec(pd), xs, k, 0),
        gsum(q1_spec(pd), xs, k, 5) == gsum(q1_spec(pd), xs, k, 1),
    decreases xs.len(),
{
    if xs.len() > 0 {
        lemma_gsum_alias(pd, xs.drop_last(), k);
    }
}

/// The absolute mass of a column-coefficient aggregate is at most `count * 10^15`.
pub proof fn lemma_gabs_columns(pd: int, xs: Seq<Row>, k: Row, j: int)
    requires
        j == 0 || j == 1 || j == 4 || j == 5 || j == 6,
        forall|i: int| 0 <= i < xs.len() ==> src_row_ok(#[trigger] xs[i]),
    ensures gabs(q1_spec(pd), xs, k, j) <= gcount(q1_spec(pd), xs, k) * coeff_bound(),
    decreases xs.len(),
{
    let g = q1_spec(pd);
    if xs.len() > 0 {
        let d = xs.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies src_row_ok(#[trigger] d[i]) by {
            assert(d[i] == xs[i]);
        }
        lemma_gabs_columns(pd, d, k, j);
        let x = xs.last();
        assert(src_row_ok(xs[xs.len() - 1]));
        assert(abs(q1_arg(j, x)) < coeff_bound());
    }
}

/// Inside the checked conditions the groups are inside `group_caps`.
pub proof fn lemma_group_caps(pd: int, c: Cols, gt: Seq<Acc>)
    requires
        cols_wf(c),
        full_table(pd, c, gt),
        forall|s: int| 0 <= s < gt.len() ==> (#[trigger] gt[s]).cnt <= int8_max(),
        forall|s: int| 0 <= s < gt.len() ==> !(#[trigger] gt[s]).over_dp && !gt[s].over_ch,
        forall|s: int, j: int| 0 <= s < gt.len() && 4 <= j <= 6 ==>
            num_div_fits(#[trigger] gsum(q1_spec(pd), crows(c), slot_key(c, gt[s]), j), 2, gt[s].cnt as int, 0),
    ensures group_caps(q1_spec(pd), crows(c)),
{
    let g = q1_spec(pd);
    let xs = crows(c);
    let ks = table_keys(c, gt);
    lemma_full_table(pd, c, gt);
    lemma_counts_bounded(pd, c, gt);
    lemma_crows(c);
    assert forall|i: int| 0 <= i < xs.len() implies src_row_ok(#[trigger] xs[i]) by {
        lemma_crow_ok(c, i);
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
        if gcount(g, xs, k) == 0 {
            lemma_zero_count(g, xs, k, j);
        } else if j == 2 || j == 3 {
            assert(ks.contains(k));
            let s = choose|s: int| 0 <= s < ks.len() && ks[s] == k;
            assert(acc_ok(pd, xs, slot_key(c, gt[s]), gt[s]));
        } else {
            lemma_gabs_columns(pd, xs, k, j);
            assert(gcount(g, xs, k) * coeff_bound() <= int8_max() * coeff_bound()) by (nonlinear_arith)
                requires gcount(g, xs, k) <= int8_max();
        }
    }
    assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && g.aggs[j] is Avg implies
        num_div_fits(#[trigger] gsum(g, xs, k, j), g.aggs[j]->Avg_scale, gcount(g, xs, k) as int, 0) by {
        if gcount(g, xs, k) > 0 {
            assert(ks.contains(k));
            let s = choose|s: int| 0 <= s < ks.len() && ks[s] == k;
            assert(acc_ok(pd, xs, slot_key(c, gt[s]), gt[s]));
            assert(num_div_fits(gsum(g, xs, slot_key(c, gt[s]), j), 2, gt[s].cnt as int, 0));
        }
    }
}

/// The output row of a group, spelled out.
pub open spec fn group_row(pd: int, xs: Seq<Row>, k: Row) -> Row {
    let g = q1_spec(pd);
    let n = gcount(g, xs, k);
    seq![
        k[0], k[1],
        Val::Num { coeff: gsum(g, xs, k, 0), scale: 2 },
        Val::Num { coeff: gsum(g, xs, k, 1), scale: 2 },
        Val::Num { coeff: gsum(g, xs, k, 2), scale: 4 },
        Val::Num { coeff: gsum(g, xs, k, 3), scale: 6 },
        avg_of(gsum(g, xs, k, 4), 2, n),
        avg_of(gsum(g, xs, k, 5), 2, n),
        avg_of(gsum(g, xs, k, 6), 2, n),
        Val::Int(n as int)
    ]
}

/// `out_row` of a group with rows and a two-column key.
pub proof fn lemma_out_row(pd: int, xs: Seq<Row>, k: Row)
    requires gcount(q1_spec(pd), xs, k) > 0, k.len() == 2,
    ensures out_row(q1_spec(pd), xs, k) == group_row(pd, xs, k),
{
    let g = q1_spec(pd);
    let f = full_row(g, xs, k);
    let a = agg_outs(g, xs, k);
    assert(a.len() == 8);
    lemma_select_identity(f, q1_outs());
    assert(f =~= group_row(pd, xs, k));
}

/// Copies a byte slice.
fn copy_bytes(b: &[u8]) -> (v: Vec<u8>)
    ensures v@ == b@,
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < b.len()
        invariant i <= b@.len(), v@ == b@.subrange(0, i as int),
        decreases b@.len() - i,
    {
        v.push(b[i]);
        i = i + 1;
        proof {
            assert(v@ =~= b@.subrange(0, i as int));
        }
    }
    proof {
        assert(b@.subrange(0, b@.len() as int) =~= b@);
    }
    v
}

/// The key values of row `r` as output values.
fn key_values(c: &Cols, r: usize) -> (out: (EVal, EVal))
    requires cols_wf(*c), r < c.n,
    ensures out.0@ == key_of(*c, r as int)[0], out.1@ == key_of(*c, r as int)[1],
{
    proof {
        lemma_crow(*c, r as int);
        assert(0 <= rf_view(*c).offsets[r as int] <= rf_view(*c).offsets[r + 1] <= rf_view(*c).bytes.len());
        assert(0 <= ls_view(*c).offsets[r as int] <= ls_view(*c).offsets[r + 1] <= ls_view(*c).bytes.len());
    }
    let rf = TextCol { offsets: c.rf_offsets, bytes: c.rf_bytes };
    let ls = TextCol { offsets: c.ls_offsets, bytes: c.ls_bytes };
    let a = copy_bytes(text_bytes(&rf, r));
    let b = copy_bytes(text_bytes(&ls, r));
    (EVal::Text(a), EVal::Text(b))
}

/// What `finalize` decides.
pub enum Outcome {
    /// The result rows, sorted.
    Rows(Vec<Vec<EVal>>),
    /// Some group counts more than int8 rows.
    CountError,
    /// Some group is outside the capacity domain (`group_capacity`).
    GroupCapacity,
}

/// The ORDER BY keys `(l_returnflag, l_linestatus)` as executable keys.
fn order_keys() -> (keys: Vec<EOrderKey>)
    ensures view_keys(keys@) == ast_order_keys(),
{
    let mut keys: Vec<EOrderKey> = Vec::new();
    keys.push(EOrderKey { col: 0, desc: false, nulls_first: false });
    keys.push(EOrderKey { col: 1, desc: false, nulls_first: false });
    proof {
        assert(view_keys(keys@) =~= ast_order_keys());
    }
    keys
}

/// The first slot counting more than int8 rows, if any.
fn count_overflow_slot(gt: &Vec<Acc>) -> (r: Option<usize>)
    ensures
        r matches Some(s) ==> s < gt@.len() && gt@[s as int].cnt > int8_max(),
        r is None ==> forall|t: int| 0 <= t < gt@.len() ==> (#[trigger] gt@[t]).cnt <= int8_max(),
{
    let mut s: usize = 0;
    while s < gt.len()
        invariant
            s <= gt@.len(),
            forall|t: int| 0 <= t < s ==> (#[trigger] gt@[t]).cnt <= int8_max(),
        decreases gt@.len() - s,
    {
        if gt[s].cnt > 0x7fff_ffff_ffff_ffff {
            return Some(s);
        }
        s = s + 1;
    }
    None
}

/// The first slot whose disc_price or charge mass exceeds `i128`, if any.
fn mass_overflow_slot(gt: &Vec<Acc>) -> (r: Option<usize>)
    ensures
        r matches Some(s) ==> s < gt@.len() && (gt@[s as int].over_dp || gt@[s as int].over_ch),
        r is None ==> forall|t: int| 0 <= t < gt@.len() ==> !(#[trigger] gt@[t]).over_dp && !gt@[t].over_ch,
{
    let mut s: usize = 0;
    while s < gt.len()
        invariant
            s <= gt@.len(),
            forall|t: int| 0 <= t < s ==> !(#[trigger] gt@[t]).over_dp && !gt@[t].over_ch,
        decreases gt@.len() - s,
    {
        if gt[s].over_dp || gt[s].over_ch {
            return Some(s);
        }
        s = s + 1;
    }
    None
}

/// The output row of one group (`None` when an AVG division leaves its executable domain).
fn group_output(c: &Cols, Ghost(pd): Ghost<int>, a: Acc) -> (r: Option<Vec<EVal>>)
    requires
        cols_wf(*c),
        a.rep < c.n,
        acc_ok(pd, crows(*c), slot_key(*c, a), a),
        !a.over_dp && !a.over_ch,
        gcount(q1_spec(pd), crows(*c), slot_key(*c, a)) > 0,
        a.cnt <= int8_max(),
    ensures
        r matches Some(row) ==> view_row(row@) == group_row(pd, crows(*c), slot_key(*c, a))
            && forall|j: int| 4 <= j <= 6 ==> num_div_fits(#[trigger] gsum(q1_spec(pd), crows(*c), slot_key(*c, a), j), 2, a.cnt as int, 0),
        r is None ==> exists|j: int| 4 <= j <= 6
            && !num_div_fits(#[trigger] gsum(q1_spec(pd), crows(*c), slot_key(*c, a), j), 2, a.cnt as int, 0),
{
    let ghost xs = crows(*c);
    let ghost k = slot_key(*c, a);
    proof {
        lemma_gsum_alias(pd, xs, k);
    }
    let avg_qty = match exec_avg_finalize(a.sum_qty, 2, a.cnt) {
        Ok(v) => v,
        Err(_) => {
            proof { assert(!num_div_fits(gsum(q1_spec(pd), xs, k, 4), 2, a.cnt as int, 0)); }
            return None;
        },
    };
    let avg_price = match exec_avg_finalize(a.sum_price, 2, a.cnt) {
        Ok(v) => v,
        Err(_) => {
            proof { assert(!num_div_fits(gsum(q1_spec(pd), xs, k, 5), 2, a.cnt as int, 0)); }
            return None;
        },
    };
    let avg_disc = match exec_avg_finalize(a.sum_disc, 2, a.cnt) {
        Ok(v) => v,
        Err(_) => {
            proof { assert(!num_div_fits(gsum(q1_spec(pd), xs, k, 6), 2, a.cnt as int, 0)); }
            return None;
        },
    };
    let (rf, ls) = key_values(c, a.rep);
    let mut row: Vec<EVal> = Vec::new();
    row.push(rf);
    row.push(ls);
    row.push(EVal::Num { coeff: a.sum_qty, scale: 2 });
    row.push(EVal::Num { coeff: a.sum_price, scale: 2 });
    row.push(EVal::Num { coeff: a.sum_dp, scale: 4 });
    row.push(EVal::Num { coeff: a.sum_ch, scale: 6 });
    row.push(avg_qty);
    row.push(avg_price);
    row.push(avg_disc);
    row.push(EVal::Int(a.cnt as i64));
    proof {
        lemma_crow(*c, a.rep as int);
        assert(view_row(row@) =~= group_row(pd, xs, k));
        assert forall|j: int| 4 <= j <= 6 implies num_div_fits(#[trigger] gsum(q1_spec(pd), xs, k, j), 2, a.cnt as int, 0) by {}
    }
    Some(row)
}

/// The outcome of the statement from the merged table of all rows.
pub fn finalize(c: &Cols, Ghost(pd): Ghost<int>, gt: &Vec<Acc>) -> (r: Outcome)
    requires
        cols_wf(*c),
        full_table(pd, *c, gt@),
    ensures
        r matches Outcome::Rows(rows) ==> group_caps(q1_spec(pd), crows(*c))
            && result_ok(q1_spec(pd), ast_order_keys(), 0, None, crows(*c), view_rows(rows@)),
        r is CountError ==> exists|k: Row| #[trigger] gcount(q1_spec(pd), crows(*c), k) > int8_max(),
        r is GroupCapacity ==> group_capacity(pd, crows(*c)),
{
    let ghost g = q1_spec(pd);
    let ghost xs = crows(*c);
    proof {
        lemma_full_table(pd, *c, gt@);
    }
    // COUNT beyond int8: the statement's meaning is the error 22003.
    if let Some(s) = count_overflow_slot(gt) {
        proof {
            let k = slot_key(*c, gt@[s as int]);
            assert(acc_ok(pd, xs, k, gt@[s as int]));
            assert(gcount(g, xs, k) > int8_max());
        }
        return Outcome::CountError;
    }
    proof {
        lemma_counts_bounded(pd, *c, gt@);
    }
    // SUM mass beyond i128.
    if let Some(s) = mass_overflow_slot(gt) {
        proof {
            let k = slot_key(*c, gt@[s as int]);
            assert(acc_ok(pd, xs, k, gt@[s as int]));
            let j = if gt@[s as int].over_dp { 2int } else { 3int };
            assert(gcount(g, xs, k) > 0 && gabs(g, xs, k, j) > i128_max());
            assert(group_violation(pd, xs, k, j));
        }
        return Outcome::GroupCapacity;
    }
    // Every group's row (AVG divisions inside their domain), in table order.
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut s: usize = 0;
    while s < gt.len()
        invariant
            cols_wf(*c),
            s <= gt@.len(),
            rows@.len() == s,
            forall|t: int| 0 <= t < gt@.len() ==> (#[trigger] gt@[t]).cnt <= int8_max(),
            forall|t: int| 0 <= t < gt@.len() ==> !(#[trigger] gt@[t]).over_dp && !gt@[t].over_ch,
            forall|t: int| 0 <= t < gt@.len() ==> acc_ok(pd, crows(*c), slot_key(*c, #[trigger] gt@[t]), gt@[t]),
            forall|t: int| 0 <= t < gt@.len() ==> gcount(q1_spec(pd), crows(*c), slot_key(*c, #[trigger] gt@[t])) > 0,
            forall|t: int| 0 <= t < gt@.len() ==> (#[trigger] gt@[t]).rep < c.n,
            forall|k: Row| #[trigger] gcount(q1_spec(pd), crows(*c), k) <= int8_max(),
            forall|t: int, j: int| 0 <= t < s && 4 <= j <= 6 ==>
                num_div_fits(#[trigger] gsum(q1_spec(pd), crows(*c), slot_key(*c, gt@[t]), j), 2, gt@[t].cnt as int, 0),
            forall|t: int| 0 <= t < s ==> view_row((#[trigger] rows@[t])@) == group_row(pd, crows(*c), slot_key(*c, gt@[t])),
        decreases gt@.len() - s,
    {
        let a = gt[s];
        match group_output(c, Ghost(pd), a) {
            Some(row) => {
                rows.push(row);
            },
            None => {
                proof {
                    let k = slot_key(*c, a);
                    let j = choose|j: int| 4 <= j <= 6
                        && !num_div_fits(#[trigger] gsum(q1_spec(pd), crows(*c), k, j), 2, a.cnt as int, 0);
                    assert(acc_ok(pd, crows(*c), k, a));
                    lemma_capacity_witness(pd, crows(*c), k, j);
                }
                return Outcome::GroupCapacity;
            },
        }
        s = s + 1;
    }
    let keys = order_keys();
    let ghost u = view_rows(rows@);
    let sorted = sort_rows_exec(&keys, rows);
    proof {
        lemma_group_caps(pd, *c, gt@);
        lemma_rows_result(pd, *c, gt@, u);
    }
    Outcome::Rows(sorted)
}

/// Capacity witness from the AVG division of slot key `k`.
pub proof fn lemma_capacity_witness(pd: int, xs: Seq<Row>, k: Row, j: int)
    requires
        4 <= j <= 6,
        gcount(q1_spec(pd), xs, k) > 0,
        forall|k2: Row| #[trigger] gcount(q1_spec(pd), xs, k2) <= int8_max(),
        !num_div_fits(gsum(q1_spec(pd), xs, k, j), 2, gcount(q1_spec(pd), xs, k) as int, 0),
    ensures group_capacity(pd, xs),
{
    assert(group_violation(pd, xs, k, j));
}

/// The table's rows, sorted by the ORDER BY keys, are an allowed output.
pub proof fn lemma_rows_result(pd: int, c: Cols, gt: Seq<Acc>, u: Seq<Row>)
    requires
        full_table(pd, c, gt),
        u.len() == gt.len(),
        forall|t: int| 0 <= t < gt.len() ==> #[trigger] u[t] == group_row(pd, crows(c), slot_key(c, gt[t])),
    ensures result_ok(q1_spec(pd), ast_order_keys(), 0, None, crows(c), sort_rows(ast_order_keys(), u)),
{
    hide(acc_ok);
    hide(table_ok);
    let g = q1_spec(pd);
    let xs = crows(c);
    let ks = table_keys(c, gt);
    let keys = ast_order_keys();
    let fams = seq![3int, 3int];
    lemma_full_table(pd, c, gt);
    // Every row's ORDER BY columns are texts.
    assert forall|t: int| 0 <= t < u.len() implies keys_ok(keys, fams, #[trigger] u[t]) by {
        let k = slot_key(c, gt[t]);
        lemma_crow(c, gt[t].rep as int);
        assert forall|i: int| 0 <= i < keys.len() implies #[trigger] key_ok(keys[i], fams[i], u[t]) by {
            assert(u[t][0] == k[0] && u[t][1] == k[1]);
        }
    }
    lemma_sort_rows(keys, fams, u);
    let p = sort_rows(keys, u);
    // The table's rows are the result rows, as a multiset.
    lemma_gkeys(g, xs);
    lemma_nodup_same_multiset(ks, gkeys(g, xs));
    let f = |k: Row| out_row(g, xs, k);
    lemma_map_multiset(ks, gkeys(g, xs), f);
    assert forall|t: int| 0 <= t < u.len() implies #[trigger] u[t] == ks.map_values(f)[t] by {
        let k = slot_key(c, gt[t]);
        assert(ks.contains(k));
        lemma_crow(c, gt[t].rep as int);
        lemma_out_row(pd, xs, k);
    }
    assert(u =~= ks.map_values(f));
    assert(result_rows(g, xs) == gkeys(g, xs).map_values(f));
    lemma_result_ok_from(g, keys, 0, None, xs, p);
    lemma_slice_all(p);
}

} // verus!
