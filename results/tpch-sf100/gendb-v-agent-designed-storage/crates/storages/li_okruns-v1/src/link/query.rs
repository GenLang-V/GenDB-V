//! The accumulator normal form of aggregation queries, and its proof of equality with the SQL meaning (optional
//! author toolkit; nothing here names a query, a table or a column).
//!
//! Many statements have the shape `SELECT <keys and aggregates> FROM <inputs> [WHERE pred] [GROUP BY <columns>]
//! [ORDER BY ..] [LIMIT n] [OFFSET o]`. An author may describe such a statement by a `QuerySpec` over the rows of
//! its FROM relation: a two-valued qualifying condition (`qual`), a group key (`key`, the empty row for a scalar
//! aggregate), the exact argument coefficient of each aggregate (`arg`), the aggregate kinds (COUNT(*), SUM or AVG
//! of a numeric argument at one static scale), the output columns and the mode (grouped or scalar). The
//! accumulators `gcount`, `gsum`, `gabs` and `gkeys` are defined by recursion on the last row, so a loop, a
//! partitioned scan or a hash table can be proved against them with the laws below, and the link lemmas
//! (`lemma_group_query`, `lemma_aggregate_query`) state that the VERUS_SQL denotation of the `GroupBy` or
//! `Aggregate` node is the normal form's rows. Nothing is generated from it: the fixed claim of the entry is stated
//! in SQL terms (`spec::order::ordered_ok`), and using this normal form is one possible choice.
//!
//! Sections, top to bottom:
//! - source relations and executable rows: the text column of the entry ABI (`TextCol`, `text_wf`, `text_at`),
//!   executable result rows (`view_rows`), projections (`proj`, `proj_all`, `select`) and the left-deep product of
//!   the FROM inputs (`joined_of`, bag semantics). The fixed entry and the generated source files state their
//!   claims with `TextCol` .. `proj_all`, which makes those definitions part of the fixed meaning (`link` doc);
//! - the normal form (`QuerySpec`), its accumulators, output rows (`result_rows`: grouped, one row per group in
//!   first-occurrence order; scalar, exactly one row, also on empty input) and allowed outputs (`result_ok`, of the
//!   form of `spec::order::ordered_ok`: a sorted permutation, sliced by OFFSET/LIMIT), and the arithmetic domain of
//!   the groups (`group_caps`: counts in int8 when there is a COUNT, absolute sums in `i128`, AVG divisions
//!   executable);
//! - accumulator laws (per row, per index range, partition and merge, one row, witnesses);
//! - allowed outputs: construction from a sorted accumulator table (`lemma_result_from_keys`), scalar and empty
//!   cases, determinacy up to ties, existence (`lemma_result_exists`);
//! - aggregate finalization: `lemma_avg_ok` and the verified executable `exec_avg_finalize`, `exec_sum_out`,
//!   `exec_count_out`;
//! - the link to VERUS_SQL: per-row agreement premises (`pred_agrees`, `keys_agree`, `args_agree`, `aggs_match`,
//!   `keys_exact`), WHERE (`lemma_filter_rows`, `lemma_table_rows`), group keys and members, the two links, and
//!   the top level (`lemma_project_cols`, `lemma_ordered_link`);
//! - per-node numeric arithmetic with digit bounds (`lemma_node_mul`, `lemma_node_add`).
//!
//! Proof strategy of the links. A GROUP BY in VERUS_SQL groups by SQL "not distinct" (`distinct_rows`,
//! `group_members`); the normal form groups by structural equality. `keys_exact` (every qualifying key has one
//! exact type per position, `lemma_row_exact`) makes the two coincide on the pool of qualifying keys, so the
//! denotation's groups are `gkeys` and each group's members are `members`. `group_caps` then puts every aggregate
//! value inside its SQL range. The link lemmas `hide` the mutually recursive denotation functions and unfold one
//! step each (`lemma_groupby_unfold`, `lemma_aggregate_unfold`), which keeps the solver's search small.
use vstd::prelude::*;
use crate::spec::limits::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::equality::*;
use crate::spec::fns::div::*;
use crate::spec::aggs::avg::*;
use crate::exec::value::*;
use crate::exec::fns::div::num_div_exec;
use crate::bridge::equality::*;
use crate::bridge::typing::val_family;
use crate::bridge::order::{keys_ok, key_ok, lemma_sort_rows, lemma_pow10_add};
use crate::bridge::collect::lemma_collect_all;
use crate::exec::relational::domain::lemma_collect_pointwise;
use crate::link::expr::i128_max;

verus! {

// ---------------------------------------------------------------------------- source relations and executable rows
// Delivered columns (the entry ABI's text column), executable result rows, projections, and the joined relation of a
// FROM list. `TextCol` .. `proj_all` are part of the fixed meaning: the fixed entry and the generated source files
// state the source binding (`table == proj_all(db.tables[t], cols)`, text values `text_at`) and the answer
// (`view_rows`) with them, so their bodies must not change. `select` and `joined_of` are optional vocabulary.

/// A canonical Utf8 column (Arrow LargeUtf8 layout): value `i` is `bytes[offsets[i]..offsets[i + 1]]`.
pub struct TextCol {
    pub offsets: &'static [i64],
    pub bytes: &'static [u8],
}

/// The mathematical view of a `TextCol`.
pub struct TextView {
    pub offsets: Seq<i64>,
    pub bytes: Seq<u8>,
}

impl View for TextCol {
    type V = TextView;

    open spec fn view(&self) -> TextView {
        TextView { offsets: self.offsets@, bytes: self.bytes@ }
    }
}

/// A text column of `n` rows: `n + 1` offsets, each value a byte range inside `bytes`.
pub open spec fn text_wf(t: TextView, n: int) -> bool {
    &&& t.offsets.len() == n + 1
    &&& forall|i: int| 0 <= i < n ==> 0 <= #[trigger] t.offsets[i] <= t.offsets[i + 1] <= t.bytes.len()
}

/// Bytes of value `i`.
pub open spec fn text_at(t: TextView, i: int) -> Seq<u8> {
    t.bytes.subrange(t.offsets[i] as int, t.offsets[i + 1] as int)
}

/// Executable result rows as VERUS_SQL rows.
pub open spec fn view_rows(rows: Seq<Vec<EVal>>) -> Seq<Row> {
    rows.map_values(|r: Vec<EVal>| view_row(r@))
}

/// The columns `cols` of a table row, in that order (values unchanged).
pub open spec fn proj(r: Row, cols: Seq<nat>) -> Row {
    Seq::new(cols.len(), |k: int| r[cols[k] as int])
}

/// `proj` of every row, in order.
pub open spec fn proj_all(rows: Seq<Row>, cols: Seq<nat>) -> Seq<Row> {
    rows.map_values(|r: Row| proj(r, cols))
}

/// Positions `outs` of a row, in that order.
pub open spec fn select(r: Row, outs: Seq<nat>) -> Row {
    Seq::new(outs.len(), |i: int| r[outs[i] as int])
}

/// The joined relation of the FROM list: input `i` reads relation `ts[inputs[i]]`; the inputs are combined by the
/// left-deep product `((in0 x in1) x in2) ..` (`product_rows`, left-major, bag semantics). With no input it is
/// one empty row (a case the lemmas here do not use: they take at least one input).
pub open spec fn joined_of(ts: Seq<Seq<Row>>, inputs: Seq<nat>) -> Seq<Row>
    decreases inputs.len(),
{
    if inputs.len() == 0 {
        seq![Seq::<Val>::empty()]
    } else if inputs.len() == 1 {
        ts[inputs[0] as int]
    } else {
        product_rows(joined_of(ts, inputs.drop_last()), ts[inputs.last() as int])
    }
}

/// One input: the joined relation is that input's relation.
pub proof fn lemma_joined_single(ts: Seq<Seq<Row>>, inputs: Seq<nat>)
    requires inputs.len() == 1,
    ensures joined_of(ts, inputs) == ts[inputs[0] as int],
{
}

// ------------------------------------------------------------------------------------- the accumulator normal form
// `QuerySpec` and the values it denotes: per-group accumulators over a relation, the output rows, the allowed
// outputs and the arithmetic domain of the groups.

/// Aggregate kinds of the fragment: `COUNT(*)` (int8), `SUM(e)` and `AVG(e)` of a numeric argument whose
/// every value has the static scale `scale`.
pub enum AggKind {
    Count,
    Sum { scale: nat },
    Avg { scale: nat },
}

/// An aggregation query in normal form over joined rows: the WHERE condition (two-valued on in-domain rows),
/// the group key (the key column values; the empty row for a scalar aggregate), the argument coefficient of
/// aggregate `j` (at its static scale), the aggregate kinds, the output columns as positions in
/// `key ++ aggregates`, and the mode: `grouped` (GROUP BY: one row per non-empty group) or scalar (no GROUP BY:
/// exactly one row, also on empty input).
pub struct QuerySpec {
    pub qual: spec_fn(Row) -> bool,
    pub key: spec_fn(Row) -> Row,
    pub arg: spec_fn(int, Row) -> int,
    pub aggs: Seq<AggKind>,
    pub outs: Seq<nat>,
    pub grouped: bool,
}

/// A scalar aggregate's key is the empty row on every row.
pub open spec fn scalar_key(g: QuerySpec) -> bool {
    forall|r: Row| #[trigger] (g.key)(r) == Seq::<Val>::empty()
}

/// Row `r` qualifies and belongs to group `k`.
pub open spec fn hit(g: QuerySpec, r: Row, k: Row) -> bool {
    (g.qual)(r) && (g.key)(r) == k
}

/// Number of qualifying rows of group `k`.
pub open spec fn gcount(g: QuerySpec, rows: Seq<Row>, k: Row) -> nat
    decreases rows.len(),
{
    if rows.len() == 0 {
        0
    } else {
        gcount(g, rows.drop_last(), k) + if hit(g, rows.last(), k) { 1nat } else { 0nat }
    }
}

/// Exact sum of aggregate `j`'s argument coefficient over the qualifying rows of group `k`.
pub open spec fn gsum(g: QuerySpec, rows: Seq<Row>, k: Row, j: int) -> int
    decreases rows.len(),
{
    if rows.len() == 0 {
        0
    } else {
        gsum(g, rows.drop_last(), k, j) + if hit(g, rows.last(), k) { (g.arg)(j, rows.last()) } else { 0 }
    }
}

/// Sum of the absolute argument coefficients (monotone under sub-relations; bounds every partial sum).
pub open spec fn gabs(g: QuerySpec, rows: Seq<Row>, k: Row, j: int) -> int
    decreases rows.len(),
{
    if rows.len() == 0 {
        0
    } else {
        gabs(g, rows.drop_last(), k, j) + if hit(g, rows.last(), k) { abs((g.arg)(j, rows.last())) } else { 0 }
    }
}

/// Group keys of the qualifying rows, one per group, in first-occurrence order.
pub open spec fn gkeys(g: QuerySpec, rows: Seq<Row>) -> Seq<Row>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        let d = gkeys(g, rows.drop_last());
        let r = rows.last();
        if (g.qual)(r) && !d.contains((g.key)(r)) { d.push((g.key)(r)) } else { d }
    }
}

/// VERUS_SQL AVG from the exact sum (at `scale`) and count: `numeric_div(sum, count)` (PostgreSQL display scale,
/// `spec::fns::div::num_div`); NULL for a zero count, and NULL stands for a division outside the domain (never
/// produced inside `group_caps`).
pub open spec fn avg_of(sum: int, scale: nat, cnt: nat) -> Val {
    match num_div(sum, scale, cnt as int, 0) {
        Ok(v) => v,
        Err(_) => Val::Null,
    }
}

/// Final value of one aggregate from the group's count and exact sum: COUNT is the count; SUM and AVG are NULL
/// when no row qualifies (only a scalar aggregate reaches that case: every group has a row).
pub open spec fn agg_out(kind: AggKind, cnt: nat, sum: int) -> Val {
    match kind {
        AggKind::Count => Val::Int(cnt as int),
        AggKind::Sum { scale } => if cnt == 0 { Val::Null } else { Val::Num { coeff: sum, scale } },
        AggKind::Avg { scale } => if cnt == 0 { Val::Null } else { avg_of(sum, scale, cnt) },
    }
}

/// The aggregate values of group `k`, one per aggregate.
pub open spec fn agg_outs(g: QuerySpec, rows: Seq<Row>, k: Row) -> Row {
    Seq::new(g.aggs.len(), |j: int| agg_out(g.aggs[j], gcount(g, rows, k), gsum(g, rows, k, j)))
}

/// `key ++ aggregates` of group `k` (the GROUP BY / Aggregate operator's row).
pub open spec fn full_row(g: QuerySpec, rows: Seq<Row>, k: Row) -> Row {
    k + agg_outs(g, rows, k)
}

/// The output row of group `k`.
pub open spec fn out_row(g: QuerySpec, rows: Seq<Row>, k: Row) -> Row {
    select(full_row(g, rows, k), g.outs)
}

/// The query body's rows: grouped, one row per group (canonical first-occurrence order); scalar, exactly one row.
pub open spec fn result_rows(g: QuerySpec, rows: Seq<Row>) -> Seq<Row> {
    if g.grouped {
        gkeys(g, rows).map_values(|k: Row| out_row(g, rows, k))
    } else {
        seq![out_row(g, rows, Seq::empty())]
    }
}

/// Allowed outputs (the form of `spec::order::ordered_ok`): a permutation of the result rows, sorted by the ORDER
/// BY keys, then OFFSET and LIMIT.
pub open spec fn result_ok(g: QuerySpec, keys: Seq<OrderKey>, offset: nat, limit: Option<nat>, rows: Seq<Row>, out: Seq<Row>) -> bool {
    exists|p: Seq<Row>| #![trigger sorted_by(keys, p)]
        p.to_multiset() == result_rows(g, rows).to_multiset() && sorted_by(keys, p) && out == slice_rows(p, offset, limit)
}

/// Arithmetic domain of the groups: when the query has a COUNT aggregate, every group count fits int8 (a query
/// with only SUM/AVG aggregates needs no count bound); every SUM/AVG group has absolute coefficient sum at most
/// `i128::MAX` (so every partial sum in any order fits `i128`); and every AVG division is inside the executable
/// division domain.
pub open spec fn group_caps(g: QuerySpec, rows: Seq<Row>) -> bool {
    &&& forall|k: Row, j: int| #![trigger gcount(g, rows, k), g.aggs[j]] 0 <= j < g.aggs.len() && g.aggs[j] is Count ==> gcount(g, rows, k) <= int8_max()
    &&& forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) ==> #[trigger] gabs(g, rows, k, j) <= i128_max()
    &&& forall|k: Row, j: int| 0 <= j < g.aggs.len() && g.aggs[j] is Avg ==>
            num_div_fits(#[trigger] gsum(g, rows, k, j), g.aggs[j]->Avg_scale, gcount(g, rows, k) as int, 0)
}

// ------------------------------------------------------------------------------------------------ accumulator laws
// Per-row, range, partition/merge and one-row laws of the accumulators; group keys and their witnesses.

/// One more row at the end.
pub proof fn lemma_push(g: QuerySpec, rows: Seq<Row>, r: Row, k: Row, j: int)
    ensures
        gcount(g, rows.push(r), k) == gcount(g, rows, k) + if hit(g, r, k) { 1nat } else { 0nat },
        gsum(g, rows.push(r), k, j) == gsum(g, rows, k, j) + if hit(g, r, k) { (g.arg)(j, r) } else { 0 },
        gabs(g, rows.push(r), k, j) == gabs(g, rows, k, j) + if hit(g, r, k) { abs((g.arg)(j, r)) } else { 0 },
{
    assert(rows.push(r).drop_last() =~= rows);
}

/// Index-range step: the rows `lo..i+1` are the rows `lo..i` and row `i`.
pub proof fn lemma_range_step(g: QuerySpec, rows: Seq<Row>, lo: int, i: int, k: Row, j: int)
    requires 0 <= lo <= i < rows.len(),
    ensures
        gcount(g, rows.subrange(lo, i + 1), k) == gcount(g, rows.subrange(lo, i), k) + if hit(g, rows[i], k) { 1nat } else { 0nat },
        gsum(g, rows.subrange(lo, i + 1), k, j) == gsum(g, rows.subrange(lo, i), k, j) + if hit(g, rows[i], k) { (g.arg)(j, rows[i]) } else { 0 },
        gabs(g, rows.subrange(lo, i + 1), k, j) == gabs(g, rows.subrange(lo, i), k, j) + if hit(g, rows[i], k) { abs((g.arg)(j, rows[i])) } else { 0 },
{
    assert(rows.subrange(lo, i + 1) =~= rows.subrange(lo, i).push(rows[i]));
    lemma_push(g, rows.subrange(lo, i), rows[i], k, j);
}

/// The empty range.
pub proof fn lemma_empty(g: QuerySpec, rows: Seq<Row>, lo: int, k: Row, j: int)
    requires 0 <= lo <= rows.len(),
    ensures
        gcount(g, rows.subrange(lo, lo), k) == 0,
        gsum(g, rows.subrange(lo, lo), k, j) == 0,
        gabs(g, rows.subrange(lo, lo), k, j) == 0,
        gkeys(g, rows.subrange(lo, lo)) == Seq::<Row>::empty(),
{
    assert(rows.subrange(lo, lo).len() == 0);
}

/// One-row relations: the accumulators are that row's contribution.
pub proof fn lemma_one_row(g: QuerySpec, w: Row, k: Row, j: int)
    ensures
        gcount(g, seq![w], k) == if hit(g, w, k) { 1nat } else { 0nat },
        gsum(g, seq![w], k, j) == if hit(g, w, k) { (g.arg)(j, w) } else { 0 },
        gabs(g, seq![w], k, j) == if hit(g, w, k) { abs((g.arg)(j, w)) } else { 0 },
        gkeys(g, seq![w]) == if (g.qual)(w) { seq![(g.key)(w)] } else { Seq::<Row>::empty() },
{
    let e = Seq::<Row>::empty();
    assert(seq![w].drop_last() =~= e);
    assert(seq![w].last() == w);
    assert(gcount(g, e, k) == 0);
    assert(gsum(g, e, k, j) == 0);
    assert(gabs(g, e, k, j) == 0);
    assert(gkeys(g, e) == e);
    if (g.qual)(w) {
        assert(Seq::<Row>::empty().push((g.key)(w)) =~= seq![(g.key)(w)]);
    }
}

/// Concatenation (partition and merge): counts and sums add.
pub proof fn lemma_append(g: QuerySpec, a: Seq<Row>, b: Seq<Row>, k: Row, j: int)
    ensures
        gcount(g, a + b, k) == gcount(g, a, k) + gcount(g, b, k),
        gsum(g, a + b, k, j) == gsum(g, a, k, j) + gsum(g, b, k, j),
        gabs(g, a + b, k, j) == gabs(g, a, k, j) + gabs(g, b, k, j),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_append(g, a, b.drop_last(), k, j);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

/// Adjacent index ranges: `lo..mid` then `mid..hi`.
pub proof fn lemma_split(g: QuerySpec, rows: Seq<Row>, lo: int, mid: int, hi: int, k: Row, j: int)
    requires 0 <= lo <= mid <= hi <= rows.len(),
    ensures
        gcount(g, rows.subrange(lo, hi), k) == gcount(g, rows.subrange(lo, mid), k) + gcount(g, rows.subrange(mid, hi), k),
        gsum(g, rows.subrange(lo, hi), k, j) == gsum(g, rows.subrange(lo, mid), k, j) + gsum(g, rows.subrange(mid, hi), k, j),
        gabs(g, rows.subrange(lo, hi), k, j) == gabs(g, rows.subrange(lo, mid), k, j) + gabs(g, rows.subrange(mid, hi), k, j),
{
    assert(rows.subrange(lo, hi) =~= rows.subrange(lo, mid) + rows.subrange(mid, hi));
    lemma_append(g, rows.subrange(lo, mid), rows.subrange(mid, hi), k, j);
}

/// The whole relation is its range `0..len`.
pub proof fn lemma_full_range(rows: Seq<Row>)
    ensures rows.subrange(0, rows.len() as int) == rows,
{
    assert(rows.subrange(0, rows.len() as int) =~= rows);
}

/// `|sum| <= abs-sum`, and the abs-sum is non-negative.
pub proof fn lemma_abs_bound(g: QuerySpec, rows: Seq<Row>, k: Row, j: int)
    ensures
        0 <= gabs(g, rows, k, j),
        -gabs(g, rows, k, j) <= gsum(g, rows, k, j) <= gabs(g, rows, k, j),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_abs_bound(g, rows.drop_last(), k, j);
    }
}

/// A group without qualifying rows has zero sums.
pub proof fn lemma_zero_count(g: QuerySpec, rows: Seq<Row>, k: Row, j: int)
    requires gcount(g, rows, k) == 0,
    ensures gsum(g, rows, k, j) == 0, gabs(g, rows, k, j) == 0,
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_zero_count(g, rows.drop_last(), k, j);
    }
}

/// The empty relation is inside `group_caps`.
pub proof fn lemma_caps_empty(g: QuerySpec)
    ensures group_caps(g, Seq::empty()),
{
}

/// The group keys are exactly the keys with a qualifying row, without duplicates.
pub proof fn lemma_gkeys(g: QuerySpec, rows: Seq<Row>)
    ensures
        gkeys(g, rows).no_duplicates(),
        forall|k: Row| #[trigger] gkeys(g, rows).contains(k) <==> gcount(g, rows, k) > 0,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let init = rows.drop_last();
        lemma_gkeys(g, init);
        let d = gkeys(g, init);
        let r = rows.last();
        assert forall|k: Row| #[trigger] gkeys(g, rows).contains(k) <==> gcount(g, rows, k) > 0 by {
            if (g.qual)(r) && !d.contains((g.key)(r)) {
                assert(gkeys(g, rows) == d.push((g.key)(r)));
                if gkeys(g, rows).contains(k) && k != (g.key)(r) {
                    let i = choose|i: int| 0 <= i < gkeys(g, rows).len() && gkeys(g, rows)[i] == k;
                    assert(d[i] == k);
                }
                if d.contains(k) {
                    let i = choose|i: int| 0 <= i < d.len() && d[i] == k;
                    assert(gkeys(g, rows)[i] == k);
                }
                assert(gkeys(g, rows)[d.len() as int] == (g.key)(r));
            }
        }
        if (g.qual)(r) && !d.contains((g.key)(r)) {
            assert forall|a: int, b: int| 0 <= a < b < gkeys(g, rows).len() implies gkeys(g, rows)[a] != gkeys(g, rows)[b] by {
                if b == d.len() {
                    assert(d.contains(d[a]));
                }
            }
        }
    }
}

/// A group with a qualifying row has a witness row.
pub proof fn lemma_count_witness(g: QuerySpec, rows: Seq<Row>, k: Row)
    requires gcount(g, rows, k) > 0,
    ensures exists|m: int| 0 <= m < rows.len() && #[trigger] hit(g, rows[m], k),
    decreases rows.len(),
{
    if hit(g, rows.last(), k) {
        assert(hit(g, rows[rows.len() - 1], k));
    } else {
        lemma_count_witness(g, rows.drop_last(), k);
        let m = choose|m: int| 0 <= m < rows.drop_last().len() && #[trigger] hit(g, rows.drop_last()[m], k);
        assert(rows[m] == rows.drop_last()[m]);
        assert(hit(g, rows[m], k));
    }
}

/// Every group key is the key of some qualifying row.
pub proof fn lemma_gkeys_witness(g: QuerySpec, rows: Seq<Row>, k: Row)
    requires gkeys(g, rows).contains(k),
    ensures
        gcount(g, rows, k) > 0,
        exists|m: int| 0 <= m < rows.len() && #[trigger] hit(g, rows[m], k),
    decreases rows.len(),
{
    lemma_gkeys(g, rows);
    lemma_count_witness(g, rows, k);
}

// ------------------------------------------------------------------------------------------------- allowed outputs
// Building `result_ok` from a sorted accumulator table, its scalar and empty cases, determinacy up to ties, and
// existence (the canonical sort of the result rows is allowed).

/// Two duplicate-free sequences with the same elements have the same multiset.
pub proof fn lemma_nodup_same_multiset<A>(s: Seq<A>, t: Seq<A>)
    requires
        s.no_duplicates(),
        t.no_duplicates(),
        forall|x: A| s.contains(x) <==> t.contains(x),
    ensures s.to_multiset() == t.to_multiset(),
{
    s.lemma_multiset_has_no_duplicates();
    t.lemma_multiset_has_no_duplicates();
    s.to_multiset_ensures();
    t.to_multiset_ensures();
    assert forall|x: A| s.to_multiset().count(x) == t.to_multiset().count(x) by {
        if s.contains(x) {
            assert(s.to_multiset().contains(x));
            assert(t.to_multiset().contains(x));
        }
    }
    assert(s.to_multiset() =~= t.to_multiset());
}

/// Equal multisets stay equal under `map_values`.
pub proof fn lemma_map_multiset<A, B>(s: Seq<A>, t: Seq<A>, f: spec_fn(A) -> B)
    requires s.to_multiset() == t.to_multiset(),
    ensures s.map_values(f).to_multiset() == t.map_values(f).to_multiset(),
    decreases s.len(),
{
    s.to_multiset_ensures();
    t.to_multiset_ensures();
    if s.len() == 0 {
        assert(t.to_multiset().len() == 0);
        assert(t.len() == 0);
        assert(s.map_values(f) =~= t.map_values(f));
    } else {
        let x = s.last();
        let si = s.drop_last();
        assert(si.push(x) =~= s);
        si.to_multiset_ensures();
        assert(s.to_multiset().count(x) > 0);
        assert(t.contains(x));
        let i = choose|i: int| 0 <= i < t.len() && t[i] == x;
        let ti = t.remove(i);
        assert(ti.to_multiset() =~= t.to_multiset().remove(x));
        assert(si.to_multiset() =~= s.to_multiset().remove(x));
        lemma_map_multiset(si, ti, f);
        let (ms, mt) = (s.map_values(f), t.map_values(f));
        assert(ms =~= si.map_values(f).push(f(x)));
        si.map_values(f).to_multiset_ensures();
        mt.to_multiset_ensures();
        assert(mt.remove(i) =~= ti.map_values(f));
        assert(mt[i] == f(x));
        assert(mt.to_multiset().count(f(x)) > 0);
        assert(ms.to_multiset() =~= mt.to_multiset());
    }
}

/// OFFSET 0 without LIMIT keeps every row.
pub proof fn lemma_slice_all(s: Seq<Row>)
    ensures slice_rows(s, 0, None) == s,
{
    assert(slice_rows(s, 0, None) =~= s);
}

/// A sorted permutation of the result rows, sliced, is an allowed output.
pub proof fn lemma_result_ok_from(g: QuerySpec, keys: Seq<OrderKey>, offset: nat, limit: Option<nat>, rows: Seq<Row>, p: Seq<Row>)
    requires
        p.to_multiset() == result_rows(g, rows).to_multiset(),
        sorted_by(keys, p),
    ensures result_ok(g, keys, offset, limit, rows, slice_rows(p, offset, limit)),
{
}

/// Without OFFSET and LIMIT, the allowed outputs are exactly the sorted permutations of the result rows.
pub proof fn lemma_result_ok_unsliced(g: QuerySpec, keys: Seq<OrderKey>, rows: Seq<Row>, out: Seq<Row>)
    ensures
        result_ok(g, keys, 0, None, rows, out) <==> (out.to_multiset() == result_rows(g, rows).to_multiset() && sorted_by(keys, out)),
{
    lemma_slice_all(out);
    if result_ok(g, keys, 0, None, rows, out) {
        let p = choose|p: Seq<Row>| #![trigger sorted_by(keys, p)]
            p.to_multiset() == result_rows(g, rows).to_multiset() && sorted_by(keys, p) && out == slice_rows(p, 0, None);
        lemma_slice_all(p);
    }
}

/// An accumulator table with distinct keys that are exactly the non-empty groups, sorted by the ORDER BY keys,
/// then sliced, is an allowed output of a grouped query.
pub proof fn lemma_result_from_keys(g: QuerySpec, keys: Seq<OrderKey>, offset: nat, limit: Option<nat>, rows: Seq<Row>, ks: Seq<Row>, full: Seq<Row>)
    requires
        g.grouped,
        ks.no_duplicates(),
        forall|k: Row| #[trigger] ks.contains(k) <==> gcount(g, rows, k) > 0,
        full.len() == ks.len(),
        forall|i: int| 0 <= i < full.len() ==> #[trigger] full[i] == out_row(g, rows, ks[i]),
        sorted_by(keys, full),
    ensures result_ok(g, keys, offset, limit, rows, slice_rows(full, offset, limit)),
{
    lemma_gkeys(g, rows);
    lemma_nodup_same_multiset(ks, gkeys(g, rows));
    let f = |k: Row| out_row(g, rows, k);
    lemma_map_multiset(ks, gkeys(g, rows), f);
    assert(full =~= ks.map_values(f));
    lemma_result_ok_from(g, keys, offset, limit, rows, full);
}

/// A one-row sequence is sorted by any keys.
pub proof fn lemma_sorted_single(keys: Seq<OrderKey>, r: Row)
    ensures sorted_by(keys, seq![r]),
{
}

/// A scalar aggregate: its one output row, sliced, is the allowed output.
pub proof fn lemma_scalar_result(g: QuerySpec, keys: Seq<OrderKey>, offset: nat, limit: Option<nat>, rows: Seq<Row>, r: Row)
    requires !g.grouped, r == out_row(g, rows, Seq::empty()),
    ensures result_ok(g, keys, offset, limit, rows, slice_rows(seq![r], offset, limit)),
{
    lemma_sorted_single(keys, r);
    lemma_result_ok_from(g, keys, offset, limit, rows, seq![r]);
}

/// A permutation of a one-row sequence is that sequence.
pub proof fn lemma_single_multiset(p: Seq<Row>, x: Row)
    requires p.to_multiset() == seq![x].to_multiset(),
    ensures p == seq![x],
{
    p.to_multiset_ensures();
    seq![x].to_multiset_ensures();
    assert(p.len() == 1);
    assert(p.contains(p[0]));
    assert(seq![x].to_multiset().count(p[0]) > 0);
    assert(seq![x].contains(p[0]));
    assert(p =~= seq![x]);
}

/// A scalar aggregate's allowed outputs: exactly its one row, sliced by OFFSET/LIMIT.
pub proof fn lemma_scalar_result_ok(g: QuerySpec, keys: Seq<OrderKey>, offset: nat, limit: Option<nat>, rows: Seq<Row>, out: Seq<Row>)
    requires !g.grouped,
    ensures
        result_rows(g, rows) == seq![out_row(g, rows, Seq::empty())],
        result_ok(g, keys, offset, limit, rows, out) <==> out == slice_rows(seq![out_row(g, rows, Seq::empty())], offset, limit),
{
    let r = out_row(g, rows, Seq::empty());
    if result_ok(g, keys, offset, limit, rows, out) {
        let p = choose|p: Seq<Row>| #![trigger sorted_by(keys, p)]
            p.to_multiset() == result_rows(g, rows).to_multiset() && sorted_by(keys, p) && out == slice_rows(p, offset, limit);
        lemma_single_multiset(p, r);
    }
    if out == slice_rows(seq![r], offset, limit) {
        lemma_scalar_result(g, keys, offset, limit, rows, r);
    }
}

/// Determinacy up to ORDER BY ties: all allowed outputs have one length; without OFFSET and LIMIT they are one
/// multiset.
pub proof fn lemma_result_determined(g: QuerySpec, keys: Seq<OrderKey>, offset: nat, limit: Option<nat>, rows: Seq<Row>, a: Seq<Row>, b: Seq<Row>)
    requires result_ok(g, keys, offset, limit, rows, a), result_ok(g, keys, offset, limit, rows, b),
    ensures
        a.len() == b.len(),
        offset == 0 && limit is None ==> a.to_multiset() == b.to_multiset(),
{
    let body = result_rows(g, rows);
    let pa = choose|p: Seq<Row>| #![trigger sorted_by(keys, p)]
        p.to_multiset() == body.to_multiset() && sorted_by(keys, p) && a == slice_rows(p, offset, limit);
    let pb = choose|p: Seq<Row>| #![trigger sorted_by(keys, p)]
        p.to_multiset() == body.to_multiset() && sorted_by(keys, p) && b == slice_rows(p, offset, limit);
    pa.to_multiset_ensures();
    pb.to_multiset_ensures();
    assert(pa.len() == pb.len());
    if offset == 0 && limit is None {
        lemma_slice_all(pa);
        lemma_slice_all(pb);
    }
}

/// Allowed outputs of a grouped query over the empty relation: only the empty sequence.
pub proof fn lemma_empty_grouped(g: QuerySpec, keys: Seq<OrderKey>, offset: nat, limit: Option<nat>, out: Seq<Row>)
    requires g.grouped,
    ensures result_ok(g, keys, offset, limit, Seq::empty(), out) <==> out.len() == 0,
{
    let e = Seq::<Row>::empty();
    assert(gkeys(g, e) =~= Seq::<Row>::empty());
    assert(result_rows(g, e) =~= Seq::<Row>::empty());
    result_rows(g, e).to_multiset_ensures();
    if result_ok(g, keys, offset, limit, e, out) {
        let p = choose|p: Seq<Row>| #![trigger sorted_by(keys, p)]
            p.to_multiset() == result_rows(g, e).to_multiset() && sorted_by(keys, p) && out == slice_rows(p, offset, limit);
        p.to_multiset_ensures();
        assert(p.len() == 0);
    }
    if out.len() == 0 {
        assert(out =~= Seq::<Row>::empty());
        lemma_result_ok_from(g, keys, offset, limit, e, e);
        assert(slice_rows(e, offset, limit) =~= out);
    }
}

/// A scalar aggregate over the empty relation: its one row has COUNT 0 and NULL SUM/AVG.
pub proof fn lemma_empty_scalar(g: QuerySpec)
    requires !g.grouped,
    ensures
        result_rows(g, Seq::empty()) == seq![out_row(g, Seq::empty(), Seq::empty())],
        forall|j: int| 0 <= j < g.aggs.len() ==> #[trigger] agg_outs(g, Seq::empty(), Seq::empty())[j]
            == (if g.aggs[j] is Count { Val::Int(0) } else { Val::Null }),
{
}

/// Static description of ORDER BY key `i` for result existence: it reads output column `keys[i].col`, which is
/// key position `outs[col] < nk` (family `fams[i]` on every qualifying row) or an aggregate (family 1).
pub open spec fn order_col_ok(g: QuerySpec, keys: Seq<OrderKey>, fams: Seq<int>, nk: nat, rows: Seq<Row>, i: int) -> bool {
    let c = keys[i].col;
    &&& c < g.outs.len()
    &&& g.outs[c as int] < nk + g.aggs.len()
    &&& (g.outs[c as int] < nk ==> forall|m: int| 0 <= m < rows.len() && (g.qual)(rows[m]) ==>
            val_family(#[trigger] (g.key)(rows[m])[g.outs[c as int] as int]) == fams[i])
    &&& (g.outs[c as int] >= nk ==> fams[i] == 1)
}

/// Every ORDER BY key satisfies `order_col_ok`, and the key rows have `nk` columns (none for a scalar aggregate).
pub open spec fn order_fams_ok(g: QuerySpec, keys: Seq<OrderKey>, fams: Seq<int>, nk: nat, rows: Seq<Row>) -> bool {
    &&& keys.len() == fams.len()
    &&& (!g.grouped ==> nk == 0 && scalar_key(g))
    &&& forall|m: int| 0 <= m < rows.len() && (g.qual)(rows[m]) ==> (#[trigger] (g.key)(rows[m])).len() == nk
    &&& forall|i: int| 0 <= i < keys.len() ==> #[trigger] order_col_ok(g, keys, fams, nk, rows, i)
}

/// ORDER BY keys of the output row of group `k` (a group with a qualifying row, or the scalar group) are in
/// their families.
pub proof fn lemma_out_row_keys_ok(g: QuerySpec, keys: Seq<OrderKey>, fams: Seq<int>, nk: nat, rows: Seq<Row>, k: Row)
    requires
        group_caps(g, rows),
        order_fams_ok(g, keys, fams, nk, rows),
        k.len() == nk,
        gcount(g, rows, k) > 0 ==> exists|m: int| 0 <= m < rows.len() && #[trigger] hit(g, rows[m], k),
        g.grouped ==> gcount(g, rows, k) > 0,
    ensures keys_ok(keys, fams, out_row(g, rows, k)),
{
    let n = gcount(g, rows, k);
    let r = out_row(g, rows, k);
    assert forall|i: int| 0 <= i < keys.len() implies #[trigger] key_ok(keys[i], fams[i], r) by {
        assert(order_col_ok(g, keys, fams, nk, rows, i));
        let c = keys[i].col;
        let p = g.outs[c as int];
        assert(r[c as int] == full_row(g, rows, k)[p as int]);
        if p < nk {
            let m = choose|m: int| 0 <= m < rows.len() && #[trigger] hit(g, rows[m], k);
            assert((g.key)(rows[m]) == k);
            assert(full_row(g, rows, k)[p as int] == k[p as int]);
            assert(val_family((g.key)(rows[m])[p as int]) == fams[i]);
        } else {
            let j = p - nk;
            assert(full_row(g, rows, k)[p as int] == agg_outs(g, rows, k)[j]);
            match g.aggs[j] {
                AggKind::Avg { scale } => {
                    if n > 0 {
                        let sm = gsum(g, rows, k, j);
                        assert(num_div_fits(sm, scale, n as int, 0));
                        lemma_avg_ok(sm, scale, n as int);
                    }
                },
                _ => {},
            }
        }
    }
}

/// Result existence: inside `group_caps`, the canonical sort of the result rows, sliced, is an allowed output.
pub proof fn lemma_result_exists(g: QuerySpec, keys: Seq<OrderKey>, offset: nat, limit: Option<nat>, fams: Seq<int>, nk: nat, rows: Seq<Row>)
    requires
        group_caps(g, rows),
        order_fams_ok(g, keys, fams, nk, rows),
    ensures result_ok(g, keys, offset, limit, rows, slice_rows(sort_rows(keys, result_rows(g, rows)), offset, limit)),
{
    let gr = result_rows(g, rows);
    if g.grouped {
        let ks = gkeys(g, rows);
        assert forall|gi: int| 0 <= gi < gr.len() implies keys_ok(keys, fams, #[trigger] gr[gi]) by {
            let k = ks[gi];
            assert(ks.contains(k));
            lemma_gkeys_witness(g, rows, k);
            let m = choose|m: int| 0 <= m < rows.len() && #[trigger] hit(g, rows[m], k);
            assert((g.key)(rows[m]) == k);
            assert(gr[gi] == out_row(g, rows, k));
            lemma_out_row_keys_ok(g, keys, fams, nk, rows, k);
        }
    } else {
        let k = Seq::<Val>::empty();
        if gcount(g, rows, k) > 0 {
            lemma_count_witness(g, rows, k);
        }
        lemma_out_row_keys_ok(g, keys, fams, nk, rows, k);
        assert forall|gi: int| 0 <= gi < gr.len() implies keys_ok(keys, fams, #[trigger] gr[gi]) by {
            assert(gr[gi] == out_row(g, rows, k));
        }
    }
    lemma_sort_rows(keys, fams, gr);
    lemma_result_ok_from(g, keys, offset, limit, rows, sort_rows(keys, gr));
}

// ------------------------------------------------------------------------------------------ aggregate finalization
// AVG as a division inside its domain, and verified executable output values of COUNT, SUM and AVG.

/// A division inside the executable domain with a nonzero count: the quotient is a numeric value in range.
pub proof fn lemma_avg_ok(s: int, scale: nat, n: int)
    requires n > 0, num_div_fits(s, scale, n, 0),
    ensures
        num_in_range(num_div_coeff(s, scale, n, 0), div_scale(s, scale, n, 0)),
        num_div(s, scale, n, 0) == Ok::<Val, SqlError>(Val::Num { coeff: num_div_coeff(s, scale, n, 0), scale: div_scale(s, scale, n, 0) }),
        avg_of(s, scale, n as nat) == (Val::Num { coeff: num_div_coeff(s, scale, n, 0), scale: div_scale(s, scale, n, 0) }),
{
    let r = div_scale(s, scale, n, 0);
    let q = div_round(abs(s) * pow10((r + 0) as nat), abs(n) * pow10(scale));
    let c = num_div_coeff(s, scale, n, 0);
    assert(c == sign(s) * sign(n) * q);
    if s == 0 {
        assert(sign(s) == 0);
        assert(sign(s) * sign(n) * q == 0) by (nonlinear_arith) requires sign(s) == 0;
    } else {
        assert(in_i128(c));
    }
    lemma_num_in_range_small(c, r);
}

/// Exec: the VERUS_SQL AVG of a group from its exact `i128` sum at `scale` and its count, with `Err(Capacity)`
/// exactly outside the division domain (`num_div_fits`). A zero count gives NULL (`agg_out` of an empty scalar
/// aggregate).
pub fn exec_avg_finalize(sum: i128, scale: u32, count: u64) -> (r: Result<EVal, Capacity>)
    ensures
        match r {
            Ok(v) => num_div_fits(sum as int, scale as nat, count as int, 0) && v@ == avg_of(sum as int, scale as nat, count as nat)
                && v@ == agg_out(AggKind::Avg { scale: scale as nat }, count as nat, sum as int),
            Err(_) => !num_div_fits(sum as int, scale as nat, count as int, 0),
        },
{
    let r = num_div_exec(sum, scale, count as i128, 0);
    proof {
        assert((count as i128) as int == count as int);
    }
    match r {
        Ok(Ok(v)) => Ok(v),
        Ok(Err(_)) => {
            proof {
                let (c1, s1, c2) = (sum as int, scale as nat, count as int);
                assert(num_div_fits(c1, s1, c2, 0));
                if c2 != 0 {
                    // A nonzero count inside the division domain gives a value (`lemma_avg_ok`), not an error.
                    lemma_avg_ok(c1, s1, c2);
                    assert(false);
                }
            }
            Ok(EVal::Null)
        },
        Err(c) => Err(c),
    }
}

/// Exec: the SUM output value from a group's count and exact `i128` sum at `scale` (NULL for a zero count).
pub fn exec_sum_out(sum: i128, scale: u32, count: u64) -> (v: EVal)
    ensures v@ == agg_out(AggKind::Sum { scale: scale as nat }, count as nat, sum as int),
{
    if count == 0 { EVal::Null } else { EVal::Num { coeff: sum, scale } }
}

/// Exec: the COUNT(*) output value.
pub fn exec_count_out(count: u64) -> (v: EVal)
    requires count as int <= int8_max(),
    ensures v@ == agg_out(AggKind::Count, count as nat, 0),
{
    EVal::Int(count as i64)
}

// ---------------------------------------------------------------------------------------- link: agreement premises
// What an author proves per row about the statement's condition, keys and aggregate arguments, and how the
// aggregate ASTs correspond to the normal form's kinds.

/// The aggregate AST matches its normal-form kind.
pub open spec fn agg_matches(a: Agg, kind: AggKind) -> bool {
    match kind {
        AggKind::Count => a == Agg::CountStar,
        AggKind::Sum { .. } => a is Sum && a->Sum_kind == NumKind::Numeric,
        AggKind::Avg { .. } => a is Avg && a->Avg_kind == NumKind::Numeric,
    }
}

/// Argument values of one projected row (`COUNT(*)` has none; NULL stands in, as `agg_arg`).
pub open spec fn arg_vals(g: QuerySpec, x: Row) -> Row {
    Seq::new(g.aggs.len(), |j: int| match g.aggs[j] {
        AggKind::Count => Val::Null,
        AggKind::Sum { scale } => Val::Num { coeff: (g.arg)(j, x), scale },
        AggKind::Avg { scale } => Val::Num { coeff: (g.arg)(j, x), scale },
    })
}

/// Per-row agreement of the WHERE condition with the normal form, for every row of `rows` (projected by `cols`):
/// the condition evaluates without error on every row (totality) to the normal form's truth value.
pub open spec fn pred_agrees(db: Database, rows: Seq<Row>, cols: Seq<nat>, pred: Pred, g: QuerySpec) -> bool {
    forall|i: int| 0 <= i < rows.len() ==>
        eval_pred(db, #[trigger] rows[i], pred) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[i], cols))))
}

/// Per-row agreement of the group key with the normal form, on qualifying rows.
pub open spec fn keys_agree(db: Database, rows: Seq<Row>, cols: Seq<nat>, keys: Seq<Expr>, g: QuerySpec) -> bool {
    forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) ==>
        eval_exprs(db, rows[i], keys) == Ok::<Row, SqlError>((g.key)(proj(rows[i], cols)))
}

/// Per-row agreement of the aggregate arguments with the normal form, on qualifying rows.
pub open spec fn args_agree(db: Database, rows: Seq<Row>, cols: Seq<nat>, aggs: Seq<Agg>, g: QuerySpec) -> bool {
    forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) ==>
        agg_args(db, rows[i], aggs) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], cols)))
}

/// The aggregate list matches the kinds.
pub open spec fn aggs_match(aggs: Seq<Agg>, g: QuerySpec) -> bool {
    &&& aggs.len() == g.aggs.len()
    &&& forall|j: int| 0 <= j < aggs.len() ==> agg_matches(#[trigger] aggs[j], g.aggs[j])
}

/// On the keys of qualifying rows, SQL "not distinct" is structural equality (exact key types).
pub open spec fn keys_exact(g: QuerySpec, xs: Seq<Row>) -> bool {
    forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) ==>
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b]))
}

// ----------------------------------------------------------------------------------------------------- link: WHERE
// The statement's filter keeps exactly the input rows whose projection qualifies.

/// Truth values of the WHERE condition under the normal form.
pub open spec fn qual_truths(g: QuerySpec, xs: Seq<Row>) -> Seq<Truth> {
    Seq::new(xs.len(), |i: int| truth_of((g.qual)(xs[i])))
}

/// Projected qualifying rows (the normal form's filter).
pub open spec fn qrows(g: QuerySpec, xs: Seq<Row>) -> Seq<Row>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Seq::empty()
    } else if (g.qual)(xs.last()) {
        qrows(g, xs.drop_last()).push(xs.last())
    } else {
        qrows(g, xs.drop_last())
    }
}

/// Keeping every row (all truths `True`) is the identity.
pub proof fn lemma_keep_all(rows: Seq<Row>, truths: Seq<Truth>)
    requires rows.len() == truths.len(), forall|i: int| 0 <= i < truths.len() ==> #[trigger] truths[i] is True,
    ensures keep_true(rows, truths) == rows,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ti.len() implies #[trigger] ti[i] is True by {
            assert(ti[i] == truths[i]);
        }
        lemma_keep_all(ri, ti);
        assert(truths.last() == truths[truths.len() - 1]);
        assert(ri.push(rows.last()) =~= rows);
    } else {
        assert(keep_true(rows, truths) =~= rows);
    }
}

/// `keep_true` keeps rows of its input.
pub proof fn lemma_keep_true_member(rows: Seq<Row>, truths: Seq<Truth>, i: int)
    requires 0 <= i < keep_true(rows, truths).len(),
    ensures rows.contains(keep_true(rows, truths)[i]),
    decreases rows.len(),
{
    if rows.len() > 0 && truths.len() > 0 {
        let init = keep_true(rows.drop_last(), truths.drop_last());
        if truths.last() is True && i == init.len() {
            assert(rows[rows.len() - 1] == rows.last());
        } else {
            lemma_keep_true_member(rows.drop_last(), truths.drop_last(), i);
            let m = choose|m: int| 0 <= m < rows.drop_last().len() && rows.drop_last()[m] == init[i];
            assert(rows[m] == init[i]);
        }
    }
}

/// WHERE: the kept input rows project to the qualifying projected rows.
pub proof fn lemma_kept_proj(g: QuerySpec, rows: Seq<Row>, cols: Seq<nat>)
    ensures ({
        let xs = proj_all(rows, cols);
        let kept = keep_true(rows, qual_truths(g, xs));
        &&& proj_all(kept, cols) == qrows(g, xs)
        &&& forall|i: int| 0 <= i < kept.len() ==> (g.qual)(proj(#[trigger] kept[i], cols))
    }),
    decreases rows.len(),
{
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    if rows.len() > 0 {
        let init = rows.drop_last();
        lemma_kept_proj(g, init, cols);
        let xi = proj_all(init, cols);
        assert(xs.drop_last() =~= xi);
        assert(qual_truths(g, xs).drop_last() =~= qual_truths(g, xi));
        let ki = keep_true(init, qual_truths(g, xi));
        assert(xs.last() == proj(rows.last(), cols));
        if (g.qual)(xs.last()) {
            assert(kept == ki.push(rows.last()));
            assert(proj_all(kept, cols) =~= proj_all(ki, cols).push(proj(rows.last(), cols)));
            assert forall|i: int| 0 <= i < kept.len() implies (g.qual)(proj(#[trigger] kept[i], cols)) by {
                if i < ki.len() {
                    assert(kept[i] == ki[i]);
                }
            }
        } else {
            assert(kept == ki);
        }
    } else {
        assert(proj_all(kept, cols) =~= qrows(g, xs));
    }
}

/// The rows a WHERE keeps under the normal form's truths: each is an input row whose projection qualifies, and
/// position by position they project to `qrows`. (The common first step of both links.)
pub proof fn lemma_kept_rows(g: QuerySpec, rows: Seq<Row>, cols: Seq<nat>)
    ensures ({
        let xs = proj_all(rows, cols);
        let kept = keep_true(rows, qual_truths(g, xs));
        &&& proj_all(kept, cols) == qrows(g, xs)
        &&& forall|i: int| 0 <= i < kept.len() ==> rows.contains(#[trigger] kept[i]) && (g.qual)(proj(kept[i], cols))
        &&& forall|i: int| 0 <= i < kept.len() ==> #[trigger] proj(kept[i], cols) == qrows(g, xs)[i]
    }),
{
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    lemma_kept_proj(g, rows, cols);
    assert forall|i: int| 0 <= i < kept.len() implies rows.contains(#[trigger] kept[i]) && (g.qual)(proj(kept[i], cols)) by {
        lemma_keep_true_member(rows, qual_truths(g, xs), i);
    }
    assert forall|i: int| 0 <= i < kept.len() implies #[trigger] proj(kept[i], cols) == qrows(g, xs)[i] by {
        assert(proj_all(kept, cols)[i] == proj(kept[i], cols));
    }
}

/// WHERE over an input that evaluates to `rows`, under per-row agreement of the condition.
pub proof fn lemma_filter_rows(db: Database, src: Query, rows: Seq<Row>, cols: Seq<nat>, pred: Pred, g: QuerySpec)
    requires
        eval_query(db, Seq::empty(), src) == Ok::<Relation, SqlError>(rows),
        pred_agrees(db, rows, cols, pred, g),
    ensures
        eval_query(db, Seq::empty(), Query::Filter { pred, input: Box::new(src) })
            == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols)))),
{
    let xs = proj_all(rows, cols);
    let ctx = Seq::<Val>::empty();
    let truths = qual_truths(g, xs);
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(ctx + rows[i] =~= rows[i]);
        assert(xs[i] == proj(rows[i], cols));
        assert(eval_pred(db, rows[i], pred) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[i], cols)))));
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(collect(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths));
}

/// No WHERE: an input evaluating to `rows` is its rows kept under an always-true condition.
pub proof fn lemma_table_rows(db: Database, src: Query, rows: Seq<Row>, cols: Seq<nat>, g: QuerySpec)
    requires
        eval_query(db, Seq::empty(), src) == Ok::<Relation, SqlError>(rows),
        forall|x: Row| #[trigger] (g.qual)(x),
    ensures
        eval_query(db, Seq::empty(), src) == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols)))),
{
    lemma_keep_all(rows, qual_truths(g, proj_all(rows, cols)));
}

// ------------------------------------------------------------------------------------ link: group keys and members
// On exact key types SQL "not distinct" is structural equality, so `distinct_rows` of the qualifying keys is
// `gkeys` and each group's members are the normal form's argument rows (`members`).

/// Rows of one exact type per position: SQL "not distinct" is structural equality.
pub proof fn lemma_row_exact(a: Row, b: Row)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> same_exact_type(#[trigger] a[i], b[i]),
    ensures row_not_distinct(a, b) <==> a == b,
{
    assert forall|i: int| 0 <= i < a.len() implies (val_not_distinct(#[trigger] a[i], b[i]) <==> a[i] == b[i]) by {
        lemma_val_not_distinct_structural(a[i], b[i]);
    }
    if row_not_distinct(a, b) {
        assert(a =~= b);
    }
    if a == b {
        assert forall|i: int| 0 <= i < a.len() implies val_not_distinct(#[trigger] a[i], b[i]) by {}
    }
}

/// Keys of the qualifying projected rows.
pub open spec fn qkeys(g: QuerySpec, xs: Seq<Row>) -> Seq<Row> {
    qrows(g, xs).map_values(|x: Row| (g.key)(x))
}

/// `qrows` contents: qualifying rows of `xs`.
pub proof fn lemma_qrows_sub(g: QuerySpec, xs: Seq<Row>)
    ensures forall|i: int| 0 <= i < qrows(g, xs).len() ==> (g.qual)(#[trigger] qrows(g, xs)[i]) && xs.contains(qrows(g, xs)[i]),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        lemma_qrows_sub(g, xi);
        let q = qrows(g, xs);
        let qi = qrows(g, xi);
        assert forall|i: int| 0 <= i < q.len() implies (g.qual)(#[trigger] q[i]) && xs.contains(q[i]) by {
            if i < qi.len() {
                assert(q[i] == qi[i]);
                let m = choose|m: int| 0 <= m < xi.len() && xi[m] == qi[i];
                assert(xi[m] == xs[m]);
                assert(xs[m] == qi[i]);
            } else {
                assert(q[i] == xs.last());
                assert(xs[xs.len() - 1] == xs.last());
            }
        }
    }
}

/// The pool of qualifying keys of `xs` (the keys `keys_exact` speaks about; the same sequence as `qkeys`).
pub open spec fn key_pool(g: QuerySpec, xs: Seq<Row>) -> Seq<Row> {
    qkeys(g, xs)
}

/// `has_not_distinct` over structurally exact keys is `contains`.
pub proof fn lemma_has_nd_contains(d: Seq<Row>, k: Row, pool: Seq<Row>)
    requires
        forall|i: int| 0 <= i < d.len() ==> pool.contains(#[trigger] d[i]),
        pool.contains(k),
        forall|a: Row, b: Row| pool.contains(a) && pool.contains(b) ==> (#[trigger] row_not_distinct(a, b) <==> a == b),
    ensures has_not_distinct(d, k) <==> d.contains(k),
    decreases d.len(),
{
    if d.len() > 0 {
        let di = d.drop_last();
        assert forall|i: int| 0 <= i < di.len() implies pool.contains(#[trigger] di[i]) by {
            assert(di[i] == d[i]);
        }
        lemma_has_nd_contains(di, k, pool);
        assert(pool.contains(d[d.len() - 1]));
        assert(row_not_distinct(d.last(), k) <==> d.last() == k);
        if di.contains(k) {
            let i = choose|i: int| 0 <= i < di.len() && di[i] == k;
            assert(d[i] == k);
        }
        if d.contains(k) && d.last() != k {
            let i = choose|i: int| 0 <= i < d.len() && d[i] == k;
            assert(di[i] == k);
        }
    }
}

/// Under `keys_exact`, SQL "not distinct" is structural equality on the key pool.
pub proof fn lemma_pool_exact(g: QuerySpec, xs: Seq<Row>)
    requires keys_exact(g, xs),
    ensures
        forall|a: Row, b: Row| key_pool(g, xs).contains(a) && key_pool(g, xs).contains(b) ==> (#[trigger] row_not_distinct(a, b) <==> a == b),
{
    lemma_qrows_sub(g, xs);
    let q = qrows(g, xs);
    let p = key_pool(g, xs);
    assert forall|a: Row, b: Row| p.contains(a) && p.contains(b) implies (#[trigger] row_not_distinct(a, b) <==> a == b) by {
        let ia = choose|i: int| 0 <= i < p.len() && p[i] == a;
        let ib = choose|i: int| 0 <= i < p.len() && p[i] == b;
        assert(p.len() == q.len());
        assert(p[ia] == (g.key)(q[ia]));
        assert(p[ib] == (g.key)(q[ib]));
        let qa = q[ia];
        let qb = q[ib];
        assert((g.qual)(qa) && xs.contains(qa));
        assert((g.qual)(qb) && xs.contains(qb));
        let ma = choose|m: int| 0 <= m < xs.len() && xs[m] == q[ia];
        let mb = choose|m: int| 0 <= m < xs.len() && xs[m] == q[ib];
        assert(a == (g.key)(xs[ma]));
        assert(b == (g.key)(xs[mb]));
    }
}

/// `distinct_rows` of the qualifying keys is `gkeys` (exact keys), and `gkeys` draws from the key pool.
pub proof fn lemma_distinct_gkeys(g: QuerySpec, xs: Seq<Row>, pool: Seq<Row>)
    requires
        forall|a: Row, b: Row| pool.contains(a) && pool.contains(b) ==> (#[trigger] row_not_distinct(a, b) <==> a == b),
        forall|i: int| 0 <= i < qkeys(g, xs).len() ==> pool.contains(#[trigger] qkeys(g, xs)[i]),
    ensures
        distinct_rows(qkeys(g, xs)) == gkeys(g, xs),
        forall|i: int| 0 <= i < gkeys(g, xs).len() ==> pool.contains(#[trigger] gkeys(g, xs)[i]),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        let qk = qkeys(g, xs);
        let qki = qkeys(g, xi);
        if (g.qual)(x) {
            assert(qk =~= qki.push((g.key)(x)));
            assert forall|i: int| 0 <= i < qki.len() implies pool.contains(#[trigger] qki[i]) by {
                assert(qk[i] == qki[i]);
            }
            lemma_distinct_gkeys(g, xi, pool);
            assert(qk.drop_last() =~= qki);
            assert(qk.last() == (g.key)(x));
            assert(pool.contains(qk[qk.len() - 1]));
            lemma_has_nd_contains(gkeys(g, xi), (g.key)(x), pool);
            let d = gkeys(g, xi);
            if !d.contains((g.key)(x)) {
                assert forall|i: int| 0 <= i < gkeys(g, xs).len() implies pool.contains(#[trigger] gkeys(g, xs)[i]) by {
                    if i < d.len() {
                        assert(gkeys(g, xs)[i] == d[i]);
                    }
                }
            }
        } else {
            assert(qk =~= qki);
            lemma_distinct_gkeys(g, xi, pool);
        }
    } else {
        assert(qkeys(g, xs) =~= Seq::<Row>::empty());
    }
}

/// Argument rows of the qualifying rows of group `k` (the GROUP BY members), in order.
pub open spec fn members(g: QuerySpec, xs: Seq<Row>, k: Row) -> Seq<Row>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Seq::empty()
    } else if hit(g, xs.last(), k) {
        members(g, xs.drop_last(), k).push(arg_vals(g, xs.last()))
    } else {
        members(g, xs.drop_last(), k)
    }
}

/// `group_members` of the prepared (key, args) sequences is `members` (exact keys, `k` from the pool).
pub proof fn lemma_group_members(g: QuerySpec, xs: Seq<Row>, k: Row, pool: Seq<Row>)
    requires
        forall|a: Row, b: Row| pool.contains(a) && pool.contains(b) ==> (#[trigger] row_not_distinct(a, b) <==> a == b),
        forall|i: int| 0 <= i < qkeys(g, xs).len() ==> pool.contains(#[trigger] qkeys(g, xs)[i]),
        pool.contains(k),
    ensures
        group_members(qkeys(g, xs), qrows(g, xs).map_values(|x: Row| arg_vals(g, x)), k) == members(g, xs, k),
    decreases xs.len(),
{
    let args = |x: Row| arg_vals(g, x);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        let qk = qkeys(g, xs);
        let qki = qkeys(g, xi);
        let qa = qrows(g, xs).map_values(args);
        let qai = qrows(g, xi).map_values(args);
        if (g.qual)(x) {
            assert(qk =~= qki.push((g.key)(x)));
            assert(qa =~= qai.push(arg_vals(g, x)));
            assert forall|i: int| 0 <= i < qki.len() implies pool.contains(#[trigger] qki[i]) by {
                assert(qk[i] == qki[i]);
            }
            lemma_group_members(g, xi, k, pool);
            assert(qk.drop_last() =~= qki);
            assert(qa.drop_last() =~= qai);
            assert(pool.contains(qk[qk.len() - 1]));
            assert(row_not_distinct((g.key)(x), k) <==> (g.key)(x) == k);
        } else {
            assert(qk =~= qki);
            assert(qa =~= qai);
            lemma_group_members(g, xi, k, pool);
        }
    } else {
        assert(qkeys(g, xs) =~= Seq::<Row>::empty());
    }
}

/// A scalar aggregate's members are the argument rows of all qualifying rows.
pub proof fn lemma_scalar_members(g: QuerySpec, xs: Seq<Row>)
    requires scalar_key(g),
    ensures qrows(g, xs).map_values(|x: Row| arg_vals(g, x)) == members(g, xs, Seq::empty()),
    decreases xs.len(),
{
    let args = |x: Row| arg_vals(g, x);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_scalar_members(g, xi);
        assert((g.key)(x) == Seq::<Val>::empty());
        if (g.qual)(x) {
            assert(qrows(g, xs).map_values(args) =~= qrows(g, xi).map_values(args).push(arg_vals(g, x)));
        } else {
            assert(qrows(g, xs).map_values(args) =~= qrows(g, xi).map_values(args));
        }
    } else {
        assert(qrows(g, xs).map_values(args) =~= Seq::<Row>::empty());
    }
}

/// The aggregate columns of the members: count, kinds and exact sums (`(0, 0)` without members).
pub proof fn lemma_members_col(g: QuerySpec, xs: Seq<Row>, k: Row, j: int)
    requires 0 <= j < g.aggs.len(),
    ensures ({
        let vs = column(members(g, xs, k), j);
        &&& vs.len() == gcount(g, xs, k)
        &&& g.aggs[j] is Count || (all_of_kind(NumKind::Numeric, vs) && count_non_null(vs) == gcount(g, xs, k))
        &&& match g.aggs[j] {
            AggKind::Sum { scale } => num_sum(vs) == (gsum(g, xs, k, j), if gcount(g, xs, k) == 0 { 0nat } else { scale }),
            AggKind::Avg { scale } => num_sum(vs) == (gsum(g, xs, k, j), if gcount(g, xs, k) == 0 { 0nat } else { scale }),
            AggKind::Count => true,
        }
    }),
    decreases xs.len(),
{
    let vs = column(members(g, xs, k), j);
    if xs.len() > 0 {
        let xi = xs.drop_last();
        let x = xs.last();
        lemma_members_col(g, xi, k, j);
        let vsi = column(members(g, xi, k), j);
        if hit(g, x, k) {
            assert(vs =~= vsi.push(arg_vals(g, x)[j]));
            assert(vs.drop_last() =~= vsi);
            assert(pow10(0) == 1);
            match g.aggs[j] {
                AggKind::Count => {},
                AggKind::Sum { scale } | AggKind::Avg { scale } => {
                    // The new member's argument is at the static scale; the running sum was at that scale, or
                    // `(0, 0)` without earlier members, so `num_sum` aligns both to `scale` without changing them.
                    let acc = num_sum(vsi);
                    let c = (g.arg)(j, x);
                    if gcount(g, xi, k) == 0 {
                        assert(align(acc.0, acc.1, scale) == 0) by (nonlinear_arith)
                            requires acc.0 == 0, align(acc.0, acc.1, scale) == acc.0 * pow10((scale - acc.1) as nat);
                    }
                    assert(align(c, scale, scale) == c) by {
                        assert((scale - scale) as nat == 0nat);
                    }
                    if gcount(g, xi, k) != 0 {
                        assert(align(acc.0, scale, scale) == acc.0) by {
                            assert((scale - scale) as nat == 0nat);
                        }
                    }
                },
            }
        } else {
            assert(vs =~= vsi);
        }
    } else {
        assert(vs =~= Seq::<Val>::empty());
    }
}

/// One group's aggregate row inside `group_caps` (any count: a scalar aggregate's group may be empty, then SUM
/// and AVG are NULL and COUNT is 0, as `agg_value`).
pub proof fn lemma_agg_row(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>, k: Row)
    requires
        aggs_match(aggs, g),
        group_caps(g, xs),
    ensures agg_row(aggs, members(g, xs, k)) == Ok::<Row, SqlError>(agg_outs(g, xs, k)),
{
    let m = members(g, xs, k);
    let n = gcount(g, xs, k);
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(m, j)));
    let outs = agg_outs(g, xs, k);
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(outs[j]) by {
        lemma_members_col(g, xs, k, j);
        let vs = column(m, j);
        assert(agg_matches(aggs[j], g.aggs[j]));
        lemma_abs_bound(g, xs, k, j);
        match g.aggs[j] {
            AggKind::Count => {
                assert(n <= int8_max());
                assert(int_in_range(IntKind::Int8, n as int));
            },
            AggKind::Sum { scale } => {
                assert(gabs(g, xs, k, j) <= i128_max());
                lemma_num_in_range_small(gsum(g, xs, k, j), scale);
            },
            AggKind::Avg { scale } => {
                assert(gabs(g, xs, k, j) <= i128_max());
                let s = gsum(g, xs, k, j);
                lemma_num_in_range_small(s, scale);
                if n > 0 {
                    assert(num_div_fits(s, scale, n as int, 0));
                    lemma_avg_ok(s, scale, n as int);
                    assert(avg_sum(NumKind::Numeric, vs) == (s, scale));
                }
            },
        }
    }
    lemma_collect_all(rs, outs);
}

// ------------------------------------------------------------------------------------ link: GROUP BY and Aggregate
// Per-row arguments and (key, arguments) pairs of the kept rows, one unfolding of each denotation, and the two
// generic links.

/// The argument of SUM is its expression (one unfolding step of `agg_arg`).
pub proof fn lemma_agg_arg_sum(db: Database, env: Row, kind: NumKind, arg: Expr)
    ensures agg_arg(db, env, Agg::Sum { kind, arg }) == eval_expr(db, env, arg),
{
}

/// The argument of AVG is its expression.
pub proof fn lemma_agg_arg_avg(db: Database, env: Row, kind: NumKind, arg: Expr)
    ensures agg_arg(db, env, Agg::Avg { kind, arg }) == eval_expr(db, env, arg),
{
}

/// COUNT(*) has no argument; NULL stands in.
pub proof fn lemma_agg_arg_count(db: Database, env: Row)
    ensures agg_arg(db, env, Agg::CountStar) == Ok::<Val, SqlError>(Val::Null),
{
}

/// Per kept row: its key tuple and aggregate arguments (the GROUP BY's prepared sequence).
pub proof fn lemma_prepared(db: Database, rows: Seq<Row>, kept: Seq<Row>, cols: Seq<nat>, keys: Seq<Expr>, aggs: Seq<Agg>, g: QuerySpec)
    requires
        keys_agree(db, rows, cols, keys, g),
        args_agree(db, rows, cols, aggs, g),
        forall|i: int| 0 <= i < kept.len() ==> rows.contains(#[trigger] kept[i]) && (g.qual)(proj(kept[i], cols)),
    ensures
        collect(Seq::new(kept.len(), |i: int|
            match eval_exprs(db, Seq::<Val>::empty() + kept[i], keys) {
                Err(err) => Err(err),
                Ok(k) => match agg_args(db, Seq::<Val>::empty() + kept[i], aggs) {
                    Err(err) => Err(err),
                    Ok(a) => Ok((k, a)),
                },
            }))
            == Ok::<Seq<(Row, Row)>, SqlError>(Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), arg_vals(g, proj(kept[i], cols))))),
{
    hide(eval_exprs);
    hide(agg_args);
    let ctx = Seq::<Val>::empty();
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), arg_vals(g, proj(kept[i], cols))));
    let pre = Seq::new(kept.len(), |i: int|
        match eval_exprs(db, ctx + kept[i], keys) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, ctx + kept[i], aggs) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        });
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<(Row, Row), SqlError>(prep[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert((g.qual)(proj(rows[m], cols)));
        assert(eval_exprs(db, rows[m], keys) == Ok::<Row, SqlError>((g.key)(proj(rows[m], cols))));
        assert(agg_args(db, rows[m], aggs) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[m], cols))));
    }
    lemma_collect_all(pre, prep);
}

/// Per kept row: its aggregate arguments (the Aggregate's argument sequence).
pub proof fn lemma_prepared_args(db: Database, rows: Seq<Row>, kept: Seq<Row>, cols: Seq<nat>, aggs: Seq<Agg>, g: QuerySpec)
    requires
        args_agree(db, rows, cols, aggs, g),
        forall|i: int| 0 <= i < kept.len() ==> rows.contains(#[trigger] kept[i]) && (g.qual)(proj(kept[i], cols)),
    ensures
        collect(Seq::new(kept.len(), |i: int| agg_args(db, Seq::<Val>::empty() + kept[i], aggs)))
            == Ok::<Seq<Row>, SqlError>(Seq::new(kept.len(), |i: int| arg_vals(g, proj(kept[i], cols)))),
{
    hide(agg_args);
    let ctx = Seq::<Val>::empty();
    let args = Seq::new(kept.len(), |i: int| arg_vals(g, proj(kept[i], cols)));
    let pre = Seq::new(kept.len(), |i: int| agg_args(db, ctx + kept[i], aggs));
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<Row, SqlError>(args[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert((g.qual)(proj(rows[m], cols)));
        assert(agg_args(db, rows[m], aggs) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[m], cols))));
    }
    lemma_collect_all(pre, args);
}

/// GROUP BY over the qualifying rows' (key, arguments): the full row of every group, first-occurrence order.
pub proof fn lemma_groups(g: QuerySpec, aggs: Seq<Agg>, xs: Seq<Row>)
    requires
        aggs_match(aggs, g),
        keys_exact(g, xs),
        group_caps(g, xs),
    ensures
        group_rows(aggs, qkeys(g, xs), qrows(g, xs).map_values(|x: Row| arg_vals(g, x)))
            == Ok::<Seq<Row>, SqlError>(gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k))),
{
    let ks = qkeys(g, xs);
    let avs = qrows(g, xs).map_values(|x: Row| arg_vals(g, x));
    let pool = key_pool(g, xs);
    lemma_pool_exact(g, xs);
    assert forall|i: int| 0 <= i < qkeys(g, xs).len() implies pool.contains(#[trigger] qkeys(g, xs)[i]) by {
        assert(pool[i] == qkeys(g, xs)[i]);
    }
    lemma_distinct_gkeys(g, xs, pool);
    let ds = gkeys(g, xs);
    lemma_gkeys(g, xs);
    let grs = Seq::new(ds.len(), |gi: int|
        match agg_row(aggs, group_members(ks, avs, ds[gi])) {
            Ok(a) => Ok(ds[gi] + a),
            Err(e) => Err(e),
        });
    let full = ds.map_values(|k: Row| full_row(g, xs, k));
    assert forall|gi: int| 0 <= gi < grs.len() implies #[trigger] grs[gi] == Ok::<Row, SqlError>(full[gi]) by {
        let k = ds[gi];
        assert(pool.contains(k));
        lemma_group_members(g, xs, k, pool);
        assert(ds.contains(k));
        lemma_agg_row(g, aggs, xs, k);
    }
    lemma_collect_all(grs, full);
}

/// One step of the GROUP BY denotation over an evaluated input and prepared (key, arguments) sequence.
pub proof fn lemma_groupby_unfold(db: Database, input: Query, keys: Seq<Expr>, aggs: Seq<Agg>, kept: Seq<Row>, prep: Seq<(Row, Row)>)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(kept),
        collect(Seq::new(kept.len(), |i: int|
            match eval_exprs(db, Seq::<Val>::empty() + kept[i], keys) {
                Err(err) => Err(err),
                Ok(k) => match agg_args(db, Seq::<Val>::empty() + kept[i], aggs) {
                    Err(err) => Err(err),
                    Ok(a) => Ok((k, a)),
                },
            })) == Ok::<Seq<(Row, Row)>, SqlError>(prep),
    ensures
        eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) })
            == group_rows(aggs, prep.map_values(|p: (Row, Row)| p.0), prep.map_values(|p: (Row, Row)| p.1)),
{
    lemma_collect_pointwise::<(Row, Row)>();
}

/// One step of the Aggregate denotation over an evaluated input and its argument sequence.
pub proof fn lemma_aggregate_unfold(db: Database, input: Query, aggs: Seq<Agg>, kept: Seq<Row>, args: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(kept),
        collect(Seq::new(kept.len(), |i: int| agg_args(db, Seq::<Val>::empty() + kept[i], aggs))) == Ok::<Seq<Row>, SqlError>(args),
    ensures
        eval_query(db, Seq::empty(), Query::Aggregate { aggs, input: Box::new(input) })
            == match agg_row(aggs, args) {
                Err(err) => Err(err),
                Ok(row) => Ok::<Relation, SqlError>(seq![row]),
            },
{
    lemma_collect_pointwise::<Row>();
}

/// The grouped link: under per-row agreement, exact keys and `group_caps`, a GROUP BY over an input that
/// evaluates to the qualifying rows of `rows` (a WHERE over an input evaluating to `rows`, `lemma_filter_rows`, or
/// that input itself with an always-true condition, `lemma_table_rows`) is the full row of every group key, in
/// first-occurrence order.
pub proof fn lemma_group_query(db: Database, rows: Seq<Row>, cols: Seq<nat>, input: Query, keys: Seq<Expr>, aggs: Seq<Agg>, g: QuerySpec)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols)))),
        keys_agree(db, rows, cols, keys, g),
        args_agree(db, rows, cols, aggs, g),
        aggs_match(aggs, g),
        keys_exact(g, proj_all(rows, cols)),
        group_caps(g, proj_all(rows, cols)),
    ensures ({
        let xs = proj_all(rows, cols);
        eval_query(db, Seq::empty(), Query::GroupBy { keys, aggs, input: Box::new(input) })
            == Ok::<Relation, SqlError>(gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k)))
    }),
{
    hide(eval_pred);
    hide(eval_exprs);
    hide(agg_args);
    hide(group_rows);
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let q = qrows(g, xs);
    lemma_kept_rows(g, rows, cols);
    lemma_prepared(db, rows, kept, cols, keys, aggs, g);
    let prep = Seq::new(kept.len(), |i: int| ((g.key)(proj(kept[i], cols)), arg_vals(g, proj(kept[i], cols))));
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= qkeys(g, xs));
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= q.map_values(|x: Row| arg_vals(g, x)));
    lemma_groups(g, aggs, xs);
    lemma_groupby_unfold(db, input, keys, aggs, kept, prep);
}

/// The scalar link: under per-row agreement of the arguments and `group_caps`, an Aggregate (no GROUP BY)
/// over an input that evaluates to the qualifying rows of `rows` is exactly one row, `key ++ aggregates` of the
/// empty key: also on an empty input (COUNT 0, SUM and AVG NULL).
pub proof fn lemma_aggregate_query(db: Database, rows: Seq<Row>, cols: Seq<nat>, input: Query, aggs: Seq<Agg>, g: QuerySpec)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(keep_true(rows, qual_truths(g, proj_all(rows, cols)))),
        args_agree(db, rows, cols, aggs, g),
        aggs_match(aggs, g),
        scalar_key(g),
        group_caps(g, proj_all(rows, cols)),
    ensures ({
        let xs = proj_all(rows, cols);
        eval_query(db, Seq::empty(), Query::Aggregate { aggs, input: Box::new(input) })
            == Ok::<Relation, SqlError>(seq![full_row(g, xs, Seq::empty())])
    }),
{
    hide(eval_pred);
    hide(agg_args);
    hide(agg_row);
    let xs = proj_all(rows, cols);
    let kept = keep_true(rows, qual_truths(g, xs));
    let q = qrows(g, xs);
    lemma_kept_rows(g, rows, cols);
    lemma_prepared_args(db, rows, kept, cols, aggs, g);
    let args = Seq::new(kept.len(), |i: int| arg_vals(g, proj(kept[i], cols)));
    assert(args =~= q.map_values(|x: Row| arg_vals(g, x)));
    lemma_scalar_members(g, xs);
    reveal(agg_row);
    lemma_agg_row(g, aggs, xs, Seq::empty());
    assert(Seq::<Val>::empty() + agg_outs(g, xs, Seq::empty()) =~= agg_outs(g, xs, Seq::empty()));
    lemma_aggregate_unfold(db, input, aggs, kept, args);
}

// ------------------------------------------------------------------------------ link: projection and the top level
// `SELECT` of columns over the aggregate rows, and the step from the body's rows to `spec::order::ordered_ok`.

/// Column references `idxs` as expressions.
pub open spec fn col_exprs(idxs: Seq<nat>) -> Seq<Expr> {
    idxs.map_values(|i: nat| Expr::Col(i))
}

/// A list of column references evaluates to the selected values.
pub proof fn lemma_eval_cols(db: Database, env: Row, idxs: Seq<nat>)
    requires forall|m: int| 0 <= m < idxs.len() ==> #[trigger] idxs[m] < env.len(),
    ensures eval_exprs(db, env, col_exprs(idxs)) == Ok::<Row, SqlError>(select(env, idxs)),
    decreases idxs.len(),
{
    if idxs.len() == 0 {
        assert(col_exprs(idxs) =~= Seq::<Expr>::empty());
        lemma_eval_exprs_empty(db, env);
        assert(select(env, idxs) =~= Seq::<Val>::empty());
    } else {
        let init = idxs.drop_last();
        assert forall|m: int| 0 <= m < init.len() implies #[trigger] init[m] < env.len() by {
            assert(init[m] == idxs[m]);
        }
        lemma_eval_cols(db, env, init);
        lemma_eval_exprs_step(db, env, col_exprs(idxs));
        assert(col_exprs(idxs).drop_last() =~= col_exprs(init));
        assert(col_exprs(idxs).last() == Expr::Col(idxs.last()));
        assert(idxs[idxs.len() - 1] < env.len());
        assert(select(env, idxs) =~= select(env, init).push(env[idxs.last() as int]));
    }
}

/// `SELECT` of columns of a relation whose rows have `width` columns.
pub proof fn lemma_project_cols(db: Database, input: Query, rows: Relation, outs: Seq<nat>, width: nat)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(rows),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == width,
        forall|m: int| 0 <= m < outs.len() ==> #[trigger] outs[m] < width,
    ensures
        eval_query(db, Seq::empty(), Query::Project { exprs: col_exprs(outs), input: Box::new(input) })
            == Ok::<Relation, SqlError>(rows.map_values(|r: Row| select(r, outs))),
{
    let ctx = Seq::<Val>::empty();
    let rs = Seq::new(rows.len(), |i: int| eval_exprs(db, ctx + rows[i], col_exprs(outs)));
    let vs = rows.map_values(|r: Row| select(r, outs));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(vs[i]) by {
        assert(ctx + rows[i] =~= rows[i]);
        assert forall|m: int| 0 <= m < outs.len() implies #[trigger] outs[m] < rows[i].len() by {
            assert(outs[m] < width);
        }
        lemma_eval_cols(db, rows[i], outs);
    }
    lemma_collect_all(rs, vs);
    lemma_collect_pointwise::<Row>();
    assert(eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows));
}

/// Selecting all positions `0..n` of an `n`-column row keeps it.
pub proof fn lemma_select_identity(r: Row, outs: Seq<nat>)
    requires outs.len() == r.len(), forall|m: int| 0 <= m < outs.len() ==> #[trigger] outs[m] == m,
    ensures select(r, outs) == r,
{
    assert(select(r, outs) =~= r);
}

/// The top level: when the body evaluates to the normal form's result rows, every output `result_ok` allows is
/// an allowed output of the statement (same witness permutation; ORDER BY, OFFSET and LIMIT are the statement's).
pub proof fn lemma_ordered_link(db: Database, oq: OrderedQuery, g: QuerySpec, rows: Seq<Row>, out: Relation)
    requires
        denote_body(db, oq) == Ok::<Relation, SqlError>(result_rows(g, rows)),
        result_ok(g, oq.keys, oq.offset, oq.limit, rows, out),
    ensures ordered_ok(db, oq, Ok::<Relation, SqlError>(out)),
{
    let p = choose|p: Seq<Row>| #![trigger sorted_by(oq.keys, p)]
        p.to_multiset() == result_rows(g, rows).to_multiset() && sorted_by(oq.keys, p) && out == slice_rows(p, oq.offset, oq.limit);
    assert(sorted_by(oq.keys, p));
}

// ------------------------------------------------------------------------------------- per-node numeric arithmetic
// Digit bounds that keep products and sums of numeric expressions inside PostgreSQL's numeric format.

/// `|c| < 10^d` with `d` digits inside PostgreSQL's format at scale `s`: the numeric value is in range.
pub proof fn lemma_digits_in_range(c: int, s: nat, d: nat)
    requires abs(c) < pow10(d), d <= numeric_int_digits_max() + s,
    ensures num_in_range(c, s),
{
    lemma_decimal_digits_bound(abs(c), d);
}

/// A product of two numeric nodes with digit bounds.
pub proof fn lemma_node_mul(db: Database, env: Row, a: Expr, b: Expr, ca: int, sa: nat, da: nat, cb: int, sb: nat, db2: nat)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(Val::Num { coeff: ca, scale: sa }),
        eval_expr(db, env, b) == Ok::<Val, SqlError>(Val::Num { coeff: cb, scale: sb }),
        abs(ca) < pow10(da),
        abs(cb) < pow10(db2),
        da + db2 <= numeric_int_digits_max() + sa + sb,
    ensures
        eval_expr(db, env, Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(a), b: Box::new(b) })
            == Ok::<Val, SqlError>(Val::Num { coeff: ca * cb, scale: sa + sb }),
        abs(ca * cb) < pow10(da + db2),
{
    lemma_pow10_add(da, db2);
    let (x, y, px, py) = (abs(ca), abs(cb), pow10(da), pow10(db2));
    assert(abs(ca * cb) == x * y) by (nonlinear_arith)
        requires x == abs(ca), y == abs(cb);
    assert(x * y < px * py) by (nonlinear_arith)
        requires 0 <= x < px, 0 <= y < py;
    lemma_digits_in_range(ca * cb, sa + sb, da + db2);
}

/// A sum or difference of two numeric nodes with digit bounds, at the common scale `s` (factors `fa`, `fb`).
pub proof fn lemma_node_add(db: Database, env: Row, op: ArithOp, a: Expr, b: Expr, ca: int, sa: nat, da: nat, cb: int, sb: nat, db2: nat, s: nat, fa: int, fb: int, d: nat)
    requires
        !(op is Mul),
        eval_expr(db, env, a) == Ok::<Val, SqlError>(Val::Num { coeff: ca, scale: sa }),
        eval_expr(db, env, b) == Ok::<Val, SqlError>(Val::Num { coeff: cb, scale: sb }),
        abs(ca) < pow10(da),
        abs(cb) < pow10(db2),
        s == max_nat(sa, sb),
        pow10((s - sa) as nat) == fa,
        pow10((s - sb) as nat) == fb,
        da + (s - sa) < d,
        db2 + (s - sb) < d,
        d <= numeric_int_digits_max() + s,
    ensures
        eval_expr(db, env, Expr::Arith { op, kind: NumKind::Numeric, a: Box::new(a), b: Box::new(b) })
            == Ok::<Val, SqlError>(Val::Num { coeff: if op is Add { ca * fa + cb * fb } else { ca * fa - cb * fb }, scale: s }),
        abs(if op is Add { ca * fa + cb * fb } else { ca * fa - cb * fb }) < pow10(d),
{
    let (ka, kb) = ((s - sa) as nat, (s - sb) as nat);
    lemma_pow10_add(da, ka);
    lemma_pow10_add(db2, kb);
    lemma_pow10_monotone(da + ka, (d - 1) as nat);
    lemma_pow10_monotone(db2 + kb, (d - 1) as nat);
    lemma_pow10_positive(ka);
    lemma_pow10_positive(kb);
    assert(pow10(d) == 10 * pow10((d - 1) as nat));
    let m = pow10((d - 1) as nat);
    let (x, y) = (abs(ca), abs(cb));
    assert(abs(ca * fa) < m) by (nonlinear_arith)
        requires x == abs(ca), 0 <= x < pow10(da), fa >= 1, pow10(da + ka) == pow10(da) * fa, pow10(da + ka) <= m;
    assert(abs(cb * fb) < m) by (nonlinear_arith)
        requires y == abs(cb), 0 <= y < pow10(db2), fb >= 1, pow10(db2 + kb) == pow10(db2) * fb, pow10(db2 + kb) <= m;
    let c = if op is Add { ca * fa + cb * fb } else { ca * fa - cb * fb };
    assert(align(ca, sa, s) == ca * fa);
    assert(align(cb, sb, s) == cb * fb);
    lemma_digits_in_range(c, s, d);
}

} // verus!
