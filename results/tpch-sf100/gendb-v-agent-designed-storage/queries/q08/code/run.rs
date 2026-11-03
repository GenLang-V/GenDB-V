//! The Q8 call around the scan kernel: the stored lineitem range worth scanning (`scan_bounds`), its split into
//! worker tasks (`make_tasks`), the exact merge of the tasks' per-year accumulators (`merge_outs`) and the statement's
//! outcome from the merged accumulators (`answer_of`).
//!
//! Every accumulator is exact: a merge whose absolute volume mass would pass `i128::MAX` reports `ovf`, which proves
//! the whole scan's mass passes it (masses never decrease along a range), so the statement is outside its capacity.
use vstd::prelude::*;
use crate::gendb_entry::{Answer, answer_meets, bound_db, outcome_ok};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::fns::div::{num_div, num_div_fits};
use crate::spec::order::ordered_ok;
use crate::exec::value::EVal;
use crate::exec::fns::div::num_div_exec;
use crate::query::{query_spec_at, param_domain};
use super::sql::*;
use super::group::*;
use super::answer::*;
use super::model::*;
use super::kernel::*;
use super::bind::acc_meets;
use std::sync::Arc;

verus! {

// ------------------------------------------------------------------------------------------------ the scanned range

/// The stored lineitem rows outside `[la, lb)` contribute nothing.
pub open spec fn bounds_ok(c: Cols, f: PFilter, nt: NTab, la: int, lb: int) -> bool {
    &&& 0 <= la <= lb <= c.n_l
    &&& forall|j: int| 0 <= j < la ==> #[trigger] lc(c, pm_of(f), nt_view(nt), j) is None
    &&& forall|j: int| lb <= j < c.n_l ==> #[trigger] lc(c, pm_of(f), nt_view(nt), j) is None
}

/// The whole scan is the scan of `[la, lb)`.
pub proof fn lemma_bounds(c: Cols, f: PFilter, nt: NTab, la: int, lb: int)
    requires bounds_ok(c, f, nt, la, lb),
    ensures acc_range(c, pm_of(f), nt_view(nt), 0, c.n_l as int) == acc_range(c, pm_of(f), nt_view(nt), la, lb),
{
    let (pm, ns) = (pm_of(f), nt_view(nt));
    lemma_acc_none(c, pm, ns, 0, la);
    lemma_acc_none(c, pm, ns, lb, c.n_l as int);
    lemma_acc_split(c, pm, ns, 0, la, lb);
    lemma_acc_split(c, pm, ns, 0, lb, c.n_l as int);
    lemma_acc_add_zero(acc_range(c, pm, ns, la, lb));
    lemma_acc_add_zero(acc_range(c, pm, ns, 0, lb));
}

// ------------------------------------------------------------------------------------------------ tasks

/// Task `t` of `ts` scans `[bs[t], bs[t + 1])` with the shared structures `c`, `f`, `nt`.
pub open spec fn tasks_ok(ts: Seq<ScanTask>, bs: Seq<int>, c: Cols, f: PFilter, nt: NTab) -> bool {
    &&& bs.len() == ts.len() + 1
    &&& forall|t: int| 0 <= t < ts.len() ==> {
        &&& (#[trigger] ts[t]).c == c && *ts[t].f == f && *ts[t].nt == nt
        &&& ts[t].l0 as int == bs[t] && ts[t].l1 as int == bs[t + 1]
        &&& ts[t].pre()
    }
}

/// At most `workers` tasks of about equal row counts over `[la, lb)`, each of at least `BLK` rows when possible.
pub fn make_tasks(c: Cols, f: Arc<PFilter>, nt: Arc<NTab>, la: usize, lb: usize, clustered: bool, workers: usize)
    -> (r: (Vec<ScanTask>, Ghost<Seq<int>>))
    requires
        scan_pre(c, *f, *nt, la as int, lb as int, clustered),
        1 <= workers <= MAX_WORKERS,
    ensures
        1 <= r.0@.len() <= workers,
        tasks_ok(r.0@, r.1@, c, *f, *nt),
        r.1@[0] == la, r.1@[r.0@.len() as int] == lb,
{
    let span = lb - la;
    let cap = span / BLK + 1;
    let nt_count = if workers < cap { workers } else { cap };
    let chunk = span / nt_count;
    let mut tasks: Vec<ScanTask> = Vec::new();
    let ghost mut bs: Seq<int> = seq![la as int];
    let mut t: usize = 0;
    while t < nt_count
        invariant
            scan_pre(c, *f, *nt, la as int, lb as int, clustered),
            1 <= nt_count <= workers,
            span == lb - la,
            chunk == span / nt_count,
            t <= nt_count,
            tasks@.len() == t,
            bs.len() == t + 1,
            bs[0] == la,
            t < nt_count ==> bs[t as int] == la + chunk * t,
            t == nt_count ==> bs[t as int] == lb,
            bs[t as int] <= lb,
            tasks_ok(tasks@, bs, c, *f, *nt),
        decreases nt_count - t,
    {
        proof {
            assert(chunk * nt_count <= span) by (nonlinear_arith) requires chunk == span / nt_count, nt_count >= 1;
            assert(chunk * (t + 1) <= chunk * nt_count) by (nonlinear_arith) requires t + 1 <= nt_count, chunk >= 0;
            assert(chunk * (t + 1) == chunk * t + chunk) by (nonlinear_arith);
        }
        let l0 = la + chunk * t;
        let l1 = if t + 1 == nt_count { lb } else { la + chunk * (t + 1) };
        let ghost old_tasks = tasks@;
        let ghost old_bs = bs;
        let task = ScanTask {
            c,
            f: f.clone(),
            nt: nt.clone(),
            l0,
            l1,
            clustered,
            cand1: vec![0u16; BLK],
            cand2: vec![0u16; BLK],
        };
        proof {
            assert(task.pre());
        }
        tasks.push(task);
        proof {
            bs = bs.push(l1 as int);
            assert forall|k: int| 0 <= k < tasks@.len() implies {
                &&& (#[trigger] tasks@[k]).c == c && *tasks@[k].f == *f && *tasks@[k].nt == *nt
                &&& tasks@[k].l0 as int == bs[k] && tasks@[k].l1 as int == bs[k + 1]
                &&& tasks@[k].pre()
            } by {
                if k < t {
                    assert(tasks@[k] == old_tasks[k]);
                    assert(bs[k] == old_bs[k] && bs[k + 1] == old_bs[k + 1]);
                }
            }
        }
        t = t + 1;
    }
    (tasks, Ghost(bs))
}

// ------------------------------------------------------------------------------------------------ merge

/// Adds the accumulators `b` (of `nb` rows) to `a` (of `na` rows); `false` (with `a` unchanged in meaning) when a
/// year's mass would pass `i128::MAX`.
pub fn acc_merge(a: &mut Acc, b: &Acc, Ghost(na): Ghost<int>, Ghost(nb): Ghost<int>) -> (ok: bool)
    requires
        !old(a).ovf,
        acc_sane(acc_view(*old(a)), na),
        acc_sane(acc_view(*b), nb),
        0 <= na, 0 <= nb, na + nb <= usize::MAX,
    ensures
        !final(a).ovf,
        ok ==> acc_view(*final(a)) == acc_add(acc_view(*old(a)), acc_view(*b)) && acc_sane(acc_view(*final(a)), na + nb),
        !ok ==> acc_add(acc_view(*old(a)), acc_view(*b)).m0 > i128::MAX
            || acc_add(acc_view(*old(a)), acc_view(*b)).m1 > i128::MAX,
{
    if a.m0 > i128::MAX - b.m0 || a.m1 > i128::MAX - b.m1 {
        return false;
    }
    a.c0 = a.c0 + b.c0;
    a.v0 = a.v0 + b.v0;
    a.hc0 = a.hc0 + b.hc0;
    a.hv0 = a.hv0 + b.hv0;
    a.m0 = a.m0 + b.m0;
    a.c1 = a.c1 + b.c1;
    a.v1 = a.v1 + b.v1;
    a.hc1 = a.hc1 + b.hc1;
    a.hv1 = a.hv1 + b.hv1;
    a.m1 = a.m1 + b.m1;
    true
}

/// The merged accumulators of task outputs over the adjacent ranges `[bs[t], bs[t + 1])`; `ovf` when the whole
/// range's mass passes `i128::MAX`.
pub fn merge_outs(outs: &Vec<Acc>, Ghost(c): Ghost<Cols>, Ghost(f): Ghost<PFilter>, Ghost(nt): Ghost<NTab>,
    Ghost(bs): Ghost<Seq<int>>) -> (r: Acc)
    requires
        outs@.len() >= 1,
        bs.len() == outs@.len() + 1,
        0 <= bs[0],
        bs[outs@.len() as int] <= c.n_l,
        forall|t: int| 0 <= t < outs@.len() ==> #[trigger] bs[t] <= bs[t + 1],
        forall|t: int| 0 <= t < outs@.len() ==> scan_post(c, f, nt, bs[t], bs[t + 1], #[trigger] outs@[t]),
    ensures
        !r.ovf ==> acc_view(r) == acc_range(c, pm_of(f), nt_view(nt), bs[0], bs[outs@.len() as int]),
        r.ovf ==> acc_range(c, pm_of(f), nt_view(nt), bs[0], bs[outs@.len() as int]).m0 > i128::MAX
            || acc_range(c, pm_of(f), nt_view(nt), bs[0], bs[outs@.len() as int]).m1 > i128::MAX,
{
    let ghost pm = pm_of(f);
    let ghost ns = nt_view(nt);
    let n = outs.len();
    let ghost end = bs[n as int];
    // bs is nondecreasing, so every boundary lies in [bs[0], end].
    proof {
        assert forall|t: int| 0 <= t <= n implies bs[0] <= #[trigger] bs[t] <= end by {
            lemma_bs_mono(bs, n as int, 0, t);
            lemma_bs_mono(bs, n as int, t, n as int);
        }
    }
    let mut tot = acc_new();
    let mut t: usize = 0;
    while t < n
        invariant
            n == outs@.len(),
            bs.len() == n + 1,
            end == bs[n as int],
            0 <= bs[0], end <= c.n_l,
            forall|k: int| 0 <= k <= n ==> bs[0] <= #[trigger] bs[k] <= end,
            forall|k: int| 0 <= k < n ==> #[trigger] bs[k] <= bs[k + 1],
            forall|k: int| 0 <= k < n ==> scan_post(c, f, nt, bs[k], bs[k + 1], #[trigger] outs@[k]),
            pm == pm_of(f), ns == nt_view(nt),
            t <= n,
            !tot.ovf,
            acc_view(tot) == acc_range(c, pm, ns, bs[0], bs[t as int]),
        decreases n - t,
    {
        let o = &outs[t];
        let ghost (a, b, e) = (bs[0], bs[t as int], bs[t + 1]);
        proof {
            assert(scan_post(c, f, nt, b, e, outs@[t as int]));
            lemma_acc_split(c, pm, ns, a, b, e);
            lemma_acc_range_sane(c, pm, ns, a, b);
            lemma_acc_range_sane(c, pm, ns, b, e);
            lemma_acc_mass_mono(c, pm, ns, a, e, end);
        }
        if o.ovf {
            proof {
                lemma_acc_range_sane(c, pm, ns, a, b);
                lemma_acc_mass_mono(c, pm, ns, b, e, end);
                lemma_acc_split(c, pm, ns, a, b, end);
                lemma_acc_split(c, pm, ns, b, e, end);
                lemma_acc_range_sane(c, pm, ns, e, end);
            }
            let mut r = acc_new();
            r.ovf = true;
            return r;
        }
        let ok = acc_merge(&mut tot, o, Ghost(b - a), Ghost(e - b));
        if !ok {
            proof {
                lemma_acc_mass_mono(c, pm, ns, a, e, end);
            }
            let mut r = acc_new();
            r.ovf = true;
            return r;
        }
        t = t + 1;
    }
    tot
}

/// Boundaries of a nondecreasing sequence are ordered.
proof fn lemma_bs_mono(bs: Seq<int>, n: int, a: int, b: int)
    requires
        bs.len() == n + 1,
        forall|k: int| 0 <= k < n ==> #[trigger] bs[k] <= bs[k + 1],
        0 <= a <= b <= n,
    ensures bs[a] <= bs[b],
    decreases b - a,
{
    if a < b {
        lemma_bs_mono(bs, n, a, b - 1);
        assert(bs[b - 1] <= bs[b]);
    }
}

// ------------------------------------------------------------------------------------------------ the outcome

/// Every database bound to the parts has the year groups `s`.
pub open spec fn acc_all(sv: StoresView, ps: Seq<Literal>, s: AccS) -> bool {
    forall|db: Database| #[trigger] bound_db(sv, db) ==> db_ok(db) && acc_meets(db, ps, s)
}

/// A mass past `i128::MAX`: the statement is outside its capacity domain.
pub proof fn lemma_capacity(sv: StoresView, ps: Seq<Literal>, s: AccS)
    requires acc_all(sv, ps, s), param_domain(ps), s.m0 > i128::MAX || s.m1 > i128::MAX,
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        assert(db_ok(db) && acc_meets(db, ps, s));
        if s.m0 > i128::MAX {
            lemma_cap_mass(db, ps, 1995);
        } else {
            lemma_cap_mass(db, ps, 1996);
        }
    }
}

/// The year row `[y, v]`.
fn year_row(y: i128, v: EVal) -> (r: Vec<EVal>)
    ensures r@.len() == 2, r@[0] == (EVal::Num { coeff: y, scale: 0 }), r@[1] == v,
{
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Num { coeff: y, scale: 0 });
    row.push(v);
    row
}

/// The share of one present year from its accumulators (`hv`: SUM of the CASE values, `hc`: rows of nation `$1`,
/// `v`: SUM(volume)); `None` when the quotient is outside its format.
fn year_share(hv: i128, hc: usize, v: i128) -> (r: Option<EVal>)
    requires v != 0, hv > i128::MIN,
    ensures
        r matches Some(x) ==> num_div(hv as int, case_scale(hc as int), v as int, 4) == Ok::<Val, SqlError>(x@),
        r is None ==> !num_div_fits(hv as int, case_scale(hc as int), v as int, 4),
{
    let s: u32 = if hc > 0 { 4 } else { 0 };
    proof {
        lemma_share_ok(hv as int, s as nat, v as int);
    }
    match num_div_exec(hv, s, v, 4) {
        Ok(Ok(x)) => Some(x),
        Ok(Err(_)) => {
            proof { assert(false); }
            None
        },
        Err(_) => None,
    }
}

/// The scale of the CASE sum: 4 when some row has nation `$1`, else 0 (the literal 0).
pub open spec fn case_scale(hc: int) -> nat {
    if hc > 0 { 4nat } else { 0nat }
}

/// A present year whose volume sum is 0: the statement fails with division by zero.
proof fn lemma_zero_all(sv: StoresView, ps: Seq<Literal>, sa: AccS, y: int)
    requires
        acc_all(sv, ps, sa), param_domain(ps), sa.m0 <= i128::MAX, sa.m1 <= i128::MAX,
        y == 1995 ==> sa.c0 > 0 && sa.v0 == 0,
        y == 1996 ==> sa.c1 > 0 && sa.v1 == 0,
        y == 1995 || y == 1996,
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(SqlError::DivisionByZero))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::SqlError(SqlError::DivisionByZero))) by {
        assert(db_ok(db) && acc_meets(db, ps, sa));
        lemma_ans_zero(db, ps, y);
    }
}

/// No present year has volume sum 0.
pub open spec fn acc_no_zero(sa: AccS) -> bool {
    &&& sa.c0 > 0 ==> sa.v0 != 0
    &&& sa.c1 > 0 ==> sa.v1 != 0
}

/// A present year whose quotient is outside its format: the statement is outside its capacity domain.
proof fn lemma_capdiv_all(sv: StoresView, ps: Seq<Literal>, sa: AccS, y: int)
    requires
        acc_all(sv, ps, sa), param_domain(ps), sa.m0 <= i128::MAX, sa.m1 <= i128::MAX, acc_no_zero(sa),
        y == 1995 ==> sa.c0 > 0 && !num_div_fits(sa.hv0, case_scale(sa.hc0), sa.v0, 4),
        y == 1996 ==> sa.c1 > 0 && !num_div_fits(sa.hv1, case_scale(sa.hc1), sa.v1, 4),
        y == 1995 || y == 1996,
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps),
        Ok::<Answer, QueryError>(Answer::Capacity)) by {
        assert(db_ok(db) && acc_meets(db, ps, sa));
        lemma_ans_cap_div(db, ps, y);
    }
}

/// The result rows from the shares of the present years (`None`: the year is absent).
pub open spec fn rows_opt(a: Option<Val>, b: Option<Val>) -> Seq<Row> {
    let ra: Seq<Row> = match a { Some(x) => seq![yrow(1995, x)], None => Seq::empty() };
    let rb: Seq<Row> = match b { Some(x) => seq![yrow(1996, x)], None => Seq::empty() };
    ra + rb
}

pub open spec fn opt_view(o: Option<EVal>) -> Option<Val> {
    match o { Some(x) => Some(x@), None => None }
}

/// The share of a present year is the quotient of its accumulators.
pub open spec fn share_ok(present: bool, o: Option<Val>, hv: int, hc: int, v: int) -> bool {
    &&& (o is Some) == present
    &&& present ==> num_div(hv, case_scale(hc), v, 4) == Ok::<Val, SqlError>(o->Some_0)
}

/// Every present year's quotient is a value: the sorted year rows are the result.
proof fn lemma_rows_all(sv: StoresView, ps: Seq<Literal>, sa: AccS, o5: Option<Val>, o6: Option<Val>)
    requires
        acc_all(sv, ps, sa), param_domain(ps), sa.m0 <= i128::MAX, sa.m1 <= i128::MAX, acc_no_zero(sa),
        share_ok(sa.c0 > 0, o5, sa.hv0, sa.hc0, sa.v0),
        share_ok(sa.c1 > 0, o6, sa.hv1, sa.hc1, sa.v1),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps),
            Ok::<Relation, SqlError>(rows_opt(o5, o6))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps),
        Ok::<Relation, SqlError>(rows_opt(o5, o6))) by {
        assert(db_ok(db) && acc_meets(db, ps, sa));
        lemma_ans_rows(db, ps);
        if sa.c0 > 0 {
            assert(o5->Some_0 == yshare(db, ps, 1995));
        }
        if sa.c1 > 0 {
            assert(o6->Some_0 == yshare(db, ps, 1996));
        }
        assert(rows_opt(o5, o6) == out_rows(db, ps));
    }
}

/// Rows whose view is a result of every bound database meet the claim.
proof fn lemma_meets_rows(sv: StoresView, ps: Seq<Literal>, rows: Vec<Vec<EVal>>, want: Seq<Row>)
    requires
        crate::exec::relational::schema::view_rows(rows@) == want,
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(want)),
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
}

/// The result rows of the present years' shares.
fn make_rows(o5: Option<EVal>, o6: Option<EVal>) -> (rows: Vec<Vec<EVal>>)
    ensures crate::exec::relational::schema::view_rows(rows@) == rows_opt(opt_view(o5), opt_view(o6)),
{
    let ghost (g5, g6) = (opt_view(o5), opt_view(o6));
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    if let Some(x) = o5 {
        rows.push(year_row(1995, x));
    }
    if let Some(x) = o6 {
        rows.push(year_row(1996, x));
    }
    proof {
        let vr = crate::exec::relational::schema::view_rows(rows@);
        let want = rows_opt(g5, g6);
        assert(vr.len() == want.len());
        assert forall|i: int| 0 <= i < vr.len() implies vr[i] == want[i] by {
            assert(vr[i] =~= want[i]);
        }
        assert(vr =~= want);
    }
    rows
}

/// The statement's outcome from the exact per-year accumulators `s` of every bound database.
pub fn answer_of(s: &Acc, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Answer, QueryError>)
    requires
        !s.ovf,
        param_domain(ps),
        acc_all(sv, ps, acc_view(*s)),
        acc_sane(acc_view(*s), usize::MAX as int),
    ensures answer_meets(sv, ps, r),
{
    let ghost sa = acc_view(*s);
    if s.c0 > 0 && s.v0 == 0 {
        proof { lemma_zero_all(sv, ps, sa, 1995); }
        return Ok(Answer::SqlError(SqlError::DivisionByZero));
    }
    if s.c1 > 0 && s.v1 == 0 {
        proof { lemma_zero_all(sv, ps, sa, 1996); }
        return Ok(Answer::SqlError(SqlError::DivisionByZero));
    }
    proof {
        assert(acc_no_zero(sa));
    }
    let mut o5: Option<EVal> = None;
    if s.c0 > 0 {
        o5 = year_share(s.hv0, s.hc0, s.v0);
        if o5.is_none() {
            proof { lemma_capdiv_all(sv, ps, sa, 1995); }
            return Ok(Answer::Capacity);
        }
    }
    let mut o6: Option<EVal> = None;
    if s.c1 > 0 {
        o6 = year_share(s.hv1, s.hc1, s.v1);
        if o6.is_none() {
            proof { lemma_capdiv_all(sv, ps, sa, 1996); }
            return Ok(Answer::Capacity);
        }
    }
    let ghost (g5, g6) = (opt_view(o5), opt_view(o6));
    proof {
        lemma_rows_all(sv, ps, sa, g5, g6);
    }
    let rows = make_rows(o5, o6);
    proof {
        lemma_meets_rows(sv, ps, rows, rows_opt(g5, g6));
    }
    Ok(Answer::Rows(rows))
}

} // verus!
