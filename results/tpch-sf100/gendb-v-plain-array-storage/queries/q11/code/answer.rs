//! From group tables to the answer: the HAVING threshold `total * $2 / 10^10` rounded down (`threshold`, or the
//! capacity answer when `total * $2` leaves `i128`), the result columns of a sorted list (`columns_of`), and the
//! answer of the general serial path (`general_answer`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::query::query_spec_at;
use crate::gendb_entry::{Answer, answer_meets, bound_db, outcome_ok};
use crate::gendb_entry::results::{ResultColumn, ResultColumns, columns_view, columns_wf, lemma_columns_view_eq, column_value};
use crate::gendb_entry::stores::StoresView;
use crate::link::expr::i128_max;
use crate::agent::model::*;
use crate::agent::sem::params_of;
use crate::agent::normal::*;
use crate::agent::groups::*;
use crate::agent::output::*;
use crate::agent::scan::{bits_ok, GO, OVER, imax};
use crate::agent::filter::{Sorted, FilterTask};
use crate::agent::fallback::{fallback_groups, groups_ok};
use crate::agent::common::msort::{pairs, desc};
use crate::gendb_entry::parallel::WorkerTask;

verus! {

/// The result columns `(ps_partkey, value)` of a sorted list.
pub fn columns_of(f: Sorted) -> (c: ResultColumns)
    requires f.wf(),
    ensures columns_wf(c), columns_view(c) == f.view().map_values(|e: (int, int)| row_of(e)),
{
    let n = f.n;
    let Sorted { v, k, n: _ } = f;
    let ghost fv = pairs(v@, k@, 0, n as int);
    let mut v = v;
    let mut k = k;
    v.truncate(n);
    k.truncate(n);
    let mut cols: Vec<ResultColumn> = Vec::new();
    cols.push(ResultColumn::Int(k));
    cols.push(ResultColumn::Num { coeffs: v, scale: 2 });
    let c = ResultColumns { rows: n, columns: cols };
    proof {
        let rows = fv.map_values(|e: (int, int)| row_of(e));
        assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < c.columns@.len()
            implies #[trigger] rows[i][j] == column_value(c.columns@[j], i) by {
            assert(rows[i] == row_of(fv[i]));
        }
        assert forall|i: int| 0 <= i < rows.len() implies #[trigger] rows[i].len() == c.columns@.len() by {
            assert(rows[i] == row_of(fv[i]));
        }
        lemma_columns_view_eq(c, rows);
        assert forall|j: int| 0 <= j < c.columns@.len() implies crate::gendb_entry::results::column_wf(#[trigger] c.columns@[j], c.rows as nat) by {}
    }
    c
}

/// `total * $2 / 10^10` rounded down, or `None` when `total * $2` leaves `i128`.
pub fn threshold(total: i128, c2: i128) -> (r: Option<i128>)
    ensures
        r matches Some(thr) ==> thr_ok(thr as int, total as int * c2 as int),
        r is None ==> !(i128::MIN as int <= total as int * c2 as int <= i128::MAX as int),
{
    match total.checked_mul(c2) {
        None => None,
        Some(tc) => {
            let d: i128 = 10_000_000_000;
            let thr = tc.checked_div_euclid(d).unwrap();
            proof {
                let t = tc as int;
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t, 10_000_000_000);
                assert(t == 10_000_000_000 * (t / 10_000_000_000) + t % 10_000_000_000);
                assert(thr as int == t / 10_000_000_000);
                assert(thr as int * 10_000_000_000 <= t < (thr as int + 1) * 10_000_000_000) by (nonlinear_arith)
                    requires t == 10_000_000_000 * (t / 10_000_000_000) + t % 10_000_000_000, 0 <= t % 10_000_000_000 < 10_000_000_000,
                        thr as int == t / 10_000_000_000;
            }
            Some(thr)
        },
    }
}

/// A list kept by HAVING from a group table: the passing groups (distinct keys) of all partsupp rows.
pub proof fn lemma_list_from_table(sv: StoresView, p: Seq<u8>, thr: int, g: Seq<(int, int)>)
    requires
        distinct(g),
        forall|i: int| 0 <= i < g.len() ==> grp_ok(sv, p, #[trigger] g[i]),
        forall|k: int| rsum(sv, p, t_cnt(sv, k), 0, ps_n(sv) as int) > 0 ==> exists|i: int| 0 <= i < g.len() && #[trigger] g[i].1 == k,
    ensures list_ok(sv, p, thr, above(g, thr)),
{
    let l = above(g, thr);
    lemma_above(g, thr);
    lemma_above_distinct(g, thr);
    assert forall|i: int| 0 <= i < l.len() implies grp_ok(sv, p, #[trigger] l[i]) && l[i].0 > thr by {
        assert(l.contains(l[i]));
        let j = choose|j: int| 0 <= j < g.len() && g[j] == l[i];
    }
    assert forall|k: int| rsum(sv, p, t_cnt(sv, k), 0, ps_n(sv) as int) > 0
        && #[trigger] rsum(sv, p, t_sum(sv, k), 0, ps_n(sv) as int) > thr
        implies exists|i: int| 0 <= i < l.len() && l[i].1 == k by {
        let j = choose|j: int| 0 <= j < g.len() && #[trigger] g[j].1 == k;
        assert(grp_ok(sv, p, g[j]));
        assert(g.contains(g[j]));
        assert(l.contains(g[j]));
        let i = choose|i: int| 0 <= i < l.len() && l[i] == g[j];
    }
}

/// The rows answer of a sorted permutation of a complete list.
pub proof fn lemma_rows_meets(sv: StoresView, p: Seq<u8>, c2: int, thr: int, l: Seq<(int, int)>, f: Sorted, c: ResultColumns)
    requires
        stores_wf(sv), keys_ok(sv), bounds_ok(sv),
        rsum(sv, p, t_absv(sv), 0, ps_n(sv) as int) <= i128_max(),
        -100000000000000000000000000000000000000 < c2 < 100000000000000000000000000000000000000,
        thr_ok(thr, rsum(sv, p, t_val(sv), 0, ps_n(sv) as int) * c2),
        list_ok(sv, p, thr, l),
        f.view().to_multiset() == l.to_multiset(), desc(f.view()),
        columns_wf(c), columns_view(c) == f.view().map_values(|e: (int, int)| row_of(e)),
    ensures answer_meets(sv, params_of(p, c2), Ok::<Answer, crate::gendb_entry::runtime::QueryError>(Answer::Columns(c))),
{
    lemma_answer_rows(sv, p, c2, thr, l, f.view());
}

/// The answer of the general serial path.
pub fn general_answer(pk: &'static [i64], sk: &'static [i64], aq: &'static [i64], cost: &'static [i128], n: usize,
    skeys: &'static [i64], ns: usize, bits: &Vec<u64>, c2: i128, Ghost(sv): Ghost<StoresView>, Ghost(p): Ghost<Seq<u8>>) -> (a: Answer)
    requires
        stores_wf(sv), keys_ok(sv), bounds_ok(sv),
        pk@ == ps_pkeys(sv), sk@ == ps_skeys(sv), aq@ == ps_aqs(sv), cost@ == ps_costs(sv), n == ps_n(sv),
        skeys@ == s_keys(sv), ns == supp_n(sv), bits_ok(bits@, ns as int, sv, p),
        -100000000000000000000000000000000000000 < c2 < 100000000000000000000000000000000000000,
    ensures answer_meets(sv, params_of(p, c2 as int), Ok::<Answer, crate::gendb_entry::runtime::QueryError>(a)),
{
    let fb = fallback_groups(pk, sk, aq, cost, n, skeys, ns, bits, Ghost(sv), Ghost(p));
    if fb.status == OVER {
        proof {
            lemma_some_row(sv, p, 0, n as int);
            lemma_answer_capacity(sv, p, c2 as int);
        }
        return Answer::Capacity;
    }
    let thr = match threshold(fb.total, c2) {
        Some(t) => t,
        None => {
            proof {
                lemma_some_row(sv, p, 0, n as int);
                lemma_answer_capacity(sv, p, c2 as int);
            }
            return Answer::Capacity;
        },
    };
    let m = fb.keys.len();
    let ghost g = pairs(fb.sums@, fb.keys@, 0, m as int);
    proof {
        assert(groups_ok(sv, p, n as int, fb.keys@, fb.sums@));
        assert forall|i: int, j: int| 0 <= i < g.len() && 0 <= j < g.len() && i != j implies (#[trigger] g[i]).1 != (#[trigger] g[j]).1 by {
            assert(fb.keys@[i] != fb.keys@[j]);
        }
        assert forall|i: int| 0 <= i < g.len() implies grp_ok(sv, p, #[trigger] g[i]) by {
            assert(fb.sums@[i] as int == rsum(sv, p, t_sum(sv, fb.keys@[i] as int), 0, n as int));
        }
        assert forall|k: int| rsum(sv, p, t_cnt(sv, k), 0, ps_n(sv) as int) > 0 implies exists|i: int| 0 <= i < g.len() && #[trigger] g[i].1 == k by {
            let i = choose|i: int| 0 <= i < fb.keys@.len() && fb.keys@[i] as int == k;
            assert(g[i].1 == k);
        }
        lemma_list_from_table(sv, p, thr as int, g);
    }
    let task = FilterTask { keys: fb.keys, sums: fb.sums, used: m, thr, av: vec![0i128; m], ak: vec![0i64; m], bv: vec![0i128; m],
        bk: vec![0i64; m] };
    assert(task.input() == g);
    let f = task.run();
    proof {
        lemma_rsum_bounds(sv, p, 0, 0, n as int);
    }
    let ghost fv = f.view();
    let c = columns_of(f);
    proof {
        lemma_answer_rows(sv, p, c2 as int, thr as int, above(g, thr as int), fv);
    }
    Answer::Columns(c)
}

} // verus!
