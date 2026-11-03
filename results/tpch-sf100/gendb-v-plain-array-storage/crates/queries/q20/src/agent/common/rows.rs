//! Facts about filtered rows and `= ANY`: a filter keeps exactly the rows whose truth value is `True` even when
//! some truths are `Unknown` (`lemma_keep_true_is`), a row satisfying the condition is kept (`lemma_keep_has`), and
//! `v = ANY (rows)` over one-column integer rows is two-valued (`lemma_any_eq`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::link::join::keep;

verus! {

/// `keep_true` keeps the rows whose truth is `True` (the others may be `False` or `Unknown`).
pub proof fn lemma_keep_true_is(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (r0, t0) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < r0.len() implies (#[trigger] t0[i] is True) == f(r0[i]) by {
            assert(t0[i] == truths[i] && r0[i] == rows[i]);
        }
        lemma_keep_true_is(r0, t0, f);
        assert(truths.last() == truths[rows.len() - 1] && rows.last() == rows[rows.len() - 1]);
    }
}

/// A row satisfying the condition is kept.
pub proof fn lemma_keep_has(rows: Seq<Row>, f: spec_fn(Row) -> bool, u: int)
    requires 0 <= u < rows.len(), f(rows[u]),
    ensures keep(rows, f).contains(rows[u]),
    decreases rows.len(),
{
    let init = rows.drop_last();
    if u == rows.len() - 1 {
        assert(keep(rows, f) == keep(init, f).push(rows.last()));
        assert(keep(rows, f)[keep(init, f).len() as int] == rows[u]);
    } else {
        assert(init[u] == rows[u]);
        lemma_keep_has(init, f, u);
        let w = choose|w: int| 0 <= w < keep(init, f).len() && keep(init, f)[w] == rows[u];
        if f(rows.last()) {
            assert(keep(rows, f)[w] == rows[u]);
        } else {
            assert(keep(rows, f) == keep(init, f));
        }
    }
}

/// `v = ANY (rows)` over one-column integer rows is two-valued: some row is `[Int(v)]`.
pub proof fn lemma_any_eq(v: int, rows: Seq<Row>)
    requires forall|t: int| 0 <= t < rows.len() ==> exists|w: int| #[trigger] rows[t] == seq![Val::Int(w)],
    ensures any_cmp_truth(CmpOp::Eq, Val::Int(v), rows)
        == Ok::<Truth, SqlError>(truth_of(exists|t: int| 0 <= t < rows.len() && #[trigger] rows[t] == seq![Val::Int(v)])),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let init = rows.drop_last();
        assert forall|t: int| 0 <= t < init.len() implies exists|w: int| #[trigger] init[t] == seq![Val::Int(w)] by {
            assert(init[t] == rows[t]);
        }
        lemma_any_eq(v, init);
        let last = rows.last();
        assert(rows[rows.len() - 1] == last);
        let w = choose|w: int| rows[rows.len() - 1] == seq![Val::Int(w)];
        assert(first_col(last) == Ok::<Val, SqlError>(Val::Int(w)));
        assert(cmp_truth(CmpOp::Eq, Val::Int(v), Val::Int(w)) == Ok::<Truth, SqlError>(truth_of(v == w)));
        let a = exists|t: int| 0 <= t < init.len() && #[trigger] init[t] == seq![Val::Int(v)];
        let b = exists|t: int| 0 <= t < rows.len() && #[trigger] rows[t] == seq![Val::Int(v)];
        if a {
            let t = choose|t: int| 0 <= t < init.len() && #[trigger] init[t] == seq![Val::Int(v)];
            assert(rows[t] == init[t]);
        }
        if v == w {
            assert(rows[rows.len() - 1] == seq![Val::Int(v)]);
        }
        if b {
            let t = choose|t: int| 0 <= t < rows.len() && #[trigger] rows[t] == seq![Val::Int(v)];
            if t < rows.len() - 1 {
                assert(init[t] == rows[t]);
            } else {
                assert(seq![Val::Int(v)][0] == seq![Val::Int(w)][0]);
            }
        }
        assert(b == (a || v == w));
    }
}

} // verus!
