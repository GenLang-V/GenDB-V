//! Element lemmas for `spec::relation`: every output row of an operator is built from input rows. Each lemma
//! follows its operator's recursion on the last input row (`drop_last`) and names the witness row explicitly.
//! Type soundness (`bridge::typing`) lifts row typing through operators with them; exec and link proofs use
//! them to relate their loops to the denotation.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::*;
use crate::spec::equality::*;

verus! {

/// `x` is `l[i] ++ r[j]` for some rows of `l` and `r`.
pub open spec fn is_concat(x: Row, l: Seq<Row>, r: Seq<Row>) -> bool {
    exists|i: int, j: int| 0 <= i < l.len() && 0 <= j < r.len() && x == #[trigger] l[i] + #[trigger] r[j]
}

/// `x` is `l[i] ++ NULL^n` for some row of `l`.
pub open spec fn is_padded(x: Row, l: Seq<Row>, n: nat) -> bool {
    exists|i: int| 0 <= i < l.len() && x == #[trigger] l[i] + null_row(n)
}

/// WHERE keeps at most as many rows as its input, each an input row.
pub proof fn lemma_keep_true_sub(rows: Seq<Row>, truths: Seq<Truth>)
    ensures
        keep_true(rows, truths).len() <= rows.len(),
        forall|k: int| 0 <= k < keep_true(rows, truths).len() ==> rows.contains(#[trigger] keep_true(rows, truths)[k]),
    decreases rows.len(),
{
    if rows.len() > 0 && truths.len() > 0 {
        let init = rows.drop_last();
        lemma_keep_true_sub(init, truths.drop_last());
        let kt = keep_true(rows, truths);
        assert forall|k: int| 0 <= k < kt.len() implies rows.contains(#[trigger] kt[k]) by {
            if k < keep_true(init, truths.drop_last()).len() {
                let j = choose|j: int| 0 <= j < init.len() && init[j] == kt[k];
                assert(rows[j] == kt[k]);
            } else {
                assert(rows[rows.len() - 1] == kt[k]);
            }
        }
    }
}

/// The cross product has `|l|·|r|` rows, each a concatenation of a left row and a right row.
pub proof fn lemma_product_rows_elems(l: Seq<Row>, r: Seq<Row>)
    ensures
        product_rows(l, r).len() == l.len() * r.len(),
        forall|k: int| 0 <= k < product_rows(l, r).len() ==> is_concat(#[trigger] product_rows(l, r)[k], l, r),
    decreases l.len(),
{
    if l.len() > 0 {
        let init = l.drop_last();
        lemma_product_rows_elems(init, r);
        let p = product_rows(l, r);
        let pi = product_rows(init, r);
        assert(l.len() * r.len() == init.len() * r.len() + r.len()) by (nonlinear_arith)
            requires l.len() == init.len() + 1;
        assert forall|k: int| 0 <= k < p.len() implies is_concat(#[trigger] p[k], l, r) by {
            if k < pi.len() {
                let (i, j) = choose|i: int, j: int| 0 <= i < init.len() && 0 <= j < r.len() && pi[k] == #[trigger] init[i] + #[trigger] r[j];
                assert(p[k] == l[i] + r[j]);
            } else {
                let j = k - pi.len();
                assert(p[k] == l[l.len() - 1] + r[j]);
            }
        }
    }
}

/// Every LEFT JOIN row is a matched concatenation or a left row padded with `n` NULLs.
pub proof fn lemma_left_join_rows_elems(l: Seq<Row>, r: Seq<Row>, truths: Seq<Seq<Truth>>, n: nat)
    ensures
        forall|k: int| 0 <= k < left_join_rows(l, r, truths, n).len() ==>
            is_concat(#[trigger] left_join_rows(l, r, truths, n)[k], l, r) || is_padded(left_join_rows(l, r, truths, n)[k], l, n),
    decreases l.len(),
{
    if l.len() > 0 && truths.len() > 0 {
        let init = l.drop_last();
        lemma_left_join_rows_elems(init, r, truths.drop_last(), n);
        let s = left_join_rows(l, r, truths, n);
        let si = left_join_rows(init, r, truths.drop_last(), n);
        let last = l[l.len() - 1];
        let matched = keep_true(r, truths.last());
        lemma_keep_true_sub(r, truths.last());
        assert forall|k: int| 0 <= k < s.len() implies
            is_concat(#[trigger] s[k], l, r) || is_padded(s[k], l, n) by {
            if k < si.len() {
                assert(s[k] == si[k]);
                if is_concat(si[k], init, r) {
                    let (i, j) = choose|i: int, j: int| 0 <= i < init.len() && 0 <= j < r.len() && si[k] == #[trigger] init[i] + #[trigger] r[j];
                    assert(s[k] == l[i] + r[j]);
                } else {
                    let i = choose|i: int| 0 <= i < init.len() && si[k] == #[trigger] init[i] + null_row(n);
                    assert(s[k] == l[i] + null_row(n));
                }
            } else {
                let m = k - si.len();
                if matched.len() == 0 {
                    assert(s[k] == last + null_row(n));
                } else {
                    assert(r.contains(matched[m]));
                    let j = choose|j: int| 0 <= j < r.len() && r[j] == matched[m];
                    assert(s[k] == l[l.len() - 1] + r[j]);
                }
            }
        }
    }
}

/// Every member of a group is an argument row.
pub proof fn lemma_group_members_sub(keys: Seq<Row>, args: Seq<Row>, k: Row)
    ensures
        forall|m: int| 0 <= m < group_members(keys, args, k).len() ==> args.contains(#[trigger] group_members(keys, args, k)[m]),
    decreases keys.len(),
{
    if keys.len() > 0 && args.len() > 0 {
        let init = args.drop_last();
        lemma_group_members_sub(keys.drop_last(), init, k);
        let g = group_members(keys, args, k);
        let gi = group_members(keys.drop_last(), init, k);
        assert forall|m: int| 0 <= m < g.len() implies args.contains(#[trigger] g[m]) by {
            if m < gi.len() {
                let j = choose|j: int| 0 <= j < init.len() && init[j] == g[m];
                assert(args[j] == g[m]);
            } else {
                assert(args[args.len() - 1] == g[m]);
            }
        }
    }
}

/// Every value of `distinct_vals(vs)` is a value of `vs`.
pub proof fn lemma_distinct_vals_sub(vs: Seq<Val>)
    ensures
        forall|m: int| 0 <= m < distinct_vals(vs).len() ==> vs.contains(#[trigger] distinct_vals(vs)[m]),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let init = vs.drop_last();
        lemma_distinct_vals_sub(init);
        let d = distinct_vals(vs);
        assert forall|m: int| 0 <= m < d.len() implies vs.contains(#[trigger] d[m]) by {
            if m < distinct_vals(init).len() {
                let j = choose|j: int| 0 <= j < init.len() && init[j] == d[m];
                assert(vs[j] == d[m]);
            } else {
                assert(vs[vs.len() - 1] == d[m]);
            }
        }
    }
}

} // verus!
