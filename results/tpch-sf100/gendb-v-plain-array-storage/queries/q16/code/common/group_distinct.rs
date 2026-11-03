//! GROUP BY with one aggregate `COUNT(DISTINCT e)` over group keys of integer and text values and integer argument
//! values (`group_rows`): the output is one row per distinct key, `key ++ [count]`, where the count is the number of
//! distinct argument values of the group (`group_vals`), or the SQL error 22003 when a count leaves int8
//! (`lemma_group_rows`). The output rows are duplicate-free, so any other duplicate-free sequence with the same
//! rows is a permutation of them.
//!
//! On integer and text values, SQL value equality ("not distinct") is equality (`lemma_plain_not_distinct`), so
//! `distinct_rows` keeps exactly one copy of every key and `distinct_vals` of every value.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::limits::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::bridge::collect::lemma_collect_all;

verus! {

/// An integer or a text value.
pub open spec fn plain_val(v: Val) -> bool {
    v is Int || v is Text
}

/// A row of integer and text values.
pub open spec fn plain_row(r: Row) -> bool {
    forall|i: int| 0 <= i < r.len() ==> #[trigger] plain_val(r[i])
}

/// Key rows: plain rows of length `n`.
pub open spec fn key_rows(rs: Seq<Row>, n: nat) -> bool {
    forall|i: int| 0 <= i < rs.len() ==> #[trigger] plain_row(rs[i]) && rs[i].len() == n
}

/// Argument rows: one integer each.
pub open spec fn int_args(rs: Seq<Row>) -> bool {
    forall|i: int| 0 <= i < rs.len() ==> (#[trigger] rs[i]).len() == 1 && rs[i][0] is Int
}

/// Some row keyed `k` has the argument value `v`.
pub open spec fn in_group(keys: Seq<Row>, args: Seq<Row>, k: Row, v: Val) -> bool {
    exists|i: int| 0 <= i < keys.len() && 0 <= i < args.len() && keys[i] == k && #[trigger] args[i][0] == v
}

/// The argument values of the rows whose key is `k` (a subset of all argument values).
pub open spec fn group_vals(keys: Seq<Row>, args: Seq<Row>, k: Row) -> Set<Val> {
    args.map_values(|r: Row| r[0]).to_set().filter(|v: Val| in_group(keys, args, k, v))
}

/// Membership in `group_vals`.
pub proof fn lemma_group_vals_contains(keys: Seq<Row>, args: Seq<Row>, k: Row, v: Val)
    ensures group_vals(keys, args, k).contains(v) == in_group(keys, args, k, v),
{
    let all = args.map_values(|r: Row| r[0]);
    if in_group(keys, args, k, v) {
        let i = choose|i: int| 0 <= i < keys.len() && 0 <= i < args.len() && keys[i] == k && #[trigger] args[i][0] == v;
        assert(all[i] == v);
        assert(all.to_set().contains(v));
    }
}

/// The single aggregate `COUNT(DISTINCT e)`.
pub open spec fn count_distinct_aggs(e: Expr) -> Seq<Agg> {
    seq![Agg::DistinctAgg(Box::new(Agg::Count(e)))]
}

/// The output row of group `k`.
pub open spec fn count_row(keys: Seq<Row>, args: Seq<Row>, k: Row) -> Row {
    k + seq![Val::Int(group_vals(keys, args, k).len() as int)]
}

// ------------------------------------------------------------------------------------------------ equality

/// On integer and text values, value equality is equality.
pub proof fn lemma_plain_not_distinct(a: Val, b: Val)
    requires plain_val(a), plain_val(b),
    ensures val_not_distinct(a, b) == (a == b),
{
    match (a, b) {
        (Val::Text(x), Val::Text(y)) => { lemma_lex_cmp_zero(x, y); },
        _ => {},
    }
}

/// On plain rows, row equality is equality.
pub proof fn lemma_plain_row_not_distinct(r: Row, s: Row)
    requires plain_row(r), plain_row(s),
    ensures row_not_distinct(r, s) == (r == s),
{
    if r.len() == s.len() {
        assert forall|i: int| 0 <= i < r.len() implies val_not_distinct(#[trigger] r[i], s[i]) == (r[i] == s[i]) by {
            lemma_plain_not_distinct(r[i], s[i]);
        }
        if row_not_distinct(r, s) {
            assert(r =~= s);
        }
    }
}

/// Some row of `d` is not distinct from `x` exactly when `d` contains `x` (plain rows).
proof fn lemma_has_not_distinct(d: Seq<Row>, x: Row)
    requires plain_row(x), forall|i: int| 0 <= i < d.len() ==> #[trigger] plain_row(d[i]),
    ensures has_not_distinct(d, x) == d.contains(x),
    decreases d.len(),
{
    if d.len() > 0 {
        let init = d.drop_last();
        assert forall|i: int| 0 <= i < init.len() implies #[trigger] plain_row(init[i]) by { assert(init[i] == d[i]); }
        lemma_has_not_distinct(init, x);
        lemma_plain_row_not_distinct(d.last(), x);
        if d.contains(x) {
            let j = choose|j: int| 0 <= j < d.len() && d[j] == x;
            if j < init.len() { assert(init[j] == x); }
        }
        if init.contains(x) {
            let j = choose|j: int| 0 <= j < init.len() && init[j] == x;
            assert(d[j] == x);
        }
    }
}

/// `distinct_rows` of plain rows: duplicate-free, with exactly the rows of the input.
pub proof fn lemma_distinct_rows_plain(rows: Seq<Row>)
    requires forall|i: int| 0 <= i < rows.len() ==> #[trigger] plain_row(rows[i]),
    ensures
        distinct_rows(rows).no_duplicates(),
        forall|k: Row| #[trigger] distinct_rows(rows).contains(k) <==> rows.contains(k),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let init = rows.drop_last();
        assert forall|i: int| 0 <= i < init.len() implies #[trigger] plain_row(init[i]) by { assert(init[i] == rows[i]); }
        lemma_distinct_rows_plain(init);
        let d = distinct_rows(init);
        let x = rows.last();
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] plain_row(d[i]) by {
            assert(d.contains(d[i]));
            assert(init.contains(d[i]));
            let j = choose|j: int| 0 <= j < init.len() && init[j] == d[i];
        }
        assert(plain_row(x)) by { assert(x == rows[rows.len() - 1]); }
        lemma_has_not_distinct(d, x);
        assert forall|k: Row| #[trigger] distinct_rows(rows).contains(k) <==> rows.contains(k) by {
            if rows.contains(k) {
                let j = choose|j: int| 0 <= j < rows.len() && rows[j] == k;
                if j < init.len() {
                    assert(init[j] == k);
                    assert(init.contains(k));
                    assert(d.contains(k));
                    let m = choose|m: int| 0 <= m < d.len() && d[m] == k;
                    if !d.contains(x) { assert(d.push(x)[m] == k); }
                } else {
                    if !d.contains(x) { assert(d.push(x)[d.len() as int] == k); }
                }
            }
            if distinct_rows(rows).contains(k) {
                let m = choose|m: int| 0 <= m < distinct_rows(rows).len() && distinct_rows(rows)[m] == k;
                if m < d.len() {
                    assert(d[m] == k);
                    assert(d.contains(k));
                    let j = choose|j: int| 0 <= j < init.len() && init[j] == k;
                    assert(rows[j] == k);
                } else {
                    assert(k == x);
                    assert(rows[rows.len() - 1] == k);
                }
            }
        }
        if !d.contains(x) {
            assert forall|i: int, j: int| 0 <= i < j < d.push(x).len() implies d.push(x)[i] != d.push(x)[j] by {
                if j == d.len() {
                    assert(d.push(x)[j] == x);
                    assert(d.push(x)[i] == d[i]);
                } else {
                    assert(d.push(x)[i] == d[i] && d.push(x)[j] == d[j]);
                }
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ members and values

/// The members of group `k` are exactly the argument rows of the rows keyed `k`.
pub proof fn lemma_members_plain(keys: Seq<Row>, args: Seq<Row>, k: Row)
    requires keys.len() == args.len(), plain_row(k), forall|i: int| 0 <= i < keys.len() ==> #[trigger] plain_row(keys[i]),
    ensures
        forall|m: Row| #[trigger] group_members(keys, args, k).contains(m)
            <==> exists|i: int| 0 <= i < keys.len() && keys[i] == k && #[trigger] args[i] == m,
    decreases keys.len(),
{
    if keys.len() > 0 {
        let (ki, ai) = (keys.drop_last(), args.drop_last());
        assert forall|i: int| 0 <= i < ki.len() implies #[trigger] plain_row(ki[i]) by { assert(ki[i] == keys[i]); }
        lemma_members_plain(ki, ai, k);
        let n = keys.len() - 1;
        lemma_plain_row_not_distinct(keys[n], k);
        let g = group_members(keys, args, k);
        let gi = group_members(ki, ai, k);
        assert forall|m: Row| #[trigger] g.contains(m)
            <==> exists|i: int| 0 <= i < keys.len() && keys[i] == k && #[trigger] args[i] == m by {
            if g.contains(m) {
                let x = choose|x: int| 0 <= x < g.len() && g[x] == m;
                if x < gi.len() {
                    assert(gi[x] == m);
                    assert(gi.contains(m));
                    let i = choose|i: int| 0 <= i < ki.len() && ki[i] == k && #[trigger] ai[i] == m;
                    assert(keys[i] == k && args[i] == m);
                } else {
                    assert(keys[n] == k && args[n] == m);
                }
            }
            if exists|i: int| 0 <= i < keys.len() && keys[i] == k && #[trigger] args[i] == m {
                let i = choose|i: int| 0 <= i < keys.len() && keys[i] == k && #[trigger] args[i] == m;
                if i < n {
                    assert(ki[i] == k && ai[i] == m);
                    assert(gi.contains(m));
                    let x = choose|x: int| 0 <= x < gi.len() && gi[x] == m;
                    if row_not_distinct(keys[n], k) { assert(g[x] == m); } else { assert(g[x] == m); }
                } else {
                    assert(g[gi.len() as int] == m);
                }
            }
        }
    }
}

/// Some value of `d` is not distinct from `x` exactly when `d` contains `x` (integer values).
proof fn lemma_has_val_not_distinct(d: Seq<Val>, x: Val)
    requires x is Int, forall|i: int| 0 <= i < d.len() ==> (#[trigger] d[i]) is Int,
    ensures has_val_not_distinct(d, x) == d.contains(x),
    decreases d.len(),
{
    if d.len() > 0 {
        let init = d.drop_last();
        assert forall|i: int| 0 <= i < init.len() implies (#[trigger] init[i]) is Int by { assert(init[i] == d[i]); }
        lemma_has_val_not_distinct(init, x);
        lemma_plain_not_distinct(d.last(), x);
        if d.contains(x) {
            let j = choose|j: int| 0 <= j < d.len() && d[j] == x;
            if j < init.len() { assert(init[j] == x); }
        }
        if init.contains(x) {
            let j = choose|j: int| 0 <= j < init.len() && init[j] == x;
            assert(d[j] == x);
        }
    }
}

/// `distinct_vals` of integer values: duplicate-free, without NULL, with exactly the values of the input.
pub proof fn lemma_distinct_vals_ints(vs: Seq<Val>)
    requires forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i]) is Int,
    ensures
        distinct_vals(vs).no_duplicates(),
        distinct_vals(vs).to_set() == vs.to_set(),
        count_non_null(distinct_vals(vs)) == distinct_vals(vs).len(),
    decreases vs.len(),
{
    let d = distinct_vals(vs);
    if vs.len() > 0 {
        let init = vs.drop_last();
        assert forall|i: int| 0 <= i < init.len() implies (#[trigger] init[i]) is Int by { assert(init[i] == vs[i]); }
        lemma_distinct_vals_ints(init);
        let di = distinct_vals(init);
        let x = vs.last();
        assert(x is Int);
        crate::bridge::relation::lemma_distinct_vals_sub(init);
        assert forall|i: int| 0 <= i < di.len() implies (#[trigger] di[i]) is Int by {
            assert(init.contains(di[i]));
            let j = choose|j: int| 0 <= j < init.len() && init[j] == di[i];
        }
        lemma_has_val_not_distinct(di, x);
        assert(vs.to_set() =~= init.to_set().insert(x)) by {
            assert(vs =~= init.push(x));
            assert forall|v: Val| vs.to_set().contains(v) <==> init.to_set().insert(x).contains(v) by {
                if vs.contains(v) {
                    let j = choose|j: int| 0 <= j < vs.len() && vs[j] == v;
                    if j < init.len() { assert(init[j] == v); }
                }
                if init.contains(v) {
                    let j = choose|j: int| 0 <= j < init.len() && init[j] == v;
                    assert(vs[j] == v);
                }
            }
        }
        if di.contains(x) {
            assert(d == di);
            assert(di.to_set().contains(x));
            assert(d.to_set() =~= vs.to_set());
        } else {
            assert(d == di.push(x));
            assert forall|i: int, j: int| 0 <= i < j < d.len() implies d[i] != d[j] by {
                if j == di.len() {
                    assert(d[j] == x && d[i] == di[i]);
                } else {
                    assert(d[i] == di[i] && d[j] == di[j]);
                }
            }
            assert(d.to_set() =~= di.to_set().insert(x)) by {
                assert forall|v: Val| d.to_set().contains(v) <==> di.to_set().insert(x).contains(v) by {
                    if d.contains(v) {
                        let j = choose|j: int| 0 <= j < d.len() && d[j] == v;
                        if j < di.len() { assert(di[j] == v); }
                    }
                    if di.contains(v) {
                        let j = choose|j: int| 0 <= j < di.len() && di[j] == v;
                        assert(d[j] == v);
                    }
                    if v == x { assert(d[di.len() as int] == v); }
                }
            }
            assert(!(x is Null));
            assert(d.drop_last() =~= di);
        }
    } else {
        assert(vs.to_set() =~= Set::<Val>::empty());
        assert(d.to_set() =~= Set::<Val>::empty());
    }
}

/// The values of group `k` are the argument values of its members.
proof fn lemma_group_vals_members(keys: Seq<Row>, args: Seq<Row>, k: Row)
    requires keys.len() == args.len(), plain_row(k), forall|i: int| 0 <= i < keys.len() ==> #[trigger] plain_row(keys[i]),
        int_args(args),
    ensures
        column(group_members(keys, args, k), 0).to_set() == group_vals(keys, args, k),
        forall|i: int| 0 <= i < column(group_members(keys, args, k), 0).len()
            ==> (#[trigger] column(group_members(keys, args, k), 0)[i]) is Int,
{
    let g = group_members(keys, args, k);
    let col = column(g, 0);
    lemma_members_plain(keys, args, k);
    crate::bridge::relation::lemma_group_members_sub(keys, args, k);
    assert forall|i: int| 0 <= i < col.len() implies (#[trigger] col[i]) is Int by {
        assert(args.contains(g[i]));
        let j = choose|j: int| 0 <= j < args.len() && args[j] == g[i];
    }
    assert forall|v: Val| col.to_set().contains(v) <==> group_vals(keys, args, k).contains(v) by {
        lemma_group_vals_contains(keys, args, k, v);
        if col.contains(v) {
            let x = choose|x: int| 0 <= x < col.len() && col[x] == v;
            assert(g.contains(g[x]));
            let i = choose|i: int| 0 <= i < keys.len() && keys[i] == k && #[trigger] args[i] == g[x];
            assert(args[i][0] == v);
        }
        if group_vals(keys, args, k).contains(v) {
            let i = choose|i: int| 0 <= i < keys.len() && 0 <= i < args.len() && keys[i] == k && #[trigger] args[i][0] == v;
            assert(g.contains(args[i]));
            let x = choose|x: int| 0 <= x < g.len() && g[x] == args[i];
            assert(col[x] == v);
        }
    }
    assert(col.to_set() =~= group_vals(keys, args, k));
}

/// The aggregate row of group `k`: its distinct count, or 22003 beyond int8.
pub proof fn lemma_group_count(e: Expr, keys: Seq<Row>, args: Seq<Row>, k: Row)
    requires keys.len() == args.len(), plain_row(k), forall|i: int| 0 <= i < keys.len() ==> #[trigger] plain_row(keys[i]),
        int_args(args),
    ensures
        agg_row(count_distinct_aggs(e), group_members(keys, args, k)) == match int_result(IntKind::Int8, group_vals(keys, args, k).len() as int) {
            Ok(v) => Ok::<Row, SqlError>(seq![v]),
            Err(err) => Err::<Row, SqlError>(err),
        },
{
    let g = group_members(keys, args, k);
    let col = column(g, 0);
    lemma_group_vals_members(keys, args, k);
    lemma_distinct_vals_ints(col);
    let d = distinct_vals(col);
    d.unique_seq_to_set();
    assert(d.to_set().len() == d.len());
    let aggs = count_distinct_aggs(e);
    let r = agg_value(aggs[0], column(g, 0));
    assert(aggs[0] == Agg::DistinctAgg(Box::new(Agg::Count(e))));
    assert(r == agg_value(Agg::Count(e), d));
    assert(agg_value(Agg::Count(e), d) == int_result(IntKind::Int8, count_non_null(d) as int));
    assert(col.to_set() == group_vals(keys, args, k));
    assert(d.to_set() == col.to_set());
    assert(r == int_result(IntKind::Int8, group_vals(keys, args, k).len() as int));
    let rs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(g, j)));
    assert(rs.len() == 1 && rs[0] == r);
    if r is Ok {
        lemma_collect_all(rs, seq![r->Ok_0]);
    } else {
        crate::bridge::collect::lemma_collect_first_err(rs, 0);
    }
}

// ------------------------------------------------------------------------------------------------ the groups

/// GROUP BY with `COUNT(DISTINCT e)`: within int8, the rows `count_row(k)` of the distinct keys (first-occurrence
/// order), a duplicate-free sequence holding exactly the `count_row` of every key; beyond int8, 22003.
pub proof fn lemma_group_rows(e: Expr, keys: Seq<Row>, args: Seq<Row>, n: nat)
    requires keys.len() == args.len(), key_rows(keys, n), int_args(args),
    ensures ({
        let out = group_rows(count_distinct_aggs(e), keys, args);
        let fits = forall|k: Row| #[trigger] keys.contains(k) ==> group_vals(keys, args, k).len() <= int8_max();
        &&& fits ==> out is Ok && out->Ok_0.no_duplicates()
            && forall|r: Row| #[trigger] out->Ok_0.contains(r) <==> exists|k: Row| #[trigger] keys.contains(k) && r == count_row(keys, args, k)
        &&& !fits ==> out == Err::<Seq<Row>, SqlError>(SqlError::NumericValueOutOfRange)
    }),
{
    let aggs = count_distinct_aggs(e);
    let ks = distinct_rows(keys);
    assert forall|i: int| 0 <= i < keys.len() implies #[trigger] plain_row(keys[i]) by {}
    lemma_distinct_rows_plain(keys);
    let rs = Seq::new(ks.len(), |g: int| match agg_row(aggs, group_members(keys, args, ks[g])) {
        Ok(a) => Ok(ks[g] + a),
        Err(err) => Err(err),
    });
    assert(group_rows(aggs, keys, args) == crate::spec::relation::collect(rs));
    // Every key of `ks` is a key row.
    assert forall|g: int| 0 <= g < ks.len() implies #[trigger] plain_row(ks[g]) && ks[g].len() == n && keys.contains(ks[g]) by {
        assert(ks.contains(ks[g]));
        let j = choose|j: int| 0 <= j < keys.len() && keys[j] == ks[g];
    }
    assert forall|g: int| 0 <= g < ks.len() implies #[trigger] rs[g] == match int_result(IntKind::Int8, group_vals(keys, args, ks[g]).len() as int) {
        Ok(v) => Ok::<Row, SqlError>(ks[g] + seq![v]),
        Err(err) => Err::<Row, SqlError>(err),
    } by {
        lemma_group_count(e, keys, args, ks[g]);
    }
    let fits = forall|k: Row| #[trigger] keys.contains(k) ==> group_vals(keys, args, k).len() <= int8_max();
    if fits {
        let out = Seq::new(ks.len(), |g: int| count_row(keys, args, ks[g]));
        assert forall|g: int| 0 <= g < rs.len() implies #[trigger] rs[g] == Ok::<Row, SqlError>(out[g]) by {
            assert(plain_row(ks[g]));
            assert(keys.contains(ks[g]));
            assert(group_vals(keys, args, ks[g]).len() <= int8_max());
            assert(int_in_range(IntKind::Int8, group_vals(keys, args, ks[g]).len() as int));
        }
        lemma_collect_all(rs, out);
        assert forall|i: int, j: int| 0 <= i < j < out.len() implies out[i] != out[j] by {
            if out[i] == out[j] {
                assert(plain_row(ks[i]) && plain_row(ks[j]));
                assert(out[i].subrange(0, n as int) =~= ks[i]);
                assert(out[j].subrange(0, n as int) =~= ks[j]);
            }
        }
        assert forall|r: Row| #[trigger] out.contains(r) <==> exists|k: Row| #[trigger] keys.contains(k) && r == count_row(keys, args, k) by {
            if out.contains(r) {
                let g = choose|g: int| 0 <= g < out.len() && out[g] == r;
                assert(plain_row(ks[g]));
                assert(keys.contains(ks[g]));
            }
            if exists|k: Row| #[trigger] keys.contains(k) && r == count_row(keys, args, k) {
                let k = choose|k: Row| #[trigger] keys.contains(k) && r == count_row(keys, args, k);
                assert(ks.contains(k));
                let g = choose|g: int| 0 <= g < ks.len() && ks[g] == k;
                assert(out[g] == r);
            }
        }
    } else {
        let k = choose|k: Row| #[trigger] keys.contains(k) && !(group_vals(keys, args, k).len() <= int8_max());
        assert(ks.contains(k));
        let g = choose|g: int| 0 <= g < ks.len() && ks[g] == k;
        assert(plain_row(ks[g]));
        assert(rs[g] == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange));
        assert forall|x: int| 0 <= x < rs.len() implies #[trigger] rs[x] is Ok
            || rs[x] == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange) by {}
        crate::link::capacity::lemma_collect_uniform_err(rs, SqlError::NumericValueOutOfRange, g);
    }
}

} // verus!
