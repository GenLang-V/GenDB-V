//! GROUP BY with one `COUNT(DISTINCT x)` aggregate over plain values (integers and texts: no NULL, and "not
//! distinct" is equality): the outcome of `spec::relation::group_rows` as a set of rows `key ++ [count]`.
//!
//! For plain keys, `distinct_rows` keeps every key once (`lemma_distinct_rows`), a group's members are its input
//! rows in order (`lemma_members`), `distinct_vals` keeps every value once (`lemma_distinct_vals`), so the count of a
//! key `k` is the size of the set of its argument values (`key_vals`). `lemma_group_count_distinct` states the whole
//! outcome: without a count beyond int8 the rows are duplicate-free and are exactly `k ++ [Int(|key_vals(k)|)]` over
//! the input keys; otherwise the outcome is the SQL error 22003 (the only error COUNT can raise).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::limits::*;

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

/// A value whose not-distinct relation is equality: an integer or a text.
pub open spec fn plain(v: Val) -> bool {
    v is Int || v is Text
}

/// Every value of `r` is plain.
pub open spec fn plain_row(r: Row) -> bool {
    forall|i: int| 0 <= i < r.len() ==> plain(#[trigger] r[i])
}

/// Two plain values are not distinct exactly when equal.
pub proof fn lemma_plain_nd(a: Val, b: Val)
    requires plain(a), plain(b),
    ensures val_not_distinct(a, b) == (a == b),
{
    match (a, b) {
        (Val::Int(x), Val::Int(y)) => {},
        (Val::Text(x), Val::Text(y)) => {
            crate::bridge::equality::lemma_lex_cmp_zero(x, y);
        },
        _ => {},
    }
}

/// Two plain rows are not distinct exactly when equal.
pub proof fn lemma_plain_row_nd(r: Row, s: Row)
    requires plain_row(r), plain_row(s),
    ensures row_not_distinct(r, s) == (r == s),
{
    if r.len() == s.len() {
        assert forall|i: int| 0 <= i < r.len() implies val_not_distinct(#[trigger] r[i], s[i]) == (r[i] == s[i]) by {
            lemma_plain_nd(r[i], s[i]);
        }
        if row_not_distinct(r, s) {
            assert(r =~= s);
        }
    }
}

// ------------------------------------------------------------------------------------------------ DISTINCT values

/// `has_val_not_distinct` over plain values is membership.
proof fn lemma_has_val(vs: Seq<Val>, v: Val)
    requires forall|i: int| 0 <= i < vs.len() ==> plain(#[trigger] vs[i]), plain(v),
    ensures has_val_not_distinct(vs, v) == vs.contains(v),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let d = vs.drop_last();
        lemma_has_val(d, v);
        lemma_plain_nd(vs.last(), v);
        if d.contains(v) {
            let i = choose|i: int| 0 <= i < d.len() && d[i] == v;
            assert(vs[i] == v);
        }
        if vs.contains(v) && !d.contains(v) {
            let i = choose|i: int| 0 <= i < vs.len() && vs[i] == v;
            if i < d.len() {
                assert(d[i] == v);
            }
        }
    }
}

/// `distinct_vals` of plain values: duplicate-free, plain, the same set of values, every one counted.
pub proof fn lemma_distinct_vals(vs: Seq<Val>)
    requires forall|i: int| 0 <= i < vs.len() ==> plain(#[trigger] vs[i]),
    ensures
        distinct_vals(vs).no_duplicates(),
        forall|i: int| 0 <= i < distinct_vals(vs).len() ==> plain(#[trigger] distinct_vals(vs)[i]),
        distinct_vals(vs).to_set() == vs.to_set(),
        count_non_null(distinct_vals(vs)) == distinct_vals(vs).len(),
        distinct_vals(vs).len() == vs.to_set().len(),
    decreases vs.len(),
{
    let d = distinct_vals(vs);
    if vs.len() == 0 {
        assert(d.to_set() =~= vs.to_set());
    } else {
        let p = vs.drop_last();
        let x = vs.last();
        let dp = distinct_vals(p);
        lemma_distinct_vals(p);
        lemma_has_val(dp, x);
        assert(!(x is Null));
        if dp.contains(x) {
            assert(d == dp);
            assert(dp.to_set().contains(x));
            assert(vs.to_set() =~= p.to_set().insert(x)) by {
                assert forall|v: Val| #[trigger] vs.to_set().contains(v) == p.to_set().insert(x).contains(v) by {
                    if vs.contains(v) {
                        let i = choose|i: int| 0 <= i < vs.len() && vs[i] == v;
                        if i < p.len() { assert(p[i] == v); }
                    }
                    if p.contains(v) {
                        let i = choose|i: int| 0 <= i < p.len() && p[i] == v;
                        assert(vs[i] == v);
                    }
                }
            }
            assert(p.to_set().insert(x) =~= p.to_set());
        } else {
            assert(d == dp.push(x));
            assert(d.no_duplicates()) by {
                assert forall|i: int, j: int| 0 <= i < d.len() && 0 <= j < d.len() && i != j implies d[i] != d[j] by {
                    if i < dp.len() && j < dp.len() {
                    } else if i < dp.len() {
                        assert(d[j] == x);
                        assert(dp.contains(d[i]));
                    } else {
                        assert(d[i] == x);
                        assert(dp.contains(d[j]));
                    }
                }
            }
            assert(d.to_set() =~= dp.to_set().insert(x));
            assert(vs.to_set() =~= p.to_set().insert(x)) by {
                assert forall|v: Val| #[trigger] vs.to_set().contains(v) == p.to_set().insert(x).contains(v) by {
                    if vs.contains(v) {
                        let i = choose|i: int| 0 <= i < vs.len() && vs[i] == v;
                        if i < p.len() { assert(p[i] == v); }
                    }
                    if p.contains(v) {
                        let i = choose|i: int| 0 <= i < p.len() && p[i] == v;
                        assert(vs[i] == v);
                    }
                }
            }
            assert(d.drop_last() == dp);
        }
        assert forall|i: int| 0 <= i < d.len() implies plain(#[trigger] d[i]) by {
            if i < dp.len() { assert(d[i] == dp[i]); }
        }
    }
    let d = distinct_vals(vs);
    d.unique_seq_to_set();
    lemma_count_plain(d);
}

/// No plain value is NULL, so every one is counted.
proof fn lemma_count_plain(vs: Seq<Val>)
    requires forall|i: int| 0 <= i < vs.len() ==> plain(#[trigger] vs[i]),
    ensures count_non_null(vs) == vs.len(),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let p = vs.drop_last();
        assert forall|i: int| 0 <= i < p.len() implies plain(#[trigger] p[i]) by { assert(p[i] == vs[i]); }
        lemma_count_plain(p);
    }
}

// ------------------------------------------------------------------------------------------------ DISTINCT rows

/// `has_not_distinct` over plain rows is membership.
proof fn lemma_has_row(rows: Seq<Row>, r: Row)
    requires forall|i: int| 0 <= i < rows.len() ==> plain_row(#[trigger] rows[i]), plain_row(r),
    ensures has_not_distinct(rows, r) == rows.contains(r),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies plain_row(#[trigger] d[i]) by { assert(d[i] == rows[i]); }
        lemma_has_row(d, r);
        lemma_plain_row_nd(rows.last(), r);
        if d.contains(r) {
            let i = choose|i: int| 0 <= i < d.len() && d[i] == r;
            assert(rows[i] == r);
        }
        if rows.contains(r) && !d.contains(r) {
            let i = choose|i: int| 0 <= i < rows.len() && rows[i] == r;
            if i < d.len() {
                assert(d[i] == r);
            }
        }
    }
}

/// `distinct_rows` of plain rows: duplicate-free, plain, and the same rows.
pub proof fn lemma_distinct_rows(rows: Seq<Row>)
    requires forall|i: int| 0 <= i < rows.len() ==> plain_row(#[trigger] rows[i]),
    ensures
        distinct_rows(rows).no_duplicates(),
        forall|i: int| 0 <= i < distinct_rows(rows).len() ==> plain_row(#[trigger] distinct_rows(rows)[i]),
        forall|r: Row| #[trigger] distinct_rows(rows).contains(r) <==> rows.contains(r),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let p = rows.drop_last();
        let x = rows.last();
        let dp = distinct_rows(p);
        assert forall|i: int| 0 <= i < p.len() implies plain_row(#[trigger] p[i]) by { assert(p[i] == rows[i]); }
        lemma_distinct_rows(p);
        lemma_has_row(dp, x);
        let d = distinct_rows(rows);
        assert forall|r: Row| rows.contains(r) <==> (p.contains(r) || r == x) by {
            if rows.contains(r) {
                let i = choose|i: int| 0 <= i < rows.len() && rows[i] == r;
                if i < p.len() { assert(p[i] == r); }
            }
            if p.contains(r) {
                let i = choose|i: int| 0 <= i < p.len() && p[i] == r;
                assert(rows[i] == r);
            }
        }
        if dp.contains(x) {
            assert(d == dp);
        } else {
            assert(d == dp.push(x));
            assert forall|i: int, j: int| 0 <= i < d.len() && 0 <= j < d.len() && i != j implies d[i] != d[j] by {
                if i < dp.len() && j < dp.len() {
                } else if i < dp.len() {
                    assert(dp.contains(d[i]));
                } else {
                    assert(dp.contains(d[j]));
                }
            }
            assert forall|r: Row| d.contains(r) <==> (dp.contains(r) || r == x) by {
                if d.contains(r) {
                    let i = choose|i: int| 0 <= i < d.len() && d[i] == r;
                    if i < dp.len() { assert(dp[i] == r); }
                }
                if dp.contains(r) {
                    let i = choose|i: int| 0 <= i < dp.len() && dp[i] == r;
                    assert(d[i] == r);
                }
                if r == x {
                    assert(d[dp.len() as int] == x);
                }
            }
            assert forall|i: int| 0 <= i < d.len() implies plain_row(#[trigger] d[i]) by {
                if i < dp.len() { assert(d[i] == dp[i]); }
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ members of a key

/// The argument rows of the input rows whose key is `k`, in input order.
pub open spec fn rows_of_key(keys: Seq<Row>, args: Seq<Row>, k: Row) -> Seq<Row>
    decreases keys.len(),
{
    if keys.len() == 0 || args.len() == 0 {
        Seq::empty()
    } else {
        let init = rows_of_key(keys.drop_last(), args.drop_last(), k);
        if keys.last() == k { init.push(args.last()) } else { init }
    }
}

/// For plain keys, a group's members are its rows (`group_members` = `rows_of_key`).
pub proof fn lemma_members(keys: Seq<Row>, args: Seq<Row>, k: Row)
    requires
        forall|i: int| 0 <= i < keys.len() ==> plain_row(#[trigger] keys[i]),
        plain_row(k),
    ensures group_members(keys, args, k) == rows_of_key(keys, args, k),
    decreases keys.len(),
{
    if keys.len() > 0 && args.len() > 0 {
        let kd = keys.drop_last();
        assert forall|i: int| 0 <= i < kd.len() implies plain_row(#[trigger] kd[i]) by { assert(kd[i] == keys[i]); }
        lemma_members(kd, args.drop_last(), k);
        lemma_plain_row_nd(keys.last(), k);
    }
}

/// The first values of a group's rows.
pub open spec fn key_vals(keys: Seq<Row>, args: Seq<Row>, k: Row) -> Set<Val> {
    column(rows_of_key(keys, args, k), 0).to_set()
}

/// `key_vals` holds exactly the first argument values of the input rows with key `k`.
pub proof fn lemma_key_vals(keys: Seq<Row>, args: Seq<Row>, k: Row, v: Val)
    requires keys.len() == args.len(),
    ensures
        key_vals(keys, args, k).contains(v)
            <==> exists|i: int| 0 <= i < keys.len() && keys[i] == k && (#[trigger] args[i])[0] == v,
    decreases keys.len(),
{
    let col = column(rows_of_key(keys, args, k), 0);
    if keys.len() > 0 {
        let (kd, ad) = (keys.drop_last(), args.drop_last());
        lemma_key_vals(kd, ad, k, v);
        let cold = column(rows_of_key(kd, ad, k), 0);
        let n = keys.len() - 1;
        if keys.last() == k {
            assert(col =~= cold.push(args.last()[0]));
        } else {
            assert(col =~= cold);
        }
        if col.contains(v) {
            if cold.contains(v) {
                let i = choose|i: int| 0 <= i < kd.len() && kd[i] == k && (#[trigger] ad[i])[0] == v;
                assert(keys[i] == k && args[i][0] == v);
            } else {
                assert(keys[n] == k && args[n][0] == v);
            }
        }
        if exists|i: int| 0 <= i < keys.len() && keys[i] == k && (#[trigger] args[i])[0] == v {
            let i = choose|i: int| 0 <= i < keys.len() && keys[i] == k && (#[trigger] args[i])[0] == v;
            if i < n {
                assert(kd[i] == k && ad[i][0] == v);
                assert(cold.contains(v));
                if keys.last() == k {
                    let q = choose|q: int| 0 <= q < cold.len() && cold[q] == v;
                    assert(col[q] == v);
                }
            } else {
                assert(col[col.len() - 1] == v);
            }
        }
    } else {
        assert(col.len() == 0);
    }
}

/// The first values of a group's rows are plain when every argument value is.
proof fn lemma_key_col_plain(keys: Seq<Row>, args: Seq<Row>, k: Row)
    requires
        keys.len() == args.len(),
        forall|i: int| 0 <= i < args.len() ==> (#[trigger] args[i]).len() == 1 && plain(args[i][0]),
    ensures
        forall|q: int| 0 <= q < column(rows_of_key(keys, args, k), 0).len()
            ==> plain(#[trigger] column(rows_of_key(keys, args, k), 0)[q]),
    decreases keys.len(),
{
    if keys.len() > 0 {
        let (kd, ad) = (keys.drop_last(), args.drop_last());
        assert forall|i: int| 0 <= i < ad.len() implies (#[trigger] ad[i]).len() == 1 && plain(ad[i][0]) by {
            assert(ad[i] == args[i]);
        }
        lemma_key_col_plain(kd, ad, k);
        let col = column(rows_of_key(keys, args, k), 0);
        let cold = column(rows_of_key(kd, ad, k), 0);
        if keys.last() == k {
            assert(col =~= cold.push(args.last()[0]));
        } else {
            assert(col =~= cold);
        }
        assert forall|q: int| 0 <= q < col.len() implies plain(#[trigger] col[q]) by {
            if q < cold.len() { assert(col[q] == cold[q]); }
        }
    }
}

// ------------------------------------------------------------------------------------------------ the outcome

/// The aggregate list `[COUNT(DISTINCT e)]`.
pub open spec fn count_distinct_aggs(e: Expr) -> Seq<Agg> {
    seq![Agg::DistinctAgg(Box::new(Agg::Count(e)))]
}

/// The output row of key `k`: the key and its distinct count.
pub open spec fn group_out(keys: Seq<Row>, args: Seq<Row>, k: Row) -> Row {
    k + seq![Val::Int(key_vals(keys, args, k).len() as int)]
}

/// The aggregate row of one group: its distinct count, or 22003 beyond int8.
proof fn lemma_agg_row_one(e: Expr, keys: Seq<Row>, args: Seq<Row>, k: Row)
    requires
        keys.len() == args.len(),
        forall|i: int| 0 <= i < keys.len() ==> plain_row(#[trigger] keys[i]),
        forall|i: int| 0 <= i < args.len() ==> (#[trigger] args[i]).len() == 1 && plain(args[i][0]),
        plain_row(k),
    ensures ({
        let n = key_vals(keys, args, k).len() as int;
        let r = agg_row(count_distinct_aggs(e), group_members(keys, args, k));
        &&& n <= int8_max() ==> r == Ok::<Row, SqlError>(seq![Val::Int(n)])
        &&& n > int8_max() ==> r == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange)
    }),
{
    let aggs = count_distinct_aggs(e);
    lemma_members(keys, args, k);
    let mem = rows_of_key(keys, args, k);
    let col = column(mem, 0);
    lemma_key_col_plain(keys, args, k);
    lemma_distinct_vals(col);
    let n = key_vals(keys, args, k).len() as int;
    assert(count_non_null(distinct_vals(col)) == n);
    let a0 = agg_value(aggs[0], column(mem, 0));
    assert(a0 == agg_value(Agg::Count(e), distinct_vals(col)));
    assert(a0 == int_result(IntKind::Int8, n));
    let vs = Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(mem, j)));
    assert(vs[0] == a0);
    assert(vs.len() == 1);
    assert(vs.drop_last() =~= Seq::<Result<Val, SqlError>>::empty());
    assert(collect(vs.drop_last()) == Ok::<Seq<Val>, SqlError>(Seq::empty()));
    if n <= int8_max() {
        assert(int_in_range(IntKind::Int8, n)) by {
            assert(int8_min() < 0);
        }
        assert(Seq::<Val>::empty().push(Val::Int(n)) =~= seq![Val::Int(n)]);
    }
}

/// The GROUP BY outcome with `[COUNT(DISTINCT e)]` over plain keys and plain single arguments.
pub proof fn lemma_group_count_distinct(e: Expr, keys: Seq<Row>, args: Seq<Row>)
    requires
        keys.len() == args.len(),
        forall|i: int| 0 <= i < keys.len() ==> plain_row(#[trigger] keys[i]),
        forall|i: int| 0 <= i < args.len() ==> (#[trigger] args[i]).len() == 1 && plain(args[i][0]),
    ensures ({
        let r = group_rows(count_distinct_aggs(e), keys, args);
        &&& (forall|i: int| 0 <= i < keys.len() ==> #[trigger] key_vals(keys, args, keys[i]).len() <= int8_max()) ==> {
            &&& r is Ok
            &&& r->Ok_0.no_duplicates()
            &&& forall|x: Row| #[trigger] r->Ok_0.contains(x)
                <==> exists|i: int| 0 <= i < keys.len() && x == group_out(keys, args, #[trigger] keys[i])
        }
        &&& (exists|i: int| 0 <= i < keys.len() && #[trigger] key_vals(keys, args, keys[i]).len() > int8_max())
            ==> r == Err::<Seq<Row>, SqlError>(SqlError::NumericValueOutOfRange)
    }),
{
    let aggs = count_distinct_aggs(e);
    let ks = distinct_rows(keys);
    lemma_distinct_rows(keys);
    let rs = Seq::new(ks.len(), |g: int|
        match agg_row(aggs, group_members(keys, args, ks[g])) {
            Ok(a) => Ok(ks[g] + a),
            Err(e) => Err(e),
        });
    assert(group_rows(aggs, keys, args) == collect(rs));
    // Every group's outcome.
    assert forall|g: int| 0 <= g < ks.len() implies {
        let n = key_vals(keys, args, ks[g]).len() as int;
        &&& n <= int8_max() ==> #[trigger] rs[g] == Ok::<Row, SqlError>(group_out(keys, args, ks[g]))
        &&& n > int8_max() ==> rs[g] == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange)
    } by {
        assert(ks.contains(ks[g]));
        lemma_agg_row_one(e, keys, args, ks[g]);
    }
    if forall|i: int| 0 <= i < keys.len() ==> #[trigger] key_vals(keys, args, keys[i]).len() <= int8_max() {
        let outs = Seq::new(ks.len(), |g: int| group_out(keys, args, ks[g]));
        assert forall|g: int| 0 <= g < rs.len() implies #[trigger] rs[g] == Ok::<Row, SqlError>(outs[g]) by {
            assert(ks.contains(ks[g]));
            let i = choose|i: int| 0 <= i < keys.len() && keys[i] == ks[g];
            assert(key_vals(keys, args, keys[i]).len() <= int8_max());
        }
        crate::bridge::collect::lemma_collect_all(rs, outs);
        // The rows are the keys' output rows; distinct keys give distinct rows (the key is the row's prefix).
        assert forall|x: Row| #[trigger] outs.contains(x)
            <==> exists|i: int| 0 <= i < keys.len() && x == group_out(keys, args, #[trigger] keys[i]) by {
            if outs.contains(x) {
                let g = choose|g: int| 0 <= g < outs.len() && outs[g] == x;
                assert(ks.contains(ks[g]));
                let i = choose|i: int| 0 <= i < keys.len() && keys[i] == ks[g];
                assert(x == group_out(keys, args, keys[i]));
            }
            if exists|i: int| 0 <= i < keys.len() && x == group_out(keys, args, #[trigger] keys[i]) {
                let i = choose|i: int| 0 <= i < keys.len() && x == group_out(keys, args, #[trigger] keys[i]);
                assert(keys.contains(keys[i]));
                assert(ks.contains(keys[i]));
                let g = choose|g: int| 0 <= g < ks.len() && ks[g] == keys[i];
                assert(outs[g] == x);
            }
        }
        assert forall|a: int, b: int| 0 <= a < outs.len() && 0 <= b < outs.len() && a != b implies outs[a] != outs[b] by {
            if outs[a] == outs[b] {
                let (ka, kb) = (ks[a], ks[b]);
                assert(plain_row(ka) && plain_row(kb));
                let la = ka.len();
                assert(outs[a].len() == la + 1);
                assert(ka =~= outs[a].subrange(0, la as int));
                assert(kb.len() == la);
                assert(kb =~= outs[b].subrange(0, la as int));
            }
        }
    } else {
        let i = choose|i: int| 0 <= i < keys.len() && #[trigger] key_vals(keys, args, keys[i]).len() > int8_max();
        assert(keys.contains(keys[i]));
        assert(ks.contains(keys[i]));
        let g0 = choose|g: int| 0 <= g < ks.len() && ks[g] == keys[i];
        assert(rs[g0] == Err::<Row, SqlError>(SqlError::NumericValueOutOfRange));
        lemma_collect_uniform_err(rs, g0, SqlError::NumericValueOutOfRange);
    }
}

/// `collect` of outcomes whose errors are all `e`: an error is `e`.
proof fn lemma_collect_uniform(rs: Seq<Result<Row, SqlError>>, e: SqlError)
    requires forall|g: int| 0 <= g < rs.len() && (#[trigger] rs[g]) is Err ==> rs[g] == Err::<Row, SqlError>(e),
    ensures collect(rs) is Err ==> collect(rs) == Err::<Seq<Row>, SqlError>(e),
    decreases rs.len(),
{
    if rs.len() > 0 {
        let p = rs.drop_last();
        assert forall|g: int| 0 <= g < p.len() && (#[trigger] p[g]) is Err implies p[g] == Err::<Row, SqlError>(e) by {
            assert(p[g] == rs[g]);
        }
        lemma_collect_uniform(p, e);
    }
}

/// `collect` of outcomes whose errors are all `e`, with some error: `e`.
proof fn lemma_collect_uniform_err(rs: Seq<Result<Row, SqlError>>, g0: int, e: SqlError)
    requires
        0 <= g0 < rs.len(),
        rs[g0] == Err::<Row, SqlError>(e),
        forall|g: int| 0 <= g < rs.len() && (#[trigger] rs[g]) is Err ==> rs[g] == Err::<Row, SqlError>(e),
    ensures collect(rs) == Err::<Seq<Row>, SqlError>(e),
{
    crate::bridge::collect::lemma_collect_ok(rs);
    lemma_collect_uniform(rs, e);
}

} // verus!
