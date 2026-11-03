//! The inner GROUP BY (`c_custkey`, `COUNT(o_orderkey)`) over the LEFT JOIN, for every database bound to the parts
//! when no `LIKE` raises (or there is no customer).
//!
//! The join (`left_join_rows`) is one block per customer row `i` (`block`): the customer's row followed by each
//! matching orders row, or by NULLs when none matches. Every row of block `i` has key `c_custkey[i]` (`ckey`), the
//! keys are distinct (PRIMARY KEY), so the groups are the customers in row order (`lemma_blocks`), and the members
//! of group `i` are block `i`'s `o_orderkey` values: `ccnt(i)` integers, or one NULL (`lemma_block_count`). The
//! GROUP BY is therefore, per customer, `(c_custkey, ccnt)` or the error of a count beyond int8 (`lemma_inner`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::query::param_domain;
use crate::bridge::collect::*;
use crate::bridge::equality::lemma_row_not_distinct_refl;
use crate::exec::relational::domain::*;
use crate::link::capacity::lemma_group_prepared;
use crate::link::query::lemma_keep_true_member;
use crate::agent::common::groups::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::denote::*;

verus! {

/// The key row of customer row `i`.
pub open spec fn ckey(sv: StoresView, i: int) -> Row { seq![Val::Int(cck(sv)[i] as int)] }

/// The join rows of the customer rows below `m`.
pub open spec fn jrows(db: Database, sv: StoresView, pat: Seq<u8>, m: int) -> Seq<Row> {
    left_join_rows(db.tables[2].subrange(0, m), db.tables[1], truths(sv, pat).subrange(0, m), 9)
}

/// The join rows of customer row `i`.
pub open spec fn block(db: Database, sv: StoresView, pat: Seq<u8>, i: int) -> Seq<Row> {
    left_join_one(db.tables[2][i], db.tables[1], truths(sv, pat)[i], 9)
}

/// Group key and COUNT argument of every row.
pub open spec fn keys_of(rows: Seq<Row>) -> Seq<Row> { rows.map_values(|r: Row| seq![r[0]]) }
pub open spec fn args_of(rows: Seq<Row>) -> Seq<Row> { rows.map_values(|r: Row| seq![r[8]]) }

/// Per customer row: `(c_custkey, c_count)`, or the error of a count beyond int8.
pub open spec fn inner_results(sv: StoresView, pat: Seq<u8>) -> Seq<Result<Row, SqlError>> {
    Seq::new(n_c(sv) as nat, |i: int| match int_result(IntKind::Int8, ccnt(sv, pat, i) as int) {
        Ok(v) => Ok(seq![Val::Int(cck(sv)[i] as int), v]),
        Err(e) => Err(e),
    })
}

// ------------------------------------------------------------------------------------------------ blocks

/// One more customer row: one more block.
proof fn lemma_jrows_step(db: Database, sv: StoresView, pat: Seq<u8>, m: int)
    requires 0 <= m < db.tables[2].len(), db.tables[2].len() == n_c(sv),
    ensures jrows(db, sv, pat, m + 1) == jrows(db, sv, pat, m) + block(db, sv, pat, m),
{
    let (l, t) = (db.tables[2].subrange(0, m + 1), truths(sv, pat).subrange(0, m + 1));
    assert(l.drop_last() =~= db.tables[2].subrange(0, m));
    assert(t.drop_last() =~= truths(sv, pat).subrange(0, m));
    assert(l.last() == db.tables[2][m]);
    assert(t.last() == truths(sv, pat)[m]);
}

/// `keep_true` of the orders rows under customer `i`'s truths keeps `ocnt` rows.
proof fn lemma_kept_count(sv: StoresView, pat: Seq<u8>, rows: Seq<Row>, i: int, n: int)
    requires 0 <= i < n_c(sv), 0 <= n <= n_o(sv), rows.len() == n_o(sv),
    ensures
        keep_true(rows.subrange(0, n), truths(sv, pat)[i].subrange(0, n)).len()
            == ocnt(sv, pat, cck(sv)[i] as int, n),
    decreases n,
{
    if n > 0 {
        lemma_kept_count(sv, pat, rows, i, n - 1);
        let (r, t) = (rows.subrange(0, n), truths(sv, pat)[i].subrange(0, n));
        assert(r.drop_last() =~= rows.subrange(0, n - 1));
        assert(t.drop_last() =~= truths(sv, pat)[i].subrange(0, n - 1));
        assert(t.last() == on_truth(sv, pat, i, n - 1));
    }
}

/// Every value non-NULL: the count of non-NULL values is the length.
proof fn lemma_count_all(vs: Seq<Val>)
    requires forall|k: int| 0 <= k < vs.len() ==> !(#[trigger] vs[k] is Null),
    ensures count_non_null(vs) == vs.len(),
    decreases vs.len(),
{
    if vs.len() > 0 {
        let d = vs.drop_last();
        assert forall|k: int| 0 <= k < d.len() implies !(#[trigger] d[k] is Null) by { assert(d[k] == vs[k]); }
        lemma_count_all(d);
        assert(!(vs[vs.len() - 1] is Null));
    }
}

/// Block `i`: non-empty, every row has 17 columns and key `c_custkey[i]`, and its non-NULL `o_orderkey` count is
/// `ccnt(i)`.
pub proof fn lemma_block(sv: StoresView, db: Database, pat: Seq<u8>, i: int)
    requires bound_db(sv, db), 0 <= i < n_c(sv),
    ensures ({
        let b = block(db, sv, pat, i);
        &&& b.len() > 0
        &&& forall|t: int| 0 <= t < b.len() ==> (#[trigger] b[t]).len() == 17 && b[t][0] == Val::Int(cck(sv)[i] as int)
        &&& count_non_null(column(args_of(b), 0)) == ccnt(sv, pat, i)
    }),
{
    lemma_table_lens(sv, db);
    lemma_customer_row(sv, db, i);
    let (c, o) = (db.tables[2][i], db.tables[1]);
    let tr = truths(sv, pat)[i];
    let kept = keep_true(o, tr);
    assert(o.subrange(0, n_o(sv)) =~= o);
    assert(tr.subrange(0, n_o(sv)) =~= tr);
    lemma_kept_count(sv, pat, o, i, n_o(sv));
    let b = block(db, sv, pat, i);
    let col = column(args_of(b), 0);
    if kept.len() == 0 {
        assert(b == seq![c + null_row(9)]);
        assert(col =~= seq![Val::Null]);
        assert(count_non_null(col) == 0) by {
            assert(col.len() == 1 && col.last() is Null);
            assert(col.drop_last() =~= Seq::<Val>::empty());
            assert(count_non_null(col.drop_last()) == 0);
        }
    } else {
        assert(b == kept.map_values(|r: Row| c + r));
        assert forall|t: int| 0 <= t < kept.len() implies (#[trigger] kept[t]).len() == 9 && kept[t][0] is Int by {
            lemma_keep_true_member(o, tr, t);
            let j = choose|j: int| 0 <= j < o.len() && o[j] == kept[t];
            lemma_orders_row(sv, db, j);
        }
        assert forall|t: int| 0 <= t < b.len() implies (#[trigger] b[t]).len() == 17 && b[t][0] == Val::Int(cck(sv)[i] as int) by {
            assert(b[t] == c + kept[t]);
        }
        assert forall|k: int| 0 <= k < col.len() implies !(#[trigger] col[k] is Null) by {
            assert(col[k] == b[k][8]);
            assert(b[k] == c + kept[k]);
            assert(b[k][8] == kept[k][0]);
        }
        lemma_count_all(col);
    }
}

/// The facts about the join rows of the customer rows below `m` (see `lemma_blocks`).
pub open spec fn blocks_ok(db: Database, sv: StoresView, pat: Seq<u8>, m: int) -> bool {
    let j = jrows(db, sv, pat, m);
    &&& distinct_rows(keys_of(j)) == Seq::new(m as nat, |i: int| ckey(sv, i))
    &&& forall|i: int| 0 <= i < m ==> #[trigger] group_members(keys_of(j), args_of(j), ckey(sv, i))
            == args_of(block(db, sv, pat, i))
    &&& forall|x: int| (forall|i: int| 0 <= i < m ==> cck(sv)[i] as int != x)
            ==> #[trigger] group_members(keys_of(j), args_of(j), seq![Val::Int(x)]) == Seq::<Row>::empty()
}

/// Block `p`'s keys are all `ckey(p)`.
proof fn lemma_block_keys(sv: StoresView, db: Database, pat: Seq<u8>, p: int)
    requires bound_db(sv, db), 0 <= p < n_c(sv),
    ensures keys_of(block(db, sv, pat, p)).len() > 0, all_rows(keys_of(block(db, sv, pat, p)), ckey(sv, p)),
{
    lemma_block(sv, db, pat, p);
    let (b, kb) = (block(db, sv, pat, p), keys_of(block(db, sv, pat, p)));
    assert forall|t: int| 0 <= t < kb.len() implies #[trigger] kb[t] == ckey(sv, p) by {
        assert(kb[t] == seq![b[t][0]]);
    }
}

/// One more block: the groups gain customer `p`'s key.
proof fn lemma_blocks_distinct(sv: StoresView, db: Database, pat: Seq<u8>, p: int)
    requires bound_db(sv, db), 0 <= p < n_c(sv), keys_unique(cck(sv)), blocks_ok(db, sv, pat, p),
    ensures distinct_rows(keys_of(jrows(db, sv, pat, p + 1))) == Seq::new((p + 1) as nat, |i: int| ckey(sv, i)),
{
    lemma_table_lens(sv, db);
    lemma_jrows_step(db, sv, pat, p);
    lemma_block_keys(sv, db, pat, p);
    let (jp, b) = (jrows(db, sv, pat, p), block(db, sv, pat, p));
    let (kp, kb) = (keys_of(jp), keys_of(b));
    assert(keys_of(jrows(db, sv, pat, p + 1)) =~= kp + kb);
    let kk = ckey(sv, p);
    let dp = Seq::new(p as nat, |i: int| ckey(sv, i));
    lemma_has_not_distinct(dp, kk);
    assert forall|t: int| 0 <= t < dp.len() implies !row_not_distinct(#[trigger] dp[t], kk) by {
        lemma_int_keys(cck(sv)[t] as int, cck(sv)[p] as int);
    }
    lemma_distinct_append_block(kp, kb, kk);
    assert(dp.push(kk) =~= Seq::new((p + 1) as nat, |i: int| ckey(sv, i)));
}

/// One more block: the members of every key.
proof fn lemma_blocks_members(sv: StoresView, db: Database, pat: Seq<u8>, p: int)
    requires bound_db(sv, db), 0 <= p < n_c(sv), keys_unique(cck(sv)), blocks_ok(db, sv, pat, p),
    ensures ({
        let j = jrows(db, sv, pat, p + 1);
        &&& forall|i: int| 0 <= i < p + 1 ==> #[trigger] group_members(keys_of(j), args_of(j), ckey(sv, i))
                == args_of(block(db, sv, pat, i))
        &&& forall|x: int| (forall|i: int| 0 <= i < p + 1 ==> cck(sv)[i] as int != x)
                ==> #[trigger] group_members(keys_of(j), args_of(j), seq![Val::Int(x)]) == Seq::<Row>::empty()
    }),
{
    lemma_table_lens(sv, db);
    lemma_jrows_step(db, sv, pat, p);
    lemma_block_keys(sv, db, pat, p);
    let j = jrows(db, sv, pat, p + 1);
    let (jp, b) = (jrows(db, sv, pat, p), block(db, sv, pat, p));
    let (kp, ap, kb, ab) = (keys_of(jp), args_of(jp), keys_of(b), args_of(b));
    assert(keys_of(j) =~= kp + kb);
    assert(args_of(j) =~= ap + ab);
    let kk = ckey(sv, p);
    assert forall|i: int| 0 <= i < p + 1 implies #[trigger] group_members(keys_of(j), args_of(j), ckey(sv, i))
        == args_of(block(db, sv, pat, i)) by {
        lemma_members_append(kp, ap, kb, ab, ckey(sv, i));
        if i < p {
            assert forall|t: int| 0 <= t < kb.len() implies !row_not_distinct(#[trigger] kb[t], ckey(sv, i)) by {
                lemma_int_keys(cck(sv)[p] as int, cck(sv)[i] as int);
            }
            lemma_members_none(kb, ab, ckey(sv, i));
            assert(args_of(block(db, sv, pat, i)) + Seq::<Row>::empty() =~= args_of(block(db, sv, pat, i)));
        } else {
            assert(forall|i2: int| 0 <= i2 < p ==> cck(sv)[i2] as int != cck(sv)[p] as int);
            assert(group_members(kp, ap, seq![Val::Int(cck(sv)[p] as int)]) == Seq::<Row>::empty());
            assert forall|t: int| 0 <= t < kb.len() implies row_not_distinct(#[trigger] kb[t], kk) by {
                lemma_row_not_distinct_refl(kk);
            }
            lemma_members_all(kb, ab, kk);
            assert(Seq::<Row>::empty() + ab =~= ab);
        }
    }
    assert forall|x: int| (forall|i: int| 0 <= i < p + 1 ==> cck(sv)[i] as int != x)
        implies #[trigger] group_members(keys_of(j), args_of(j), seq![Val::Int(x)]) == Seq::<Row>::empty() by {
        lemma_members_append(kp, ap, kb, ab, seq![Val::Int(x)]);
        assert(forall|i: int| 0 <= i < p ==> cck(sv)[i] as int != x);
        assert(cck(sv)[p] as int != x);
        assert forall|t: int| 0 <= t < kb.len() implies !row_not_distinct(#[trigger] kb[t], seq![Val::Int(x)]) by {
            lemma_int_keys(cck(sv)[p] as int, x);
        }
        lemma_members_none(kb, ab, seq![Val::Int(x)]);
        assert(Seq::<Row>::empty() + Seq::<Row>::empty() =~= Seq::<Row>::empty());
    }
}

/// The groups of the join rows of the customer rows below `m` are those customers' keys, the members of
/// customer `i`'s group are its block's `o_orderkey` values, and another key has no member.
pub proof fn lemma_blocks(sv: StoresView, db: Database, pat: Seq<u8>, m: int)
    requires bound_db(sv, db), 0 <= m <= n_c(sv), keys_unique(cck(sv)),
    ensures blocks_ok(db, sv, pat, m),
    decreases m,
{
    lemma_table_lens(sv, db);
    if m == 0 {
        let j = jrows(db, sv, pat, 0);
        assert(db.tables[2].subrange(0, 0).len() == 0);
        assert(j == Seq::<Row>::empty());
        assert(keys_of(j) =~= Seq::<Row>::empty());
        assert(args_of(j) =~= Seq::<Row>::empty());
        assert(distinct_rows(keys_of(j)) =~= Seq::new(0, |i: int| ckey(sv, i)));
    } else {
        lemma_blocks(sv, db, pat, m - 1);
        lemma_blocks_distinct(sv, db, pat, m - 1);
        lemma_blocks_members(sv, db, pat, m - 1);
    }
}

// ------------------------------------------------------------------------------------------------ the GROUP BY

/// The group input of one join row: its key and its `o_orderkey`.
proof fn lemma_group_input_row(db: Database, r: Row)
    requires r.len() == 17,
    ensures group_input(db, Seq::<Val>::empty() + r, q_inner_keys(), q_inner_aggs()) == Ok::<(Row, Row), SqlError>((seq![r[0]], seq![r[8]])),
{
    let env = Seq::<Val>::empty() + r;
    assert(env =~= r);
    let keys = q_inner_keys();
    lemma_expr_results_index(db, env, keys);
    lemma_collect_all(expr_results(db, env, keys), seq![r[0]]);
    let aggs = q_inner_aggs();
    lemma_agg_arg_results_index(db, env, aggs);
    assert(agg_arg(db, env, aggs[0]) == eval_expr(db, env, Expr::Col(8)));
    lemma_collect_all(agg_arg_results(db, env, aggs), seq![r[8]]);
}

/// One aggregate over one argument column: the collected value.
proof fn lemma_count_row(args: Seq<Row>)
    ensures agg_row(q_inner_aggs(), args) == match int_result(IntKind::Int8, count_non_null(column(args, 0)) as int) {
        Ok(v) => Ok::<Row, SqlError>(seq![v]),
        Err(e) => Err(e),
    },
{
    lemma_agg_row(q_inner_aggs(), args);
    let rs = agg_value_results(q_inner_aggs(), args);
    assert(rs.len() == 1);
    assert(rs[0] == int_result(IntKind::Int8, count_non_null(column(args, 0)) as int));
    assert(rs.drop_last() =~= Seq::<Result<Val, SqlError>>::empty());
    assert(collect(rs.drop_last()) == Ok::<Seq<Val>, SqlError>(Seq::empty()));
    assert(Seq::<Val>::empty().push(rs[0]->Ok_0) =~= seq![rs[0]->Ok_0]);
}

/// The groups of all join rows, per customer row: the outcome of `inner_results`.
proof fn lemma_inner_groups(sv: StoresView, db: Database, pat: Seq<u8>)
    requires bound_db(sv, db), keys_unique(cck(sv)), blocks_ok(db, sv, pat, n_c(sv)),
    ensures ({
        let j = jrows(db, sv, pat, n_c(sv));
        collect(group_results(q_inner_aggs(), keys_of(j), args_of(j))) == collect(inner_results(sv, pat))
    }),
{
    let j = jrows(db, sv, pat, n_c(sv));
    let (ks, args) = (keys_of(j), args_of(j));
    let grs = group_results(q_inner_aggs(), ks, args);
    let irs = inner_results(sv, pat);
    assert forall|g: int| 0 <= g < grs.len() implies #[trigger] grs[g] == irs[g] by {
        assert(distinct_rows(ks)[g] == ckey(sv, g));
        assert(group_members(ks, args, ckey(sv, g)) == args_of(block(db, sv, pat, g)));
        lemma_block(sv, db, pat, g);
        lemma_count_row(args_of(block(db, sv, pat, g)));
        match int_result(IntKind::Int8, ccnt(sv, pat, g) as int) {
            Ok(v) => { assert(ckey(sv, g) + seq![v] =~= seq![Val::Int(cck(sv)[g] as int), v]); },
            Err(e) => {},
        }
    }
    lemma_collect_pointwise::<Row>();
}

/// The inner GROUP BY: per customer row, `(c_custkey, ccnt)` or the error of a count beyond int8.
pub proof fn lemma_inner(sv: StoresView, db: Database, ps: Seq<Literal>)
    requires bound_db(sv, db), param_domain(ps), n_c(sv) == 0 || likes_ok(sv, pat_of(ps)),
    ensures eval_query(db, Seq::empty(), q_inner(ps)) == collect(inner_results(sv, pat_of(ps))),
{
    let pat = pat_of(ps);
    let ctx = Seq::<Val>::empty();
    lemma_table_lens(sv, db);
    lemma_cust_keys_unique(sv, db);
    lemma_join(sv, db, ps);
    let n = n_c(sv);
    let j = jrows(db, sv, pat, n);
    assert(db.tables[2].subrange(0, n) =~= db.tables[2]);
    assert(truths(sv, pat).subrange(0, n) =~= truths(sv, pat));
    assert(eval_query(db, ctx, q_join(ps)) == Ok::<Relation, SqlError>(j));
    lemma_blocks(sv, db, pat, n);
    let (ks, args) = (keys_of(j), args_of(j));
    assert forall|r: int| 0 <= r < j.len() implies #[trigger] group_input(db, ctx + j[r], q_inner_keys(), q_inner_aggs())
        == Ok::<(Row, Row), SqlError>((ks[r], args[r])) by {
        lemma_join_row_len(sv, db, pat, n, r);
        lemma_group_input_row(db, j[r]);
    }
    let prepared = lemma_group_prepared(db, ctx, q_inner_keys(), q_inner_aggs(), j, ks, args);
    lemma_eval_group_by(db, ctx, q_inner_keys(), q_inner_aggs(), Box::new(q_join(ps)));
    lemma_inner_groups(sv, db, pat);
}

/// Every join row of the customer rows below `m` has 17 columns.
proof fn lemma_join_row_len(sv: StoresView, db: Database, pat: Seq<u8>, m: int, r: int)
    requires bound_db(sv, db), 0 <= m <= n_c(sv), 0 <= r < jrows(db, sv, pat, m).len(),
    ensures jrows(db, sv, pat, m)[r].len() == 17,
    decreases m,
{
    lemma_table_lens(sv, db);
    if m == 0 {
        assert(db.tables[2].subrange(0, 0).len() == 0);
    } else {
        lemma_jrows_step(db, sv, pat, m - 1);
        let jp = jrows(db, sv, pat, m - 1);
        if r < jp.len() {
            lemma_join_row_len(sv, db, pat, m - 1, r);
        } else {
            lemma_block(sv, db, pat, m - 1);
            assert(jrows(db, sv, pat, m)[r] == block(db, sv, pat, m - 1)[r - jp.len()]);
        }
    }
}

} // verus!
