//! L7 constraint facts: what declared keys and foreign keys give a join plan (engine toolkit; nothing here names a
//! query, a table or a column).
//!
//! The engine claim holds for every database whose declared integrity constraints hold (`constraints_hold` of the
//! declared database, `spec::constraints`); the lemmas here take any such database `cdb` and positions of its
//! declarations, never a particular schema.
//! - A key (PRIMARY KEY or UNIQUE, either NULLS mode) gives at most one row per probe: `key_probe` (SQL equality on
//!   every key column) has at most one row (`lemma_key_match_unique`, `lemma_key_probe`).
//! - A foreign key onto a key gives every child row whose referencing tuple has no NULL exactly one parent
//!   (`lemma_fk_parent`). For one-column keys this is a bucket of `engine_link::joins` (`lemma_probe_one_col`).
//! - A join in which every left row has exactly one partner is the left rows, each followed by its partner, in
//!   left order (`lemma_one_match_join`); projected on the left columns it is the left rows themselves (join
//!   elimination, `lemma_join_elim`).
//! - Dense keys (a checked storage flag: row `l` has key `base + l`) make the partner an array lookup
//!   (`dense_on`, `lemma_dense_bucket`, `lemma_array_join`).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::text::lex_cmp;
use crate::spec::datetime::date_as_usecs;
use crate::spec::scalar::*;
use crate::spec::equality::*;
use crate::spec::constraints::*;
use crate::bridge::constraints::{lemma_constraint_at, lemma_foreign_key_target};
use crate::bridge::order::{lemma_compare_antisym, lemma_compare_trans};
use crate::bridge::typing::val_family;
use crate::link::join::{keep, lemma_keep_ext, lemma_keep_none};
use crate::engine_link::bag::flat_by;
use crate::engine_link::colmap::*;
use crate::engine_link::joins::*;

verus! {

// ------------------------------------------------------------------------------------- SQL equality

/// Comparable values are of one comparison family (not NULL).
pub proof fn lemma_compare_family(u: Val, v: Val)
    requires compare(u, v) is Some,
    ensures val_family(u) >= 0, val_family(u) == val_family(v),
{
    hide(num_cmp);
    hide(lex_cmp);
    hide(sign);
    hide(date_as_usecs);
}

/// SQL equality is transitive through a common value: `k = a` and `k = b` give `a = b`.
pub proof fn lemma_eq_through(k: Val, a: Val, b: Val)
    requires compare(k, a) == Some(0int), compare(k, b) == Some(0int),
    ensures compare(a, b) == Some(0int),
{
    hide(compare);
    lemma_compare_family(k, a);
    lemma_compare_family(k, b);
    lemma_compare_antisym(k, a);
    lemma_compare_antisym(k, b);
    lemma_compare_trans(a, k, b);
    lemma_compare_trans(b, k, a);
    lemma_compare_antisym(a, b);
}

/// Key tuples that both SQL-equal one probe tuple have no NULL and are not distinct from each other.
pub proof fn lemma_matches_not_distinct(k: Row, u: Row, v: Row)
    requires key_matches(k, u), key_matches(k, v),
    ensures row_not_distinct(u, v), !has_null(u), !has_null(v),
{
    hide(compare);
    assert(u.len() == k.len() && v.len() == k.len());
    assert forall|i: int| #![trigger u[i]] #![trigger v[i]] 0 <= i < k.len() implies
        val_not_distinct(u[i], v[i]) && !(u[i] is Null) && !(v[i] is Null) by {
        assert(compare(k[i], u[i]) == Some(0int) && compare(k[i], v[i]) == Some(0int));
        lemma_eq_through(k[i], u[i], v[i]);
        lemma_compare_family(k[i], u[i]);
        lemma_compare_family(k[i], v[i]);
    }
}

// ------------------------------------------------------------------------------------- keys

/// The rows whose key on `cols` SQL-equals the probe tuple `k`.
pub open spec fn probe_keeps(cols: Seq<nat>, k: Row) -> spec_fn(Row) -> bool {
    |r: Row| key_matches(k, key_of(r, cols))
}

/// The rows of `rows` whose key on `cols` SQL-equals `k`, in order (one index probe).
pub open spec fn key_probe(rows: Seq<Row>, cols: Seq<nat>, k: Row) -> Seq<Row> {
    keep(rows, probe_keeps(cols, k))
}

/// Constraint `kc` of table `t` of `cdb` is the key `Key { cols, primary, nulls_distinct }`, and the constraints hold.
pub open spec fn key_at(cdb: Database, t: int, kc: int, cols: Seq<nat>, primary: bool, nulls_distinct: bool) -> bool {
    &&& constraints_hold(cdb)
    &&& 0 <= t < cdb.schema.len()
    &&& t < cdb.tables.len()
    &&& 0 <= kc < cdb.schema[t].constraints.len()
    &&& cdb.schema[t].constraints[kc] == (Constraint::Key { cols, primary, nulls_distinct })
}

/// A declared key: two rows matching one probe are the same row.
pub proof fn lemma_key_match_unique(cdb: Database, t: int, kc: int, cols: Seq<nat>, primary: bool, nulls_distinct: bool,
    k: Row, i1: int, i2: int)
    requires
        key_at(cdb, t, kc, cols, primary, nulls_distinct),
        0 <= i1 < cdb.tables[t].len(), 0 <= i2 < cdb.tables[t].len(),
        key_matches(k, key_of(cdb.tables[t][i1], cols)), key_matches(k, key_of(cdb.tables[t][i2], cols)),
    ensures i1 == i2,
{
    lemma_constraint_at(cdb, t, kc);
    let rows = cdb.tables[t];
    assert(key_holds(rows, cols, primary, nulls_distinct));
    if i1 != i2 {
        let (lo, hi) = if i1 < i2 { (i1, i2) } else { (i2, i1) };
        lemma_matches_not_distinct(k, key_of(rows[lo], cols), key_of(rows[hi], cols));
        assert(key_collides(rows[lo], rows[hi], cols, nulls_distinct));
    }
}

/// When at most one position satisfies `f`, `keep` has at most one row, and exactly the row of a satisfying
/// position when there is one.
pub proof fn lemma_keep_unique(rows: Seq<Row>, f: spec_fn(Row) -> bool)
    requires
        forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && f(#[trigger] rows[i]) && f(#[trigger] rows[j]) ==> i == j,
    ensures
        keep(rows, f).len() <= 1,
        forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) ==> keep(rows, f) == seq![rows[i]],
    decreases rows.len(),
{
    if rows.len() > 0 {
        let n = rows.len() - 1;
        let init = rows.drop_last();
        assert forall|i: int, j: int| 0 <= i < init.len() && 0 <= j < init.len() && f(#[trigger] init[i]) && f(#[trigger] init[j])
            implies i == j by {
            assert(init[i] == rows[i] && init[j] == rows[j]);
        }
        lemma_keep_unique(init, f);
        if f(rows[n]) {
            assert forall|i: int| 0 <= i < init.len() implies !f(#[trigger] init[i]) by {
                assert(init[i] == rows[i]);
                if f(rows[i]) {
                    assert(i == n);
                }
            }
            lemma_keep_none(init, f);
            assert(keep(rows, f) =~= seq![rows[n]]);
            assert forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) implies keep(rows, f) == seq![rows[i]] by {
                assert(i == n);
            }
        } else {
            assert forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) implies keep(rows, f) == seq![rows[i]] by {
                assert(i != n);
                assert(init[i] == rows[i]);
            }
        }
    }
}

/// L7, key probe: a declared key gives at most one row per probe; a matching row is the probe's one row.
pub proof fn lemma_key_probe(cdb: Database, t: int, kc: int, cols: Seq<nat>, primary: bool, nulls_distinct: bool, k: Row)
    requires key_at(cdb, t, kc, cols, primary, nulls_distinct),
    ensures
        key_probe(cdb.tables[t], cols, k).len() <= 1,
        forall|i: int| 0 <= i < cdb.tables[t].len() && key_matches(k, key_of(#[trigger] cdb.tables[t][i], cols))
            ==> key_probe(cdb.tables[t], cols, k) == seq![cdb.tables[t][i]],
{
    let rows = cdb.tables[t];
    let f = probe_keeps(cols, k);
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && f(#[trigger] rows[i]) && f(#[trigger] rows[j])
        implies i == j by {
        lemma_key_match_unique(cdb, t, kc, cols, primary, nulls_distinct, k, i, j);
    }
    lemma_keep_unique(rows, f);
    assert forall|i: int| 0 <= i < rows.len() && key_matches(k, key_of(#[trigger] rows[i], cols))
        implies key_probe(rows, cols, k) == seq![rows[i]] by {
        assert(f(rows[i]));
    }
}

// ------------------------------------------------------------------------------------- foreign keys

/// Constraint `kf` of table `t` is the foreign key `cols -> pt(ref_cols)` and constraint `kp` of table `pt` is a key
/// on exactly `ref_cols` (in that order), and the constraints hold.
pub open spec fn fk_at(cdb: Database, t: int, kf: int, cols: Seq<nat>, pt: nat, ref_cols: Seq<nat>, match_full: bool,
    kp: int, primary: bool, nulls_distinct: bool) -> bool {
    &&& constraints_hold(cdb)
    &&& 0 <= t < cdb.schema.len()
    &&& t < cdb.tables.len()
    &&& 0 <= kf < cdb.schema[t].constraints.len()
    &&& cdb.schema[t].constraints[kf] == (Constraint::ForeignKey { cols, table: pt, ref_cols, match_full })
    &&& pt < cdb.schema.len()
    &&& 0 <= kp < cdb.schema[pt as int].constraints.len()
    &&& cdb.schema[pt as int].constraints[kp] == (Constraint::Key { cols: ref_cols, primary, nulls_distinct })
}

/// L7, foreign key: a child row whose referencing tuple has no NULL has exactly one parent row (position `j`); the
/// probe of the parent key with its tuple is that row.
pub proof fn lemma_fk_parent(cdb: Database, t: int, kf: int, cols: Seq<nat>, pt: nat, ref_cols: Seq<nat>, match_full: bool,
    kp: int, primary: bool, nulls_distinct: bool, i: int) -> (j: int)
    requires
        fk_at(cdb, t, kf, cols, pt, ref_cols, match_full, kp, primary, nulls_distinct),
        0 <= i < cdb.tables[t].len(),
        !has_null(key_of(cdb.tables[t][i], cols)),
    ensures
        pt < cdb.tables.len(),
        0 <= j < cdb.tables[pt as int].len(),
        key_matches(key_of(cdb.tables[t][i], cols), key_of(cdb.tables[pt as int][j], ref_cols)),
        key_probe(cdb.tables[pt as int], ref_cols, key_of(cdb.tables[t][i], cols)) == seq![cdb.tables[pt as int][j]],
{
    lemma_foreign_key_target(cdb, t, kf, cols, pt, ref_cols, match_full, i);
    let k = key_of(cdb.tables[t][i], cols);
    let parent = cdb.tables[pt as int];
    let j = choose|j: int| 0 <= j < parent.len() && key_matches(k, key_of(#[trigger] parent[j], ref_cols));
    lemma_key_probe(cdb, pt as int, kp, ref_cols, primary, nulls_distinct, k);
    j
}

/// A one-column probe is a bucket of `joins` (SQL equality on that column).
pub proof fn lemma_probe_one_col(rows: Seq<Row>, j: nat, v: Val)
    ensures key_probe(rows, seq![j], seq![v]) == eq_bucket(rows, j, v),
{
    assert forall|l: int| 0 <= l < rows.len() implies #[trigger] probe_keeps(seq![j], seq![v])(rows[l]) == bucket_keeps(j, v)(rows[l]) by {
        let kk = key_of(rows[l], seq![j]);
        assert(kk =~= seq![rows[l][j as int]]);
        if key_matches(seq![v], kk) {
            assert(compare(seq![v][0], kk[0]) == Some(0int));
        }
    }
    lemma_keep_ext(rows, probe_keeps(seq![j], seq![v]), bucket_keeps(j, v));
}

// ------------------------------------------------------------------------------------- joins with one partner

/// Blocks of one row each are a map.
proof fn lemma_flat_by_singletons(s: Seq<Row>, g: spec_fn(Row) -> Seq<Row>, h: spec_fn(Row) -> Row)
    requires forall|i: int| 0 <= i < s.len() ==> #[trigger] g(s[i]) == seq![h(s[i])],
    ensures flat_by(s, g) == s.map_values(h),
    decreases s.len(),
{
    if s.len() > 0 {
        let init = s.drop_last();
        assert forall|i: int| 0 <= i < init.len() implies #[trigger] g(init[i]) == seq![h(init[i])] by {
            assert(init[i] == s[i]);
        }
        lemma_flat_by_singletons(init, g, h);
        assert(g(s.last()) == seq![h(s.last())]) by {
            assert(s[s.len() - 1] == s.last());
        }
        assert(s.map_values(h) =~= init.map_values(h) + seq![h(s.last())]);
    } else {
        assert(s.map_values(h) =~= Seq::<Row>::empty());
    }
}

/// A left row followed by its partner.
pub open spec fn with_partner(partner: spec_fn(Row) -> Row) -> spec_fn(Row) -> Row {
    |x: Row| x + partner(x)
}

/// A join in which every left row's bucket is exactly its partner is the left rows, each followed by its partner,
/// in left order.
pub proof fn lemma_one_match_join(a: Seq<Row>, b: Seq<Row>, i: nat, j: nat, partner: spec_fn(Row) -> Row)
    requires forall|k: int| 0 <= k < a.len() ==> #[trigger] eq_bucket(b, j, a[k][i as int]) == seq![partner(a[k])],
    ensures equi_join(a, b, i, j) == a.map_values(with_partner(partner)),
{
    assert forall|k: int| 0 <= k < a.len() implies #[trigger] equi_block(b, i, j)(a[k]) == seq![with_partner(partner)(a[k])] by {
        let x = a[k];
        assert(eq_bucket(b, j, x[i as int]).map_values(|y: Row| x + y) =~= seq![x + partner(x)]);
    }
    lemma_flat_by_singletons(a, equi_block(b, i, j), with_partner(partner));
}

/// L7 join elimination: when every left row has exactly one partner, the join projected on the left columns is the
/// left rows, in order (`SELECT child.* FROM child JOIN parent ON fk = key` is `child`).
pub proof fn lemma_join_elim(a: Seq<Row>, b: Seq<Row>, i: nat, j: nat, wa: nat, partner: spec_fn(Row) -> Row)
    requires
        width_of(a, wa),
        forall|k: int| 0 <= k < a.len() ==> #[trigger] eq_bucket(b, j, a[k][i as int]) == seq![partner(a[k])],
    ensures map_rows(id_map(wa), equi_join(a, b, i, j)) == a,
{
    lemma_one_match_join(a, b, i, j, partner);
    let joined = a.map_values(with_partner(partner));
    assert forall|k: int| 0 <= k < a.len() implies #[trigger] map_rows(id_map(wa), joined)[k] == a[k] by {
        assert(map_row(id_map(wa), a[k] + partner(a[k])) =~= a[k]);
    }
    assert(map_rows(id_map(wa), joined) =~= a);
}

/// L7, the one-column foreign key join: every child row (table `t`, column `ci` not NULL) has its parent row (table
/// `pt`, key column `pj`) as the one row of its bucket.
pub proof fn lemma_fk_bucket(cdb: Database, t: int, kf: int, ci: nat, pt: nat, pj: nat, match_full: bool,
    kp: int, primary: bool, nulls_distinct: bool, i: int) -> (j: int)
    requires
        fk_at(cdb, t, kf, seq![ci], pt, seq![pj], match_full, kp, primary, nulls_distinct),
        0 <= i < cdb.tables[t].len(),
        ci < cdb.tables[t][i].len(),
        !(cdb.tables[t][i][ci as int] is Null),
    ensures
        pt < cdb.tables.len(),
        0 <= j < cdb.tables[pt as int].len(),
        eq_bucket(cdb.tables[pt as int], pj, cdb.tables[t][i][ci as int]) == seq![cdb.tables[pt as int][j]],
{
    let x = cdb.tables[t][i];
    let k = key_of(x, seq![ci]);
    assert(k =~= seq![x[ci as int]]);
    assert(!has_null(k));
    let j = lemma_fk_parent(cdb, t, kf, seq![ci], pt, seq![pj], match_full, kp, primary, nulls_distinct, i);
    lemma_probe_one_col(cdb.tables[pt as int], pj, x[ci as int]);
    j
}

// ------------------------------------------------------------------------------------- dense keys

/// The value of an integer (0 otherwise).
pub open spec fn int_of(v: Val) -> int {
    match v {
        Val::Int(x) => x,
        _ => 0,
    }
}

/// Row `l` of `b` has the integer key `base + l` in column `j` (a dense key column; a checked storage flag).
pub open spec fn dense_on(b: Seq<Row>, j: nat, base: int) -> bool {
    forall|l: int| 0 <= l < b.len() ==> #[trigger] b[l][j as int] == Val::Int(base + l)
}

/// The bucket of an integer in dense rows is the one row at its offset, or none.
pub proof fn lemma_dense_bucket(b: Seq<Row>, j: nat, base: int, v: int)
    requires dense_on(b, j, base),
    ensures
        eq_bucket(b, j, Val::Int(v)) == if 0 <= v - base < b.len() { seq![b[v - base]] } else { Seq::<Row>::empty() },
{
    let f = bucket_keeps(j, Val::Int(v));
    assert forall|l: int| 0 <= l < b.len() implies #[trigger] f(b[l]) == (l == v - base) by {
        assert(b[l][j as int] == Val::Int(base + l));
        assert(compare(Val::Int(v), Val::Int(base + l)) == Some(sign(v - (base + l))));
    }
    assert forall|i: int, k: int| 0 <= i < b.len() && 0 <= k < b.len() && f(#[trigger] b[i]) && f(#[trigger] b[k]) implies i == k by {}
    lemma_keep_unique(b, f);
    if 0 <= v - base < b.len() {
        assert(f(b[v - base]));
    } else {
        lemma_keep_none(b, f);
    }
}

/// The partner of a left row in dense rows: the row at the offset of its key (column `i`).
pub open spec fn dense_partner(b: Seq<Row>, i: nat, base: int) -> spec_fn(Row) -> Row {
    |x: Row| b[int_of(x[i as int]) - base]
}

/// L7, array join: when every left key (column `i`) is an integer inside the dense range of `b`, the equi-join is
/// one array lookup per left row.
pub proof fn lemma_array_join(a: Seq<Row>, b: Seq<Row>, i: nat, j: nat, base: int)
    requires
        dense_on(b, j, base),
        forall|k: int| 0 <= k < a.len() ==> (#[trigger] a[k][i as int]) is Int && 0 <= int_of(a[k][i as int]) - base < b.len(),
    ensures equi_join(a, b, i, j) == a.map_values(with_partner(dense_partner(b, i, base))),
{
    assert forall|k: int| 0 <= k < a.len() implies #[trigger] eq_bucket(b, j, a[k][i as int]) == seq![dense_partner(b, i, base)(a[k])] by {
        let v = int_of(a[k][i as int]);
        assert(a[k][i as int] == Val::Int(v));
        lemma_dense_bucket(b, j, base, v);
    }
    lemma_one_match_join(a, b, i, j, dense_partner(b, i, base));
}

} // verus!
