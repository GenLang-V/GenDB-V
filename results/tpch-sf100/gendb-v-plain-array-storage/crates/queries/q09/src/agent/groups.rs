//! The groups of the normal form are sums over the lineitem rows (`lemma_group_sums`).
//!
//! A group accumulator of `g2` over the SELECT rows is a sum over the kept joined rows, hence over all joined rows
//! of a contribution that vanishes off the WHERE (`lemma_sum_kept`). The WHERE contains the six key equalities and
//! every key it compares against is a primary key, so each joined row with a non-zero contribution is determined by
//! its lineitem row. The sum over `from6` collapses level by level (`common::sum_pick`): nation on `s_nationkey`,
//! orders on `l_orderkey`, partsupp on `(l_partkey, l_suppkey)` (`lift5`, `lift4`, `lift3`); the remaining sum over
//! `(part x supplier) x lineitem` is exchanged into a sum over the lineitem rows of a sum over `part x supplier`, in
//! which the part on `l_partkey` and the supplier on `l_suppkey` are unique (`lift1`, `lemma_reduce`). The
//! contribution of row `l` is then its `kterm` (`lemma_lift_line`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::query::param_domain;
use crate::link::query::*;
use crate::link::join::{sum_of, keep, count_term, sum_term, abs_term, lemma_acc_sum_of, lemma_sum_of_map,
    lemma_sum_of_keep, lemma_sum_of_ext, lemma_keep_true_keep, lemma_keep_members, lemma_sum_of_product,
    lemma_sum_of_product_swap};
use crate::link::source::lemma_proj_all_index;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::denotation::*;
use crate::agent::lines::*;
use crate::agent::common::sum_pick::*;

verus! {

// ------------------------------------------------------------------------------------------------ table shapes

/// Widths of the input rows and of the product rows; the joined key columns are duplicate-free.
pub proof fn lemma_shapes(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        forall|p: int| 0 <= p < db.tables[3].len() ==> (#[trigger] db.tables[3][p]).len() == 9,
        forall|p: int| 0 <= p < db.tables[5].len() ==> (#[trigger] db.tables[5][p]).len() == 7,
        forall|p: int| 0 <= p < db.tables[0].len() ==> (#[trigger] db.tables[0][p]).len() == 16,
        forall|p: int| 0 <= p < db.tables[4].len() ==> (#[trigger] db.tables[4][p]).len() == 5,
        forall|p: int| 0 <= p < db.tables[1].len() ==> (#[trigger] db.tables[1][p]).len() == 9,
        forall|p: int| 0 <= p < db.tables[6].len() ==> (#[trigger] db.tables[6][p]).len() == 4,
        forall|k: int| 0 <= k < from2(db).len() ==> (#[trigger] from2(db)[k]).len() == 16,
        forall|k: int| 0 <= k < from3(db).len() ==> (#[trigger] from3(db)[k]).len() == 32,
        forall|k: int| 0 <= k < from4(db).len() ==> (#[trigger] from4(db)[k]).len() == 37,
        forall|k: int| 0 <= k < from5(db).len() ==> (#[trigger] from5(db)[k]).len() == 46,
        col_unique(db.tables[3], 0), col_unique(db.tables[5], 0), col_unique(db.tables[1], 0), col_unique(db.tables[6], 0),
        col2_unique(db.tables[4], 0, 1),
{
    lemma_parts_shape(sv, db);
    lemma_keys_unique(sv, db);
    assert forall|p: int| 0 <= p < db.tables[3].len() implies (#[trigger] db.tables[3][p]).len() == 9 by {
        lemma_part_row(sv, db, p);
    }
    assert forall|p: int| 0 <= p < db.tables[5].len() implies (#[trigger] db.tables[5][p]).len() == 7 by {
        lemma_supplier_row(sv, db, p);
    }
    assert forall|p: int| 0 <= p < db.tables[0].len() implies (#[trigger] db.tables[0][p]).len() == 16 by {
        lemma_lineitem_row(sv, db, p);
    }
    assert forall|p: int| 0 <= p < db.tables[4].len() implies (#[trigger] db.tables[4][p]).len() == 5 by {
        lemma_partsupp_row(sv, db, p);
    }
    assert forall|p: int| 0 <= p < db.tables[1].len() implies (#[trigger] db.tables[1][p]).len() == 9 by {
        lemma_orders_row(sv, db, p);
    }
    assert forall|p: int| 0 <= p < db.tables[6].len() implies (#[trigger] db.tables[6][p]).len() == 4 by {
        lemma_nation_row(sv, db, p);
    }
    lemma_product_widths(db.tables[3], db.tables[5], 9, 7);
    lemma_product_widths(from2(db), db.tables[0], 16, 16);
    lemma_product_widths(from3(db), db.tables[4], 32, 5);
    lemma_product_widths(from4(db), db.tables[1], 37, 9);
    assert forall|p: int, q: int| 0 <= p < db.tables[3].len() && 0 <= q < db.tables[3].len()
        && #[trigger] db.tables[3][p][0] == #[trigger] db.tables[3][q][0] implies p == q by {
        lemma_part_row(sv, db, p);
        lemma_part_row(sv, db, q);
        assert(pk(sv)[p] == pk(sv)[q]);
    }
    assert forall|p: int, q: int| 0 <= p < db.tables[5].len() && 0 <= q < db.tables[5].len()
        && #[trigger] db.tables[5][p][0] == #[trigger] db.tables[5][q][0] implies p == q by {
        lemma_supplier_row(sv, db, p);
        lemma_supplier_row(sv, db, q);
        assert(sk(sv)[p] == sk(sv)[q]);
    }
    assert forall|p: int, q: int| 0 <= p < db.tables[1].len() && 0 <= q < db.tables[1].len()
        && #[trigger] db.tables[1][p][0] == #[trigger] db.tables[1][q][0] implies p == q by {
        lemma_orders_row(sv, db, p);
        lemma_orders_row(sv, db, q);
        assert(ok(sv)[p] == ok(sv)[q]);
    }
    assert forall|p: int, q: int| 0 <= p < db.tables[6].len() && 0 <= q < db.tables[6].len()
        && #[trigger] db.tables[6][p][0] == #[trigger] db.tables[6][q][0] implies p == q by {
        lemma_nation_row(sv, db, p);
        lemma_nation_row(sv, db, q);
        assert(nk(sv)[p] == nk(sv)[q]);
    }
    assert forall|p: int, q: int| 0 <= p < db.tables[4].len() && 0 <= q < db.tables[4].len()
        && #[trigger] db.tables[4][p][0] == #[trigger] db.tables[4][q][0] && db.tables[4][p][1] == db.tables[4][q][1]
        implies p == q by {
        lemma_partsupp_row(sv, db, p);
        lemma_partsupp_row(sv, db, q);
        assert(pspk(sv)[p] == pspk(sv)[q] && pssk(sv)[p] == pssk(sv)[q]);
    }
}

/// The key equalities of a qualifying 50-column joined row.
pub proof fn lemma_qual_keys(ps: Seq<Literal>, r: Row)
    requires r.len() == 50, qual_row(ps, r),
    ensures r[9] == r[18], r[33] == r[18], r[32] == r[17], r[0] == r[17], r[37] == r[16], r[12] == r[46],
{
    lemma_joined_proj(r);
}

// ------------------------------------------------------------------------------------------------ the collapse

/// Sum over `nation` of the rows extending a 46-column prefix (joined on `s_nationkey`).
pub open spec fn lift5(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| at_pick(db.tables[6], 0, x[12], |y: Row| f(x + y))
}

/// Sum over `orders` of the rows extending a 37-column prefix (joined on `l_orderkey`).
pub open spec fn lift4(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| at_pick(db.tables[1], 0, x[16], |y: Row| lift5(db, f)(x + y))
}

/// Sum over `partsupp` of the rows extending a 32-column prefix (joined on `(l_partkey, l_suppkey)`).
pub open spec fn lift3(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| at_pick2(db.tables[4], 0, x[17], 1, x[18], |y: Row| lift4(db, f)(x + y))
}

/// Sum over `part x supplier` of the rows of one lineitem row (joined on `l_partkey` and `l_suppkey`).
pub open spec fn lift1(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |y: Row| at_pick(db.tables[3], 0, y[1], |x: Row| at_pick(db.tables[5], 0, y[2], |z: Row| lift3(db, f)(x + z + y)))
}

/// A contribution that vanishes off the WHERE.
pub open spec fn vanishes(ps: Seq<Literal>, f: spec_fn(Row) -> int) -> bool {
    forall|r: Row| #[trigger] f(r) != 0 ==> qual_row(ps, r)
}

proof fn lemma_level6(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_db(sv, db), vanishes(ps, f),
    ensures forall|p: int, q: int| 0 <= p < from5(db).len() && 0 <= q < db.tables[6].len()
        && f(#[trigger] from5(db)[p] + #[trigger] db.tables[6][q]) != 0 ==> db.tables[6][q][0] == from5(db)[p][12],
{
    lemma_shapes(sv, db);
    assert forall|p: int, q: int| 0 <= p < from5(db).len() && 0 <= q < db.tables[6].len()
        && f(#[trigger] from5(db)[p] + #[trigger] db.tables[6][q]) != 0 implies db.tables[6][q][0] == from5(db)[p][12] by {
        let r = from5(db)[p] + db.tables[6][q];
        lemma_qual_keys(ps, r);
    }
}

/// A non-zero `lift5` of a 46-column row: its nation row, with a qualifying joined row.
proof fn lemma_lift5_nonzero(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int, x5: Row)
    requires bound_db(sv, db), vanishes(ps, f), x5.len() == 46, lift5(db, f)(x5) != 0,
    ensures qual_row(ps, x5 + db.tables[6][pick(db.tables[6], 0, x5[12])]),
        0 <= pick(db.tables[6], 0, x5[12]) < db.tables[6].len(),
{
    let n = db.tables[6];
    lemma_shapes(sv, db);
    lemma_at_pick_nonzero(n, 0, x5[12], |y: Row| f(x5 + y));
}

proof fn lemma_level5(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_db(sv, db), vanishes(ps, f),
    ensures forall|p: int, q: int| 0 <= p < from4(db).len() && 0 <= q < db.tables[1].len()
        && lift5(db, f)(#[trigger] from4(db)[p] + #[trigger] db.tables[1][q]) != 0 ==> db.tables[1][q][0] == from4(db)[p][16],
{
    lemma_shapes(sv, db);
    let o = db.tables[1];
    let n = db.tables[6];
    assert forall|p: int, q: int| 0 <= p < from4(db).len() && 0 <= q < o.len()
        && lift5(db, f)(#[trigger] from4(db)[p] + #[trigger] o[q]) != 0 implies o[q][0] == from4(db)[p][16] by {
        let x = from4(db)[p] + o[q];
        lemma_lift5_nonzero(sv, db, ps, f, x);
        let a = pick(n, 0, x[12]);
        let r = x + n[a];
        lemma_qual_keys(ps, r);
    }
}

/// A non-zero `lift4` of a 37-column row: its order and nation rows, with a qualifying joined row.
proof fn lemma_lift4_nonzero(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int, x4: Row) -> (r: Row)
    requires bound_db(sv, db), vanishes(ps, f), x4.len() == 37, lift4(db, f)(x4) != 0,
    ensures r.len() == 50, qual_row(ps, r), r.subrange(0, 37) == x4,
{
    let (o, n) = (db.tables[1], db.tables[6]);
    lemma_shapes(sv, db);
    lemma_at_pick_nonzero(o, 0, x4[16], |y: Row| lift5(db, f)(x4 + y));
    let oo = pick(o, 0, x4[16]);
    let x5 = x4 + o[oo];
    lemma_lift5_nonzero(sv, db, ps, f, x5);
    let r = x5 + n[pick(n, 0, x5[12])];
    assert(r.subrange(0, 37) =~= x4);
    r
}

proof fn lemma_level4(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_db(sv, db), vanishes(ps, f),
    ensures forall|p: int, q: int| 0 <= p < from3(db).len() && 0 <= q < db.tables[4].len()
        && lift4(db, f)(#[trigger] from3(db)[p] + #[trigger] db.tables[4][q]) != 0
        ==> db.tables[4][q][0] == from3(db)[p][17] && db.tables[4][q][1] == from3(db)[p][18],
{
    lemma_shapes(sv, db);
    let t = db.tables[4];
    assert forall|p: int, q: int| 0 <= p < from3(db).len() && 0 <= q < t.len()
        && lift4(db, f)(#[trigger] from3(db)[p] + #[trigger] t[q]) != 0
        implies t[q][0] == from3(db)[p][17] && t[q][1] == from3(db)[p][18] by {
        let x = from3(db)[p] + t[q];
        let r = lemma_lift4_nonzero(sv, db, ps, f, x);
        lemma_qual_keys(ps, r);
        assert(r[32] == x[32] && r[33] == x[33] && r[17] == x[17] && r[18] == x[18]);
    }
}

/// A non-zero `lift3` of a 32-column row: a qualifying joined row extending it.
proof fn lemma_lift3_nonzero(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int, x3: Row) -> (r: Row)
    requires bound_db(sv, db), vanishes(ps, f), x3.len() == 32, lift3(db, f)(x3) != 0,
    ensures r.len() == 50, qual_row(ps, r), r.subrange(0, 32) == x3,
{
    let t = db.tables[4];
    lemma_shapes(sv, db);
    lemma_at_pick2_nonzero(t, 0, x3[17], 1, x3[18], |y: Row| lift4(db, f)(x3 + y));
    let q = pick2(t, 0, x3[17], 1, x3[18]);
    let x4 = x3 + t[q];
    let r = lemma_lift4_nonzero(sv, db, ps, f, x4);
    assert(r.subrange(0, 32) =~= r.subrange(0, 37).subrange(0, 32));
    assert(x4.subrange(0, 32) =~= x3);
    r
}

/// The part and supplier of a non-zero `lift3` of `P[p] + S[s] + L[l]` are joined to the lineitem row.
proof fn lemma_level12(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int, x: Row, z: Row, y: Row)
    requires bound_db(sv, db), vanishes(ps, f), x.len() == 9, z.len() == 7, y.len() == 16, lift3(db, f)(x + z + y) != 0,
    ensures x[0] == y[1], z[0] == y[2],
{
    let x3 = x + z + y;
    let r = lemma_lift3_nonzero(sv, db, ps, f, x3);
    lemma_qual_keys(ps, r);
    assert(r[0] == x3[0] && r[9] == x3[9] && r[17] == x3[17] && r[18] == x3[18]);
    assert(x3[0] == x[0] && x3[9] == z[0] && x3[17] == y[1] && x3[18] == y[2]);
}

/// The sum over `(part x supplier) x lineitem` of a 32-column contribution that is non-zero only on joined part and
/// supplier rows, as a sum over the lineitem rows.
proof fn lemma_reduce_front(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_db(sv, db), vanishes(ps, f),
    ensures sum_of(from3(db), lift3(db, f)) == sum_of(db.tables[0], lift1(db, f)),
{
    lemma_shapes(sv, db);
    let (tp, ts, tl) = (db.tables[3], db.tables[5], db.tables[0]);
    let h = lift3(db, f);
    lemma_sum_of_product_swap(from2(db), tl, h);
    let inner = |y: Row| sum_of(from2(db), |x: Row| h(x + y));
    assert forall|i: int| 0 <= i < tl.len() implies inner(#[trigger] tl[i]) == lift1(db, f)(tl[i]) by {
        let y = tl[i];
        let hy = |x: Row| h(x + y);
        lemma_sum_of_product(tp, ts, hy);
        // over the suppliers of each part: only the supplier with key l_suppkey
        let mid = |x: Row| sum_of(ts, |z: Row| hy(x + z));
        let mid2 = |x: Row| at_pick(ts, 0, y[2], |z: Row| h(x + z + y));
        assert forall|p: int| 0 <= p < tp.len() implies mid(#[trigger] tp[p]) == mid2(tp[p]) by {
            let x = tp[p];
            let hz = |z: Row| hy(x + z);
            let hz2 = |z: Row| h(x + z + y);
            assert forall|s: int| 0 <= s < ts.len() implies hz(#[trigger] ts[s]) == hz2(ts[s]) by {
                assert(x + ts[s] + y =~= (x + ts[s]) + y);
            }
            lemma_sum_of_ext(ts, hz, hz2);
            assert forall|s: int| 0 <= s < ts.len() && hz2(#[trigger] ts[s]) != 0 implies ts[s][0] == y[2] by {
                lemma_level12(sv, db, ps, f, x, ts[s], y);
            }
            lemma_sum_one_match(ts, 0, y[2], hz2);
        }
        lemma_sum_of_ext(tp, mid, mid2);
        // over the parts: only the part with key l_partkey
        assert forall|p: int| 0 <= p < tp.len() && mid2(#[trigger] tp[p]) != 0 implies tp[p][0] == y[1] by {
            let x = tp[p];
            lemma_at_pick_nonzero(ts, 0, y[2], |z: Row| h(x + z + y));
            let s = pick(ts, 0, y[2]);
            lemma_level12(sv, db, ps, f, x, ts[s], y);
        }
        lemma_sum_one_match(tp, 0, y[1], mid2);
        assert((|x: Row| at_pick(ts, 0, y[2], |z: Row| h(x + z + y))) =~= mid2);
    }
    lemma_sum_of_ext(tl, inner, lift1(db, f));
}

/// The sum of a contribution vanishing off the WHERE over all joined rows is the sum over the lineitem rows of
/// its value at each row's unique part, supplier, partsupp row, order and nation.
pub proof fn lemma_reduce(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_db(sv, db), vanishes(ps, f),
    ensures sum_of(from6(db), f) == sum_of(db.tables[0], lift1(db, f)),
{
    lemma_shapes(sv, db);
    lemma_level6(sv, db, ps, f);
    lemma_sum_product_right(from5(db), db.tables[6], f, 12, 0);
    assert((|x: Row| at_pick(db.tables[6], 0, x[12], |y: Row| f(x + y))) =~= lift5(db, f));
    lemma_level5(sv, db, ps, f);
    lemma_sum_product_right(from4(db), db.tables[1], lift5(db, f), 16, 0);
    assert((|x: Row| at_pick(db.tables[1], 0, x[16], |y: Row| lift5(db, f)(x + y))) =~= lift4(db, f));
    lemma_level4(sv, db, ps, f);
    lemma_sum_product_right2(from3(db), db.tables[4], lift4(db, f), 17, 18, 0, 1);
    assert((|x: Row| at_pick2(db.tables[4], 0, x[17], 1, x[18], |y: Row| lift4(db, f)(x + y))) =~= lift3(db, f));
    lemma_reduce_front(sv, db, ps, f);
}

// ------------------------------------------------------------------------------------------------ one lineitem row

/// A table whose column 0 is the key column `keys`: the picked row of a key is its `key_row`.
pub proof fn lemma_pick_key(b: Seq<Row>, keys: Seq<i64>, k: i64)
    requires
        b.len() == keys.len(), keys_unique(keys),
        forall|q: int| 0 <= q < b.len() ==> (#[trigger] b[q])[0] == Val::Int(keys[q] as int),
    ensures
        has_pick(b, 0, Val::Int(k as int)) == has_key(keys, k),
        has_key(keys, k) ==> pick(b, 0, Val::Int(k as int)) == key_row(keys, k),
{
    let v = Val::Int(k as int);
    lemma_key_row(keys, k);
    lemma_pick(b, 0, v);
    if has_pick(b, 0, v) {
        let q = pick(b, 0, v);
        assert(b[q][0] == Val::Int(keys[q] as int));
        assert(keys[q] == k);
        assert(has_key(keys, k));
    }
    if has_key(keys, k) {
        let j = key_row(keys, k);
        assert(b[j][0] == v);
        assert(has_pick(b, 0, v));
        let q = pick(b, 0, v);
        assert(b[q][0] == Val::Int(keys[q] as int));
        assert(keys[q] == k);
    }
}

/// A table whose columns 0 and 1 are the key column pair `(s, t)`: the picked row of a key pair is its `key_row2`.
pub proof fn lemma_pick2_key(b: Seq<Row>, s: Seq<i64>, t: Seq<i64>, x: i64, y: i64)
    requires
        b.len() == s.len(), s.len() == t.len(), keys2_unique(s, t),
        forall|q: int| 0 <= q < b.len() ==> (#[trigger] b[q])[0] == Val::Int(s[q] as int) && b[q][1] == Val::Int(t[q] as int),
    ensures
        has_pick2(b, 0, Val::Int(x as int), 1, Val::Int(y as int)) == has_key2(s, t, x, y),
        has_key2(s, t, x, y) ==> pick2(b, 0, Val::Int(x as int), 1, Val::Int(y as int)) == key_row2(s, t, x, y),
{
    let (vx, vy) = (Val::Int(x as int), Val::Int(y as int));
    lemma_key_row2(s, t, x, y);
    lemma_pick2(b, 0, vx, 1, vy);
    if has_pick2(b, 0, vx, 1, vy) {
        let q = pick2(b, 0, vx, 1, vy);
        assert(holds2(b, 0, vx, 1, vy, q));
        assert(b[q][0] == Val::Int(s[q] as int) && b[q][1] == Val::Int(t[q] as int));
        assert(at2(s, t, x, y, q));
        assert(has_key2(s, t, x, y));
    }
    if has_key2(s, t, x, y) {
        let j = key_row2(s, t, x, y);
        assert(at2(s, t, x, y, j));
        assert(b[j][0] == Val::Int(s[j] as int) && b[j][1] == Val::Int(t[j] as int));
        assert(holds2(b, 0, vx, 1, vy, j));
        assert(has_pick2(b, 0, vx, 1, vy));
        let q = pick2(b, 0, vx, 1, vy);
        assert(holds2(b, 0, vx, 1, vy, q));
        assert(b[q][0] == Val::Int(s[q] as int) && b[q][1] == Val::Int(t[q] as int));
        assert(at2(s, t, x, y, q));
    }
}

/// The key columns of each table.
proof fn lemma_key_cols(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        forall|q: int| 0 <= q < db.tables[3].len() ==> (#[trigger] db.tables[3][q])[0] == Val::Int(pk(sv)[q] as int),
        forall|q: int| 0 <= q < db.tables[5].len() ==> (#[trigger] db.tables[5][q])[0] == Val::Int(sk(sv)[q] as int),
        forall|q: int| 0 <= q < db.tables[4].len() ==> (#[trigger] db.tables[4][q])[0] == Val::Int(pspk(sv)[q] as int)
            && db.tables[4][q][1] == Val::Int(pssk(sv)[q] as int),
        forall|q: int| 0 <= q < db.tables[1].len() ==> (#[trigger] db.tables[1][q])[0] == Val::Int(ok(sv)[q] as int),
        forall|q: int| 0 <= q < db.tables[6].len() ==> (#[trigger] db.tables[6][q])[0] == Val::Int(nk(sv)[q] as int),
        keys_unique(pk(sv)), keys_unique(sk(sv)), keys_unique(ok(sv)), keys_unique(nk(sv)), keys2_unique(pspk(sv), pssk(sv)),
{
    lemma_parts_shape(sv, db);
    lemma_keys_unique(sv, db);
    assert forall|q: int| 0 <= q < db.tables[3].len() implies (#[trigger] db.tables[3][q])[0] == Val::Int(pk(sv)[q] as int) by {
        lemma_part_row(sv, db, q);
    }
    assert forall|q: int| 0 <= q < db.tables[5].len() implies (#[trigger] db.tables[5][q])[0] == Val::Int(sk(sv)[q] as int) by {
        lemma_supplier_row(sv, db, q);
    }
    assert forall|q: int| 0 <= q < db.tables[4].len() implies (#[trigger] db.tables[4][q])[0] == Val::Int(pspk(sv)[q] as int)
        && db.tables[4][q][1] == Val::Int(pssk(sv)[q] as int) by {
        lemma_partsupp_row(sv, db, q);
    }
    assert forall|q: int| 0 <= q < db.tables[1].len() implies (#[trigger] db.tables[1][q])[0] == Val::Int(ok(sv)[q] as int) by {
        lemma_orders_row(sv, db, q);
    }
    assert forall|q: int| 0 <= q < db.tables[6].len() implies (#[trigger] db.tables[6][q])[0] == Val::Int(nk(sv)[q] as int) by {
        lemma_nation_row(sv, db, q);
    }
}

/// The joined row of lineitem row `l`.
pub open spec fn l_joined(sv: StoresView, db: Database, l: int) -> Row {
    joined6(db, l_part(sv, l), l_supp(sv, l), l, l_ps(sv, l), l_ord(sv, l), l_nat(sv, l))
}

/// The chain of a lineitem row: its rows exist and join.
pub proof fn lemma_chain(sv: StoresView, db: Database, l: int)
    requires bound_db(sv, db), 0 <= l < n_l(sv), chain_full(sv, l),
    ensures
        in6(sv, l_part(sv, l), l_supp(sv, l), l, l_ps(sv, l), l_ord(sv, l), l_nat(sv, l)),
        eqs_hold(sv, l_part(sv, l), l_supp(sv, l), l, l_ps(sv, l), l_ord(sv, l), l_nat(sv, l)),
{
    lemma_parts_shape(sv, db);
    lemma_key_row(pk(sv), lpk(sv)[l]);
    lemma_key_row(sk(sv), lsk(sv)[l]);
    lemma_key_row2(pspk(sv), pssk(sv), lpk(sv)[l], lsk(sv)[l]);
    lemma_key_row(ok(sv), lok(sv)[l]);
    lemma_key_row(nk(sv), sn(sv)[l_supp(sv, l)]);
}

/// `lift1` of lineitem row `l` is the contribution of its joined row, or 0 when its chain is broken.
pub proof fn lemma_lift_chain(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int, l: int)
    requires bound_db(sv, db), 0 <= l < n_l(sv),
    ensures lift1(db, f)(db.tables[0][l]) == if chain_full(sv, l) { f(l_joined(sv, db, l)) } else { 0 },
{
    lemma_parts_shape(sv, db);
    lemma_key_cols(sv, db);
    lemma_lineitem_row(sv, db, l);
    let (tp, ts, tl, tq, to, tn) = (db.tables[3], db.tables[5], db.tables[0], db.tables[4], db.tables[1], db.tables[6]);
    let y = tl[l];
    lemma_pick_key(tp, pk(sv), lpk(sv)[l]);
    lemma_pick_key(ts, sk(sv), lsk(sv)[l]);
    if has_key(pk(sv), lpk(sv)[l]) && has_key(sk(sv), lsk(sv)[l]) {
        let p = l_part(sv, l);
        let s = l_supp(sv, l);
        lemma_key_row(pk(sv), lpk(sv)[l]);
        lemma_key_row(sk(sv), lsk(sv)[l]);
        lemma_part_row(sv, db, p);
        lemma_supplier_row(sv, db, s);
        let x3 = tp[p] + ts[s] + y;
        assert(lift1(db, f)(y) == lift3(db, f)(x3));
        assert(x3[17] == Val::Int(lpk(sv)[l] as int) && x3[18] == Val::Int(lsk(sv)[l] as int));
        lemma_pick2_key(tq, pspk(sv), pssk(sv), lpk(sv)[l], lsk(sv)[l]);
        if has_key2(pspk(sv), pssk(sv), lpk(sv)[l], lsk(sv)[l]) {
            let q = l_ps(sv, l);
            lemma_key_row2(pspk(sv), pssk(sv), lpk(sv)[l], lsk(sv)[l]);
            lemma_partsupp_row(sv, db, q);
            let x4 = x3 + tq[q];
            assert(x4[16] == Val::Int(lok(sv)[l] as int));
            assert(lift3(db, f)(x3) == lift4(db, f)(x4));
            lemma_pick_key(to, ok(sv), lok(sv)[l]);
            if has_key(ok(sv), lok(sv)[l]) {
                let o = l_ord(sv, l);
                lemma_key_row(ok(sv), lok(sv)[l]);
                lemma_orders_row(sv, db, o);
                let x5 = x4 + to[o];
                assert(x5[12] == Val::Int(sn(sv)[s] as int));
                assert(lift4(db, f)(x4) == lift5(db, f)(x5));
                lemma_pick_key(tn, nk(sv), sn(sv)[s]);
                if has_key(nk(sv), sn(sv)[s]) {
                    let a = l_nat(sv, l);
                    assert(lift5(db, f)(x5) == f(x5 + tn[a]));
                    assert(x5 + tn[a] == l_joined(sv, db, l));
                }
            }
        }
    } else if has_key(pk(sv), lpk(sv)[l]) {
        let p = l_part(sv, l);
        lemma_key_row(pk(sv), lpk(sv)[l]);
        let hx = |x: Row| at_pick(ts, 0, y[2], |z: Row| lift3(db, f)(x + z + y));
        assert(y[2] == Val::Int(lsk(sv)[l] as int));
        assert(hx(tp[p]) == 0);
    }
}

/// The year of a stored day as the SQL year value.
pub proof fn lemma_day_year(d: i32)
    ensures year_val(date32_val(d)) == (Val::Num { coeff: day_year(d), scale: 0 }),
{
}

/// The SELECT row of a qualifying lineitem row is its group key and its amount.
proof fn lemma_line_select(sv: StoresView, db: Database, ps: Seq<Literal>, l: int)
    requires bound_db(sv, db), 0 <= l < n_l(sv), chain_full(sv, l),
    ensures
        qual_row(ps, l_joined(sv, db, l)) == line_qual(sv, ps, l),
        select_of(l_joined(sv, db, l)) == line_key(sv, l).push(Val::Num { coeff: line_val(sv, l), scale: 4 }),
{
    lemma_chain(sv, db, l);
    let (p, s, q, o, a) = (l_part(sv, l), l_supp(sv, l), l_ps(sv, l), l_ord(sv, l), l_nat(sv, l));
    lemma_qual_joined(sv, db, ps, p, s, l, q, o, a);
    lemma_day_year(od(sv)[o]);
    assert(shape_select(sv, l, q, o, a) =~= line_key(sv, l).push(Val::Num { coeff: line_val(sv, l), scale: 4 }));
}

/// A function of the SELECT rows that is, on three-column rows, the summed quantity `w` of the rows of group `k`.
pub open spec fn picks_group(h: spec_fn(Row) -> int, k: Row, w: int) -> bool {
    forall|x: Row| x.len() == 3 ==> #[trigger] h(x) == if seq![x[0], x[1]] == k { wval(w, coeff_of(x[2])) } else { 0 }
}

/// The contribution of a SELECT-row function, on the joined rows.
pub open spec fn on_joined(ps: Seq<Literal>, h: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |r: Row| if qual_row(ps, r) { h(select_of(r)) } else { 0 }
}

/// The collapsed contribution of lineitem row `l` is its `kterm`.
pub proof fn lemma_lift_line(sv: StoresView, db: Database, ps: Seq<Literal>, h: spec_fn(Row) -> int, k: Row, w: int, l: int)
    requires bound_db(sv, db), 0 <= l < n_l(sv), picks_group(h, k, w),
    ensures lift1(db, on_joined(ps, h))(db.tables[0][l]) == kterm(sv, ps, k, w, l),
{
    let f = on_joined(ps, h);
    lemma_lift_chain(sv, db, ps, f, l);
    if chain_full(sv, l) {
        lemma_line_select(sv, db, ps, l);
        if line_qual(sv, ps, l) {
            let x = select_of(l_joined(sv, db, l));
            let lk = line_key(sv, l);
            assert(x.len() == 3);
            assert(seq![x[0], x[1]] =~= lk);
            assert(coeff_of(x[2]) == line_val(sv, l));
        }
    }
}

// ------------------------------------------------------------------------------------------------ the accumulators

/// `Σ_{i < n} t(i)`.
pub open spec fn isum(t: spec_fn(int) -> int, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { isum(t, n - 1) + t(n - 1) }
}

/// A sum over a sequence whose element `i` contributes `t(i)`.
pub proof fn lemma_sum_index(s: Seq<Row>, h: spec_fn(Row) -> int, t: spec_fn(int) -> int)
    requires forall|i: int| 0 <= i < s.len() ==> h(#[trigger] s[i]) == t(i),
    ensures sum_of(s, h) == isum(t, s.len() as int),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies h(#[trigger] d[i]) == t(i) by {
            assert(d[i] == s[i]);
        }
        lemma_sum_index(d, h, t);
        assert(s.last() == s[s.len() - 1]);
    }
}

/// `ksum` as an index sum.
proof fn lemma_ksum_isum(sv: StoresView, ps: Seq<Literal>, k: Row, w: int, n: int)
    requires n >= 0,
    ensures ksum(sv, ps, k, w, n) == isum(|l: int| kterm(sv, ps, k, w, l), n),
    decreases n,
{
    if n > 0 {
        lemma_ksum_isum(sv, ps, k, w, n - 1);
    }
}

/// The kept rows are the joined rows satisfying the two-valued WHERE.
proof fn lemma_kept_keep(sv: StoresView, db: Database, ps: Seq<Literal>)
    ensures kept(db, ps) == keep(from6(db), |r: Row| qual_row(ps, r)),
{
    let rows = from6(db);
    let cols = q9_cols();
    let q = |r: Row| qual_row(ps, r);
    let xs = proj_all(rows, cols);
    lemma_proj_all_index(rows, cols);
    let truths = qual_truths(g1(ps), xs);
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] truths[i] == truth_of(q(rows[i])) by {
        assert(xs[i] == proj(rows[i], cols));
    }
    lemma_keep_true_keep(rows, truths, q);
}

/// A sum over the images of the kept rows is the sum over all rows of the image's value on kept rows, 0 elsewhere.
pub proof fn lemma_sum_keep_map(rows: Seq<Row>, q: spec_fn(Row) -> bool, m: spec_fn(Row) -> Row, h: spec_fn(Row) -> int)
    ensures sum_of(keep(rows, q).map_values(m), h) == sum_of(rows, |r: Row| if q(r) { h(m(r)) } else { 0int }),
{
    let ks = keep(rows, q);
    let f = |r: Row| if q(r) { h(m(r)) } else { 0int };
    let hm = |r: Row| h(m(r));
    lemma_sum_of_map(ks, m, h);
    assert forall|i: int| 0 <= i < rows.len() && !q(#[trigger] rows[i]) implies f(rows[i]) == 0 by {}
    lemma_sum_of_keep(rows, q, f);
    lemma_keep_members(rows, q);
    assert forall|i: int| 0 <= i < ks.len() implies f(#[trigger] ks[i]) == hm(ks[i]) by {
        assert(q(ks[i]));
    }
    lemma_sum_of_ext(ks, f, hm);
}

/// The sum of a SELECT-row function over the SELECT rows is the sum of its contribution over all joined rows.
pub proof fn lemma_sum_kept(sv: StoresView, db: Database, ps: Seq<Literal>, h: spec_fn(Row) -> int)
    ensures sum_of(sel_rows(db, ps), h) == sum_of(from6(db), on_joined(ps, h)),
{
    let q = |r: Row| qual_row(ps, r);
    let m = |r: Row| select_of(r);
    lemma_kept_keep(sv, db, ps);
    lemma_sum_keep_map(from6(db), q, m, h);
    assert(sel_rows(db, ps) == keep(from6(db), q).map_values(m));
    assert((|r: Row| if q(r) { h(m(r)) } else { 0int }) =~= on_joined(ps, h));
}

/// A group accumulator's quantity over the SELECT rows is its `ksum` over the lineitem rows.
pub proof fn lemma_group_sum(sv: StoresView, db: Database, ps: Seq<Literal>, h: spec_fn(Row) -> int, k: Row, w: int)
    requires bound_db(sv, db), picks_group(h, k, w),
    ensures sum_of(sel_rows(db, ps), h) == ksum(sv, ps, k, w, n_l(sv)),
{
    lemma_parts_shape(sv, db);
    lemma_sum_kept(sv, db, ps, h);
    let f = on_joined(ps, h);
    assert(vanishes(ps, f));
    lemma_reduce(sv, db, ps, f);
    let t = |l: int| kterm(sv, ps, k, w, l);
    assert forall|l: int| 0 <= l < db.tables[0].len() implies lift1(db, f)(#[trigger] db.tables[0][l]) == t(l) by {
        lemma_lift_line(sv, db, ps, h, k, w, l);
    }
    lemma_sum_index(db.tables[0], lift1(db, f), t);
    lemma_ksum_isum(sv, ps, k, w, n_l(sv));
}

/// The group accumulators of `g2` over the SELECT rows: count, sum and absolute sum of the lineitem rows whose group
/// key is `k`.
pub proof fn lemma_group_sums(sv: StoresView, db: Database, ps: Seq<Literal>, k: Row)
    requires bound_db(sv, db),
    ensures
        gcount(g2(), sel_rows(db, ps), k) == ksum(sv, ps, k, 0, n_l(sv)),
        gsum(g2(), sel_rows(db, ps), k, 0) == ksum(sv, ps, k, 1, n_l(sv)),
        gabs(g2(), sel_rows(db, ps), k, 0) == ksum(sv, ps, k, 2, n_l(sv)),
{
    let g = g2();
    let xs = sel_rows(db, ps);
    lemma_acc_sum_of(g, xs, k, 0);
    assert(picks_group(count_term(g, k), k, 0));
    lemma_group_sum(sv, db, ps, count_term(g, k), k, 0);
    assert(picks_group(sum_term(g, k, 0), k, 1));
    lemma_group_sum(sv, db, ps, sum_term(g, k, 0), k, 1);
    assert(picks_group(abs_term(g, k, 0), k, 2));
    lemma_group_sum(sv, db, ps, abs_term(g, k, 0), k, 2);
}

} // verus!
