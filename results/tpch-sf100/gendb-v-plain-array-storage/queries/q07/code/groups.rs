//! The groups of the normal form are sums over the lineitem rows (`lemma_group_sums`).
//!
//! A group accumulator of `g2` over the SELECT rows is a sum over the kept joined rows, hence over all joined rows
//! of a contribution that vanishes off the WHERE (`lemma_sum_kept`). The WHERE contains the five key equalities
//! and every key column it compares against is a primary key, so each joined row with a non-zero contribution is
//! determined by its lineitem row: the sum over `from6` collapses level by level (`common::sum_pick`) to a sum over
//! lineitem rows (`lemma_reduce`; the contribution of row `l` is `lift1`, the contribution at its unique supplier,
//! order, customer and nations). That contribution is the row's `kterm` (`lemma_lift_line`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::fns::extract::extract_field;
use crate::spec::datetime::{civil_from_date, civil_from_unix_days};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::source_check::date32_val;
use crate::query::param_domain;
use crate::link::query::*;
use crate::link::join::{sum_of, keep, count_term, sum_term, abs_term, lemma_acc_sum_of, lemma_sum_of_map,
    lemma_sum_of_keep, lemma_sum_of_ext, lemma_keep_true_keep, lemma_keep_members};
use crate::link::source::lemma_proj_all_index;
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::denotation::*;
use crate::agent::lines::*;
use crate::agent::dates::*;
use crate::agent::common::sum_pick::*;

verus! {

// ------------------------------------------------------------------------------------------------ table shapes

/// Widths of the input rows and of the product rows; the joined key columns are duplicate-free.
pub proof fn lemma_shapes(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        forall|p: int| 0 <= p < db.tables[5].len() ==> (#[trigger] db.tables[5][p]).len() == 7,
        forall|p: int| 0 <= p < db.tables[0].len() ==> (#[trigger] db.tables[0][p]).len() == 16,
        forall|p: int| 0 <= p < db.tables[1].len() ==> (#[trigger] db.tables[1][p]).len() == 9,
        forall|p: int| 0 <= p < db.tables[2].len() ==> (#[trigger] db.tables[2][p]).len() == 8,
        forall|p: int| 0 <= p < db.tables[6].len() ==> (#[trigger] db.tables[6][p]).len() == 4,
        forall|k: int| 0 <= k < from2(db).len() ==> (#[trigger] from2(db)[k]).len() == 23,
        forall|k: int| 0 <= k < from3(db).len() ==> (#[trigger] from3(db)[k]).len() == 32,
        forall|k: int| 0 <= k < from4(db).len() ==> (#[trigger] from4(db)[k]).len() == 40,
        forall|k: int| 0 <= k < from5(db).len() ==> (#[trigger] from5(db)[k]).len() == 44,
        col_unique(db.tables[5], 0), col_unique(db.tables[1], 0), col_unique(db.tables[2], 0), col_unique(db.tables[6], 0),
{
    lemma_parts_shape(sv, db);
    lemma_keys_unique(sv, db);
    assert forall|p: int| 0 <= p < db.tables[5].len() implies (#[trigger] db.tables[5][p]).len() == 7 by {
        lemma_supplier_row(sv, db, p);
    }
    assert forall|p: int| 0 <= p < db.tables[0].len() implies (#[trigger] db.tables[0][p]).len() == 16 by {
        lemma_lineitem_row(sv, db, p);
    }
    assert forall|p: int| 0 <= p < db.tables[1].len() implies (#[trigger] db.tables[1][p]).len() == 9 by {
        lemma_orders_row(sv, db, p);
    }
    assert forall|p: int| 0 <= p < db.tables[2].len() implies (#[trigger] db.tables[2][p]).len() == 8 by {
        lemma_customer_row(sv, db, p);
    }
    assert forall|p: int| 0 <= p < db.tables[6].len() implies (#[trigger] db.tables[6][p]).len() == 4 by {
        lemma_nation_row(sv, db, p);
    }
    lemma_product_widths(db.tables[5], db.tables[0], 7, 16);
    lemma_product_widths(from2(db), db.tables[1], 23, 9);
    lemma_product_widths(from3(db), db.tables[2], 32, 8);
    lemma_product_widths(from4(db), db.tables[6], 40, 4);
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
    assert forall|p: int, q: int| 0 <= p < db.tables[2].len() && 0 <= q < db.tables[2].len()
        && #[trigger] db.tables[2][p][0] == #[trigger] db.tables[2][q][0] implies p == q by {
        lemma_customer_row(sv, db, p);
        lemma_customer_row(sv, db, q);
        assert(ck(sv)[p] == ck(sv)[q]);
    }
    assert forall|p: int, q: int| 0 <= p < db.tables[6].len() && 0 <= q < db.tables[6].len()
        && #[trigger] db.tables[6][p][0] == #[trigger] db.tables[6][q][0] implies p == q by {
        lemma_nation_row(sv, db, p);
        lemma_nation_row(sv, db, q);
        assert(nk(sv)[p] == nk(sv)[q]);
    }
}

/// The key equalities of a qualifying 48-column joined row.
pub proof fn lemma_qual_keys(ps: Seq<Literal>, r: Row)
    requires r.len() == 48, qual_row(ps, r),
    ensures r[0] == r[9], r[23] == r[7], r[32] == r[24], r[3] == r[40], r[35] == r[44],
{
    lemma_joined_proj(r);
}

// ------------------------------------------------------------------------------------------------ the collapse

/// Sum over `nation n2` of the rows extending a 44-column prefix (joined on `c_nationkey`).
pub open spec fn lift5(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| at_pick(db.tables[6], 0, x[35], |y: Row| f(x + y))
}

/// Sum over `nation n1` of the rows extending a 40-column prefix (joined on `s_nationkey`).
pub open spec fn lift4(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| at_pick(db.tables[6], 0, x[3], |y: Row| lift5(db, f)(x + y))
}

/// Sum over `customer` of the rows extending a 32-column prefix (joined on `o_custkey`).
pub open spec fn lift3(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| at_pick(db.tables[2], 0, x[24], |y: Row| lift4(db, f)(x + y))
}

/// Sum over `orders` of the rows extending a 23-column prefix (joined on `l_orderkey`).
pub open spec fn lift2(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| at_pick(db.tables[1], 0, x[7], |y: Row| lift3(db, f)(x + y))
}

/// Sum over `supplier` of the rows of one lineitem row (joined on `l_suppkey`).
pub open spec fn lift1(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |y: Row| at_pick(db.tables[5], 0, y[2], |x: Row| lift2(db, f)(x + y))
}

/// A contribution that vanishes off the WHERE.
pub open spec fn vanishes(ps: Seq<Literal>, f: spec_fn(Row) -> int) -> bool {
    forall|r: Row| #[trigger] f(r) != 0 ==> qual_row(ps, r)
}

proof fn lemma_level6(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_db(sv, db), vanishes(ps, f),
    ensures forall|p: int, q: int| 0 <= p < from5(db).len() && 0 <= q < db.tables[6].len()
        && f(#[trigger] from5(db)[p] + #[trigger] db.tables[6][q]) != 0 ==> db.tables[6][q][0] == from5(db)[p][35],
{
    lemma_shapes(sv, db);
    assert forall|p: int, q: int| 0 <= p < from5(db).len() && 0 <= q < db.tables[6].len()
        && f(#[trigger] from5(db)[p] + #[trigger] db.tables[6][q]) != 0 implies db.tables[6][q][0] == from5(db)[p][35] by {
        let r = from5(db)[p] + db.tables[6][q];
        lemma_qual_keys(ps, r);
    }
}

proof fn lemma_level5(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_db(sv, db), vanishes(ps, f),
    ensures forall|p: int, q: int| 0 <= p < from4(db).len() && 0 <= q < db.tables[6].len()
        && lift5(db, f)(#[trigger] from4(db)[p] + #[trigger] db.tables[6][q]) != 0 ==> db.tables[6][q][0] == from4(db)[p][3],
{
    lemma_shapes(sv, db);
    let n = db.tables[6];
    assert forall|p: int, q: int| 0 <= p < from4(db).len() && 0 <= q < n.len()
        && lift5(db, f)(#[trigger] from4(db)[p] + #[trigger] n[q]) != 0 implies n[q][0] == from4(db)[p][3] by {
        let x = from4(db)[p] + n[q];
        lemma_at_pick_nonzero(n, 0, x[35], |y: Row| f(x + y));
        let b = pick(n, 0, x[35]);
        let r = x + n[b];
        lemma_qual_keys(ps, r);
    }
}

proof fn lemma_level4(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_db(sv, db), vanishes(ps, f),
    ensures forall|p: int, q: int| 0 <= p < from3(db).len() && 0 <= q < db.tables[2].len()
        && lift4(db, f)(#[trigger] from3(db)[p] + #[trigger] db.tables[2][q]) != 0 ==> db.tables[2][q][0] == from3(db)[p][24],
{
    lemma_shapes(sv, db);
    let n = db.tables[6];
    let c = db.tables[2];
    assert forall|p: int, q: int| 0 <= p < from3(db).len() && 0 <= q < c.len()
        && lift4(db, f)(#[trigger] from3(db)[p] + #[trigger] c[q]) != 0 implies c[q][0] == from3(db)[p][24] by {
        let x = from3(db)[p] + c[q];
        lemma_at_pick_nonzero(n, 0, x[3], |y: Row| lift5(db, f)(x + y));
        let a = pick(n, 0, x[3]);
        let x5 = x + n[a];
        lemma_at_pick_nonzero(n, 0, x5[35], |y: Row| f(x5 + y));
        let b = pick(n, 0, x5[35]);
        let r = x5 + n[b];
        lemma_qual_keys(ps, r);
    }
}

proof fn lemma_level3(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_db(sv, db), vanishes(ps, f),
    ensures forall|p: int, q: int| 0 <= p < from2(db).len() && 0 <= q < db.tables[1].len()
        && lift3(db, f)(#[trigger] from2(db)[p] + #[trigger] db.tables[1][q]) != 0 ==> db.tables[1][q][0] == from2(db)[p][7],
{
    lemma_shapes(sv, db);
    let n = db.tables[6];
    let c = db.tables[2];
    let o = db.tables[1];
    assert forall|p: int, q: int| 0 <= p < from2(db).len() && 0 <= q < o.len()
        && lift3(db, f)(#[trigger] from2(db)[p] + #[trigger] o[q]) != 0 implies o[q][0] == from2(db)[p][7] by {
        let x = from2(db)[p] + o[q];
        lemma_at_pick_nonzero(c, 0, x[24], |y: Row| lift4(db, f)(x + y));
        let cc = pick(c, 0, x[24]);
        let x4 = x + c[cc];
        lemma_at_pick_nonzero(n, 0, x4[3], |y: Row| lift5(db, f)(x4 + y));
        let a = pick(n, 0, x4[3]);
        let x5 = x4 + n[a];
        lemma_at_pick_nonzero(n, 0, x5[35], |y: Row| f(x5 + y));
        let b = pick(n, 0, x5[35]);
        let r = x5 + n[b];
        lemma_qual_keys(ps, r);
    }
}

proof fn lemma_level2(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_db(sv, db), vanishes(ps, f),
    ensures forall|p: int, q: int| 0 <= p < db.tables[5].len() && 0 <= q < db.tables[0].len()
        && lift2(db, f)(#[trigger] db.tables[5][p] + #[trigger] db.tables[0][q]) != 0 ==> db.tables[5][p][0] == db.tables[0][q][2],
{
    lemma_shapes(sv, db);
    let n = db.tables[6];
    let c = db.tables[2];
    let o = db.tables[1];
    let s = db.tables[5];
    let l = db.tables[0];
    assert forall|p: int, q: int| 0 <= p < s.len() && 0 <= q < l.len()
        && lift2(db, f)(#[trigger] s[p] + #[trigger] l[q]) != 0 implies s[p][0] == l[q][2] by {
        let x = s[p] + l[q];
        lemma_at_pick_nonzero(o, 0, x[7], |y: Row| lift3(db, f)(x + y));
        let oo = pick(o, 0, x[7]);
        let x3 = x + o[oo];
        lemma_at_pick_nonzero(c, 0, x3[24], |y: Row| lift4(db, f)(x3 + y));
        let cc = pick(c, 0, x3[24]);
        let x4 = x3 + c[cc];
        lemma_at_pick_nonzero(n, 0, x4[3], |y: Row| lift5(db, f)(x4 + y));
        let a = pick(n, 0, x4[3]);
        let x5 = x4 + n[a];
        lemma_at_pick_nonzero(n, 0, x5[35], |y: Row| f(x5 + y));
        let b = pick(n, 0, x5[35]);
        let r = x5 + n[b];
        lemma_qual_keys(ps, r);
    }
}

/// The sum of a contribution vanishing off the WHERE over all joined rows is the sum over the lineitem rows of
/// its value at each row's unique supplier, order, customer and nations.
pub proof fn lemma_reduce(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int)
    requires bound_db(sv, db), vanishes(ps, f),
    ensures sum_of(from6(db), f) == sum_of(db.tables[0], lift1(db, f)),
{
    lemma_shapes(sv, db);
    let n = db.tables[6];
    lemma_level6(sv, db, ps, f);
    lemma_sum_product_right(from5(db), n, f, 35, 0);
    assert((|x: Row| at_pick(n, 0, x[35], |y: Row| f(x + y))) =~= lift5(db, f));
    lemma_level5(sv, db, ps, f);
    lemma_sum_product_right(from4(db), n, lift5(db, f), 3, 0);
    assert((|x: Row| at_pick(n, 0, x[3], |y: Row| lift5(db, f)(x + y))) =~= lift4(db, f));
    lemma_level4(sv, db, ps, f);
    lemma_sum_product_right(from3(db), db.tables[2], lift4(db, f), 24, 0);
    assert((|x: Row| at_pick(db.tables[2], 0, x[24], |y: Row| lift4(db, f)(x + y))) =~= lift3(db, f));
    lemma_level3(sv, db, ps, f);
    lemma_sum_product_right(from2(db), db.tables[1], lift3(db, f), 7, 0);
    assert((|x: Row| at_pick(db.tables[1], 0, x[7], |y: Row| lift3(db, f)(x + y))) =~= lift2(db, f));
    lemma_level2(sv, db, ps, f);
    lemma_sum_product_left(db.tables[5], db.tables[0], lift2(db, f), 2, 0);
    assert((|y: Row| at_pick(db.tables[5], 0, y[2], |x: Row| lift2(db, f)(x + y))) =~= lift1(db, f));
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

/// Column 0 of each table is its key column.
proof fn lemma_key_cols(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        forall|q: int| 0 <= q < db.tables[5].len() ==> (#[trigger] db.tables[5][q])[0] == Val::Int(sk(sv)[q] as int),
        forall|q: int| 0 <= q < db.tables[1].len() ==> (#[trigger] db.tables[1][q])[0] == Val::Int(ok(sv)[q] as int),
        forall|q: int| 0 <= q < db.tables[2].len() ==> (#[trigger] db.tables[2][q])[0] == Val::Int(ck(sv)[q] as int),
        forall|q: int| 0 <= q < db.tables[6].len() ==> (#[trigger] db.tables[6][q])[0] == Val::Int(nk(sv)[q] as int),
        keys_unique(ok(sv)), keys_unique(ck(sv)), keys_unique(sk(sv)), keys_unique(nk(sv)),
{
    lemma_parts_shape(sv, db);
    lemma_keys_unique(sv, db);
    assert forall|q: int| 0 <= q < db.tables[5].len() implies (#[trigger] db.tables[5][q])[0] == Val::Int(sk(sv)[q] as int) by {
        lemma_supplier_row(sv, db, q);
    }
    assert forall|q: int| 0 <= q < db.tables[1].len() implies (#[trigger] db.tables[1][q])[0] == Val::Int(ok(sv)[q] as int) by {
        lemma_orders_row(sv, db, q);
    }
    assert forall|q: int| 0 <= q < db.tables[2].len() implies (#[trigger] db.tables[2][q])[0] == Val::Int(ck(sv)[q] as int) by {
        lemma_customer_row(sv, db, q);
    }
    assert forall|q: int| 0 <= q < db.tables[6].len() implies (#[trigger] db.tables[6][q])[0] == Val::Int(nk(sv)[q] as int) by {
        lemma_nation_row(sv, db, q);
    }
}

/// The supplier's and the customer's nations of lineitem row `l` resolve (with its keys).
pub open spec fn chain_full(sv: StoresView, l: int) -> bool {
    &&& line_keys(sv, l)
    &&& has_key(nk(sv), sn(sv)[l_supp(sv, l)])
    &&& has_key(nk(sv), cn(sv)[l_cust(sv, l)])
}

/// Nation row of the supplier of lineitem row `l`.
pub open spec fn l_snat(sv: StoresView, l: int) -> int { key_row(nk(sv), sn(sv)[l_supp(sv, l)]) }

/// Nation row of the customer of lineitem row `l`.
pub open spec fn l_cnat(sv: StoresView, l: int) -> int { key_row(nk(sv), cn(sv)[l_cust(sv, l)]) }

/// The joined row of lineitem row `l`.
pub open spec fn l_joined(sv: StoresView, db: Database, l: int) -> Row {
    joined6(db, l_supp(sv, l), l, l_ord(sv, l), l_cust(sv, l), l_snat(sv, l), l_cnat(sv, l))
}

/// The chain of a lineitem row: its rows exist and join.
proof fn lemma_chain(sv: StoresView, db: Database, l: int)
    requires bound_db(sv, db), 0 <= l < n_l(sv), chain_full(sv, l),
    ensures
        in6(sv, l_supp(sv, l), l, l_ord(sv, l), l_cust(sv, l), l_snat(sv, l), l_cnat(sv, l)),
        sk(sv)[l_supp(sv, l)] == lsk(sv)[l], ok(sv)[l_ord(sv, l)] == lok(sv)[l],
        ck(sv)[l_cust(sv, l)] == oc(sv)[l_ord(sv, l)], nk(sv)[l_snat(sv, l)] == sn(sv)[l_supp(sv, l)],
        nk(sv)[l_cnat(sv, l)] == cn(sv)[l_cust(sv, l)],
{
    lemma_parts_shape(sv, db);
    lemma_key_row(sk(sv), lsk(sv)[l]);
    lemma_key_row(ok(sv), lok(sv)[l]);
    lemma_key_row(ck(sv), oc(sv)[l_ord(sv, l)]);
    lemma_key_row(nk(sv), sn(sv)[l_supp(sv, l)]);
    lemma_key_row(nk(sv), cn(sv)[l_cust(sv, l)]);
}

/// `lift1` of lineitem row `l` is the contribution of its joined row, or 0 when its chain is broken.
pub proof fn lemma_lift_chain(sv: StoresView, db: Database, ps: Seq<Literal>, f: spec_fn(Row) -> int, l: int)
    requires bound_db(sv, db), 0 <= l < n_l(sv),
    ensures lift1(db, f)(db.tables[0][l]) == if chain_full(sv, l) { f(l_joined(sv, db, l)) } else { 0 },
{
    lemma_parts_shape(sv, db);
    lemma_key_cols(sv, db);
    lemma_lineitem_row(sv, db, l);
    let (ts, tl, to, tc, tn) = (db.tables[5], db.tables[0], db.tables[1], db.tables[2], db.tables[6]);
    let y = tl[l];
    lemma_pick_key(ts, sk(sv), lsk(sv)[l]);
    if has_key(sk(sv), lsk(sv)[l]) {
        let s = l_supp(sv, l);
        lemma_key_row(sk(sv), lsk(sv)[l]);
        lemma_supplier_row(sv, db, s);
        let x2 = ts[s] + y;
        assert(x2[7] == Val::Int(lok(sv)[l] as int));
        assert(lift1(db, f)(y) == lift2(db, f)(x2));
        lemma_pick_key(to, ok(sv), lok(sv)[l]);
        if has_key(ok(sv), lok(sv)[l]) {
            let o = l_ord(sv, l);
            lemma_key_row(ok(sv), lok(sv)[l]);
            lemma_orders_row(sv, db, o);
            let x3 = x2 + to[o];
            assert(x3[24] == Val::Int(oc(sv)[o] as int));
            assert(lift2(db, f)(x2) == lift3(db, f)(x3));
            lemma_pick_key(tc, ck(sv), oc(sv)[o]);
            if has_key(ck(sv), oc(sv)[o]) {
                let c = l_cust(sv, l);
                lemma_key_row(ck(sv), oc(sv)[o]);
                lemma_customer_row(sv, db, c);
                let x4 = x3 + tc[c];
                assert(x4[3] == Val::Int(sn(sv)[s] as int));
                assert(lift3(db, f)(x3) == lift4(db, f)(x4));
                lemma_pick_key(tn, nk(sv), sn(sv)[s]);
                if has_key(nk(sv), sn(sv)[s]) {
                    let a = l_snat(sv, l);
                    lemma_key_row(nk(sv), sn(sv)[s]);
                    lemma_nation_row(sv, db, a);
                    let x5 = x4 + tn[a];
                    assert(x5[35] == Val::Int(cn(sv)[c] as int));
                    assert(lift4(db, f)(x4) == lift5(db, f)(x5));
                    lemma_pick_key(tn, nk(sv), cn(sv)[c]);
                    if has_key(nk(sv), cn(sv)[c]) {
                        let b = l_cnat(sv, l);
                        assert(lift5(db, f)(x5) == f(x5 + tn[b]));
                        assert(x5 + tn[b] == l_joined(sv, db, l));
                    }
                }
            }
        }
    }
}

/// The nation-name condition is the tag match.
proof fn lemma_names_tags(sv: StoresView, ps: Seq<Literal>, a: int, b: int)
    ensures
        names_ok(Val::Text(nname(sv, a)), Val::Text(nname(sv, b)), p1_of(ps), p2_of(ps))
            == tags_match(name_tag(sv, ps, a), name_tag(sv, ps, b)),
        name_tag(sv, ps, a) % 2 == 1 <==> nname(sv, a) == p1_of(ps),
        name_tag(sv, ps, a) >= 2 <==> nname(sv, a) == p2_of(ps),
        name_tag(sv, ps, b) % 2 == 1 <==> nname(sv, b) == p1_of(ps),
        name_tag(sv, ps, b) >= 2 <==> nname(sv, b) == p2_of(ps),
{
}

/// The year of a stored ship day of the window.
pub proof fn lemma_ship_year(d: i32)
    requires ship_in(d as int),
    ensures year_val(date32_val(d)) == (Val::Num { coeff: ship_year(d as int), scale: 0 }),
{
    let x = d as int - 10957;
    assert(civil_from_date(x) == civil_from_unix_days(x + 10957));
    if (d as int) < 9496 {
        lemma_year_1995(d as int);
    } else {
        lemma_year_1996(d as int);
    }
}

/// The SELECT row of a qualifying lineitem row is its group key and its volume.
proof fn lemma_line_select(sv: StoresView, db: Database, ps: Seq<Literal>, l: int)
    requires bound_db(sv, db), 0 <= l < n_l(sv), chain_full(sv, l),
    ensures
        qual_row(ps, l_joined(sv, db, l)) == line_qual(sv, ps, l),
        line_qual(sv, ps, l) ==> select_of(l_joined(sv, db, l))
            == grp_key(ps, line_grp(sv, ps, l)).push(Val::Num { coeff: line_val(sv, l), scale: 4 }),
{
    lemma_chain(sv, db, l);
    let (s, o, c, a, b) = (l_supp(sv, l), l_ord(sv, l), l_cust(sv, l), l_snat(sv, l), l_cnat(sv, l));
    lemma_qual_joined(sv, db, ps, s, l, o, c, a, b);
    lemma_names_tags(sv, ps, a, b);
    assert(supp_tag(sv, ps, s) == name_tag(sv, ps, a));
    assert(cust_tag(sv, ps, c) == name_tag(sv, ps, b));
    if line_qual(sv, ps, l) {
        lemma_ship_year(lsd(sv)[l]);
        let g = line_grp(sv, ps, l);
        let x = select_of(l_joined(sv, db, l));
        let k = grp_key(ps, g).push(Val::Num { coeff: line_val(sv, l), scale: 4 });
        assert(x =~= k);
    }
}

/// A function of the SELECT rows that is, on four-column rows, the summed quantity `w` of the rows of group `k`.
pub open spec fn picks_group(h: spec_fn(Row) -> int, k: Row, w: int) -> bool {
    forall|x: Row| x.len() == 4 ==> #[trigger] h(x) == if seq![x[0], x[1], x[2]] == k { wval(w, coeff_of(x[3])) } else { 0 }
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
            let gk = grp_key(ps, line_grp(sv, ps, l));
            assert(x.len() == 4);
            assert(seq![x[0], x[1], x[2]] =~= gk);
            assert(coeff_of(x[3]) == line_val(sv, l));
        }
    } else {
        // a missing key or nation: the row cannot qualify (a missing nation has tag 0)
        if line_keys(sv, l) {
            if !has_key(nk(sv), sn(sv)[l_supp(sv, l)]) {
                assert(supp_tag(sv, ps, l_supp(sv, l)) == 0);
            } else {
                assert(cust_tag(sv, ps, l_cust(sv, l)) == 0);
            }
        }
        assert(!line_qual(sv, ps, l));
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
    requires bound_db(sv, db), param_domain(ps),
    ensures kept(db, ps) == keep(from6(db), |r: Row| qual_row(ps, r)),
{
    let rows = from6(db);
    let cols = q7_cols();
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
    requires bound_db(sv, db), param_domain(ps),
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
    requires bound_db(sv, db), param_domain(ps), picks_group(h, k, w),
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
    requires bound_db(sv, db), param_domain(ps),
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
