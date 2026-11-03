//! SQL meaning of TPC-H Q8, part 3: the statement's body in normal form.
//!
//! The group accumulators over the inner rows (`group::gcnt` .. `gsum0`) are sums over the joined rows `jrows(db)`
//! of per-row terms `jterm(ps, w)`: the weight `w(x)` of a qualifying row (`jqual`), 0 otherwise. The weights of
//! year `y` are `w_cnt(y)` (count), `w_vol(y)` (volume coefficient at scale 4), and `w_hcnt(b0, y)`, `w_hvol(b0, y)`
//! (the same for rows whose supplier nation is `$1`), and `w_mass(y)` (absolute volume). `lemma_body` states the
//! body's value in these terms.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::link::expr::*;
use crate::link::join::{keep, sum_of};
use crate::query::{query_spec_at, param_domain};
use super::sql::*;
use super::group::*;

verus! {

// ------------------------------------------------------------------------------------------------ per-row weights

/// The year of a joined row's order date.
pub open spec fn jyear(x: Row) -> int {
    year_of(dval(x[36]))
}

pub open spec fn w_cnt(y: int) -> spec_fn(Row) -> int {
    |x: Row| if jyear(x) == y { 1int } else { 0int }
}

pub open spec fn w_vol(y: int) -> spec_fn(Row) -> int {
    |x: Row| if jyear(x) == y { vol_of(x) } else { 0int }
}

pub open spec fn w_hcnt(b0: Seq<u8>, y: int) -> spec_fn(Row) -> int {
    |x: Row| if jyear(x) == y && x[54] == Val::Text(b0) { 1int } else { 0int }
}

pub open spec fn w_hvol(b0: Seq<u8>, y: int) -> spec_fn(Row) -> int {
    |x: Row| if jyear(x) == y && x[54] == Val::Text(b0) { vol_of(x) } else { 0int }
}

pub open spec fn w_mass(y: int) -> spec_fn(Row) -> int {
    |x: Row| if jyear(x) == y { abs(vol_of(x)) } else { 0int }
}

/// The contribution of a joined row: its weight if it qualifies.
pub open spec fn jterm(ps: Seq<Literal>, w: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| if jqual(ps, x) { w(x) } else { 0int }
}

/// The sums of year `y` over the joined rows.
pub open spec fn ycnt(db: Database, ps: Seq<Literal>, y: int) -> int {
    sum_of(jrows(db), jterm(ps, w_cnt(y)))
}

pub open spec fn yvol(db: Database, ps: Seq<Literal>, y: int) -> int {
    sum_of(jrows(db), jterm(ps, w_vol(y)))
}

pub open spec fn yhcnt(db: Database, ps: Seq<Literal>, y: int) -> int {
    sum_of(jrows(db), jterm(ps, w_hcnt(txt(ps[0]), y)))
}

pub open spec fn yhvol(db: Database, ps: Seq<Literal>, y: int) -> int {
    sum_of(jrows(db), jterm(ps, w_hvol(txt(ps[0]), y)))
}

pub open spec fn ymass(db: Database, ps: Seq<Literal>, y: int) -> int {
    sum_of(jrows(db), jterm(ps, w_mass(y)))
}

// ------------------------------------------------------------------------------------------------ accumulators as sums

/// The group key of a joined row's inner row is its year key.
proof fn lemma_inner_key(x: Row, y: int)
    ensures (gkey(inner_row(x)) == ykey(y)) == (jyear(x) == y),
{
    if gkey(inner_row(x)) == ykey(y) {
        assert(gkey(inner_row(x))[0] == ykey(y)[0]);
    }
    if jyear(x) == y {
        assert(gkey(inner_row(x)) =~= ykey(y));
    }
}

/// The accumulators of group `ykey(y)` over the inner rows of the qualifying rows of `rows` are sums over `rows`.
pub proof fn lemma_accs(ps: Seq<Literal>, rows: Seq<Row>, y: int)
    ensures ({
        let zs = keep(rows, |x: Row| jqual(ps, x)).map_values(|x: Row| inner_row(x));
        let b0 = txt(ps[0]);
        let k = ykey(y);
        &&& gcnt(zs, k) == sum_of(rows, jterm(ps, w_cnt(y)))
        &&& gsum1(zs, k) == sum_of(rows, jterm(ps, w_vol(y)))
        &&& hcnt(b0, zs, k) == sum_of(rows, jterm(ps, w_hcnt(b0, y)))
        &&& gsum0(b0, zs, k) == sum_of(rows, jterm(ps, w_hvol(b0, y)))
        &&& gmass(zs, k) == sum_of(rows, jterm(ps, w_mass(y)))
    }),
    decreases rows.len(),
{
    let q = |x: Row| jqual(ps, x);
    let zs = keep(rows, q).map_values(|x: Row| inner_row(x));
    if rows.len() > 0 {
        let ri = rows.drop_last();
        let x = rows.last();
        lemma_accs(ps, ri, y);
        let zi = keep(ri, q).map_values(|x: Row| inner_row(x));
        lemma_inner_key(x, y);
        if q(x) {
            assert(keep(rows, q) == keep(ri, q).push(x));
            assert(zs =~= zi.push(inner_row(x)));
            assert(zs.drop_last() =~= zi);
        } else {
            assert(keep(rows, q) == keep(ri, q));
            assert(zs =~= zi);
        }
    } else {
        assert(zs =~= Seq::<Row>::empty());
    }
}

// ------------------------------------------------------------------------------------------------ keys of the inner rows

pub open spec fn y95v() -> Val {
    Val::Num { coeff: 1995, scale: 0 }
}

pub open spec fn y96v() -> Val {
    Val::Num { coeff: 1996, scale: 0 }
}

/// The inner rows are year keyed, and every year is 1995 or 1996.
pub proof fn lemma_inner_rows(db: Database, ps: Seq<Literal>)
    requires db_ok(db),
    ensures
        keys_ykeys(inner_rows(db, ps)),
        forall|i: int| 0 <= i < inner_rows(db, ps).len() ==>
            (#[trigger] inner_rows(db, ps)[i])[0] == y95v()
            || inner_rows(db, ps)[i][0] == y96v(),
{
    lemma_kept_rows(db, ps);
    let k = kept(db, ps);
    let zs = inner_rows(db, ps);
    assert forall|i: int| 0 <= i < zs.len() implies irow_ok(#[trigger] zs[i])
        && (zs[i][0] == y95v() || zs[i][0] == y96v()) by {
        let x = k[i];
        assert(zs[i] == inner_row(x));
        assert(jrow_ok(x) && jqual(ps, x));
        lemma_jrow_inner_typed(x);
        lemma_years(dval(x[36]));
    }
}

/// The distinct group keys are year keys of 1995 or 1996, each with rows.
pub proof fn lemma_group_keys(db: Database, ps: Seq<Literal>)
    requires db_ok(db),
    ensures ({
        let ds = distinct_rows(gkeys(inner_rows(db, ps)));
        &&& ds.no_duplicates()
        &&& forall|k: Row| #[trigger] ds.contains(k) <==> gcnt(inner_rows(db, ps), k) > 0
        &&& forall|i: int| 0 <= i < ds.len() ==> #[trigger] ds[i] == ykey(1995) || ds[i] == ykey(1996)
    }),
{
    lemma_inner_rows(db, ps);
    let zs = inner_rows(db, ps);
    lemma_distinct_keys(zs);
    let ds = distinct_rows(gkeys(zs));
    assert forall|i: int| 0 <= i < ds.len() implies #[trigger] ds[i] == ykey(1995) || ds[i] == ykey(1996) by {
        let k = ds[i];
        assert(ds.contains(k));
        assert(gcnt(zs, k) > 0);
        lemma_gcnt_witness(zs, k);
        let j = choose|j: int| 0 <= j < zs.len() && gkey(zs[j]) == k;
        assert(zs[j][0] == y95v() || zs[j][0] == y96v());
        assert(k =~= ykey(1995) || k =~= ykey(1996));
    }
}

/// A group with rows has a row with its key.
pub proof fn lemma_gcnt_witness(zs: Seq<Row>, k: Row)
    requires gcnt(zs, k) > 0,
    ensures exists|j: int| 0 <= j < zs.len() && gkey(zs[j]) == k,
    decreases zs.len(),
{
    if gkey(zs.last()) == k {
        assert(gkey(zs[zs.len() - 1]) == k);
    } else {
        lemma_gcnt_witness(zs.drop_last(), k);
        let j = choose|j: int| 0 <= j < zs.drop_last().len() && gkey(zs.drop_last()[j]) == k;
        assert(zs[j] == zs.drop_last()[j]);
    }
}

// ------------------------------------------------------------------------------------------------ the body

/// The body's value: per distinct group key (first-occurrence order) the output row or its error, when every
/// group's sums lie inside PostgreSQL's numeric format.
pub proof fn lemma_body(db: Database, ps: Seq<Literal>)
    requires db_ok(db), param_domain(ps), sums_in_range(txt(ps[0]), inner_rows(db, ps)),
    ensures
        denote_body(db, query_spec_at(ps))
            == collect(distinct_rows(gkeys(inner_rows(db, ps))).map_values(|k: Row| out_res(txt(ps[0]), inner_rows(db, ps), k))),
{
    hide(eval_query);
    lemma_statement(ps);
    lemma_params(ps);
    lemma_inner(db, ps);
    lemma_inner_rows(db, ps);
    let zs = inner_rows(db, ps);
    lemma_groupby(db, ps, inner_q(ps), zs);
    lemma_body_groups(db, ps, inner_q(ps), zs);
}

} // verus!
