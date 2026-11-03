//! FROM: the left-deep product `p8` of the eight inputs (part, supplier, lineitem, orders, customer, nation,
//! nation, region; row widths 9, 7, 16, 9, 8, 4, 4, 3, so 60 values per joined row).
//!
//! Every joined row is `row8(t, l)` for a tuple `t` of the other inputs and a lineitem row `l`
//! (`lemma_p8_contains`); the rows are pairwise different because every input has a primary key
//! (`lemma_p8_nodup`). `lemma_row8` gives the 20 values the statement reads, and `keep8` is the WHERE condition
//! as a function of a joined row, which on `row8(t, l)` is `line::tup_ok` (`lemma_keep8`).
//!
//! Positions in a joined row: part 0..9, supplier 9..16, lineitem 16..32, orders 32..41, customer 41..49,
//! n1 49..53, n2 53..57, region 57..60.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::source_check::date32_val;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::ast::*;
use crate::agent::common::relations::*;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_customer::interface as ci;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_supplier::interface as si;
use crate::stores::flat_nation::interface as ni;
use crate::stores::flat_region::interface as ri;

verus! {

// ------------------------------------------------------------------------------------------------ the product

pub open spec fn p1(sv: StoresView) -> Seq<Row> { product_rows(part_rows(sv), supp_rows(sv)) }
pub open spec fn p2(sv: StoresView) -> Seq<Row> { product_rows(p1(sv), line_rows(sv)) }
pub open spec fn p3(sv: StoresView) -> Seq<Row> { product_rows(p2(sv), ord_rows(sv)) }
pub open spec fn p4(sv: StoresView) -> Seq<Row> { product_rows(p3(sv), cust_rows(sv)) }
pub open spec fn p5(sv: StoresView) -> Seq<Row> { product_rows(p4(sv), nat_rows(sv)) }
pub open spec fn p6(sv: StoresView) -> Seq<Row> { product_rows(p5(sv), nat_rows(sv)) }

/// The FROM relation.
pub open spec fn p8(sv: StoresView) -> Seq<Row> { product_rows(p6(sv), reg_rows(sv)) }

/// The joined row of tuple `t` and lineitem row `l`.
pub open spec fn row8(sv: StoresView, t: Tup, l: int) -> Row {
    part_rows(sv)[t.p] + supp_rows(sv)[t.s] + line_rows(sv)[l] + ord_rows(sv)[t.o] + cust_rows(sv)[t.c]
        + nat_rows(sv)[t.n1] + nat_rows(sv)[t.n2] + reg_rows(sv)[t.r]
}

/// FROM evaluates to `p8`.
pub proof fn lemma_eval_from(sv: StoresView, db: Database)
    requires tables_of(sv, db),
    ensures eval_query(db, Seq::empty(), q8_from()) == Ok::<Relation, SqlError>(p8(sv)),
{
    let e = Seq::<Val>::empty();
    let q1 = prod(Query::Table(3), Query::Table(5));
    let q2 = prod(q1, Query::Table(0));
    let q3 = prod(q2, Query::Table(1));
    let q4 = prod(q3, Query::Table(2));
    let q5 = prod(q4, Query::Table(6));
    let q6 = prod(q5, Query::Table(6));
    assert(eval_query(db, e, Query::Table(3)) == Ok::<Relation, SqlError>(part_rows(sv)));
    assert(eval_query(db, e, Query::Table(5)) == Ok::<Relation, SqlError>(supp_rows(sv)));
    assert(eval_query(db, e, Query::Table(0)) == Ok::<Relation, SqlError>(line_rows(sv)));
    assert(eval_query(db, e, Query::Table(1)) == Ok::<Relation, SqlError>(ord_rows(sv)));
    assert(eval_query(db, e, Query::Table(2)) == Ok::<Relation, SqlError>(cust_rows(sv)));
    assert(eval_query(db, e, Query::Table(6)) == Ok::<Relation, SqlError>(nat_rows(sv)));
    assert(eval_query(db, e, Query::Table(7)) == Ok::<Relation, SqlError>(reg_rows(sv)));
    assert(eval_query(db, e, q1) == Ok::<Relation, SqlError>(p1(sv)));
    assert(eval_query(db, e, q2) == Ok::<Relation, SqlError>(p2(sv)));
    assert(eval_query(db, e, q3) == Ok::<Relation, SqlError>(p3(sv)));
    assert(eval_query(db, e, q4) == Ok::<Relation, SqlError>(p4(sv)));
    assert(eval_query(db, e, q5) == Ok::<Relation, SqlError>(p5(sv)));
    assert(eval_query(db, e, q6) == Ok::<Relation, SqlError>(p6(sv)));
}

// ------------------------------------------------------------------------------------------------ membership

/// The joined rows are exactly the `row8` of tuples and lineitem rows in range.
pub proof fn lemma_p8_contains(sv: StoresView, x: Row)
    ensures
        p8(sv).contains(x) <==> exists|t: Tup, l: int| tup_in(sv, t) && 0 <= l < n_l(sv) && x == #[trigger] row8(sv, t, l),
{
    let (pr, sr, lr, or, cr, nr, rr) = (part_rows(sv), supp_rows(sv), line_rows(sv), ord_rows(sv), cust_rows(sv),
        nat_rows(sv), reg_rows(sv));
    if p8(sv).contains(x) {
        lemma_product_contains(p6(sv), rr, x);
        let (i6, r) = choose|i: int, j: int| 0 <= i < p6(sv).len() && 0 <= j < rr.len() && x == #[trigger] p6(sv)[i] + #[trigger] rr[j];
        let y6 = p6(sv)[i6];
        lemma_product_contains(p5(sv), nr, y6);
        let (i5, n2) = choose|i: int, j: int| 0 <= i < p5(sv).len() && 0 <= j < nr.len() && y6 == #[trigger] p5(sv)[i] + #[trigger] nr[j];
        let y5 = p5(sv)[i5];
        lemma_product_contains(p4(sv), nr, y5);
        let (i4, n1) = choose|i: int, j: int| 0 <= i < p4(sv).len() && 0 <= j < nr.len() && y5 == #[trigger] p4(sv)[i] + #[trigger] nr[j];
        let y4 = p4(sv)[i4];
        lemma_product_contains(p3(sv), cr, y4);
        let (i3, c) = choose|i: int, j: int| 0 <= i < p3(sv).len() && 0 <= j < cr.len() && y4 == #[trigger] p3(sv)[i] + #[trigger] cr[j];
        let y3 = p3(sv)[i3];
        lemma_product_contains(p2(sv), or, y3);
        let (i2, o) = choose|i: int, j: int| 0 <= i < p2(sv).len() && 0 <= j < or.len() && y3 == #[trigger] p2(sv)[i] + #[trigger] or[j];
        let y2 = p2(sv)[i2];
        lemma_product_contains(p1(sv), lr, y2);
        let (i1, l) = choose|i: int, j: int| 0 <= i < p1(sv).len() && 0 <= j < lr.len() && y2 == #[trigger] p1(sv)[i] + #[trigger] lr[j];
        let y1 = p1(sv)[i1];
        lemma_product_contains(pr, sr, y1);
        let (p, s) = choose|i: int, j: int| 0 <= i < pr.len() && 0 <= j < sr.len() && y1 == #[trigger] pr[i] + #[trigger] sr[j];
        let t = Tup { p, s, o, c, n1, n2, r };
        assert(tup_in(sv, t));
        assert(x == row8(sv, t, l));
    }
    if exists|t: Tup, l: int| tup_in(sv, t) && 0 <= l < n_l(sv) && x == #[trigger] row8(sv, t, l) {
        let (t, l) = choose|t: Tup, l: int| tup_in(sv, t) && 0 <= l < n_l(sv) && x == #[trigger] row8(sv, t, l);
        let y1 = pr[t.p] + sr[t.s];
        lemma_product_contains(pr, sr, y1);
        let y2 = y1 + lr[l];
        lemma_product_contains(p1(sv), lr, y2);
        let y3 = y2 + or[t.o];
        lemma_product_contains(p2(sv), or, y3);
        let y4 = y3 + cr[t.c];
        lemma_product_contains(p3(sv), cr, y4);
        let y5 = y4 + nr[t.n1];
        lemma_product_contains(p4(sv), nr, y5);
        let y6 = y5 + nr[t.n2];
        lemma_product_contains(p5(sv), nr, y6);
        lemma_product_contains(p6(sv), rr, x);
    }
}

// ------------------------------------------------------------------------------------------------ duplicate-free

/// Rows of a table whose column 0 holds distinct keys are pairwise different.
proof fn lemma_rows_nodup_by_key(rows: Seq<Row>, keys: Seq<i64>)
    requires
        rows.len() == keys.len(),
        keys_unique(keys),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() > 0 && rows[i][0] == Val::Int(keys[i] as int),
    ensures rows.no_duplicates(),
{
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && i != j implies rows[i] != rows[j] by {
        assert(rows[i][0] == Val::Int(keys[i] as int) && rows[j][0] == Val::Int(keys[j] as int));
    }
}

/// Rows of a product of relations with rows of widths `wa` and `wb` have width `wa + wb`.
proof fn lemma_product_width(a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat)
    requires
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == wa,
        forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]).len() == wb,
    ensures forall|i: int| 0 <= i < product_rows(a, b).len() ==> (#[trigger] product_rows(a, b)[i]).len() == wa + wb,
{
    lemma_product_rows_elems(a, b);
    let p = product_rows(a, b);
    assert forall|i: int| 0 <= i < p.len() implies (#[trigger] p[i]).len() == wa + wb by {
        assert(is_concat(p[i], a, b));
        let (x, y) = choose|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() && p[i] == #[trigger] a[x] + #[trigger] b[y];
    }
}

/// The widths of the table rows.
pub proof fn lemma_widths(sv: StoresView)
    ensures
        forall|i: int| 0 <= i < part_rows(sv).len() ==> (#[trigger] part_rows(sv)[i]).len() == 9,
        forall|i: int| 0 <= i < supp_rows(sv).len() ==> (#[trigger] supp_rows(sv)[i]).len() == 7,
        forall|i: int| 0 <= i < line_rows(sv).len() ==> (#[trigger] line_rows(sv)[i]).len() == 16,
        forall|i: int| 0 <= i < ord_rows(sv).len() ==> (#[trigger] ord_rows(sv)[i]).len() == 9,
        forall|i: int| 0 <= i < cust_rows(sv).len() ==> (#[trigger] cust_rows(sv)[i]).len() == 8,
        forall|i: int| 0 <= i < nat_rows(sv).len() ==> (#[trigger] nat_rows(sv)[i]).len() == 4,
        forall|i: int| 0 <= i < reg_rows(sv).len() ==> (#[trigger] reg_rows(sv)[i]).len() == 3,
{
}

/// The joined rows are pairwise different (every input has a primary key).
pub proof fn lemma_p8_nodup(sv: StoresView)
    requires keys_ok(sv),
    ensures p8(sv).no_duplicates(),
{
    let (pr, sr, lr, or, cr, nr, rr) = (part_rows(sv), supp_rows(sv), line_rows(sv), ord_rows(sv), cust_rows(sv),
        nat_rows(sv), reg_rows(sv));
    lemma_widths(sv);
    assert forall|i: int| 0 <= i < pr.len() implies (#[trigger] pr[i]).len() > 0 && pr[i][0] == Val::Int(p_key(sv)[i] as int) by {}
    lemma_rows_nodup_by_key(pr, p_key(sv));
    assert forall|i: int| 0 <= i < sr.len() implies (#[trigger] sr[i]).len() > 0 && sr[i][0] == Val::Int(s_key(sv)[i] as int) by {}
    lemma_rows_nodup_by_key(sr, s_key(sv));
    assert forall|i: int| 0 <= i < or.len() implies (#[trigger] or[i]).len() > 0 && or[i][0] == Val::Int(o_key(sv)[i] as int) by {}
    lemma_rows_nodup_by_key(or, o_key(sv));
    assert forall|i: int| 0 <= i < cr.len() implies (#[trigger] cr[i]).len() > 0 && cr[i][0] == Val::Int(c_key(sv)[i] as int) by {}
    lemma_rows_nodup_by_key(cr, c_key(sv));
    assert forall|i: int| 0 <= i < nr.len() implies (#[trigger] nr[i]).len() > 0 && nr[i][0] == Val::Int(n_key(sv)[i] as int) by {}
    lemma_rows_nodup_by_key(nr, n_key(sv));
    assert forall|i: int| 0 <= i < rr.len() implies (#[trigger] rr[i]).len() > 0 && rr[i][0] == Val::Int(r_key(sv)[i] as int) by {}
    lemma_rows_nodup_by_key(rr, r_key(sv));
    lemma_product_nodup(pr, sr, 9);
    lemma_product_width(pr, sr, 9, 7);
    lemma_product_nodup(p1(sv), lr, 16);
    lemma_product_width(p1(sv), lr, 16, 16);
    lemma_product_nodup(p2(sv), or, 32);
    lemma_product_width(p2(sv), or, 32, 9);
    lemma_product_nodup(p3(sv), cr, 41);
    lemma_product_width(p3(sv), cr, 41, 8);
    lemma_product_nodup(p4(sv), nr, 49);
    lemma_product_width(p4(sv), nr, 49, 4);
    lemma_product_nodup(p5(sv), nr, 53);
    lemma_product_width(p5(sv), nr, 53, 4);
    lemma_product_nodup(p6(sv), rr, 57);
}

// ------------------------------------------------------------------------------------------------ values

/// The values of a joined row at the positions the statement reads.
pub proof fn lemma_row8(sv: StoresView, t: Tup, l: int)
    requires tup_in(sv, t), 0 <= l < n_l(sv),
    ensures ({
        let x = row8(sv, t, l);
        &&& x.len() == 60
        &&& x[0] == Val::Int(p_key(sv)[t.p] as int)
        &&& x[4] == Val::Text(p_type(sv, t.p))
        &&& x[9] == Val::Int(s_key(sv)[t.s] as int)
        &&& x[12] == Val::Int(s_nat(sv)[t.s] as int)
        &&& x[16] == Val::Int(l_okey(sv)[l] as int)
        &&& x[17] == Val::Int(l_pkey(sv)[l] as int)
        &&& x[18] == Val::Int(l_skey(sv)[l] as int)
        &&& x[21] == (Val::Num { coeff: l_price(sv)[l] as int, scale: 2 })
        &&& x[22] == (Val::Num { coeff: l_disc(sv)[l] as int, scale: 2 })
        &&& x[32] == Val::Int(o_key(sv)[t.o] as int)
        &&& x[33] == Val::Int(o_cust(sv)[t.o] as int)
        &&& x[36] == date32_val(o_date(sv)[t.o])
        &&& x[41] == Val::Int(c_key(sv)[t.c] as int)
        &&& x[44] == Val::Int(c_nat(sv)[t.c] as int)
        &&& x[49] == Val::Int(n_key(sv)[t.n1] as int)
        &&& x[51] == Val::Int(n_reg(sv)[t.n1] as int)
        &&& x[53] == Val::Int(n_key(sv)[t.n2] as int)
        &&& x[54] == Val::Text(n_name(sv, t.n2))
        &&& x[57] == Val::Int(r_key(sv)[t.r] as int)
        &&& x[58] == Val::Text(r_name(sv, t.r))
    }),
{
    let a = part_rows(sv)[t.p];
    let b = supp_rows(sv)[t.s];
    let c = line_rows(sv)[l];
    let d = ord_rows(sv)[t.o];
    let e = cust_rows(sv)[t.c];
    let f = nat_rows(sv)[t.n1];
    let g = nat_rows(sv)[t.n2];
    let h = reg_rows(sv)[t.r];
    assert(a == pi::row_at(sv.flat_part, t.p));
    assert(b == si::row_at(sv.flat_supplier, t.s));
    assert(c == li::row_at(sv.flat_lineitem, l));
    assert(d == oi::row_at(sv.flat_orders, t.o));
    assert(e == ci::row_at(sv.flat_customer, t.c));
    assert(f == ni::row_at(sv.flat_nation, t.n1));
    assert(g == ni::row_at(sv.flat_nation, t.n2));
    assert(h == ri::row_at(sv.flat_region, t.r));
    let y1 = a + b;
    let y2 = y1 + c;
    let y3 = y2 + d;
    let y4 = y3 + e;
    let y5 = y4 + f;
    let y6 = y5 + g;
    let x = y6 + h;
    assert(y1.len() == 16 && y1[0] == a[0] && y1[4] == a[4] && y1[9] == b[0] && y1[12] == b[3]);
    assert(y2.len() == 32 && y2[0] == y1[0] && y2[4] == y1[4] && y2[9] == y1[9] && y2[12] == y1[12]
        && y2[16] == c[0] && y2[17] == c[1] && y2[18] == c[2] && y2[21] == c[5] && y2[22] == c[6]);
    assert(y3.len() == 41 && y3[0] == y2[0] && y3[4] == y2[4] && y3[9] == y2[9] && y3[12] == y2[12]
        && y3[16] == y2[16] && y3[17] == y2[17] && y3[18] == y2[18] && y3[21] == y2[21] && y3[22] == y2[22]
        && y3[32] == d[0] && y3[33] == d[1] && y3[36] == d[4]);
    assert(y4.len() == 49 && y4[0] == y3[0] && y4[4] == y3[4] && y4[9] == y3[9] && y4[12] == y3[12]
        && y4[16] == y3[16] && y4[17] == y3[17] && y4[18] == y3[18] && y4[21] == y3[21] && y4[22] == y3[22]
        && y4[32] == y3[32] && y4[33] == y3[33] && y4[36] == y3[36] && y4[41] == e[0] && y4[44] == e[3]);
    assert(y5.len() == 53 && y5[0] == y4[0] && y5[4] == y4[4] && y5[9] == y4[9] && y5[12] == y4[12]
        && y5[16] == y4[16] && y5[17] == y4[17] && y5[18] == y4[18] && y5[21] == y4[21] && y5[22] == y4[22]
        && y5[32] == y4[32] && y5[33] == y4[33] && y5[36] == y4[36] && y5[41] == y4[41] && y5[44] == y4[44]
        && y5[49] == f[0] && y5[51] == f[2]);
    assert(y6.len() == 57 && y6[0] == y5[0] && y6[4] == y5[4] && y6[9] == y5[9] && y6[12] == y5[12]
        && y6[16] == y5[16] && y6[17] == y5[17] && y6[18] == y5[18] && y6[21] == y5[21] && y6[22] == y5[22]
        && y6[32] == y5[32] && y6[33] == y5[33] && y6[36] == y5[36] && y6[41] == y5[41] && y6[44] == y5[44]
        && y6[49] == y5[49] && y6[51] == y5[51] && y6[53] == g[0] && y6[54] == g[1]);
    assert(x.len() == 60 && x[0] == y6[0] && x[4] == y6[4] && x[9] == y6[9] && x[12] == y6[12]
        && x[16] == y6[16] && x[17] == y6[17] && x[18] == y6[18] && x[21] == y6[21] && x[22] == y6[22]
        && x[32] == y6[32] && x[33] == y6[33] && x[36] == y6[36] && x[41] == y6[41] && x[44] == y6[44]
        && x[49] == y6[49] && x[51] == y6[51] && x[53] == y6[53] && x[54] == y6[54]
        && x[57] == h[0] && x[58] == h[1]);
    assert(x == row8(sv, t, l));
}

// ------------------------------------------------------------------------------------------------ the WHERE condition

/// A SQL date (days since 2000-01-01) inside the window 1995-01-01 ..= 1996-12-31.
pub open spec fn date_val_in(v: Val) -> bool {
    match v { Val::Date(d) => -1826 <= d <= -1096, _ => false }
}

/// The WHERE condition as a function of a joined row (two-valued: every operand is a non-NULL value).
pub open spec fn keep8(ps: Seq<Literal>) -> spec_fn(Row) -> bool {
    |x: Row| x[0] == x[17] && x[9] == x[18] && x[16] == x[32] && x[33] == x[41] && x[44] == x[49] && x[51] == x[57]
        && x[58] == Val::Text(reg_of(ps)) && x[12] == x[53] && date_val_in(x[36]) && x[4] == Val::Text(typ_of(ps))
}

/// On a joined row of the database, the condition is the tuple's `tup_ok`.
pub proof fn lemma_keep8(sv: StoresView, ps: Seq<Literal>, t: Tup, l: int)
    requires tup_in(sv, t), 0 <= l < n_l(sv),
    ensures (keep8(ps))(row8(sv, t, l)) == tup_ok(sv, ps, l, t),
{
    lemma_row8(sv, t, l);
}

} // verus!
