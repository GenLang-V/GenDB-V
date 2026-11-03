//! The kept joined rows as a bag: exactly one per qualifying lineitem row.
//!
//! `jrow(l)` is the joined row of qualifying lineitem row `l` and its tuple; `wrows(n)` lists them for the rows
//! `0..n` in order. Both the kept rows and `wrows(n_l)` are duplicate-free with the same elements, so they are the
//! same bag (`lemma_kept_bag`), whatever the order of the product. Any sum over the derived table therefore is a
//! sum over the qualifying lineitem rows of their derived rows `zrow(l)` (`lemma_zsum`), and the per-year group
//! sums are the scan's totals `line::tot` (`lemma_group_sums`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::source_check::date32_val;
use crate::link::join::{keep, sum_of, lemma_sum_of_map, lemma_sum_of_perm, lemma_sum_of_ext};
use crate::link::query::lemma_nodup_same_multiset;
use crate::link::expr::ival;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::from::*;
use crate::agent::pred::*;
use crate::agent::common::relations::*;

verus! {

// ------------------------------------------------------------------------------------------------ the bag

/// The joined row of lineitem row `l` and its ok tuple.
pub open spec fn jrow(sv: StoresView, ps: Seq<Literal>, l: int) -> Row {
    row8(sv, line_tup(sv, ps, l), l)
}

/// The joined rows of the qualifying lineitem rows `0..n`, in order.
pub open spec fn wrows(sv: StoresView, ps: Seq<Literal>, n: int) -> Seq<Row>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else if line_q(sv, ps, n - 1) {
        wrows(sv, ps, n - 1).push(jrow(sv, ps, n - 1))
    } else {
        wrows(sv, ps, n - 1)
    }
}

/// The elements of `wrows(n)`.
pub proof fn lemma_wrows_contains(sv: StoresView, ps: Seq<Literal>, n: int, x: Row)
    ensures wrows(sv, ps, n).contains(x) <==> exists|l: int| 0 <= l < n && line_q(sv, ps, l) && x == #[trigger] jrow(sv, ps, l),
    decreases n,
{
    if n > 0 {
        lemma_wrows_contains(sv, ps, n - 1, x);
        let w = wrows(sv, ps, n);
        let wi = wrows(sv, ps, n - 1);
        if line_q(sv, ps, n - 1) {
            if w.contains(x) {
                let i = choose|i: int| 0 <= i < w.len() && w[i] == x;
                if i < wi.len() {
                    assert(wi[i] == x);
                }
            }
            if exists|l: int| 0 <= l < n && line_q(sv, ps, l) && x == #[trigger] jrow(sv, ps, l) {
                let l = choose|l: int| 0 <= l < n && line_q(sv, ps, l) && x == #[trigger] jrow(sv, ps, l);
                if l == n - 1 {
                    assert(w[wi.len() as int] == x);
                } else {
                    let i = choose|i: int| 0 <= i < wi.len() && wi[i] == x;
                    assert(w[i] == x);
                }
            }
        }
    }
}

/// Equal joined rows have the same lineitem row.
pub proof fn lemma_row8_line(sv: StoresView, t1: Tup, l1: int, t2: Tup, l2: int)
    requires
        tup_in(sv, t1), 0 <= l1 < n_l(sv), tup_in(sv, t2), 0 <= l2 < n_l(sv),
        row8(sv, t1, l1) == row8(sv, t2, l2),
    ensures line_rows(sv)[l1] == line_rows(sv)[l2],
{
    lemma_widths(sv);
    let (pr, sr, lr, or, cr, nr, rr) = (part_rows(sv), supp_rows(sv), line_rows(sv), ord_rows(sv), cust_rows(sv),
        nat_rows(sv), reg_rows(sv));
    let a1 = pr[t1.p] + sr[t1.s] + lr[l1];
    let a2 = pr[t2.p] + sr[t2.s] + lr[l2];
    let b1 = a1 + or[t1.o] + cr[t1.c] + nr[t1.n1] + nr[t1.n2];
    let b2 = a2 + or[t2.o] + cr[t2.c] + nr[t2.n1] + nr[t2.n2];
    lemma_concat_parts(b1, rr[t1.r], b2, rr[t2.r], 57);
    lemma_concat_parts(a1 + or[t1.o] + cr[t1.c] + nr[t1.n1], nr[t1.n2], a2 + or[t2.o] + cr[t2.c] + nr[t2.n1], nr[t2.n2], 53);
    lemma_concat_parts(a1 + or[t1.o] + cr[t1.c], nr[t1.n1], a2 + or[t2.o] + cr[t2.c], nr[t2.n1], 49);
    lemma_concat_parts(a1 + or[t1.o], cr[t1.c], a2 + or[t2.o], cr[t2.c], 41);
    lemma_concat_parts(a1, or[t1.o], a2, or[t2.o], 32);
    lemma_concat_parts(pr[t1.p] + sr[t1.s], lr[l1], pr[t2.p] + sr[t2.s], lr[l2], 16);
}

/// The joined rows of different qualifying lineitem rows differ.
pub proof fn lemma_wrows_nodup(sv: StoresView, ps: Seq<Literal>, n: int)
    requires keys_ok(sv), n <= n_l(sv),
    ensures wrows(sv, ps, n).no_duplicates(),
    decreases n,
{
    if n > 0 {
        lemma_wrows_nodup(sv, ps, n - 1);
        let wi = wrows(sv, ps, n - 1);
        if line_q(sv, ps, n - 1) {
            let x = jrow(sv, ps, n - 1);
            let w = wi.push(x);
            assert(tup_ok(sv, ps, n - 1, line_tup(sv, ps, n - 1)));
            assert forall|i: int, j: int| 0 <= i < w.len() && 0 <= j < w.len() && i != j implies w[i] != w[j] by {
                if i < wi.len() && j < wi.len() {
                    assert(w[i] == wi[i] && w[j] == wi[j]);
                } else {
                    let m = if i < wi.len() { i } else { j };
                    assert(w[m] == wi[m]);
                    lemma_wrows_contains(sv, ps, n - 1, wi[m]);
                    assert(wi.contains(wi[m]));
                    let l = choose|l: int| 0 <= l < n - 1 && line_q(sv, ps, l) && wi[m] == #[trigger] jrow(sv, ps, l);
                    assert(tup_ok(sv, ps, l, line_tup(sv, ps, l)));
                    if wi[m] == x {
                        lemma_row8_line(sv, line_tup(sv, ps, l), l, line_tup(sv, ps, n - 1), n - 1);
                        assert(line_rows(sv)[l] == line_rows(sv)[n - 1]);
                    }
                }
            }
        }
    }
}

/// The kept rows are, as a bag, the joined rows of the qualifying lineitem rows.
pub proof fn lemma_kept_bag(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv),
    ensures kept8(sv, ps).to_multiset() == wrows(sv, ps, n_l(sv) as int).to_multiset(),
{
    let kept = kept8(sv, ps);
    let w = wrows(sv, ps, n_l(sv) as int);
    lemma_p8_nodup(sv);
    lemma_keep_nodup(p8(sv), keep8(ps));
    lemma_wrows_nodup(sv, ps, n_l(sv) as int);
    assert forall|x: Row| kept.contains(x) <==> w.contains(x) by {
        lemma_wrows_contains(sv, ps, n_l(sv) as int, x);
        if kept.contains(x) {
            lemma_kept_row(sv, ps, x);
            let (t, l) = choose|t: Tup, l: int| 0 <= l < n_l(sv) && tup_ok(sv, ps, l, t) && x == #[trigger] row8(sv, t, l);
            lemma_tup_is(sv, ps, l, t);
            assert(x == jrow(sv, ps, l));
        }
        if w.contains(x) {
            let l = choose|l: int| 0 <= l < n_l(sv) && line_q(sv, ps, l) && x == #[trigger] jrow(sv, ps, l);
            let t = line_tup(sv, ps, l);
            assert(tup_ok(sv, ps, l, t));
            lemma_keep8(sv, ps, t, l);
            lemma_p8_contains(sv, x);
            lemma_keep_contains(p8(sv), keep8(ps), x);
        }
    }
    lemma_nodup_same_multiset(kept, w);
}

// ------------------------------------------------------------------------------------------------ sums

/// The derived table's row of a qualifying lineitem row: `o_year, volume, nation`.
pub open spec fn zrow(sv: StoresView, ps: Seq<Literal>, l: int) -> Row {
    seq![Val::Num { coeff: line_year(sv, ps, l), scale: 0 }, Val::Num { coeff: line_vol(sv, l), scale: 4 },
        Val::Text(n_name(sv, line_tup(sv, ps, l).n2))]
}

pub proof fn lemma_zrow(sv: StoresView, ps: Seq<Literal>, l: int)
    requires model_ok(sv), 0 <= l < n_l(sv), line_q(sv, ps, l),
    ensures inner_row(jrow(sv, ps, l)) == zrow(sv, ps, l),
{
    let t = line_tup(sv, ps, l);
    assert(tup_ok(sv, ps, l, t));
    lemma_row8(sv, t, l);
    lemma_window_year(o_date(sv)[t.o]);
    let x = jrow(sv, ps, l);
    assert(ival(x[21]) == l_price(sv)[l] as int && ival(x[22]) == l_disc(sv)[l] as int);
    assert(inner_row(x) =~= zrow(sv, ps, l));
}

/// Sum of `h` over the derived rows of the qualifying lineitem rows `0..n`.
pub open spec fn lsum(sv: StoresView, ps: Seq<Literal>, h: spec_fn(Row) -> int, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { lsum(sv, ps, h, n - 1) + if line_q(sv, ps, n - 1) { h(zrow(sv, ps, n - 1)) } else { 0 } }
}

proof fn lemma_wsum(sv: StoresView, ps: Seq<Literal>, h: spec_fn(Row) -> int, n: int)
    requires model_ok(sv), n <= n_l(sv),
    ensures sum_of(wrows(sv, ps, n), |x: Row| h(inner_row(x))) == lsum(sv, ps, h, n),
    decreases n,
{
    if n > 0 {
        lemma_wsum(sv, ps, h, n - 1);
        if line_q(sv, ps, n - 1) {
            lemma_zrow(sv, ps, n - 1);
            let wi = wrows(sv, ps, n - 1);
            assert(wi.push(jrow(sv, ps, n - 1)).drop_last() =~= wi);
        }
    }
}

/// Any sum over the derived table is the sum over the qualifying lineitem rows.
pub proof fn lemma_zsum(sv: StoresView, ps: Seq<Literal>, h: spec_fn(Row) -> int)
    requires model_ok(sv),
    ensures sum_of(zrows(sv, ps), h) == lsum(sv, ps, h, n_l(sv) as int),
{
    let kept = kept8(sv, ps);
    let m = |x: Row| inner_row(x);
    let hi = |x: Row| h(inner_row(x));
    assert(zrows(sv, ps) =~= kept.map_values(m));
    lemma_sum_of_map(kept, m, h);
    lemma_sum_of_ext(kept, |r: Row| h(m(r)), hi);
    lemma_kept_bag(sv, ps);
    lemma_sum_of_perm(kept, wrows(sv, ps, n_l(sv) as int), hi);
    lemma_wsum(sv, ps, h, n_l(sv) as int);
}

// ------------------------------------------------------------------------------------------------ group sums

/// The group key of a derived row.
pub open spec fn zkey(z: Row) -> Row { seq![z[0]] }

/// The key of year `y`.
pub open spec fn ykey(y: int) -> Row { seq![Val::Num { coeff: y, scale: 0 }] }

/// The derived row counts for `$1`.
pub open spec fn zthen(ps: Seq<Literal>, z: Row) -> bool { z[2] == Val::Text(nat_of(ps)) }

/// Per-row terms of the six group sums of key `k`.
pub open spec fn t_cnt(k: Row) -> spec_fn(Row) -> int { |z: Row| if zkey(z) == k { 1int } else { 0int } }
pub open spec fn t_all(k: Row) -> spec_fn(Row) -> int { |z: Row| if zkey(z) == k { ival(z[1]) } else { 0int } }
pub open spec fn t_aall(k: Row) -> spec_fn(Row) -> int { |z: Row| if zkey(z) == k { abs(ival(z[1])) } else { 0int } }
pub open spec fn t_nthen(ps: Seq<Literal>, k: Row) -> spec_fn(Row) -> int {
    |z: Row| if zkey(z) == k && zthen(ps, z) { 1int } else { 0int }
}
pub open spec fn t_then(ps: Seq<Literal>, k: Row) -> spec_fn(Row) -> int {
    |z: Row| if zkey(z) == k && zthen(ps, z) { ival(z[1]) } else { 0int }
}
pub open spec fn t_athen(ps: Seq<Literal>, k: Row) -> spec_fn(Row) -> int {
    |z: Row| if zkey(z) == k && zthen(ps, z) { abs(ival(z[1])) } else { 0int }
}

/// The six group sums of key `k` over rows `zs`, as a `Tot`.
pub open spec fn zsums(ps: Seq<Literal>, zs: Seq<Row>, k: Row) -> Tot {
    Tot {
        cnt: sum_of(zs, t_cnt(k)),
        s_all: sum_of(zs, t_all(k)),
        a_all: sum_of(zs, t_aall(k)),
        n_then: sum_of(zs, t_nthen(ps, k)),
        s_then: sum_of(zs, t_then(ps, k)),
        a_then: sum_of(zs, t_athen(ps, k)),
    }
}

/// The per-lineitem sums of the six terms are the scan's totals of the year.
proof fn lemma_lsum_tot(sv: StoresView, ps: Seq<Literal>, y: int, n: int)
    requires 0 <= n,
    ensures
        lsum(sv, ps, t_cnt(ykey(y)), n) == tot(sv, ps, y, 0, n).cnt,
        lsum(sv, ps, t_all(ykey(y)), n) == tot(sv, ps, y, 0, n).s_all,
        lsum(sv, ps, t_aall(ykey(y)), n) == tot(sv, ps, y, 0, n).a_all,
        lsum(sv, ps, t_nthen(ps, ykey(y)), n) == tot(sv, ps, y, 0, n).n_then,
        lsum(sv, ps, t_then(ps, ykey(y)), n) == tot(sv, ps, y, 0, n).s_then,
        lsum(sv, ps, t_athen(ps, ykey(y)), n) == tot(sv, ps, y, 0, n).a_then,
    decreases n,
{
    if n > 0 {
        lemma_tot_step(sv, ps, y, 0, n - 1);
        lemma_lsum_tot(sv, ps, y, n - 1);
        let l = n - 1;
        let z = zrow(sv, ps, l);
        assert(zkey(z) =~= seq![Val::Num { coeff: line_year(sv, ps, l), scale: 0 }]);
        assert((zkey(z) == ykey(y)) == (line_year(sv, ps, l) == y)) by {
            if zkey(z) == ykey(y) {
                assert(zkey(z)[0] == ykey(y)[0]);
            }
        }
        assert(zthen(ps, z) == line_then(sv, ps, l));
    }
}

/// The group sums of year `y` over the derived table are the scan's totals over all lineitem rows.
pub proof fn lemma_group_sums(sv: StoresView, ps: Seq<Literal>, y: int)
    requires model_ok(sv),
    ensures zsums(ps, zrows(sv, ps), ykey(y)) == tot(sv, ps, y, 0, n_l(sv) as int),
{
    let k = ykey(y);
    lemma_zsum(sv, ps, t_cnt(k));
    lemma_zsum(sv, ps, t_all(k));
    lemma_zsum(sv, ps, t_aall(k));
    lemma_zsum(sv, ps, t_nthen(ps, k));
    lemma_zsum(sv, ps, t_then(ps, k));
    lemma_zsum(sv, ps, t_athen(ps, k));
    lemma_lsum_tot(sv, ps, y, n_l(sv) as int);
}

/// Every derived row has the shape `[year, volume, name]` with a year 1995 or 1996.
pub open spec fn zrow_shape(z: Row) -> bool {
    &&& z.len() == 3
    &&& z[0] is Num && z[0]->Num_scale == 0 && (z[0]->Num_coeff == 1995 || z[0]->Num_coeff == 1996)
    &&& z[1] is Num && z[1]->Num_scale == 4
    &&& z[2] is Text
}

/// One derived row has the shape.
proof fn lemma_zrow_shape_at(sv: StoresView, ps: Seq<Literal>, x: Row)
    requires model_ok(sv), kept8(sv, ps).contains(x),
    ensures zrow_shape(inner_row(x)),
{
    lemma_kept_row(sv, ps, x);
    let (t, l) = choose|t: Tup, l: int| 0 <= l < n_l(sv) && tup_ok(sv, ps, l, t) && x == #[trigger] row8(sv, t, l);
    lemma_row8(sv, t, l);
    lemma_window_year(o_date(sv)[t.o]);
    assert(x[36] == date32_val(o_date(sv)[t.o]));
    let z = inner_row(x);
    assert(z[0] == Val::Num { coeff: year_of_day(o_date(sv)[t.o]), scale: 0 });
    assert(z[2] == Val::Text(n_name(sv, t.n2)));
}

pub proof fn lemma_zrows_shape(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv),
    ensures forall|i: int| 0 <= i < zrows(sv, ps).len() ==> zrow_shape(#[trigger] zrows(sv, ps)[i]),
{
    let kept = kept8(sv, ps);
    assert forall|i: int| 0 <= i < zrows(sv, ps).len() implies zrow_shape(#[trigger] zrows(sv, ps)[i]) by {
        assert(kept.contains(kept[i]));
        lemma_zrow_shape_at(sv, ps, kept[i]);
        assert(zrows(sv, ps)[i] == inner_row(kept[i]));
    }
}

} // verus!
