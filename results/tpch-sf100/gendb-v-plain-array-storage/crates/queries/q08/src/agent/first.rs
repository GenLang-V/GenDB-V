//! The first group in the GROUP BY's order (needed only when the two years' divisions fail differently).
//!
//! The groups come in the order of their first kept joined row. The product `from::p8` is left-major, so the
//! joined row of tuple `t` and lineitem row `l` sits at the mixed-radix index `idx8(t, l)` (`lemma_p8_index`),
//! whose order is the lexicographic order of `(part row, supplier row, lineitem row)` (`lemma_lex_idx`; the rest
//! of a qualifying tuple is determined by the lineitem row). The first kept row is therefore the joined row of the
//! qualifying lineitem row whose `(part, supplier, lineitem)` rows are least (`lex_least`), and the first group
//! is its year (`lemma_first_key`). `first_year` finds that row by one serial pass.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::relation::product_rows;
use crate::gendb_entry::stores::StoresView;
use crate::link::join::{keep, lemma_keep_none, lemma_product_index};
use crate::link::query::{gkeys, QuerySpec};
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::cols::*;
use crate::agent::lookup::*;
use crate::agent::partpass::*;
use crate::agent::acc::*;
use crate::agent::stages::{pidx, lemma_bit01};
use crate::agent::from::*;
use crate::agent::pred::*;
use crate::agent::bag::*;
use crate::agent::group::*;
use crate::agent::common::bits::{bit, word_bit};
use crate::agent::common::relations::*;
use crate::agent::common::text::text_eq_at;

verus! {

// ------------------------------------------------------------------------------------------------ product order

/// The index of the part, supplier and lineitem rows in `p2`.
pub open spec fn idx3(sv: StoresView, t: Tup, l: int) -> int { (t.p * n_s(sv) + t.s) * n_l(sv) + l }

/// The index of `row8(t, l)` in `p8`.
pub open spec fn idx8(sv: StoresView, t: Tup, l: int) -> int {
    ((((idx3(sv, t, l) * n_o(sv) + t.o) * n_c(sv) + t.c) * n_n(sv) + t.n1) * n_n(sv) + t.n2) * n_r(sv) + t.r
}

/// One level of a left-major product.
proof fn lemma_level(a: Seq<Row>, b: Seq<Row>, i: int, j: int)
    requires 0 <= i < a.len(), 0 <= j < b.len(),
    ensures
        0 <= i * b.len() + j < product_rows(a, b).len(),
        product_rows(a, b)[i * b.len() + j] == a[i] + b[j],
{
    lemma_product_index(a, b);
    let nb = b.len() as int;
    assert(0 <= i * nb + j < a.len() * nb) by (nonlinear_arith) requires 0 <= i < a.len(), 0 <= j < nb;
}

/// The joined row of `t` and `l` is at `idx8(t, l)`.
pub proof fn lemma_p8_index(sv: StoresView, t: Tup, l: int)
    requires tup_in(sv, t), 0 <= l < n_l(sv),
    ensures 0 <= idx8(sv, t, l) < p8(sv).len(), p8(sv)[idx8(sv, t, l)] == row8(sv, t, l),
{
    let (pr, sr, lr, or, cr, nr, rr) = (part_rows(sv), supp_rows(sv), line_rows(sv), ord_rows(sv), cust_rows(sv),
        nat_rows(sv), reg_rows(sv));
    let i1 = t.p * n_s(sv) + t.s;
    lemma_level(pr, sr, t.p, t.s);
    let i2 = i1 * n_l(sv) + l;
    lemma_level(p1(sv), lr, i1, l);
    let i3 = i2 * n_o(sv) + t.o;
    lemma_level(p2(sv), or, i2, t.o);
    let i4 = i3 * n_c(sv) + t.c;
    lemma_level(p3(sv), cr, i3, t.c);
    let i5 = i4 * n_n(sv) + t.n1;
    lemma_level(p4(sv), nr, i4, t.n1);
    let i6 = i5 * n_n(sv) + t.n2;
    lemma_level(p5(sv), nr, i5, t.n2);
    lemma_level(p6(sv), rr, i6, t.r);
}

/// Mixed radix: a smaller prefix gives a smaller index.
proof fn lemma_radix(x1: int, x2: int, j1: int, j2: int, b: int)
    requires 0 <= x1 < x2, 0 <= j1 < b, 0 <= j2 < b,
    ensures x1 * b + j1 < x2 * b + j2,
{
    assert(x1 * b + j1 < x2 * b + j2) by (nonlinear_arith) requires 0 <= x1 < x2, 0 <= j1 < b, 0 <= j2 < b;
}

/// `(p1, s1, l1)` precedes `(p2, s2, l2)` lexicographically.
pub open spec fn lex_lt(p1: int, s1: int, l1: int, p2: int, s2: int, l2: int) -> bool {
    p1 < p2 || (p1 == p2 && (s1 < s2 || (s1 == s2 && l1 < l2)))
}

/// Lexicographic order of `(part, supplier, lineitem)` is index order in `p8`.
pub proof fn lemma_lex_idx(sv: StoresView, t1: Tup, l1: int, t2: Tup, l2: int)
    requires tup_in(sv, t1), tup_in(sv, t2), 0 <= l1 < n_l(sv), 0 <= l2 < n_l(sv), lex_lt(t1.p, t1.s, l1, t2.p, t2.s, l2),
    ensures idx8(sv, t1, l1) < idx8(sv, t2, l2),
{
    let (i1a, i1b) = (t1.p * n_s(sv) + t1.s, t2.p * n_s(sv) + t2.s);
    assert(0 <= i1a && 0 <= i1b) by (nonlinear_arith)
        requires 0 <= t1.p, 0 <= t2.p, 0 <= t1.s, 0 <= t2.s, n_s(sv) >= 0,
            i1a == t1.p * n_s(sv) + t1.s, i1b == t2.p * n_s(sv) + t2.s;
    let (i2a, i2b) = (idx3(sv, t1, l1), idx3(sv, t2, l2));
    assert(i2a == i1a * n_l(sv) + l1 && i2b == i1b * n_l(sv) + l2);
    if t1.p < t2.p {
        lemma_radix(t1.p, t2.p, t1.s, t2.s, n_s(sv) as int);
        lemma_radix(i1a, i1b, l1, l2, n_l(sv) as int);
    } else if t1.s < t2.s {
        assert(t1.p == t2.p);
        assert(i1a < i1b);
        lemma_radix(i1a, i1b, l1, l2, n_l(sv) as int);
    } else {
        assert(t1.p == t2.p && t1.s == t2.s && l1 < l2);
        assert(i1a == i1b);
    }
    assert(i2a < i2b);
    assert(0 <= i2a) by (nonlinear_arith) requires 0 <= i1a, 0 <= l1, n_l(sv) >= 0, i2a == i1a * n_l(sv) + l1;
    lemma_radix(i2a, i2b, t1.o, t2.o, n_o(sv) as int);
    let (i3a, i3b) = (i2a * n_o(sv) + t1.o, i2b * n_o(sv) + t2.o);
    assert(0 <= i3a) by (nonlinear_arith) requires 0 <= i2a, 0 <= t1.o, n_o(sv) >= 0, i3a == i2a * n_o(sv) + t1.o;
    lemma_radix(i3a, i3b, t1.c, t2.c, n_c(sv) as int);
    let (i4a, i4b) = (i3a * n_c(sv) + t1.c, i3b * n_c(sv) + t2.c);
    assert(0 <= i4a) by (nonlinear_arith) requires 0 <= i3a, 0 <= t1.c, n_c(sv) >= 0, i4a == i3a * n_c(sv) + t1.c;
    lemma_radix(i4a, i4b, t1.n1, t2.n1, n_n(sv) as int);
    let (i5a, i5b) = (i4a * n_n(sv) + t1.n1, i4b * n_n(sv) + t2.n1);
    assert(0 <= i5a) by (nonlinear_arith) requires 0 <= i4a, 0 <= t1.n1, n_n(sv) >= 0, i5a == i4a * n_n(sv) + t1.n1;
    lemma_radix(i5a, i5b, t1.n2, t2.n2, n_n(sv) as int);
    let (i6a, i6b) = (i5a * n_n(sv) + t1.n2, i5b * n_n(sv) + t2.n2);
    assert(0 <= i6a) by (nonlinear_arith) requires 0 <= i5a, 0 <= t1.n2, n_n(sv) >= 0, i6a == i5a * n_n(sv) + t1.n2;
    lemma_radix(i6a, i6b, t1.r, t2.r, n_r(sv) as int);
}

// ------------------------------------------------------------------------------------------------ first kept row

/// The first kept row is the first row satisfying the condition.
proof fn lemma_keep_first(rows: Seq<Row>, f: spec_fn(Row) -> bool, m: int)
    requires 0 <= m < rows.len(), f(rows[m]), forall|i: int| 0 <= i < m ==> !f(#[trigger] rows[i]),
    ensures keep(rows, f).len() > 0, keep(rows, f)[0] == rows[m],
    decreases rows.len(),
{
    let ri = rows.drop_last();
    if m == rows.len() - 1 {
        assert forall|i: int| 0 <= i < ri.len() implies !f(#[trigger] ri[i]) by { assert(ri[i] == rows[i]); }
        lemma_keep_none(ri, f);
        assert(rows.last() == rows[m]);
    } else {
        assert forall|i: int| 0 <= i < m implies !f(#[trigger] ri[i]) by { assert(ri[i] == rows[i]); }
        lemma_keep_first(ri, f, m);
        assert(ri[m] == rows[m]);
    }
}

/// With every row qualifying, the first group key is the first row's key.
proof fn lemma_gkeys_first(g: QuerySpec, rows: Seq<Row>)
    requires rows.len() > 0, forall|r: Row| #[trigger] (g.qual)(r),
    ensures gkeys(g, rows).len() > 0, gkeys(g, rows)[0] == (g.key)(rows[0]),
    decreases rows.len(),
{
    let ri = rows.drop_last();
    if rows.len() == 1 {
        assert(gkeys(g, ri) =~= Seq::<Row>::empty());
        assert((g.qual)(rows.last()));
        assert(rows.last() == rows[0]);
    } else {
        lemma_gkeys_first(g, ri);
        assert(ri[0] == rows[0]);
    }
}

/// Lineitem row `l` qualifies and its `(part, supplier, lineitem)` rows precede those of every other qualifying row.
pub open spec fn lex_least(sv: StoresView, ps: Seq<Literal>, l: int) -> bool {
    &&& 0 <= l < n_l(sv)
    &&& line_q(sv, ps, l)
    &&& forall|l2: int| 0 <= l2 < n_l(sv) && l2 != l && #[trigger] line_q(sv, ps, l2) ==>
            lex_lt(line_tup(sv, ps, l).p, line_tup(sv, ps, l).s, l, line_tup(sv, ps, l2).p, line_tup(sv, ps, l2).s, l2)
}

/// The first group is the year of the lexicographically least qualifying row.
pub proof fn lemma_first_key(sv: StoresView, ps: Seq<Literal>, l: int)
    requires model_ok(sv), lex_least(sv, ps, l),
    ensures dkeys(zrows(sv, ps)).len() > 0, dkeys(zrows(sv, ps))[0] == ykey(line_year(sv, ps, l)),
{
    let t = line_tup(sv, ps, l);
    assert(tup_ok(sv, ps, l, t));
    let m = idx8(sv, t, l);
    lemma_p8_index(sv, t, l);
    lemma_keep8(sv, ps, t, l);
    lemma_p8_nodup(sv);
    let rows = p8(sv);
    let f = keep8(ps);
    assert forall|i: int| 0 <= i < m implies !f(#[trigger] rows[i]) by {
        if f(rows[i]) {
            assert(rows.contains(rows[i]));
            lemma_p8_contains(sv, rows[i]);
            let (t2, l2) = choose|t2: Tup, l2: int| tup_in(sv, t2) && 0 <= l2 < n_l(sv) && rows[i] == #[trigger] row8(sv, t2, l2);
            lemma_keep8(sv, ps, t2, l2);
            lemma_tup_is(sv, ps, l2, t2);
            lemma_p8_index(sv, t2, l2);
            assert(rows[idx8(sv, t2, l2)] == rows[i]);
            assert(idx8(sv, t2, l2) == i);
            if l2 == l {
                assert(t2 == t);
            } else {
                lemma_lex_idx(sv, t, l, t2, l2);
            }
        }
    }
    lemma_keep_first(rows, f, m);
    let zs = zrows(sv, ps);
    assert(zs[0] == inner_row(kept8(sv, ps)[0]));
    lemma_zrow(sv, ps, l);
    lemma_gkeys_first(gspec(), zs);
    assert(zkey(zs[0]) =~= ykey(line_year(sv, ps, l)));
}

// ------------------------------------------------------------------------------------------------ the search

/// The part row of key `k` with type `$3`, if any (by the type bits when positional, else by search).
fn part_row_of(c: &Cols, d: &Dir, pat: &[u8], plen: usize, k: i64, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Option<usize>)
    requires cols_ok(*c, sv), dir_ok(*d, sv, ps), pat@ == typ_of(ps), plen == pat@.len(),
    ensures
        match r {
            Some(p) => p < n_p(sv) && p_key(sv)[p as int] == k && p_type(sv, p as int) == typ_of(ps),
            None => forall|p: int| 0 <= p < n_p(sv) ==> !(p_key(sv)[p] == k && #[trigger] p_type(sv, p) == typ_of(ps)),
        },
{
    if d.pos {
        let u: u64 = if k >= 1 { (k - 1) as u64 } else { u64::MAX };
        if u < c.np as u64 {
            proof {
                assert((u >> 6) == u / 64 && (u & 63) == u % 64 && (u & 63) < 64) by (bit_vector);
            }
            let w = d.pbits[(u >> 6) as usize];
            proof { lemma_bit01(w, u & 63); }
            if (w >> (u & 63)) & 1 == 1 {
                proof {
                    assert(word_bit(d.pbits@, u as int));
                    assert(p_type(sv, u as int) == typ_of(ps));
                }
                return Some(u as usize);
            }
            proof {
                assert(!word_bit(d.pbits@, u as int));
                assert forall|p: int| 0 <= p < n_p(sv) implies !(p_key(sv)[p] == k && #[trigger] p_type(sv, p) == typ_of(ps)) by {
                    if p_key(sv)[p] == k && p_type(sv, p) == typ_of(ps) {
                        assert(p_key(sv)[p] as int == p + 1);
                        assert(word_bit(d.pbits@, p));
                    }
                }
            }
            return None;
        }
        proof {
            assert forall|p: int| 0 <= p < n_p(sv) implies !(p_key(sv)[p] == k && #[trigger] p_type(sv, p) == typ_of(ps)) by {
                if p_key(sv)[p] == k && p_type(sv, p) == typ_of(ps) {
                    assert(p_key(sv)[p] as int == p + 1);
                }
            }
        }
        return None;
    }
    let mut p: usize = 0;
    while p < c.np
        invariant
            cols_ok(*c, sv), pat@ == typ_of(ps), plen == pat@.len(), p <= c.np,
            forall|x: int| 0 <= x < p ==> !(p_key(sv)[x] == k && #[trigger] p_type(sv, x) == typ_of(ps)),
        decreases c.np - p,
    {
        if c.p_key[p] == k {
            let eq = text_eq_at(c.p_toffs, c.p_tbytes, c.p_tnb, p, pat, plen, Ghost(n_p(sv) as int));
            if eq {
                return Some(p);
            }
        }
        p = p + 1;
    }
    None
}

/// Lineitem row `l`'s part row, supplier row and order date when it qualifies.
fn row_cand(c: &Cols, d: &Dir, pat: &[u8], plen: usize, l: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Option<(usize, usize, i32)>)
    requires scan_ok(*c, *d, sv, ps), pat@ == typ_of(ps), plen == pat@.len(), l < c.nl,
    ensures
        r is Some <==> line_q(sv, ps, l as int),
        r matches Some((p, s, dt)) ==> line_tup(sv, ps, l as int).p == p && line_tup(sv, ps, l as int).s == s
            && dt == o_date(sv)[line_tup(sv, ps, l as int).o],
{
    let ghost lq = line_q(sv, ps, l as int);
    let p = match part_row_of(c, d, pat, plen, c.l_pk[l], Ghost(sv), Ghost(ps)) {
        Some(p) => p,
        None => {
            proof {
                if lq {
                    let t = line_tup(sv, ps, l as int);
                    assert(tup_ok(sv, ps, l as int, t));
                    assert(part_hit(sv, ps, t.p, l as int));
                }
            }
            return None;
        },
    };
    proof { assert(part_hit(sv, ps, p as int, l as int)); }
    let j = match order_row(c, c.l_ok[l], Ghost(sv)) {
        Some(j) => j,
        None => {
            proof {
                if lq {
                    let t = line_tup(sv, ps, l as int);
                    assert(tup_ok(sv, ps, l as int, t));
                }
            }
            return None;
        },
    };
    let dt = c.o_date[j];
    if !(9131 <= dt && dt <= 9861) {
        proof {
            if lq {
                let t = line_tup(sv, ps, l as int);
                assert(tup_ok(sv, ps, l as int, t));
                assert(o_key(sv)[t.o] == o_key(sv)[j as int]);
            }
        }
        return None;
    }
    let (q, _) = line_eval(c, d, l, j, Ghost(sv), Ghost(ps));
    if !q {
        return None;
    }
    match supp_row(c, c.l_sk[l], Ghost(sv)) {
        Some(s) => {
            proof {
                let t = line_tup(sv, ps, l as int);
                assert(tup_ok(sv, ps, l as int, t));
                assert(p_key(sv)[t.p] == p_key(sv)[p as int]);
                assert(s_key(sv)[t.s] == s_key(sv)[s as int]);
            }
            Some((p, s, dt))
        },
        None => {
            proof {
                let t = line_tup(sv, ps, l as int);
                assert(tup_ok(sv, ps, l as int, t));
            }
            None
        },
    }
}

/// The best row so far: `(part row, supplier row, lineitem row, order date)` of the least qualifying row of `0..l`.
pub open spec fn best_ok(sv: StoresView, ps: Seq<Literal>, best: Option<(usize, usize, usize, i32)>, l: int) -> bool {
    match best {
        None => forall|l2: int| 0 <= l2 < l ==> !#[trigger] line_q(sv, ps, l2),
        Some((bp, bs, bl, bd)) => {
            &&& (bl as int) < l && line_q(sv, ps, bl as int)
            &&& line_tup(sv, ps, bl as int).p == bp && line_tup(sv, ps, bl as int).s == bs
            &&& bd == o_date(sv)[line_tup(sv, ps, bl as int).o]
            &&& forall|l2: int| 0 <= l2 < l && l2 != bl && #[trigger] line_q(sv, ps, l2) ==>
                    lex_lt(bp as int, bs as int, bl as int, line_tup(sv, ps, l2).p, line_tup(sv, ps, l2).s, l2)
        },
    }
}

/// The least qualifying row of `0..l`, then the least of `0..n_l`, is `lex_least`.
proof fn lemma_best_final(sv: StoresView, ps: Seq<Literal>, bp: usize, bs: usize, bl: usize, bd: i32)
    requires best_ok(sv, ps, Some((bp, bs, bl, bd)), n_l(sv) as int),
    ensures lex_least(sv, ps, bl as int),
{
}

/// One step of the search: the least of the best so far and row `l`.
fn update_best(best: Option<(usize, usize, usize, i32)>, cand: Option<(usize, usize, i32)>, l: usize,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Option<(usize, usize, usize, i32)>)
    requires
        best_ok(sv, ps, best, l as int),
        cand is Some <==> line_q(sv, ps, l as int),
        cand matches Some((p, s, dt)) ==> line_tup(sv, ps, l as int).p == p && line_tup(sv, ps, l as int).s == s
            && dt == o_date(sv)[line_tup(sv, ps, l as int).o],
    ensures best_ok(sv, ps, r, l + 1),
{
    match cand {
        Some((p, s, dt)) => {
            match best {
                None => Some((p, s, l, dt)),
                Some((bp, bs, bl, bd)) => {
                    if p < bp || (p == bp && s < bs) {
                        proof {
                            assert forall|l2: int| 0 <= l2 < l + 1 && l2 != l && #[trigger] line_q(sv, ps, l2) implies
                                lex_lt(p as int, s as int, l as int, line_tup(sv, ps, l2).p, line_tup(sv, ps, l2).s, l2) by {
                                if l2 != bl {
                                    assert(lex_lt(bp as int, bs as int, bl as int, line_tup(sv, ps, l2).p, line_tup(sv, ps, l2).s, l2));
                                }
                            }
                        }
                        Some((p, s, l, dt))
                    } else {
                        best
                    }
                },
            }
        },
        None => {
            proof {
                if best is None {
                    assert forall|l2: int| 0 <= l2 < l + 1 implies !#[trigger] line_q(sv, ps, l2) by {}
                }
            }
            best
        },
    }
}

/// The year of the first group: the order year of the least qualifying lineitem row (`None` without one).
pub fn first_year(c: &Cols, d: &Dir, pat: &[u8], plen: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Option<i64>)
    requires scan_ok(*c, *d, sv, ps), model_ok(sv), pat@ == typ_of(ps), plen == pat@.len(),
    ensures
        match r {
            Some(y) => dkeys(zrows(sv, ps)).len() > 0 && dkeys(zrows(sv, ps))[0] == ykey(y as int),
            None => forall|l: int| 0 <= l < n_l(sv) ==> !#[trigger] line_q(sv, ps, l),
        },
{
    let mut best: Option<(usize, usize, usize, i32)> = None;
    let mut l: usize = 0;
    while l < c.nl
        invariant scan_ok(*c, *d, sv, ps), model_ok(sv), pat@ == typ_of(ps), plen == pat@.len(), l <= c.nl,
            best_ok(sv, ps, best, l as int),
        decreases c.nl - l,
    {
        let cand = row_cand(c, d, pat, plen, l, Ghost(sv), Ghost(ps));
        best = update_best(best, cand, l, Ghost(sv), Ghost(ps));
        l = l + 1;
    }
    match best {
        None => None,
        Some((bp, bs, bl, bd)) => {
            proof {
                lemma_best_final(sv, ps, bp, bs, bl, bd);
                lemma_first_key(sv, ps, bl as int);
                assert(line_year(sv, ps, bl as int) == year_of_day(bd));
            }
            if bd < 9496 { Some(1995) } else { Some(1996) }
        },
    }
}

} // verus!
