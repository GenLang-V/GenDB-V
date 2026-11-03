//! The sum-algebra layer: over the product of the stored relations, any accumulator of group `k` whose term
//! depends only on the lineitem part (`w(line_of(y))` on qualifying rows of group `k`) is the sum over lineitem
//! rows of `line_mult * w` (`lemma_group_sum`). The product sum is unfolded one input at a time
//! (`link::join::lemma_sum_of_product`), the inner sums over region, nation and supplier rows are evaluated in
//! closed form (`lemma_e4` .. `lemma_e2`), and the three outer sums are reversed so that lineitem rows come first
//! (`lemma_sum3_reverse`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::*;
use crate::link::query::*;
use crate::link::join::*;
use crate::agent::q5spec::*;
use crate::agent::common::sums::*;

verus! {

// ------------------------------------------------------------------------------------------- the nested sums

/// The term of one joined stored row.
pub open spec fn t_of(prm: Prm, k: Row, w: spec_fn(Row) -> int, y: Row) -> int {
    if hit(q5_g(prm), y, k) { w(line_of(y)) } else { 0 }
}

/// Region rows appended to a joined prefix of five relations.
pub open spec fn t4(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int, y: Row) -> int {
    sum_of(rs.r, |r: Row| t_of(prm, k, w, y + r))
}

/// Nation then region rows appended to a prefix of four relations.
pub open spec fn t3(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int, y: Row) -> int {
    sum_of(rs.n, |n: Row| t4(rs, prm, k, w, y + n))
}

/// Supplier, nation, region rows appended to a prefix of three relations.
pub open spec fn t2(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int, y: Row) -> int {
    sum_of(rs.s, |s: Row| t3(rs, prm, k, w, y + s))
}

/// Lineitem and later rows appended to a (customer, orders) prefix.
pub open spec fn t1(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int, y: Row) -> int {
    sum_of(rs.l, |l: Row| t2(rs, prm, k, w, y + l))
}

/// Orders and later rows appended to a customer row.
pub open spec fn t0(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int, c: Row) -> int {
    sum_of(rs.o, |o: Row| t1(rs, prm, k, w, c + o))
}

/// The product sum is the nested sum over the six relations.
pub proof fn lemma_unfold_products(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int)
    ensures
        sum_of(xs_of(rs), |y: Row| t_of(prm, k, w, y)) == sum_of(rs.c, |c: Row| t0(rs, prm, k, w, c)),
{
    let p1 = product_rows(rs.c, rs.o);
    let p2 = product_rows(p1, rs.l);
    let p3 = product_rows(p2, rs.s);
    let p4 = product_rows(p3, rs.n);
    let f5 = |y: Row| t_of(prm, k, w, y);
    let f4 = |y: Row| t4(rs, prm, k, w, y);
    let f3 = |y: Row| t3(rs, prm, k, w, y);
    let f2 = |y: Row| t2(rs, prm, k, w, y);
    let f1 = |y: Row| t1(rs, prm, k, w, y);
    let f0 = |c: Row| t0(rs, prm, k, w, c);
    lemma_sum_of_product(p4, rs.r, f5);
    assert forall|i: int| 0 <= i < p4.len() implies
        (|x: Row| sum_of(rs.r, |y: Row| f5(x + y)))(#[trigger] p4[i]) == f4(p4[i]) by {
        let x = p4[i];
        lemma_sum_of_ext(rs.r, |y: Row| f5(x + y), |r: Row| t_of(prm, k, w, x + r));
    }
    lemma_sum_of_ext(p4, |x: Row| sum_of(rs.r, |y: Row| f5(x + y)), f4);
    lemma_sum_of_product(p3, rs.n, f4);
    assert forall|i: int| 0 <= i < p3.len() implies
        (|x: Row| sum_of(rs.n, |y: Row| f4(x + y)))(#[trigger] p3[i]) == f3(p3[i]) by {
        let x = p3[i];
        lemma_sum_of_ext(rs.n, |y: Row| f4(x + y), |n: Row| t4(rs, prm, k, w, x + n));
    }
    lemma_sum_of_ext(p3, |x: Row| sum_of(rs.n, |y: Row| f4(x + y)), f3);
    lemma_sum_of_product(p2, rs.s, f3);
    assert forall|i: int| 0 <= i < p2.len() implies
        (|x: Row| sum_of(rs.s, |y: Row| f3(x + y)))(#[trigger] p2[i]) == f2(p2[i]) by {
        let x = p2[i];
        lemma_sum_of_ext(rs.s, |y: Row| f3(x + y), |s: Row| t3(rs, prm, k, w, x + s));
    }
    lemma_sum_of_ext(p2, |x: Row| sum_of(rs.s, |y: Row| f3(x + y)), f2);
    lemma_sum_of_product(p1, rs.l, f2);
    assert forall|i: int| 0 <= i < p1.len() implies
        (|x: Row| sum_of(rs.l, |y: Row| f2(x + y)))(#[trigger] p1[i]) == f1(p1[i]) by {
        let x = p1[i];
        lemma_sum_of_ext(rs.l, |y: Row| f2(x + y), |l: Row| t2(rs, prm, k, w, x + l));
    }
    lemma_sum_of_ext(p1, |x: Row| sum_of(rs.l, |y: Row| f2(x + y)), f1);
    lemma_sum_of_product(rs.c, rs.o, f1);
    assert forall|i: int| 0 <= i < rs.c.len() implies
        (|x: Row| sum_of(rs.o, |y: Row| f1(x + y)))(#[trigger] rs.c[i]) == f0(rs.c[i]) by {
        let x = rs.c[i];
        lemma_sum_of_ext(rs.o, |y: Row| f1(x + y), |o: Row| t1(rs, prm, k, w, x + o));
    }
    lemma_sum_of_ext(rs.c, |x: Row| sum_of(rs.o, |y: Row| f1(x + y)), f0);
}

// ------------------------------------------------------------------------------------------- closed forms

/// The joined conditions of a customer, order, lineitem, supplier and nation row in group `k`.
pub open spec fn pre4(prm: Prm, k: Row, c: Row, o: Row, l: Row, s: Row, n: Row) -> bool {
    &&& c[0] == o[1] && l[0] == o[0] && date_ok(o, prm)
    &&& l[2] == s[0] && c[3] == s[3]
    &&& s[3] == n[0] && seq![n[1]] == k
}

/// The region conditions on nation row `n`.
pub open spec fn r_hit(n: Row, name: Seq<u8>, r: Row) -> bool {
    n[2] == r[0] && r[1] == Val::Text(name)
}

/// One joined row: its term is `w(l)` exactly when every condition holds.
proof fn lemma_term(prm: Prm, k: Row, w: spec_fn(Row) -> int, c: Row, o: Row, l: Row, s: Row, n: Row, r: Row)
    requires c.len() == 8, o.len() == 7, l.len() == 15, s.len() == 7, n.len() == 4, r.len() == 3,
    ensures
        t_of(prm, k, w, ((((c + o) + l) + s) + n) + r)
            == if pre4(prm, k, c, o, l, s, n) && r_hit(n, prm.name, r) { w(l) * 1 } else { 0int },
{
    let y = ((((c + o) + l) + s) + n) + r;
    assert(y.len() == 44);
    assert(y[0] == c[0] && y[3] == c[3]);
    assert(y[8] == o[0] && y[9] == o[1] && y[12] == o[4]);
    assert(y[15] == l[0] && y[17] == l[2]);
    assert(y[30] == s[0] && y[33] == s[3]);
    assert(y[37] == n[0] && y[38] == n[1] && y[39] == n[2]);
    assert(y[41] == r[0] && y[42] == r[1]);
    assert(line_of(y) =~= l);
    assert(q5_key(y) =~= seq![n[1]]);
}

/// Sum over region rows.
pub proof fn lemma_e4(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int, c: Row, o: Row, l: Row, s: Row, n: Row)
    requires rels_widths(rs), c.len() == 8, o.len() == 7, l.len() == 15, s.len() == 7, n.len() == 4,
    ensures
        t4(rs, prm, k, w, (((c + o) + l) + s) + n)
            == if pre4(prm, k, c, o, l, s, n) { w(l) * r_cnt(rs.r, n, prm.name) } else { 0int },
{
    let y4 = (((c + o) + l) + s) + n;
    let p = pre4(prm, k, c, o, l, s, n);
    let q = |r: Row| r_hit(n, prm.name, r);
    let one = |r: Row| 1int;
    assert forall|i: int| 0 <= i < rs.r.len() implies
        (|r: Row| t_of(prm, k, w, y4 + r))(#[trigger] rs.r[i])
            == (|r: Row| if p && q(r) { w(l) * one(r) } else { 0int })(rs.r[i]) by {
        lemma_term(prm, k, w, c, o, l, s, n, rs.r[i]);
    }
    lemma_sum_of_ext(rs.r, |r: Row| t_of(prm, k, w, y4 + r), |r: Row| if p && q(r) { w(l) * one(r) } else { 0int });
    lemma_sum_guard(rs.r, p, w(l), q, one);
    lemma_sum_of_ext(rs.r, |r: Row| if q(r) { one(r) } else { 0int }, |r: Row| r_term(n, prm.name, r));
}

/// The joined conditions of a customer, order, lineitem and supplier row.
pub open spec fn pre3(prm: Prm, c: Row, o: Row, l: Row, s: Row) -> bool {
    &&& c[0] == o[1] && l[0] == o[0] && date_ok(o, prm)
    &&& l[2] == s[0] && c[3] == s[3]
}

/// Sum over nation rows.
pub proof fn lemma_e3(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int, c: Row, o: Row, l: Row, s: Row)
    requires rels_widths(rs), c.len() == 8, o.len() == 7, l.len() == 15, s.len() == 7,
    ensures
        t3(rs, prm, k, w, ((c + o) + l) + s)
            == if pre3(prm, c, o, l, s) { w(l) * n_cnt(rs, s, k, prm.name) } else { 0int },
{
    let y3 = ((c + o) + l) + s;
    let p = pre3(prm, c, o, l, s);
    let q = |n: Row| s[3] == n[0] && seq![n[1]] == k;
    let f = |n: Row| r_cnt(rs.r, n, prm.name);
    assert forall|i: int| 0 <= i < rs.n.len() implies
        (|n: Row| t4(rs, prm, k, w, y3 + n))(#[trigger] rs.n[i])
            == (|n: Row| if p && q(n) { w(l) * f(n) } else { 0int })(rs.n[i]) by {
        lemma_e4(rs, prm, k, w, c, o, l, s, rs.n[i]);
    }
    lemma_sum_of_ext(rs.n, |n: Row| t4(rs, prm, k, w, y3 + n), |n: Row| if p && q(n) { w(l) * f(n) } else { 0int });
    assert(t3(rs, prm, k, w, y3) == sum_of(rs.n, |n: Row| if p && q(n) { w(l) * f(n) } else { 0int }));
    lemma_sum_guard(rs.n, p, w(l), q, f);
    lemma_sum_of_ext(rs.n, |n: Row| if q(n) { f(n) } else { 0int }, |n: Row| n_term(rs, s, k, prm.name, n));
    assert(sum_of(rs.n, |n: Row| if q(n) { f(n) } else { 0int }) == n_cnt(rs, s, k, prm.name));
}

/// The joined conditions of a customer, order and lineitem row.
pub open spec fn pre2(prm: Prm, c: Row, o: Row, l: Row) -> bool {
    c[0] == o[1] && l[0] == o[0] && date_ok(o, prm)
}

/// Sum over supplier rows.
pub proof fn lemma_e2(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int, c: Row, o: Row, l: Row)
    requires rels_widths(rs), c.len() == 8, o.len() == 7, l.len() == 15,
    ensures
        t2(rs, prm, k, w, (c + o) + l)
            == if pre2(prm, c, o, l) { w(l) * s_cnt(rs, c, l, k, prm.name) } else { 0int },
{
    let y2 = (c + o) + l;
    let p = pre2(prm, c, o, l);
    let q = |s: Row| l[2] == s[0] && c[3] == s[3];
    let f = |s: Row| n_cnt(rs, s, k, prm.name);
    assert forall|i: int| 0 <= i < rs.s.len() implies
        (|s: Row| t3(rs, prm, k, w, y2 + s))(#[trigger] rs.s[i])
            == (|s: Row| if p && q(s) { w(l) * f(s) } else { 0int })(rs.s[i]) by {
        lemma_e3(rs, prm, k, w, c, o, l, rs.s[i]);
    }
    lemma_sum_of_ext(rs.s, |s: Row| t3(rs, prm, k, w, y2 + s), |s: Row| if p && q(s) { w(l) * f(s) } else { 0int });
    lemma_sum_guard(rs.s, p, w(l), q, f);
    lemma_sum_of_ext(rs.s, |s: Row| if q(s) { f(s) } else { 0int }, |s: Row| s_term(rs, c, l, k, prm.name, s));
}

/// The term of a (customer, order, lineitem) triple after the inner sums.
pub open spec fn g_of(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int, c: Row, o: Row, l: Row) -> int {
    if pre2(prm, c, o, l) { w(l) * s_cnt(rs, c, l, k, prm.name) } else { 0int }
}

/// The three outer sums over customer, orders and lineitem rows.
pub proof fn lemma_e0(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int)
    requires rels_widths(rs),
    ensures
        sum_of(rs.c, |c: Row| t0(rs, prm, k, w, c))
            == sum_of(rs.c, |c: Row| sum_of(rs.o, |o: Row| sum_of(rs.l, |l: Row| g_of(rs, prm, k, w, c, o, l)))),
{
    assert forall|i: int| 0 <= i < rs.c.len() implies
        (|c: Row| t0(rs, prm, k, w, c))(#[trigger] rs.c[i])
            == (|c: Row| sum_of(rs.o, |o: Row| sum_of(rs.l, |l: Row| g_of(rs, prm, k, w, c, o, l))))(rs.c[i]) by {
        let c = rs.c[i];
        assert forall|j: int| 0 <= j < rs.o.len() implies
            (|o: Row| t1(rs, prm, k, w, c + o))(#[trigger] rs.o[j])
                == (|o: Row| sum_of(rs.l, |l: Row| g_of(rs, prm, k, w, c, o, l)))(rs.o[j]) by {
            let o = rs.o[j];
            assert forall|m: int| 0 <= m < rs.l.len() implies
                (|l: Row| t2(rs, prm, k, w, (c + o) + l))(#[trigger] rs.l[m])
                    == (|l: Row| g_of(rs, prm, k, w, c, o, l))(rs.l[m]) by {
                lemma_e2(rs, prm, k, w, c, o, rs.l[m]);
            }
            lemma_sum_of_ext(rs.l, |l: Row| t2(rs, prm, k, w, (c + o) + l), |l: Row| g_of(rs, prm, k, w, c, o, l));
        }
        lemma_sum_of_ext(rs.o, |o: Row| t1(rs, prm, k, w, c + o),
            |o: Row| sum_of(rs.l, |l: Row| g_of(rs, prm, k, w, c, o, l)));
    }
    lemma_sum_of_ext(rs.c, |c: Row| t0(rs, prm, k, w, c),
        |c: Row| sum_of(rs.o, |o: Row| sum_of(rs.l, |l: Row| g_of(rs, prm, k, w, c, o, l))));
}

// ------------------------------------------------------------------------------------------- reversal

/// Reversing three nested sums: customer-major to lineitem-major.
pub proof fn lemma_sum3_reverse(a: Seq<Row>, b: Seq<Row>, c: Seq<Row>, h: spec_fn(Row, Row, Row) -> int)
    ensures
        sum_of(a, |x: Row| sum_of(b, |y: Row| sum_of(c, |z: Row| h(x, y, z))))
            == sum_of(c, |z: Row| sum_of(b, |y: Row| sum_of(a, |x: Row| h(x, y, z)))),
{
    // a, b swap
    let h1 = |x: Row, y: Row| sum_of(c, |z: Row| h(x, y, z));
    lemma_sum_of_swap(a, b, h1);
    assert forall|i: int| 0 <= i < a.len() implies
        (|x: Row| sum_of(b, |y: Row| sum_of(c, |z: Row| h(x, y, z))))(#[trigger] a[i])
            == (|x: Row| sum_of(b, |y: Row| h1(x, y)))(a[i]) by {
        let x = a[i];
        lemma_sum_of_ext(b, |y: Row| sum_of(c, |z: Row| h(x, y, z)), |y: Row| h1(x, y));
    }
    lemma_sum_of_ext(a, |x: Row| sum_of(b, |y: Row| sum_of(c, |z: Row| h(x, y, z))), |x: Row| sum_of(b, |y: Row| h1(x, y)));
    // now sum_of(b, |y| sum_of(a, |x| h1(x, y))); swap a, c inside for each y
    assert forall|j: int| 0 <= j < b.len() implies
        (|y: Row| sum_of(a, |x: Row| h1(x, y)))(#[trigger] b[j])
            == (|y: Row| sum_of(c, |z: Row| sum_of(a, |x: Row| h(x, y, z))))(b[j]) by {
        let y = b[j];
        let h2 = |x: Row, z: Row| h(x, y, z);
        lemma_sum_of_swap(a, c, h2);
        assert forall|i: int| 0 <= i < a.len() implies
            (|x: Row| h1(x, y))(#[trigger] a[i]) == (|x: Row| sum_of(c, |z: Row| h2(x, z)))(a[i]) by {
            let x = a[i];
            lemma_sum_of_ext(c, |z: Row| h(x, y, z), |z: Row| h2(x, z));
        }
        lemma_sum_of_ext(a, |x: Row| h1(x, y), |x: Row| sum_of(c, |z: Row| h2(x, z)));
        assert forall|m: int| 0 <= m < c.len() implies
            (|z: Row| sum_of(a, |x: Row| h2(x, z)))(#[trigger] c[m]) == (|z: Row| sum_of(a, |x: Row| h(x, y, z)))(c[m]) by {
            let z = c[m];
            lemma_sum_of_ext(a, |x: Row| h2(x, z), |x: Row| h(x, y, z));
        }
        lemma_sum_of_ext(c, |z: Row| sum_of(a, |x: Row| h2(x, z)), |z: Row| sum_of(a, |x: Row| h(x, y, z)));
    }
    lemma_sum_of_ext(b, |y: Row| sum_of(a, |x: Row| h1(x, y)), |y: Row| sum_of(c, |z: Row| sum_of(a, |x: Row| h(x, y, z))));
    // b, c swap
    let h3 = |y: Row, z: Row| sum_of(a, |x: Row| h(x, y, z));
    lemma_sum_of_swap(b, c, h3);
    assert forall|j: int| 0 <= j < b.len() implies
        (|y: Row| sum_of(c, |z: Row| sum_of(a, |x: Row| h(x, y, z))))(#[trigger] b[j])
            == (|y: Row| sum_of(c, |z: Row| h3(y, z)))(b[j]) by {
        let y = b[j];
        lemma_sum_of_ext(c, |z: Row| sum_of(a, |x: Row| h(x, y, z)), |z: Row| h3(y, z));
    }
    lemma_sum_of_ext(b, |y: Row| sum_of(c, |z: Row| sum_of(a, |x: Row| h(x, y, z))), |y: Row| sum_of(c, |z: Row| h3(y, z)));
    assert forall|m: int| 0 <= m < c.len() implies
        (|z: Row| sum_of(b, |y: Row| h3(y, z)))(#[trigger] c[m]) == (|z: Row| sum_of(b, |y: Row| sum_of(a, |x: Row| h(x, y, z))))(c[m]) by {
        let z = c[m];
        lemma_sum_of_ext(b, |y: Row| h3(y, z), |y: Row| sum_of(a, |x: Row| h(x, y, z)));
    }
    lemma_sum_of_ext(c, |z: Row| sum_of(b, |y: Row| h3(y, z)), |z: Row| sum_of(b, |y: Row| sum_of(a, |x: Row| h(x, y, z))));
}

// ------------------------------------------------------------------------------------------- per lineitem row

/// For one lineitem row: the sum over orders and customer rows of the triple term is `w(l) * line_mult`.
pub proof fn lemma_per_line(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int, l: Row)
    ensures
        sum_of(rs.o, |o: Row| sum_of(rs.c, |c: Row| g_of(rs, prm, k, w, c, o, l))) == line_mult(rs, prm, k, l) * w(l),
{
    reveal(line_mult);
    let po = |o: Row| l[0] == o[0] && date_ok(o, prm);
    // inner: customers
    assert forall|j: int| 0 <= j < rs.o.len() implies
        (|o: Row| sum_of(rs.c, |c: Row| g_of(rs, prm, k, w, c, o, l)))(#[trigger] rs.o[j])
            == (|o: Row| w(l) * (if po(o) { c_cnt(rs, o, l, k, prm.name) } else { 0int }))(rs.o[j]) by {
        let o = rs.o[j];
        let q = |c: Row| c[0] == o[1];
        let f = |c: Row| s_cnt(rs, c, l, k, prm.name);
        assert forall|i: int| 0 <= i < rs.c.len() implies
            (|c: Row| g_of(rs, prm, k, w, c, o, l))(#[trigger] rs.c[i])
                == (|c: Row| if po(o) && q(c) { w(l) * f(c) } else { 0int })(rs.c[i]) by {}
        lemma_sum_of_ext(rs.c, |c: Row| g_of(rs, prm, k, w, c, o, l), |c: Row| if po(o) && q(c) { w(l) * f(c) } else { 0int });
        lemma_sum_guard(rs.c, po(o), w(l), q, f);
        lemma_sum_of_ext(rs.c, |c: Row| if q(c) { f(c) } else { 0int }, |c: Row| c_term(rs, o, l, k, prm.name, c));
    }
    let fo = |o: Row| if po(o) { c_cnt(rs, o, l, k, prm.name) } else { 0int };
    lemma_sum_of_ext(rs.o, |o: Row| sum_of(rs.c, |c: Row| g_of(rs, prm, k, w, c, o, l)),
        |o: Row| w(l) * (if po(o) { c_cnt(rs, o, l, k, prm.name) } else { 0int }));
    lemma_sum_of_ext(rs.o, |o: Row| w(l) * (if po(o) { c_cnt(rs, o, l, k, prm.name) } else { 0int }),
        |x: Row| w(l) * fo(x));
    lemma_sum_scale(rs.o, w(l), fo);
    lemma_sum_of_ext(rs.o, fo, |o: Row| o_term(rs, prm, k, l, o));
    assert(w(l) * line_mult(rs, prm, k, l) == line_mult(rs, prm, k, l) * w(l)) by (nonlinear_arith);
}

/// The group accumulator with lineitem weight `w` is the sum over lineitem rows of `line_mult * w`.
pub proof fn lemma_group_sum(rs: Rels, prm: Prm, k: Row, w: spec_fn(Row) -> int)
    requires rels_widths(rs),
    ensures
        sum_of(xs_of(rs), |y: Row| t_of(prm, k, w, y)) == sum_of(rs.l, |l: Row| line_mult(rs, prm, k, l) * w(l)),
{
    lemma_unfold_products(rs, prm, k, w);
    lemma_e0(rs, prm, k, w);
    let h = |c: Row, o: Row, l: Row| g_of(rs, prm, k, w, c, o, l);
    lemma_sum3_reverse(rs.c, rs.o, rs.l, h);
    // match the closures of the reversal with the explicit ones
    assert forall|i: int| 0 <= i < rs.c.len() implies
        (|c: Row| sum_of(rs.o, |o: Row| sum_of(rs.l, |l: Row| g_of(rs, prm, k, w, c, o, l))))(#[trigger] rs.c[i])
            == (|x: Row| sum_of(rs.o, |y: Row| sum_of(rs.l, |z: Row| h(x, y, z))))(rs.c[i]) by {
        let c = rs.c[i];
        assert forall|j: int| 0 <= j < rs.o.len() implies
            (|o: Row| sum_of(rs.l, |l: Row| g_of(rs, prm, k, w, c, o, l)))(#[trigger] rs.o[j])
                == (|y: Row| sum_of(rs.l, |z: Row| h(c, y, z)))(rs.o[j]) by {
            let o = rs.o[j];
            lemma_sum_of_ext(rs.l, |l: Row| g_of(rs, prm, k, w, c, o, l), |z: Row| h(c, o, z));
        }
        lemma_sum_of_ext(rs.o, |o: Row| sum_of(rs.l, |l: Row| g_of(rs, prm, k, w, c, o, l)),
            |y: Row| sum_of(rs.l, |z: Row| h(c, y, z)));
    }
    lemma_sum_of_ext(rs.c, |c: Row| sum_of(rs.o, |o: Row| sum_of(rs.l, |l: Row| g_of(rs, prm, k, w, c, o, l))),
        |x: Row| sum_of(rs.o, |y: Row| sum_of(rs.l, |z: Row| h(x, y, z))));
    assert forall|m: int| 0 <= m < rs.l.len() implies
        (|z: Row| sum_of(rs.o, |y: Row| sum_of(rs.c, |x: Row| h(x, y, z))))(#[trigger] rs.l[m])
            == (|l: Row| line_mult(rs, prm, k, l) * w(l))(rs.l[m]) by {
        let l = rs.l[m];
        assert forall|j: int| 0 <= j < rs.o.len() implies
            (|y: Row| sum_of(rs.c, |x: Row| h(x, y, l)))(#[trigger] rs.o[j])
                == (|o: Row| sum_of(rs.c, |c: Row| g_of(rs, prm, k, w, c, o, l)))(rs.o[j]) by {
            let o = rs.o[j];
            lemma_sum_of_ext(rs.c, |x: Row| h(x, o, l), |c: Row| g_of(rs, prm, k, w, c, o, l));
        }
        lemma_sum_of_ext(rs.o, |y: Row| sum_of(rs.c, |x: Row| h(x, y, l)),
            |o: Row| sum_of(rs.c, |c: Row| g_of(rs, prm, k, w, c, o, l)));
        lemma_per_line(rs, prm, k, w, l);
    }
    lemma_sum_of_ext(rs.l, |z: Row| sum_of(rs.o, |y: Row| sum_of(rs.c, |x: Row| h(x, y, z))),
        |l: Row| line_mult(rs, prm, k, l) * w(l));
}

} // verus!
