//! Relation composition (optional author toolkit; nothing here names a query, a table or a column). Bag semantics
//! throughout: duplicates in any input multiply, and no key, uniqueness or foreign-key property is assumed.
//!
//! - Rows kept by a two-valued condition (`keep`, in order and with multiplicity): the SQL filter of two-valued
//!   truths is `keep` (`lemma_keep_true_keep`); extensionality, all/none, members, sequencing, append, map, and
//!   bucket positions (`lemma_keep_positions`: an increasing list of exactly the positions of the rows with a
//!   property, such as an index or hash bucket, lists `keep` of that property).
//! - Products: the index law of the left-major product (`lemma_product_index`), one-row, append and prefix laws,
//!   associativity (`lemma_product_assoc`, `lemma_joined_split`: any bracketing of the FROM inputs is the left-deep
//!   product `link::query::joined_of`), and conditions of the two sides commuting with the product
//!   (`lemma_product_keep`).
//! - Joined rows by parts: every row of the left-deep product is one row of each input at the offsets of the inputs'
//!   widths (`parts_ok`, `lemma_joined_parts`), and projecting the product of full rows onto each input's fields is
//!   the product of the projected inputs (`join_cols`, `lemma_proj_joined`).
//! - Evaluation of FROM trees: a tree of `Table`, `Product` (comma, CROSS JOIN) and inner-join `Filter`s (`JOIN .. ON
//!   p`) evaluates to the left-deep product of its inputs kept by a two-valued condition (`lemma_eval_table`,
//!   `lemma_eval_filter`, `lemma_eval_product`). `lemma_eval_filter` requires the condition to evaluate without
//!   error on every row that reaches it; a condition that does so on every well-typed row can be moved without
//!   changing the rows or the absence of errors. (This `lemma_eval_filter` is not
//!   `exec::relational::domain::lemma_eval_filter`, the one-step unfolding of `Filter`.)
//! - Sums over relations (`sum_of`): the accumulators `gcount`, `gsum`, `gabs` of `link::query` are sums of
//!   per-row terms (`lemma_acc_sum_of`); append, extensionality, zero, pointwise addition, map, removal,
//!   permutation (`lemma_sum_of_perm`: the same multiset gives the same sum), rows contributing zero dropped by a
//!   condition (`lemma_sum_of_keep`), and product decomposition in left-major or right-major order
//!   (`lemma_sum_of_product`, `lemma_sum_of_product_swap`, `lemma_sum_of_swap`). With these a hash, sort-merge or
//!   index join proves its accumulators equal those over the joined relation without enumerating the product at
//!   run time.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};
use crate::bridge::collect::lemma_collect_all;
use crate::exec::relational::domain::lemma_collect_pointwise;
use crate::link::query::{proj, proj_all, joined_of, QuerySpec, hit, gcount, gsum, gabs};

verus! {

// ------------------------------------------------------------------------------------------ rows kept by a condition

/// The rows satisfying `f`, in order and with their multiplicity.
pub open spec fn keep(rows: Seq<Row>, f: spec_fn(Row) -> bool) -> Seq<Row>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else if f(rows.last()) {
        keep(rows.drop_last(), f).push(rows.last())
    } else {
        keep(rows.drop_last(), f)
    }
}

/// One more row at the end.
pub proof fn lemma_keep_push(rows: Seq<Row>, x: Row, f: spec_fn(Row) -> bool)
    ensures keep(rows.push(x), f) == if f(x) { keep(rows, f).push(x) } else { keep(rows, f) },
{
    assert(rows.push(x).drop_last() =~= rows);
}

/// The SQL filter (`keep_true`) of two-valued truths is `keep`.
pub proof fn lemma_keep_true_keep(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] truths[i] == truth_of(f(rows[i])),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies #[trigger] ti[i] == truth_of(f(ri[i])) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true_keep(ri, ti, f);
        assert(truths[rows.len() - 1] == truth_of(f(rows[rows.len() - 1])));
    }
}

/// Conditions that agree on every row keep the same rows.
pub proof fn lemma_keep_ext(rows: Seq<Row>, f: spec_fn(Row) -> bool, h: spec_fn(Row) -> bool)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) == h(rows[i]),
    ensures keep(rows, f) == keep(rows, h),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies f(#[trigger] ri[i]) == h(ri[i]) by {
            assert(ri[i] == rows[i]);
        }
        lemma_keep_ext(ri, f, h);
        assert(f(rows[rows.len() - 1]) == h(rows[rows.len() - 1]));
    }
}

/// A condition true on every row keeps every row.
pub proof fn lemma_keep_all(rows: Seq<Row>, f: spec_fn(Row) -> bool)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]),
    ensures keep(rows, f) == rows,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies f(#[trigger] ri[i]) by {
            assert(ri[i] == rows[i]);
        }
        lemma_keep_all(ri, f);
        assert(f(rows[rows.len() - 1]));
        assert(ri.push(rows.last()) =~= rows);
    }
}

/// A condition false on every row keeps no row.
pub proof fn lemma_keep_none(rows: Seq<Row>, f: spec_fn(Row) -> bool)
    requires forall|i: int| 0 <= i < rows.len() ==> !f(#[trigger] rows[i]),
    ensures keep(rows, f) == Seq::<Row>::empty(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies !f(#[trigger] ri[i]) by {
            assert(ri[i] == rows[i]);
        }
        lemma_keep_none(ri, f);
        assert(!f(rows[rows.len() - 1]));
    }
}

/// Kept rows are rows of the input satisfying the condition.
pub proof fn lemma_keep_members(rows: Seq<Row>, f: spec_fn(Row) -> bool)
    ensures
        keep(rows, f).len() <= rows.len(),
        forall|i: int| 0 <= i < keep(rows, f).len() ==> rows.contains(#[trigger] keep(rows, f)[i]) && f(keep(rows, f)[i]),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        lemma_keep_members(ri, f);
        let k = keep(rows, f);
        let ki = keep(ri, f);
        assert forall|i: int| 0 <= i < k.len() implies rows.contains(#[trigger] k[i]) && f(k[i]) by {
            if i < ki.len() {
                assert(k[i] == ki[i]);
                let m = choose|m: int| 0 <= m < ri.len() && ri[m] == ki[i];
                assert(rows[m] == ki[i]);
            } else {
                assert(k[i] == rows[rows.len() - 1]);
            }
        }
    }
}

/// Two conditions in sequence keep the rows of their conjunction.
pub proof fn lemma_keep_keep(rows: Seq<Row>, f: spec_fn(Row) -> bool, h: spec_fn(Row) -> bool)
    ensures keep(keep(rows, f), h) == keep(rows, |x: Row| f(x) && h(x)),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        lemma_keep_keep(ri, f, h);
        if f(rows.last()) {
            lemma_keep_push(keep(ri, f), rows.last(), h);
        }
    }
}

/// `keep` distributes over concatenation.
pub proof fn lemma_keep_append(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> bool)
    ensures keep(a + b, f) == keep(a, f) + keep(b, f),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(keep(a, f) + keep(b, f) =~= keep(a, f));
    } else {
        let bi = b.drop_last();
        lemma_keep_append(a, bi, f);
        assert((a + b).drop_last() =~= a + bi);
        assert((a + b).last() == b.last());
        if f(b.last()) {
            assert(keep(a, f) + keep(bi, f).push(b.last()) =~= (keep(a, f) + keep(bi, f)).push(b.last()));
        }
    }
}

/// `keep` of mapped rows is the mapped `keep` of the composed condition.
pub proof fn lemma_keep_map(b: Seq<Row>, m: spec_fn(Row) -> Row, f: spec_fn(Row) -> bool)
    ensures keep(b.map_values(m), f) == keep(b, |y: Row| f(m(y))).map_values(m),
    decreases b.len(),
{
    let fm = |y: Row| f(m(y));
    if b.len() == 0 {
        assert(b.map_values(m) =~= Seq::<Row>::empty());
        assert(keep(b, fm).map_values(m) =~= Seq::<Row>::empty());
    } else {
        let bi = b.drop_last();
        lemma_keep_map(bi, m, f);
        assert(b.map_values(m).drop_last() =~= bi.map_values(m));
        assert(b.map_values(m).last() == m(b.last()));
        if fm(b.last()) {
            assert(keep(bi, fm).push(b.last()).map_values(m) =~= keep(bi, fm).map_values(m).push(m(b.last())));
        }
    }
}

/// Bucket positions: an increasing list of exactly the positions whose rows satisfy `c` (for example the entries of
/// an index or hash bucket for one key value) lists the rows `keep(rows, c)`, in order and with multiplicity.
pub proof fn lemma_keep_positions(rows: Seq<Row>, c: spec_fn(Row) -> bool, ps: Seq<int>)
    requires
        forall|t: int| 0 <= t < ps.len() ==> 0 <= #[trigger] ps[t] < rows.len() && c(rows[ps[t]]),
        forall|t: int, u: int| 0 <= t < u < ps.len() ==> #[trigger] ps[t] < #[trigger] ps[u],
        forall|i: int| 0 <= i < rows.len() && c(#[trigger] rows[i]) ==> exists|t: int| 0 <= t < ps.len() && ps[t] == i,
    ensures keep(rows, c) == ps.map_values(|p: int| rows[p]),
    decreases rows.len(),
{
    let n = rows.len() as int;
    if n == 0 {
        if ps.len() > 0 {
            assert(0 <= ps[0] < rows.len());
        }
        assert(ps.map_values(|p: int| rows[p]) =~= Seq::<Row>::empty());
    } else {
        let ri = rows.drop_last();
        if c(rows[n - 1]) {
            let t0 = choose|t: int| 0 <= t < ps.len() && ps[t] == n - 1;
            if t0 < ps.len() - 1 {
                assert(ps[t0] < ps[t0 + 1]);
                assert(false);
            }
            let pi = ps.drop_last();
            assert forall|t: int| 0 <= t < pi.len() implies 0 <= #[trigger] pi[t] < ri.len() && c(ri[pi[t]]) by {
                assert(pi[t] == ps[t]);
                assert(ps[t] < ps[ps.len() - 1]);
                assert(ri[pi[t]] == rows[ps[t]]);
            }
            assert forall|t: int, u: int| 0 <= t < u < pi.len() implies #[trigger] pi[t] < #[trigger] pi[u] by {
                assert(pi[t] == ps[t] && pi[u] == ps[u]);
            }
            assert forall|i: int| 0 <= i < ri.len() && c(#[trigger] ri[i]) implies exists|t: int| 0 <= t < pi.len() && pi[t] == i by {
                assert(ri[i] == rows[i]);
                let t = choose|t: int| 0 <= t < ps.len() && ps[t] == i;
                assert(t != ps.len() - 1);
                assert(pi[t] == i);
            }
            lemma_keep_positions(ri, c, pi);
            assert(ps.map_values(|p: int| rows[p]) =~= pi.map_values(|p: int| ri[p]).push(rows[n - 1]));
        } else {
            assert forall|t: int| 0 <= t < ps.len() implies 0 <= #[trigger] ps[t] < ri.len() && c(ri[ps[t]]) by {
                if ps[t] == n - 1 {
                    assert(c(rows[n - 1]));
                }
                assert(ri[ps[t]] == rows[ps[t]]);
            }
            assert forall|i: int| 0 <= i < ri.len() && c(#[trigger] ri[i]) implies exists|t: int| 0 <= t < ps.len() && ps[t] == i by {
                assert(ri[i] == rows[i]);
            }
            lemma_keep_positions(ri, c, ps);
            assert(ps.map_values(|p: int| rows[p]) =~= ps.map_values(|p: int| ri[p]));
        }
    }
}

// ------------------------------------------------------------------------------------------ products

/// The first `w` values of a joined row (its left part).
pub open spec fn left_of(x: Row, w: nat) -> Row {
    x.subrange(0, w as int)
}

/// The values after the first `w` (its right part).
pub open spec fn right_of(x: Row, w: nat) -> Row {
    x.subrange(w as int, x.len() as int)
}

/// Index law of the left-major product: row `i * |b| + j` is `a[i] ++ b[j]`.
pub proof fn lemma_product_index(a: Seq<Row>, b: Seq<Row>)
    ensures
        product_rows(a, b).len() == a.len() * b.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==>
            product_rows(a, b)[i * b.len() + j] == #[trigger] a[i] + #[trigger] b[j],
    decreases a.len(),
{
    if a.len() > 0 {
        let ai = a.drop_last();
        lemma_product_index(ai, b);
        let p = product_rows(a, b);
        let pi = product_rows(ai, b);
        let nb = b.len() as int;
        assert(a.len() * b.len() == ai.len() * b.len() + b.len()) by (nonlinear_arith)
            requires a.len() == ai.len() + 1;
        assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() implies
            product_rows(a, b)[i * b.len() + j] == #[trigger] a[i] + #[trigger] b[j] by {
            if i < ai.len() {
                assert(i * nb + j < ai.len() * nb) by (nonlinear_arith)
                    requires 0 <= i < ai.len(), 0 <= j < nb;
                assert(0 <= i * nb) by (nonlinear_arith) requires 0 <= i, 0 <= nb;
                assert(p[i * nb + j] == pi[i * nb + j]);
                assert(ai[i] == a[i]);
            } else {
                assert(i == ai.len());
                assert(i * nb == ai.len() * nb);
                assert(p[i * nb + j] == a.last() + b[j]);
            }
        }
    }
}

/// The product of two one-row relations is their one concatenated row.
pub proof fn lemma_product_one(a: Row, b: Row)
    ensures product_rows(seq![a], seq![b]) == seq![a + b],
{
    let (l, r) = (seq![a], seq![b]);
    assert(l.drop_last() =~= Seq::<Row>::empty());
    assert(product_rows(Seq::<Row>::empty(), r) == Seq::<Row>::empty());
    assert(product_rows(l, r) == product_rows(l.drop_last(), r) + r.map_values(|y: Row| l.last() + y));
    assert(r.map_values(|y: Row| l.last() + y) =~= seq![a + b]);
    assert(Seq::<Row>::empty() + seq![a + b] =~= seq![a + b]);
}

/// The product of concatenated left inputs is the concatenation of the products.
pub proof fn lemma_product_append(a1: Seq<Row>, a2: Seq<Row>, c: Seq<Row>)
    ensures product_rows(a1 + a2, c) == product_rows(a1, c) + product_rows(a2, c),
    decreases a2.len(),
{
    if a2.len() == 0 {
        assert(a1 + a2 =~= a1);
        assert(product_rows(a1, c) + product_rows(a2, c) =~= product_rows(a1, c));
    } else {
        let a2i = a2.drop_last();
        lemma_product_append(a1, a2i, c);
        assert((a1 + a2).drop_last() =~= a1 + a2i);
        assert((a1 + a2).last() == a2.last());
        assert(c.map_values(|r: Row| (a1 + a2).last() + r) =~= c.map_values(|r: Row| a2.last() + r));
        assert(product_rows(a1, c) + product_rows(a2i, c) + c.map_values(|r: Row| a2.last() + r)
            =~= product_rows(a1, c) + (product_rows(a2i, c) + c.map_values(|r: Row| a2.last() + r)));
    }
}

/// A common prefix of the left rows moves out of the product.
pub proof fn lemma_product_prefix(x: Row, b: Seq<Row>, c: Seq<Row>)
    ensures product_rows(b.map_values(|r: Row| x + r), c) == product_rows(b, c).map_values(|r: Row| x + r),
    decreases b.len(),
{
    let m = |r: Row| x + r;
    if b.len() == 0 {
        assert(b.map_values(m) =~= Seq::<Row>::empty());
        assert(product_rows(b, c).map_values(m) =~= Seq::<Row>::empty());
    } else {
        let bi = b.drop_last();
        lemma_product_prefix(x, bi, c);
        let bm = b.map_values(m);
        assert(bm.drop_last() =~= bi.map_values(m));
        assert(bm.last() == x + b.last());
        assert(c.map_values(|s: Row| bm.last() + s) =~= c.map_values(|s: Row| b.last() + s).map_values(m)) by {
            assert forall|i: int| 0 <= i < c.len() implies (x + b.last()) + #[trigger] c[i] == x + (b.last() + c[i]) by {
                assert((x + b.last()) + c[i] =~= x + (b.last() + c[i]));
            }
        }
        assert((product_rows(bi, c) + c.map_values(|s: Row| b.last() + s)).map_values(m)
            =~= product_rows(bi, c).map_values(m) + c.map_values(|s: Row| b.last() + s).map_values(m));
    }
}

/// Associativity of the product (row concatenation is associative): any bracketing of the FROM inputs.
pub proof fn lemma_product_assoc(a: Seq<Row>, b: Seq<Row>, c: Seq<Row>)
    ensures product_rows(a, product_rows(b, c)) == product_rows(product_rows(a, b), c),
    decreases a.len(),
{
    if a.len() > 0 {
        let ai = a.drop_last();
        lemma_product_assoc(ai, b, c);
        let m = |r: Row| a.last() + r;
        lemma_product_append(product_rows(ai, b), b.map_values(m), c);
        lemma_product_prefix(a.last(), b, c);
        assert(product_rows(b, c).map_values(m) =~= product_rows(b, c).map_values(|r: Row| a.last() + r));
    }
}

/// Conditions of the two sides commute with the product: the product of the kept rows is the product kept by the
/// conjunction of the left condition on the left part and the right condition on the right part (left rows of width
/// `wa`).
pub proof fn lemma_product_keep(a: Seq<Row>, b: Seq<Row>, fa: spec_fn(Row) -> bool, fb: spec_fn(Row) -> bool, wa: nat)
    requires forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == wa,
    ensures product_rows(keep(a, fa), keep(b, fb)) == keep(product_rows(a, b), |x: Row| fa(left_of(x, wa)) && fb(right_of(x, wa))),
    decreases a.len(),
{
    let phi = |x: Row| fa(left_of(x, wa)) && fb(right_of(x, wa));
    if a.len() > 0 {
        let ai = a.drop_last();
        let x = a.last();
        assert forall|i: int| 0 <= i < ai.len() implies (#[trigger] ai[i]).len() == wa by {
            assert(ai[i] == a[i]);
        }
        lemma_product_keep(ai, b, fa, fb, wa);
        assert(x.len() == wa) by {
            assert(a[a.len() - 1] == x);
        }
        let m = |r: Row| a.last() + r;
        assert(product_rows(a, b) == product_rows(ai, b) + b.map_values(m));
        lemma_keep_append(product_rows(ai, b), b.map_values(m), phi);
        lemma_keep_map(b, m, phi);
        let psi = |y: Row| phi(m(y));
        let kb = keep(b, fb);
        assert forall|i: int| 0 <= i < b.len() implies left_of(#[trigger] m(b[i]), wa) == x && right_of(m(b[i]), wa) == b[i] by {
            assert(left_of(x + b[i], wa) =~= x);
            assert(right_of(x + b[i], wa) =~= b[i]);
        }
        if fa(x) {
            assert forall|i: int| 0 <= i < b.len() implies psi(#[trigger] b[i]) == fb(b[i]) by {
                assert(left_of(m(b[i]), wa) == x);
            }
            lemma_keep_ext(b, psi, fb);
            let ka = keep(a, fa);
            assert(ka == keep(ai, fa).push(x));
            assert(ka.drop_last() =~= keep(ai, fa));
            assert(product_rows(ka, kb) == product_rows(keep(ai, fa), kb) + kb.map_values(|r: Row| ka.last() + r));
            assert(kb.map_values(|r: Row| ka.last() + r) =~= kb.map_values(m));
        } else {
            assert forall|i: int| 0 <= i < b.len() implies !psi(#[trigger] b[i]) by {
                assert(left_of(m(b[i]), wa) == x);
            }
            lemma_keep_none(b, psi);
            assert(keep(b, psi).map_values(m) =~= Seq::<Row>::empty());
            assert(keep(product_rows(ai, b), phi) + Seq::<Row>::empty() =~= keep(product_rows(ai, b), phi));
        }
    }
}

/// Any split point of the FROM inputs: the product of the left-deep products of the two parts is the left-deep
/// product of all inputs (so a parenthesized join tree denotes `joined_of`).
pub proof fn lemma_joined_split(ts: Seq<Seq<Row>>, s: Seq<nat>, m: int)
    requires 1 <= m < s.len(),
    ensures product_rows(joined_of(ts, s.take(m)), joined_of(ts, s.skip(m))) == joined_of(ts, s),
    decreases s.len(),
{
    let n = s.len() as int;
    if n - m == 1 {
        assert(s.take(m) =~= s.drop_last());
        assert(s.skip(m).len() == 1);
        assert(s.skip(m)[0] == s.last());
    } else {
        let si = s.drop_last();
        lemma_joined_split(ts, si, m);
        assert(si.take(m) =~= s.take(m));
        assert(si.skip(m) =~= s.skip(m).drop_last());
        assert(s.skip(m).last() == s.last());
        lemma_product_assoc(joined_of(ts, s.take(m)), joined_of(ts, si.skip(m)), ts[s.last() as int]);
    }
}

// ------------------------------------------------------------------------------------------ joined rows by parts

/// Start offsets of consecutive parts of widths `ws` (and the total width last).
pub open spec fn offsets(ws: Seq<nat>) -> Seq<nat>
    decreases ws.len(),
{
    if ws.len() == 0 {
        seq![0nat]
    } else {
        let p = offsets(ws.drop_last());
        p.push(p.last() + ws.last())
    }
}

/// `offsets` starts at 0, steps by each width, and ends at the largest offset (the total width).
pub proof fn lemma_offsets(ws: Seq<nat>)
    ensures
        offsets(ws).len() == ws.len() + 1,
        offsets(ws)[0] == 0,
        forall|i: int| 0 <= i < ws.len() ==> #[trigger] offsets(ws)[i + 1] == offsets(ws)[i] + ws[i],
        forall|i: int| 0 <= i <= ws.len() ==> #[trigger] offsets(ws)[i] <= offsets(ws)[ws.len() as int],
    decreases ws.len(),
{
    if ws.len() > 0 {
        let wi = ws.drop_last();
        lemma_offsets(wi);
        let p = offsets(wi);
        let o = offsets(ws);
        assert(o == p.push(p.last() + ws.last()));
        assert forall|i: int| 0 <= i < ws.len() implies #[trigger] o[i + 1] == o[i] + ws[i] by {
            if i < wi.len() {
                assert(p[i + 1] == p[i] + wi[i]);
            }
        }
        assert forall|i: int| 0 <= i <= ws.len() implies #[trigger] o[i] <= o[ws.len() as int] by {
            if i < ws.len() {
                assert(p[i] <= p[wi.len() as int]);
            }
        }
    }
}

/// `x` is one part per width, part `i` satisfying `ok(i, part)` (a joined row: one row of each input).
pub open spec fn parts_ok(x: Row, ws: Seq<nat>, ok: spec_fn(int, Row) -> bool) -> bool {
    &&& x.len() == offsets(ws).last()
    &&& forall|i: int| 0 <= i < ws.len() ==> #[trigger] ok(i, x.subrange(offsets(ws)[i] as int, offsets(ws)[i + 1] as int))
}

/// One part of a row that is `parts_ok`.
pub proof fn lemma_parts_at(x: Row, ws: Seq<nat>, ok: spec_fn(int, Row) -> bool, i: int)
    requires parts_ok(x, ws, ok), 0 <= i < ws.len(),
    ensures
        x.len() == offsets(ws)[ws.len() as int],
        offsets(ws)[i + 1] == offsets(ws)[i] + ws[i],
        offsets(ws)[i + 1] <= x.len(),
        ok(i, x.subrange(offsets(ws)[i] as int, offsets(ws)[i + 1] as int)),
{
    lemma_offsets(ws);
}

/// Every row of input `i`'s relation has width `ws[i]` and satisfies `ok(i, row)`.
pub open spec fn inputs_ok(ts: Seq<Seq<Row>>, inputs: Seq<nat>, ws: Seq<nat>, ok: spec_fn(int, Row) -> bool) -> bool {
    &&& ws.len() == inputs.len()
    &&& forall|i: int, k: int| 0 <= i < inputs.len() && 0 <= k < ts[inputs[i] as int].len() ==>
        (#[trigger] ts[inputs[i] as int][k]).len() == ws[i] && ok(i, ts[inputs[i] as int][k])
}

/// Every row of the left-deep product is the concatenation of one row of each input, at the offsets of the widths.
pub proof fn lemma_joined_parts(ts: Seq<Seq<Row>>, inputs: Seq<nat>, ws: Seq<nat>, ok: spec_fn(int, Row) -> bool)
    requires inputs.len() >= 1, inputs_ok(ts, inputs, ws, ok),
    ensures forall|k: int| 0 <= k < joined_of(ts, inputs).len() ==> parts_ok(#[trigger] joined_of(ts, inputs)[k], ws, ok),
    decreases inputs.len(),
{
    lemma_offsets(ws);
    let n = inputs.len() as int;
    let j = joined_of(ts, inputs);
    if n == 1 {
        assert forall|k: int| 0 <= k < j.len() implies parts_ok(#[trigger] j[k], ws, ok) by {
            let x = j[k];
            assert(x == ts[inputs[0] as int][k]);
            assert(x.len() == ws[0] && ok(0, x));
            assert(offsets(ws)[1] == offsets(ws)[0] + ws[0]);
            assert(x.subrange(0, ws[0] as int) =~= x);
        }
    } else {
        let (ii, wi) = (inputs.drop_last(), ws.drop_last());
        assert(inputs_ok(ts, ii, wi, ok)) by {
            assert forall|i: int, k: int| 0 <= i < ii.len() && 0 <= k < ts[ii[i] as int].len() implies
                (#[trigger] ts[ii[i] as int][k]).len() == wi[i] && ok(i, ts[ii[i] as int][k]) by {
                assert(ii[i] == inputs[i] && wi[i] == ws[i]);
                assert(ts[inputs[i] as int][k].len() == ws[i]);
            }
        }
        lemma_joined_parts(ts, ii, wi, ok);
        lemma_offsets(wi);
        let l = joined_of(ts, ii);
        let r = ts[inputs.last() as int];
        assert(j == product_rows(l, r));
        lemma_product_rows_elems(l, r);
        let (o, p) = (offsets(ws), offsets(wi));
        assert(o == p.push(p.last() + ws.last()));
        assert forall|k: int| 0 <= k < j.len() implies parts_ok(#[trigger] j[k], ws, ok) by {
            assert(is_concat(j[k], l, r));
            let (a, b) = choose|a: int, b: int| 0 <= a < l.len() && 0 <= b < r.len() && j[k] == #[trigger] l[a] + #[trigger] r[b];
            let x = j[k];
            assert(parts_ok(l[a], wi, ok));
            assert(r[b].len() == ws[n - 1] && ok(n - 1, r[b])) by {
                assert(ts[inputs[n - 1] as int][b] == r[b]);
            }
            assert(l[a].len() == p[wi.len() as int]);
            assert forall|i: int| 0 <= i < ws.len() implies #[trigger] ok(i, x.subrange(o[i] as int, o[i + 1] as int)) by {
                if i < n - 1 {
                    lemma_parts_at(l[a], wi, ok, i);
                    assert(o[i] == p[i] && o[i + 1] == p[i + 1]);
                    assert(x.subrange(o[i] as int, o[i + 1] as int) =~= l[a].subrange(p[i] as int, p[i + 1] as int));
                } else {
                    assert(o[i] == p[wi.len() as int]);
                    assert(x.subrange(o[i] as int, o[i + 1] as int) =~= r[b]);
                }
            }
        }
    }
}

/// Columns `cols` shifted by `d` (the columns of a part inside the concatenated row).
pub open spec fn shift(cols: Seq<nat>, d: nat) -> Seq<nat> {
    cols.map_values(|c: nat| c + d)
}

/// The joined row's columns in the concatenated full rows: input `i`'s fields `fcols[i]` shifted by the widths of the
/// inputs before it.
pub open spec fn join_cols(ws: Seq<nat>, fcols: Seq<Seq<nat>>) -> Seq<nat>
    decreases ws.len(),
{
    if ws.len() == 0 {
        Seq::empty()
    } else {
        join_cols(ws.drop_last(), fcols.drop_last()) + shift(fcols.last(), offsets(ws.drop_last()).last())
    }
}

/// Projection of a concatenated row onto `ca ++ shift(cb, |left|)` is the concatenation of the projections.
pub proof fn lemma_proj_concat(x: Row, y: Row, ca: Seq<nat>, cb: Seq<nat>)
    requires
        forall|k: int| 0 <= k < ca.len() ==> #[trigger] ca[k] < x.len(),
        forall|k: int| 0 <= k < cb.len() ==> #[trigger] cb[k] < y.len(),
    ensures proj(x + y, ca + shift(cb, x.len())) == proj(x, ca) + proj(y, cb),
{
    let cs = ca + shift(cb, x.len());
    let (px, py) = (proj(x, ca), proj(y, cb));
    assert forall|k: int| 0 <= k < cs.len() implies #[trigger] proj(x + y, cs)[k] == (px + py)[k] by {
        if k < ca.len() {
            assert(cs[k] == ca[k]);
            assert((x + y)[ca[k] as int] == x[ca[k] as int]);
            assert(px[k] == x[ca[k] as int]);
        } else {
            let c = k - ca.len();
            assert(cs[k] == cb[c] + x.len());
            assert((x + y)[(cb[c] + x.len()) as int] == y[cb[c] as int]);
            assert(py[c] == y[cb[c] as int]);
        }
    }
    assert(proj(x + y, cs) =~= px + py);
}

/// Projection distributes over a product: `ca` of left rows of width `wa`, then `cb` (of right rows of width `wb`)
/// shifted by `wa`.
pub proof fn lemma_proj_product(a: Seq<Row>, b: Seq<Row>, ca: Seq<nat>, cb: Seq<nat>, wa: nat, wb: nat)
    requires
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == wa,
        forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]).len() == wb,
        forall|k: int| 0 <= k < ca.len() ==> #[trigger] ca[k] < wa,
        forall|k: int| 0 <= k < cb.len() ==> #[trigger] cb[k] < wb,
    ensures proj_all(product_rows(a, b), ca + shift(cb, wa)) == product_rows(proj_all(a, ca), proj_all(b, cb)),
    decreases a.len(),
{
    let cs = ca + shift(cb, wa);
    if a.len() == 0 {
        assert(proj_all(product_rows(a, b), cs) =~= Seq::<Row>::empty());
        assert(proj_all(a, ca) =~= Seq::<Row>::empty());
    } else {
        let ai = a.drop_last();
        let x = a.last();
        assert forall|i: int| 0 <= i < ai.len() implies (#[trigger] ai[i]).len() == wa by {
            assert(ai[i] == a[i]);
        }
        lemma_proj_product(ai, b, ca, cb, wa, wb);
        assert(x.len() == wa) by {
            assert(a[a.len() - 1] == x);
        }
        let pa = proj_all(a, ca);
        let pb = proj_all(b, cb);
        assert(pa.drop_last() =~= proj_all(ai, ca));
        assert(pa.last() == proj(x, ca));
        let m = |r: Row| a.last() + r;
        assert(product_rows(a, b) == product_rows(ai, b) + b.map_values(m));
        assert forall|j: int| 0 <= j < b.len() implies proj(#[trigger] m(b[j]), cs) == proj(x, ca) + proj(b[j], cb) by {
            lemma_proj_concat(x, b[j], ca, cb);
        }
        assert(proj_all(b.map_values(m), cs) =~= pb.map_values(|r: Row| pa.last() + r));
        assert(proj_all(product_rows(ai, b) + b.map_values(m), cs) =~= proj_all(product_rows(ai, b), cs) + proj_all(b.map_values(m), cs));
    }
}

/// Every joined column lies inside the concatenated full row.
pub proof fn lemma_join_cols_bound(ws: Seq<nat>, fcols: Seq<Seq<nat>>)
    requires
        fcols.len() == ws.len(),
        forall|i: int, c: int| 0 <= i < ws.len() && 0 <= c < fcols[i].len() ==> #[trigger] fcols[i][c] < ws[i],
    ensures forall|k: int| 0 <= k < join_cols(ws, fcols).len() ==> #[trigger] join_cols(ws, fcols)[k] < offsets(ws).last(),
    decreases ws.len(),
{
    lemma_offsets(ws);
    if ws.len() > 0 {
        let (wi, fi) = (ws.drop_last(), fcols.drop_last());
        assert forall|i: int, c: int| 0 <= i < wi.len() && 0 <= c < fi[i].len() implies #[trigger] fi[i][c] < wi[i] by {
            assert(fi[i] == fcols[i] && wi[i] == ws[i]);
        }
        lemma_join_cols_bound(wi, fi);
        lemma_offsets(wi);
        let jc = join_cols(ws, fcols);
        let ji = join_cols(wi, fi);
        let base = offsets(wi).last();
        assert(offsets(ws).last() == base + ws.last());
        assert forall|k: int| 0 <= k < jc.len() implies #[trigger] jc[k] < offsets(ws).last() by {
            if k < ji.len() {
                assert(jc[k] == ji[k]);
            } else {
                let c = k - ji.len();
                assert(jc[k] == fcols.last()[c] + base);
                assert(fcols[ws.len() - 1][c] < ws[ws.len() - 1]);
            }
        }
    }
}

/// Projecting the left-deep product of full table rows onto every input's fields is the left-deep product of the
/// projected relations: `pts[inputs[i]]` is input `i`'s table `full[tids[i]]` projected onto `fcols[i]`.
pub proof fn lemma_proj_joined(full: Seq<Seq<Row>>, tids: Seq<nat>, pts: Seq<Seq<Row>>, inputs: Seq<nat>, ws: Seq<nat>,
    fcols: Seq<Seq<nat>>, ok: spec_fn(int, Row) -> bool)
    requires
        tids.len() >= 1,
        inputs.len() == tids.len(),
        fcols.len() == tids.len(),
        inputs_ok(full, tids, ws, ok),
        forall|i: int, c: int| 0 <= i < ws.len() && 0 <= c < fcols[i].len() ==> #[trigger] fcols[i][c] < ws[i],
        forall|i: int| 0 <= i < tids.len() ==> #[trigger] pts[inputs[i] as int] == proj_all(full[tids[i] as int], fcols[i]),
    ensures proj_all(joined_of(full, tids), join_cols(ws, fcols)) == joined_of(pts, inputs),
    decreases tids.len(),
{
    lemma_offsets(ws);
    let n = tids.len() as int;
    if n == 1 {
        assert(join_cols(ws, fcols) =~= fcols[0]) by {
            assert(ws.drop_last().len() == 0);
            assert(join_cols(ws.drop_last(), fcols.drop_last()) =~= Seq::<nat>::empty());
            assert(offsets(ws.drop_last()) =~= seq![0nat]);
            assert(shift(fcols[0], 0) =~= fcols[0]);
        }
        assert(pts[inputs[0] as int] == proj_all(full[tids[0] as int], fcols[0]));
    } else {
        let (ti, ii, wi, fi) = (tids.drop_last(), inputs.drop_last(), ws.drop_last(), fcols.drop_last());
        assert(inputs_ok(full, ti, wi, ok)) by {
            assert forall|i: int, k: int| 0 <= i < ti.len() && 0 <= k < full[ti[i] as int].len() implies
                (#[trigger] full[ti[i] as int][k]).len() == wi[i] && ok(i, full[ti[i] as int][k]) by {
                assert(ti[i] == tids[i] && wi[i] == ws[i]);
                assert(full[tids[i] as int][k].len() == ws[i]);
            }
        }
        assert forall|i: int, c: int| 0 <= i < wi.len() && 0 <= c < fi[i].len() implies #[trigger] fi[i][c] < wi[i] by {
            assert(fi[i] == fcols[i] && wi[i] == ws[i]);
        }
        assert forall|i: int| 0 <= i < ti.len() implies #[trigger] pts[ii[i] as int] == proj_all(full[ti[i] as int], fi[i]) by {
            assert(ii[i] == inputs[i] && ti[i] == tids[i] && fi[i] == fcols[i]);
        }
        lemma_proj_joined(full, ti, pts, ii, wi, fi, ok);
        let l = joined_of(full, ti);
        let r = full[tids.last() as int];
        lemma_joined_parts(full, ti, wi, ok);
        lemma_offsets(wi);
        let wl = offsets(wi).last();
        assert forall|i: int| 0 <= i < l.len() implies (#[trigger] l[i]).len() == wl by {
            assert(parts_ok(l[i], wi, ok));
        }
        lemma_join_cols_bound(wi, fi);
        let jc = join_cols(wi, fi);
        assert forall|k: int| 0 <= k < jc.len() implies #[trigger] jc[k] < wl by {}
        let wr = ws[n - 1];
        assert forall|i: int| 0 <= i < r.len() implies (#[trigger] r[i]).len() == wr by {
            assert(full[tids[n - 1] as int][i].len() == ws[n - 1]);
        }
        assert forall|c: int| 0 <= c < fcols.last().len() implies #[trigger] fcols.last()[c] < wr by {
            assert(fcols[n - 1][c] < ws[n - 1]);
        }
        lemma_proj_product(l, r, jc, fcols.last(), wl, wr);
        assert(join_cols(ws, fcols) == jc + shift(fcols.last(), wl));
        assert(pts[inputs[n - 1] as int] == proj_all(full[tids[n - 1] as int], fcols[n - 1]));
    }
}

// ------------------------------------------------------------------------------------------ evaluation of FROM trees

/// A condition over an input that evaluates to `keep(rows, f)`: when the condition evaluates without error on every
/// row that reaches it, to the truth of `h`, the result is `keep(rows, fh)` for `fh = f && h` (no error).
pub proof fn lemma_eval_filter(db: Database, src: Query, rows: Seq<Row>, f: spec_fn(Row) -> bool, pred: Pred, h: spec_fn(Row) -> bool,
    fh: spec_fn(Row) -> bool)
    requires
        eval_query(db, Seq::empty(), src) == Ok::<Relation, SqlError>(keep(rows, f)),
        forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) ==>
            eval_pred(db, rows[i], pred) == Ok::<Truth, SqlError>(truth_of(h(rows[i]))),
        forall|i: int| 0 <= i < rows.len() ==> fh(#[trigger] rows[i]) == (f(rows[i]) && h(rows[i])),
    ensures
        eval_query(db, Seq::empty(), Query::Filter { pred, input: Box::new(src) }) == Ok::<Relation, SqlError>(keep(rows, fh)),
{
    let kept = keep(rows, f);
    let ctx = Seq::<Val>::empty();
    lemma_keep_members(rows, f);
    let truths = Seq::new(kept.len(), |i: int| truth_of(h(kept[i])));
    let prs = Seq::new(kept.len(), |i: int| eval_pred(db, ctx + kept[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(ctx + kept[i] =~= kept[i]);
        assert(rows.contains(kept[i]) && f(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(f(rows[m]));
    }
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(collect(Seq::new(kept.len(), |i: int| eval_pred(db, ctx + kept[i], pred))) == Ok::<Seq<Truth>, SqlError>(truths));
    lemma_keep_true_keep(kept, truths, h);
    lemma_keep_keep(rows, f, h);
    lemma_keep_ext(rows, |x: Row| f(x) && h(x), fh);
}

/// A product of two inputs that evaluate to kept rows (left rows of width `wa`): the rows of the product
/// (`rows == product_rows(ra, rb)`) kept by `fp`, the conjunction of the conditions on the two parts.
pub proof fn lemma_eval_product(db: Database, l: Query, r: Query, ra: Seq<Row>, fa: spec_fn(Row) -> bool, wa: nat,
    rb: Seq<Row>, fb: spec_fn(Row) -> bool, rows: Seq<Row>, fp: spec_fn(Row) -> bool)
    requires
        eval_query(db, Seq::empty(), l) == Ok::<Relation, SqlError>(keep(ra, fa)),
        eval_query(db, Seq::empty(), r) == Ok::<Relation, SqlError>(keep(rb, fb)),
        forall|i: int| 0 <= i < ra.len() ==> (#[trigger] ra[i]).len() == wa,
        product_rows(ra, rb) == rows,
        forall|i: int| 0 <= i < rows.len() ==> fp(#[trigger] rows[i]) == (fa(left_of(rows[i], wa)) && fb(right_of(rows[i], wa))),
    ensures
        eval_query(db, Seq::empty(), Query::Product { left: Box::new(l), right: Box::new(r) }) == Ok::<Relation, SqlError>(keep(rows, fp)),
{
    lemma_product_keep(ra, rb, fa, fb, wa);
    lemma_keep_ext(rows, |x: Row| fa(left_of(x, wa)) && fb(right_of(x, wa)), fp);
}

/// A base table is its rows, kept by any condition true on every row.
pub proof fn lemma_eval_table(db: Database, t: nat, f: spec_fn(Row) -> bool)
    requires
        t < db.tables.len(),
        forall|i: int| 0 <= i < db.tables[t as int].len() ==> f(#[trigger] db.tables[t as int][i]),
    ensures eval_query(db, Seq::empty(), Query::Table(t)) == Ok::<Relation, SqlError>(keep(db.tables[t as int], f)),
{
    lemma_keep_all(db.tables[t as int], f);
}

// ------------------------------------------------------------------------------------------ sums over relations

/// The sum of `f` over the rows.
pub open spec fn sum_of(rows: Seq<Row>, f: spec_fn(Row) -> int) -> int
    decreases rows.len(),
{
    if rows.len() == 0 {
        0
    } else {
        sum_of(rows.drop_last(), f) + f(rows.last())
    }
}

/// Per-row contribution to `gcount(g, rows, k)`.
pub open spec fn count_term(g: QuerySpec, k: Row) -> spec_fn(Row) -> int {
    |r: Row| if hit(g, r, k) { 1int } else { 0int }
}

/// Per-row contribution to `gsum(g, rows, k, j)`.
pub open spec fn sum_term(g: QuerySpec, k: Row, j: int) -> spec_fn(Row) -> int {
    |r: Row| if hit(g, r, k) { (g.arg)(j, r) } else { 0int }
}

/// Per-row contribution to `gabs(g, rows, k, j)`.
pub open spec fn abs_term(g: QuerySpec, k: Row, j: int) -> spec_fn(Row) -> int {
    |r: Row| if hit(g, r, k) { abs((g.arg)(j, r)) } else { 0int }
}

/// The group accumulators are sums of per-row contributions.
pub proof fn lemma_acc_sum_of(g: QuerySpec, rows: Seq<Row>, k: Row, j: int)
    ensures
        gcount(g, rows, k) == sum_of(rows, count_term(g, k)),
        gsum(g, rows, k, j) == sum_of(rows, sum_term(g, k, j)),
        gabs(g, rows, k, j) == sum_of(rows, abs_term(g, k, j)),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_acc_sum_of(g, rows.drop_last(), k, j);
    }
}

/// The sum over concatenated relations is the sum of the sums.
pub proof fn lemma_sum_of_append(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> int)
    ensures sum_of(a + b, f) == sum_of(a, f) + sum_of(b, f),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_sum_of_append(a, b.drop_last(), f);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

/// Functions that agree on every row have the same sum.
pub proof fn lemma_sum_of_ext(rows: Seq<Row>, f: spec_fn(Row) -> int, h: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) == h(rows[i]),
    ensures sum_of(rows, f) == sum_of(rows, h),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies f(#[trigger] ri[i]) == h(ri[i]) by {
            assert(ri[i] == rows[i]);
        }
        lemma_sum_of_ext(ri, f, h);
        assert(f(rows[rows.len() - 1]) == h(rows[rows.len() - 1]));
    }
}

/// Zero on every row: zero sum.
pub proof fn lemma_sum_of_zero(rows: Seq<Row>, f: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> f(#[trigger] rows[i]) == 0,
    ensures sum_of(rows, f) == 0,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies f(#[trigger] ri[i]) == 0 by {
            assert(ri[i] == rows[i]);
        }
        lemma_sum_of_zero(ri, f);
        assert(f(rows[rows.len() - 1]) == 0);
    }
}

/// Pointwise sum.
pub proof fn lemma_sum_of_add(rows: Seq<Row>, f: spec_fn(Row) -> int, h: spec_fn(Row) -> int)
    ensures sum_of(rows, |r: Row| f(r) + h(r)) == sum_of(rows, f) + sum_of(rows, h),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_sum_of_add(rows.drop_last(), f, h);
    }
}

/// The sum over mapped rows.
pub proof fn lemma_sum_of_map(rows: Seq<Row>, m: spec_fn(Row) -> Row, f: spec_fn(Row) -> int)
    ensures sum_of(rows.map_values(m), f) == sum_of(rows, |r: Row| f(m(r))),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        lemma_sum_of_map(ri, m, f);
        assert(rows.map_values(m).drop_last() =~= ri.map_values(m));
        assert(rows.map_values(m).last() == m(rows.last()));
    }
}

/// Removing row `i` removes its contribution.
pub proof fn lemma_sum_of_remove(s: Seq<Row>, i: int, f: spec_fn(Row) -> int)
    requires 0 <= i < s.len(),
    ensures sum_of(s, f) == sum_of(s.remove(i), f) + f(s[i]),
{
    let (a, one, b) = (s.take(i), seq![s[i]], s.skip(i + 1));
    assert(s =~= a + one + b);
    assert(s.remove(i) =~= a + b);
    lemma_sum_of_append(a + one, b, f);
    lemma_sum_of_append(a, one, f);
    lemma_sum_of_append(a, b, f);
    assert(one.drop_last() =~= Seq::<Row>::empty());
    assert(sum_of(Seq::<Row>::empty(), f) == 0);
    assert(sum_of(one, f) == f(s[i]));
}

/// The same multiset of rows gives the same sum (any order, for example a different join order or a partition).
pub proof fn lemma_sum_of_perm(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> int)
    requires a.to_multiset() == b.to_multiset(),
    ensures sum_of(a, f) == sum_of(b, f),
    decreases a.len(),
{
    a.to_multiset_ensures();
    b.to_multiset_ensures();
    if a.len() == 0 {
        assert(b.to_multiset().len() == 0);
        assert(b.len() == 0);
    } else {
        let x = a.last();
        let ai = a.drop_last();
        assert(ai.push(x) =~= a);
        ai.to_multiset_ensures();
        assert(a.to_multiset().count(x) > 0);
        assert(b.contains(x));
        let i = choose|i: int| 0 <= i < b.len() && b[i] == x;
        let bi = b.remove(i);
        assert(bi.to_multiset() =~= b.to_multiset().remove(x));
        assert(ai.to_multiset() =~= a.to_multiset().remove(x));
        lemma_sum_of_perm(ai, bi, f);
        lemma_sum_of_remove(b, i, f);
    }
}

/// Rows on which `f` is zero can be dropped by any condition true on the others.
pub proof fn lemma_sum_of_keep(rows: Seq<Row>, c: spec_fn(Row) -> bool, f: spec_fn(Row) -> int)
    requires forall|i: int| 0 <= i < rows.len() && !c(#[trigger] rows[i]) ==> f(rows[i]) == 0,
    ensures sum_of(rows, f) == sum_of(keep(rows, c), f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() && !c(#[trigger] ri[i]) implies f(ri[i]) == 0 by {
            assert(ri[i] == rows[i]);
        }
        lemma_sum_of_keep(ri, c, f);
        if c(rows.last()) {
            assert(keep(rows, c).drop_last() =~= keep(ri, c));
        } else {
            assert(f(rows[rows.len() - 1]) == 0);
        }
    }
}

/// A product in left-major order: the sum over each left row of the sum over the right rows.
pub proof fn lemma_sum_of_product(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> int)
    ensures sum_of(product_rows(a, b), f) == sum_of(a, |x: Row| sum_of(b, |y: Row| f(x + y))),
    decreases a.len(),
{
    if a.len() > 0 {
        let ai = a.drop_last();
        lemma_sum_of_product(ai, b, f);
        let m = |r: Row| a.last() + r;
        lemma_sum_of_append(product_rows(ai, b), b.map_values(m), f);
        lemma_sum_of_map(b, m, f);
        lemma_sum_of_ext(b, |r: Row| f(m(r)), |y: Row| f(a.last() + y));
    }
}

/// Exchange of two sums.
pub proof fn lemma_sum_of_swap(a: Seq<Row>, b: Seq<Row>, h: spec_fn(Row, Row) -> int)
    ensures sum_of(a, |x: Row| sum_of(b, |y: Row| h(x, y))) == sum_of(b, |y: Row| sum_of(a, |x: Row| h(x, y))),
    decreases a.len(),
{
    if a.len() > 0 {
        let ai = a.drop_last();
        let z = a.last();
        lemma_sum_of_swap(ai, b, h);
        let lf = |x: Row| sum_of(b, |y: Row| h(x, y));
        let g1 = |y: Row| sum_of(ai, |x: Row| h(x, y));
        let g2 = |y: Row| h(z, y);
        let ga = |y: Row| sum_of(a, |x: Row| h(x, y));
        assert(sum_of(a, lf) == sum_of(ai, lf) + lf(z));
        lemma_sum_of_ext(b, |y: Row| h(z, y), g2);
        assert(lf(z) == sum_of(b, g2));
        assert(sum_of(ai, lf) == sum_of(b, g1));
        lemma_sum_of_add(b, g1, g2);
        assert forall|i: int| 0 <= i < b.len() implies ga(#[trigger] b[i]) == (|r: Row| g1(r) + g2(r))(b[i]) by {
            let y = b[i];
            assert(a.drop_last() == ai);
            assert(sum_of(a, |x: Row| h(x, y)) == sum_of(ai, |x: Row| h(x, y)) + h(z, y));
        }
        lemma_sum_of_ext(b, ga, |r: Row| g1(r) + g2(r));
    } else {
        let ga = |y: Row| sum_of(a, |x: Row| h(x, y));
        assert forall|i: int| 0 <= i < b.len() implies ga(#[trigger] b[i]) == 0 by {}
        lemma_sum_of_zero(b, ga);
    }
}

/// A product in right-major order: the sum over each right row of the sum over the left rows (for example a probe
/// of the right input against an index of the left input).
pub proof fn lemma_sum_of_product_swap(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> int)
    ensures sum_of(product_rows(a, b), f) == sum_of(b, |y: Row| sum_of(a, |x: Row| f(x + y))),
{
    lemma_sum_of_product(a, b, f);
    lemma_sum_of_swap(a, b, |x: Row, y: Row| f(x + y));
    assert forall|i: int| 0 <= i < a.len() implies (|x: Row| sum_of(b, |y: Row| f(x + y)))(#[trigger] a[i])
        == (|x: Row| sum_of(b, |y: Row| (|x: Row, y: Row| f(x + y))(x, y)))(a[i]) by {
        let x = a[i];
        lemma_sum_of_ext(b, |y: Row| f(x + y), |y: Row| (|x: Row, y: Row| f(x + y))(x, y));
    }
    lemma_sum_of_ext(a, |x: Row| sum_of(b, |y: Row| f(x + y)), |x: Row| sum_of(b, |y: Row| (|x: Row, y: Row| f(x + y))(x, y)));
    assert forall|i: int| 0 <= i < b.len() implies (|y: Row| sum_of(a, |x: Row| (|x: Row, y: Row| f(x + y))(x, y)))(#[trigger] b[i])
        == (|y: Row| sum_of(a, |x: Row| f(x + y)))(b[i]) by {
        let y = b[i];
        lemma_sum_of_ext(a, |x: Row| (|x: Row, y: Row| f(x + y))(x, y), |x: Row| f(x + y));
    }
    lemma_sum_of_ext(b, |y: Row| sum_of(a, |x: Row| (|x: Row, y: Row| f(x + y))(x, y)), |y: Row| sum_of(a, |x: Row| f(x + y)));
}

} // verus!
