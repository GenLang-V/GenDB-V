//! The normal form's group accumulators over the joined rows `num x sub x pre` are `ctx::gacc` (`lemma_gsums`).
//!
//! The sum over the left-major product is reordered to `pre`-major (`link::join::lemma_sum_of_product_swap`, twice);
//! for one `pre` row `k` and one `sub` row `s` the condition splits into a part on `(s, k)` and the match of the
//! `num` row with `k`, so the sum over `num` is `acc(k)` or 0; over `sub` only the member with `k`'s adsh
//! contributes (the key of `sub`), which gives `gacc`'s term of `k`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::link::join::*;
use crate::agent::ctx::*;
use crate::agent::sem::*;
use crate::agent::nf::*;

verus! {

/// `f(0) + .. + f(n - 1)`.
pub open spec fn isum(f: spec_fn(int) -> int, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { isum(f, n - 1) + f(n - 1) }
}

/// A sum over rows given pointwise by an index function.
pub proof fn lemma_sum_of_isum(rows: Seq<Row>, f: spec_fn(Row) -> int, t: spec_fn(int) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> #[trigger] f(rows[i]) == t(i),
    ensures sum_of(rows, f) == isum(t, rows.len() as int),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] f(d[i]) == t(i) by {
            assert(d[i] == rows[i]);
        }
        lemma_sum_of_isum(d, f, t);
        assert(f(rows[rows.len() - 1]) == t(rows.len() - 1));
    }
}

pub proof fn lemma_isum_ext(f: spec_fn(int) -> int, g: spec_fn(int) -> int, n: int)
    requires forall|i: int| 0 <= i < n ==> #[trigger] f(i) == g(i),
    ensures isum(f, n) == isum(g, n),
    decreases n,
{
    if n > 0 {
        lemma_isum_ext(f, g, n - 1);
    }
}

pub proof fn lemma_isum_zero(f: spec_fn(int) -> int, n: int)
    requires forall|i: int| 0 <= i < n ==> #[trigger] f(i) == 0,
    ensures isum(f, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_isum_zero(f, n - 1);
    }
}

/// A sum with one non-zero term.
pub proof fn lemma_isum_one(f: spec_fn(int) -> int, n: int, j: int)
    requires 0 <= j < n, forall|i: int| 0 <= i < n && i != j ==> #[trigger] f(i) == 0,
    ensures isum(f, n) == f(j),
    decreases n,
{
    if j == n - 1 {
        lemma_isum_zero(f, n - 1);
    } else {
        lemma_isum_one(f, n - 1, j);
    }
}

/// `acc` as an index sum.
pub proof fn lemma_acc_isum(c: Ctx, sel: int, k: int, hi: int)
    ensures acc(c, sel, k, hi) == isum(|i: int| if nmatch(c, i, k) { wt(c, sel, i) } else { 0int }, hi),
    decreases hi,
{
    if hi > 0 {
        lemma_acc_isum(c, sel, k, hi - 1);
    }
}

/// `gacc` as an index sum.
pub proof fn lemma_gacc_isum(c: Ctx, sel: int, key: Row, hi: int)
    ensures gacc(c, sel, key, hi) == isum(|k: int| if pre_ok(c, k) && gkey(c, k) == key { acc(c, sel, k, c.n) } else { 0int }, hi),
    decreases hi,
{
    if hi > 0 {
        lemma_gacc_isum(c, sel, key, hi - 1);
    }
}

/// The key of `sub` row `s` with `pre` row `k`.
pub open spec fn skey(c: Ctx, s: int, k: int) -> Row {
    seq![Val::Text(s_name(c, s)), Val::Text(c.stmt), Val::Text(p_tag(c, k)), p_plabel_val(c, k)]
}

/// The condition on `(s, k)`: same adsh, `stmt = $2`, `fy = $3`.
pub open spec fn sk_ok(c: Ctx, s: int, k: int) -> bool {
    s_adsh(c, s) == p_adsh(c, k) && p_stmtv_s(c)[k] != 0 && p_stmt(c, k) == c.stmt && s_fyv_s(c)[s] != 0
        && s_fy_s(c)[s] as int == c.fy
}

/// The condition on `(i, k)`: same adsh, tag and version, `uom = $1`.
pub open spec fn nk_ok(c: Ctx, i: int, k: int) -> bool {
    n_adsh(c, i) == p_adsh(c, k) && n_tag(c, i) == p_tag(c, k) && n_ver(c, i) == p_ver(c, k) && n_uom(c, i) == c.uom
}

/// The sum over `num` for one `(s, k)`.
proof fn lemma_mid(c: Ctx, sel: int, key: Row, s: int, k: int, t: spec_fn(int) -> int)
    requires
        ctx_ok(c), 0 <= s < c.m, 0 <= k < c.q,
        forall|i: int| 0 <= i < c.n ==> #[trigger] t(i) == if joined_ok(c, i, s, k) && skey(c, s, k) == key { wt(c, sel, i) } else { 0int },
    ensures isum(t, c.n) == if sk_ok(c, s, k) && skey(c, s, k) == key { acc(c, sel, k, c.n) } else { 0int },
{
    let tn = |i: int| if nmatch(c, i, k) { wt(c, sel, i) } else { 0int };
    lemma_acc_isum(c, sel, k, c.n);
    if sk_ok(c, s, k) && skey(c, s, k) == key {
        assert(member(c, s));
        assert(has_member(c, p_adsh(c, k)));
        assert(pre_ok(c, k));
        assert forall|i: int| 0 <= i < c.n implies #[trigger] t(i) == tn(i) by {
            assert(joined_ok(c, i, s, k) == nmatch(c, i, k));
        }
        lemma_isum_ext(t, tn, c.n);
    } else {
        assert forall|i: int| 0 <= i < c.n implies #[trigger] t(i) == 0 by {
            if joined_ok(c, i, s, k) {
                assert(sk_ok(c, s, k));
            }
        }
        lemma_isum_zero(t, c.n);
    }
}

/// The sum over `sub` for one `pre` row `k`: `gacc`'s term of `k`.
proof fn lemma_over_sub(c: Ctx, sel: int, key: Row, k: int, t: spec_fn(int) -> int)
    requires
        ctx_ok(c), sub_key(c), 0 <= k < c.q,
        forall|s: int| 0 <= s < c.m ==> #[trigger] t(s) == if sk_ok(c, s, k) && skey(c, s, k) == key { acc(c, sel, k, c.n) } else { 0int },
    ensures isum(t, c.m) == if pre_ok(c, k) && gkey(c, k) == key { acc(c, sel, k, c.n) } else { 0int },
{
    if pre_ok(c, k) {
        let s0 = sub_for(c, p_adsh(c, k));
        lemma_sub_for(c, p_adsh(c, k));
        assert forall|s: int| 0 <= s < c.m && s != s0 implies #[trigger] t(s) == 0 by {
            if sk_ok(c, s, k) {
                assert(s_adsh(c, s) == s_adsh(c, s0));
            }
        }
        assert(sk_ok(c, s0, k));
        assert(skey(c, s0, k) == gkey(c, k));
        lemma_isum_one(t, c.m, s0);
    } else {
        assert forall|s: int| 0 <= s < c.m implies #[trigger] t(s) == 0 by {
            if sk_ok(c, s, k) {
                assert(member(c, s));
                assert(has_member(c, p_adsh(c, k)));
            }
        }
        lemma_isum_zero(t, c.m);
    }
}

/// A per-joined-row term given by its source rows sums, over the joined relation, to `gacc`.
#[verifier::spinoff_prover]
pub proof fn lemma_jsum(db: Database, c: Ctx, sel: int, key: Row, f: spec_fn(Row) -> int)
    requires
        db_ok(db, c),
        forall|i: int, s: int, k: int| 0 <= i < c.n && 0 <= s < c.m && 0 <= k < c.q ==>
            #[trigger] f(jrow(c, i, s, k)) == if joined_ok(c, i, s, k) && skey(c, s, k) == key { wt(c, sel, i) } else { 0int },
    ensures sum_of(jrows(db), f) == gacc(c, sel, key, c.q),
{
    let nn = db.tables[1];
    let ss = db.tables[0];
    let pp = db.tables[3];
    let ns = product_rows(nn, ss);
    lemma_sum_of_product_swap(ns, pp, f);
    let outer = |y: Row| sum_of(ns, |x: Row| f(x + y));
    let ot = |k: int| if pre_ok(c, k) && gkey(c, k) == key { acc(c, sel, k, c.n) } else { 0int };
    assert forall|k: int| 0 <= k < pp.len() implies #[trigger] outer(pp[k]) == ot(k) by {
        let y = pp[k];
        assert(y == prow(c, k));
        let h = |x: Row| f(x + y);
        lemma_sum_of_product_swap(nn, ss, h);
        let mid = |sy: Row| sum_of(nn, |nx: Row| h(nx + sy));
        let mt = |s: int| if sk_ok(c, s, k) && skey(c, s, k) == key { acc(c, sel, k, c.n) } else { 0int };
        assert forall|s: int| 0 <= s < ss.len() implies #[trigger] mid(ss[s]) == mt(s) by {
            let sy = ss[s];
            assert(sy == srow(c, s));
            let it = |i: int| f(jrow(c, i, s, k));
            let hs = |nx: Row| h(nx + sy);
            assert forall|i: int| 0 <= i < nn.len() implies #[trigger] hs(nn[i]) == it(i) by {
                assert(nn[i] == nrow(c, i));
                assert(nn[i] + sy + y == jrow(c, i, s, k));
            }
            lemma_sum_of_isum(nn, hs, it);
            lemma_mid(c, sel, key, s, k, it);
        }
        lemma_sum_of_isum(ss, mid, mt);
        lemma_over_sub(c, sel, key, k, mt);
        assert(outer(y) == sum_of(ns, h));
    }
    lemma_sum_of_isum(pp, outer, ot);
    lemma_gacc_isum(c, sel, key, c.q);
    lemma_isum_ext(ot, |k: int| if pre_ok(c, k) && gkey(c, k) == key { acc(c, sel, k, c.n) } else { 0int }, c.q);
}

/// `hit` of a joined row: `joined_ok` with the key of its `sub` and `pre` rows.
proof fn lemma_hit_cells(c: Ctx, i: int, s: int, k: int, key: Row)
    ensures hit(qs(c), jrow(c, i, s, k), key) == (joined_ok(c, i, s, k) && skey(c, s, k) == key),
{
    lemma_qual_cells(c, i, s, k);
    lemma_row_key(c, i, s, k);
    if joined_ok(c, i, s, k) {
        assert(((qs(c)).key)(jrow(c, i, s, k)) =~= skey(c, s, k));
    }
}

/// The normal form's accumulators over the joined rows are `gacc`.
pub proof fn lemma_gsums(db: Database, c: Ctx, key: Row)
    requires db_ok(db, c),
    ensures
        gcount(qs(c), jrows(db), key) == gacc(c, 0, key, c.q),
        gsum(qs(c), jrows(db), key, 0) == gacc(c, 1, key, c.q),
        gabs(qs(c), jrows(db), key, 0) == gacc(c, 2, key, c.q),
{
    let g = qs(c);
    let jr = jrows(db);
    lemma_acc_sum_of(g, jr, key, 0);
    assert forall|i: int, s: int, k: int| 0 <= i < c.n && 0 <= s < c.m && 0 <= k < c.q implies
        #[trigger] (count_term(g, key))(jrow(c, i, s, k)) == if joined_ok(c, i, s, k) && skey(c, s, k) == key { wt(c, 0, i) } else { 0int } by {
        lemma_hit_cells(c, i, s, k, key);
    }
    assert forall|i: int, s: int, k: int| 0 <= i < c.n && 0 <= s < c.m && 0 <= k < c.q implies
        #[trigger] (sum_term(g, key, 0))(jrow(c, i, s, k)) == if joined_ok(c, i, s, k) && skey(c, s, k) == key { wt(c, 1, i) } else { 0int } by {
        lemma_hit_cells(c, i, s, k, key);
        lemma_jcells(c, i, s, k);
    }
    assert forall|i: int, s: int, k: int| 0 <= i < c.n && 0 <= s < c.m && 0 <= k < c.q implies
        #[trigger] (abs_term(g, key, 0))(jrow(c, i, s, k)) == if joined_ok(c, i, s, k) && skey(c, s, k) == key { wt(c, 2, i) } else { 0int } by {
        lemma_hit_cells(c, i, s, k, key);
        lemma_jcells(c, i, s, k);
    }
    lemma_jsum(db, c, 0, key, count_term(g, key));
    lemma_jsum(db, c, 1, key, sum_term(g, key, 0));
    lemma_jsum(db, c, 2, key, abs_term(g, key, 0));
}

} // verus!
