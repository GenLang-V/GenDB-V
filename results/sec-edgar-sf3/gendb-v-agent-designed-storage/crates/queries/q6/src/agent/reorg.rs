//! The group accumulators of the normal form (`gcount`, `gsum`, `gabs` over `R = (num x sub) x pre`, canonical
//! rows) as triple sums over the stored positions: `sub` row `j` outermost, stored `pre` row `l`, stored `num` row
//! `i` innermost, of a parts-level cell (`cell`: the weight of triple `(i, j, l)` when it qualifies with key `k`).
//! Steps: the product decomposition of `link::join`, the storages' stored-order permutations (sums are
//! order-independent), and two exchanges of summation order.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::numeric::abs;
use crate::spec::relation::product_rows;
use crate::gendb_entry::stores::StoresView;
use crate::link::query::*;
use crate::link::join::*;
use crate::stores::num::interface as ni;
use crate::stores::pre::interface as pi;
use crate::agent::meaning::*;
use crate::agent::views::*;
use crate::agent::common::sums::*;

verus! {

/// Weight of one `num` row: 1 (count), its value (sum) or its absolute value (mass).
pub open spec fn wt(sv: StoresView, wsel: int, i: int) -> int {
    if wsel == 0 { 1 } else if wsel == 1 { n_val(sv, i) } else { abs(n_val(sv, i)) }
}

/// The weight of triple `(i, j, l)` in group `k`.
pub open spec fn cell(sv: StoresView, ps: Seq<Literal>, k: Row, wsel: int, i: int, j: int, l: int) -> int {
    if pq(sv, ps, i, j, l) && pkey(sv, i, j, l) == k { wt(sv, wsel, i) } else { 0 }
}

/// Sum over the stored `num` rows of one `(j, l)`.
pub open spec fn cell_i(sv: StoresView, ps: Seq<Literal>, k: Row, wsel: int, j: int, l: int) -> int {
    isum(0, n_count(sv), |i: int| cell(sv, ps, k, wsel, i, j, l))
}

/// Sum over the stored `pre` rows of one `sub` row `j`.
pub open spec fn cell_l(sv: StoresView, ps: Seq<Literal>, k: Row, wsel: int, j: int) -> int {
    isum(0, p_count(sv), |l: int| cell_i(sv, ps, k, wsel, j, l))
}

/// The triple sum.
pub open spec fn tri(sv: StoresView, ps: Seq<Literal>, k: Row, wsel: int) -> int {
    isum(0, s_count(sv), |j: int| cell_l(sv, ps, k, wsel, j))
}

pub proof fn lemma_sum_of_isum(rows: Seq<Row>, f: spec_fn(Row) -> int)
    ensures sum_of(rows, f) == isum(0, rows.len() as int, |i: int| f(rows[i])),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let init = rows.drop_last();
        lemma_sum_of_isum(init, f);
        lemma_isum_ext(0, init.len() as int, |i: int| f(init[i]), |i: int| f(rows[i]));
    }
}

pub open spec fn sn_seq(sv: StoresView, db: Database) -> Seq<Row> {
    Seq::new(n_count(sv) as nat, |i: int| sn(sv, db, i))
}

pub open spec fn sp_seq(sv: StoresView, db: Database) -> Seq<Row> {
    Seq::new(p_count(sv) as nat, |l: int| sp(sv, db, l))
}

/// The tables in stored order have the tables' multisets.
proof fn lemma_stored_perms(sv: StoresView, db: Database)
    requires base(sv, db),
    ensures
        sn_seq(sv, db).to_multiset() == db.tables[1].to_multiset(),
        sp_seq(sv, db).to_multiset() == db.tables[3].to_multiset(),
        db.tables[1].len() == n_count(sv),
        db.tables[3].len() == p_count(sv),
        db.tables[0].len() == s_count(sv),
{
    lemma_stored_tables(db);
    let rn = crate::stores::num::declaration::stored_relations(db);
    let rp = crate::stores::pre::declaration::stored_relations(db);
    ni::lemma_stored_rows_multiset(sv.num, rn);
    pi::lemma_stored_rows_multiset(sv.pre, rp);
    assert(Seq::new(ni::row_count(sv.num) as nat, |i: int| ni::stored_row(sv.num, rn, i)) =~= sn_seq(sv, db));
    assert(Seq::new(pi::row_count(sv.pre) as nat, |i: int| pi::stored_row(sv.pre, rp, i)) =~= sp_seq(sv, db));
    let rs = crate::stores::sub::declaration::stored_relations(db);
    assert(crate::stores::sub::interface::represents(sv.sub, rs));
}

/// The inner sum over `pre` rows, in stored order.
pub open spec fn in_p(sv: StoresView, db: Database, f: spec_fn(Row) -> int, y: Row) -> int {
    isum(0, p_count(sv), |l: int| f(y + sp(sv, db, l)))
}

/// The middle sum over `sub` rows.
pub open spec fn in_s(sv: StoresView, db: Database, f: spec_fn(Row) -> int, a: Row) -> int {
    isum(0, s_count(sv), |j: int| in_p(sv, db, f, a + db.tables[0][j]))
}

/// Any sum over `R` as a triple sum over stored positions, `num` row outermost.
proof fn lemma_sum_r(sv: StoresView, db: Database, f: spec_fn(Row) -> int)
    requires base(sv, db),
    ensures sum_of(joined(db), f) == isum(0, n_count(sv), |i: int| in_s(sv, db, f, sn(sv, db, i))),
{
    lemma_stored_perms(sv, db);
    let (nt, st, pt) = (db.tables[1], db.tables[0], db.tables[3]);
    let ns = product_rows(nt, st);
    // (num x sub) x pre
    lemma_sum_of_product(ns, pt, f);
    let gp = |y: Row| sum_of(pt, |c: Row| f(y + c));
    lemma_sum_of_product(nt, st, gp);
    // the pre sum in stored order
    let hp = |y: Row| in_p(sv, db, f, y);
    assert forall|y: Row| #[trigger] gp(y) == hp(y) by {
        lemma_sum_of_perm(pt, sp_seq(sv, db), |c: Row| f(y + c));
        lemma_sum_of_isum(sp_seq(sv, db), |c: Row| f(y + c));
        lemma_isum_ext(0, p_count(sv), |l: int| (|c: Row| f(y + c))(sp_seq(sv, db)[l]), |l: int| f(y + sp(sv, db, l)));
    }
    // the sub sum as a range sum
    let hs = |a: Row| sum_of(st, |b: Row| gp(a + b));
    let hs2 = |a: Row| in_s(sv, db, f, a);
    assert forall|a: Row| #[trigger] hs(a) == hs2(a) by {
        lemma_sum_of_isum(st, |b: Row| gp(a + b));
        lemma_isum_ext(0, s_count(sv), |j: int| (|b: Row| gp(a + b))(st[j]), |j: int| in_p(sv, db, f, a + st[j]));
    }
    lemma_sum_of_ext(nt, |a: Row| sum_of(st, |b: Row| gp(a + b)), hs2);
    // the num sum in stored order
    lemma_sum_of_perm(nt, sn_seq(sv, db), hs2);
    lemma_sum_of_isum(sn_seq(sv, db), hs2);
    lemma_isum_ext(0, n_count(sv), |i: int| hs2(sn_seq(sv, db)[i]), |i: int| in_s(sv, db, f, sn(sv, db, i)));
    assert(sum_of(ns, |y: Row| sum_of(pt, |c: Row| f(y + c))) == sum_of(nt, |a: Row| sum_of(st, |b: Row| gp(a + b))));
}

/// A row function equal to the cell on every stored triple.
pub open spec fn agrees(sv: StoresView, db: Database, ps: Seq<Literal>, k: Row, wsel: int, f: spec_fn(Row) -> int) -> bool {
    forall|i: int, j: int, l: int| 0 <= i < n_count(sv) && 0 <= j < s_count(sv) && 0 <= l < p_count(sv) ==>
        #[trigger] f(sn(sv, db, i) + db.tables[0][j] + sp(sv, db, l)) == cell(sv, ps, k, wsel, i, j, l)
}

/// The `num` sum of one `j` over the `pre` sums.
pub open spec fn sum_over_i(sv: StoresView, ps: Seq<Literal>, k: Row, wsel: int, j: int) -> int {
    isum(0, n_count(sv), |i: int| cell_l_i(sv, ps, k, wsel, i, j))
}

/// The `pre` sum of one `(i, j)` over the cells.
pub open spec fn cell_l_i(sv: StoresView, ps: Seq<Literal>, k: Row, wsel: int, i: int, j: int) -> int {
    isum(0, p_count(sv), |l: int| cell(sv, ps, k, wsel, i, j, l))
}

/// The `sub` sum of one `i` over the `pre` sums.
pub open spec fn sum_over_j(sv: StoresView, ps: Seq<Literal>, k: Row, wsel: int, i: int) -> int {
    isum(0, s_count(sv), |j: int| cell_l_i(sv, ps, k, wsel, i, j))
}

proof fn lemma_tri_step1(sv: StoresView, db: Database, ps: Seq<Literal>, k: Row, wsel: int, f: spec_fn(Row) -> int)
    requires base(sv, db), agrees(sv, db, ps, k, wsel, f),
    ensures
        isum(0, n_count(sv), |i: int| in_s(sv, db, f, sn(sv, db, i)))
            == isum(0, n_count(sv), |i: int| sum_over_j(sv, ps, k, wsel, i)),
{
    let (nn, ns, np) = (n_count(sv), s_count(sv), p_count(sv));
    assert forall|i: int| 0 <= i < nn implies #[trigger] in_s(sv, db, f, sn(sv, db, i)) == sum_over_j(sv, ps, k, wsel, i) by {
        assert forall|j: int| 0 <= j < ns implies #[trigger] in_p(sv, db, f, sn(sv, db, i) + db.tables[0][j])
            == cell_l_i(sv, ps, k, wsel, i, j) by {
            assert forall|l: int| 0 <= l < np implies #[trigger] f(sn(sv, db, i) + db.tables[0][j] + sp(sv, db, l))
                == cell(sv, ps, k, wsel, i, j, l) by {
            }
            lemma_isum_ext(0, np, |l: int| f(sn(sv, db, i) + db.tables[0][j] + sp(sv, db, l)),
                |l: int| cell(sv, ps, k, wsel, i, j, l));
        }
        lemma_isum_ext(0, ns, |j: int| in_p(sv, db, f, sn(sv, db, i) + db.tables[0][j]),
            |j: int| cell_l_i(sv, ps, k, wsel, i, j));
    }
    lemma_isum_ext(0, nn, |i: int| in_s(sv, db, f, sn(sv, db, i)), |i: int| sum_over_j(sv, ps, k, wsel, i));
}

proof fn lemma_tri_step2(sv: StoresView, ps: Seq<Literal>, k: Row, wsel: int)
    ensures
        isum(0, n_count(sv), |i: int| sum_over_j(sv, ps, k, wsel, i))
            == isum(0, s_count(sv), |j: int| sum_over_i(sv, ps, k, wsel, j)),
{
    let (nn, ns) = (n_count(sv), s_count(sv));
    let h3 = |i: int, j: int| cell_l_i(sv, ps, k, wsel, i, j);
    lemma_isum_swap(0, nn, 0, ns, h3);
    assert forall|i: int| 0 <= i < nn implies #[trigger] sum_over_j(sv, ps, k, wsel, i) == isum(0, ns, |j: int| h3(i, j)) by {
        lemma_isum_ext(0, ns, |j: int| cell_l_i(sv, ps, k, wsel, i, j), |j: int| h3(i, j));
    }
    lemma_isum_ext(0, nn, |i: int| sum_over_j(sv, ps, k, wsel, i), |i: int| isum(0, ns, |j: int| h3(i, j)));
    assert forall|j: int| 0 <= j < ns implies #[trigger] sum_over_i(sv, ps, k, wsel, j) == isum(0, nn, |i: int| h3(i, j)) by {
        lemma_isum_ext(0, nn, |i: int| cell_l_i(sv, ps, k, wsel, i, j), |i: int| h3(i, j));
    }
    lemma_isum_ext(0, ns, |j: int| sum_over_i(sv, ps, k, wsel, j), |j: int| isum(0, nn, |i: int| h3(i, j)));
}

proof fn lemma_tri_step3(sv: StoresView, ps: Seq<Literal>, k: Row, wsel: int, j: int)
    ensures sum_over_i(sv, ps, k, wsel, j) == cell_l(sv, ps, k, wsel, j),
{
    let (nn, np) = (n_count(sv), p_count(sv));
    let c3 = |i: int, l: int| cell(sv, ps, k, wsel, i, j, l);
    lemma_isum_swap(0, nn, 0, np, c3);
    assert forall|i: int| 0 <= i < nn implies #[trigger] cell_l_i(sv, ps, k, wsel, i, j) == isum(0, np, |l: int| c3(i, l)) by {
        lemma_isum_ext(0, np, |l: int| cell(sv, ps, k, wsel, i, j, l), |l: int| c3(i, l));
    }
    lemma_isum_ext(0, nn, |i: int| cell_l_i(sv, ps, k, wsel, i, j), |i: int| isum(0, np, |l: int| c3(i, l)));
    assert forall|l: int| 0 <= l < np implies #[trigger] cell_i(sv, ps, k, wsel, j, l) == isum(0, nn, |i: int| c3(i, l)) by {
        lemma_isum_ext(0, nn, |i: int| cell(sv, ps, k, wsel, i, j, l), |i: int| c3(i, l));
    }
    lemma_isum_ext(0, np, |l: int| cell_i(sv, ps, k, wsel, j, l), |l: int| isum(0, nn, |i: int| c3(i, l)));
}

/// The triple sum, reordered.
proof fn lemma_sum_r_tri(sv: StoresView, db: Database, ps: Seq<Literal>, k: Row, wsel: int, f: spec_fn(Row) -> int)
    requires base(sv, db), agrees(sv, db, ps, k, wsel, f),
    ensures sum_of(joined(db), f) == tri(sv, ps, k, wsel),
{
    lemma_sum_r(sv, db, f);
    lemma_tri_step1(sv, db, ps, k, wsel, f);
    lemma_tri_step2(sv, ps, k, wsel);
    assert forall|j: int| 0 <= j < s_count(sv) implies #[trigger] sum_over_i(sv, ps, k, wsel, j) == cell_l(sv, ps, k, wsel, j) by {
        lemma_tri_step3(sv, ps, k, wsel, j);
    }
    lemma_isum_ext(0, s_count(sv), |j: int| sum_over_i(sv, ps, k, wsel, j), |j: int| cell_l(sv, ps, k, wsel, j));
}

/// The normal form's accumulators of group `k` are the triple sums of the cells.
pub proof fn lemma_acc_tri(sv: StoresView, db: Database, ps: Seq<Literal>, k: Row)
    requires base(sv, db),
    ensures
        gcount(qspec(ps), joined(db), k) == tri(sv, ps, k, 0),
        gsum(qspec(ps), joined(db), k, 0) == tri(sv, ps, k, 1),
        gabs(qspec(ps), joined(db), k, 0) == tri(sv, ps, k, 2),
{
    let g = qspec(ps);
    lemma_acc_sum_of(g, joined(db), k, 0);
    lemma_stored_perms(sv, db);
    assert(agrees(sv, db, ps, k, 0, count_term(g, k))) by {
        assert forall|i: int, j: int, l: int| 0 <= i < n_count(sv) && 0 <= j < s_count(sv) && 0 <= l < p_count(sv) implies
            #[trigger] count_term(g, k)(sn(sv, db, i) + db.tables[0][j] + sp(sv, db, l)) == cell(sv, ps, k, 0, i, j, l) by {
            lemma_joined_row(sv, db, ps, i, j, l);
        }
    }
    assert(agrees(sv, db, ps, k, 1, sum_term(g, k, 0))) by {
        assert forall|i: int, j: int, l: int| 0 <= i < n_count(sv) && 0 <= j < s_count(sv) && 0 <= l < p_count(sv) implies
            #[trigger] sum_term(g, k, 0)(sn(sv, db, i) + db.tables[0][j] + sp(sv, db, l)) == cell(sv, ps, k, 1, i, j, l) by {
            lemma_joined_row(sv, db, ps, i, j, l);
        }
    }
    assert(agrees(sv, db, ps, k, 2, abs_term(g, k, 0))) by {
        assert forall|i: int, j: int, l: int| 0 <= i < n_count(sv) && 0 <= j < s_count(sv) && 0 <= l < p_count(sv) implies
            #[trigger] abs_term(g, k, 0)(sn(sv, db, i) + db.tables[0][j] + sp(sv, db, l)) == cell(sv, ps, k, 2, i, j, l) by {
            lemma_joined_row(sv, db, ps, i, j, l);
        }
    }
    lemma_sum_r_tri(sv, db, ps, k, 0, count_term(g, k));
    lemma_sum_r_tri(sv, db, ps, k, 1, sum_term(g, k, 0));
    lemma_sum_r_tri(sv, db, ps, k, 2, abs_term(g, k, 0));
}

} // verus!
