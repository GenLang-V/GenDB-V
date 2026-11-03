//! TPC-H Q5 (revenue per nation of one region in one year of orders) over the storages `li_okruns` (storage
//! `facts`' lineitem and orders, orders stored by date with lineitem co-clustered, plus the l_orderkey run starts;
//! `facts` is listed for its interface only), `custpart` (customer) and `suppliers` (supplier, nation, region).
//!
//! Plan: the qualifying nations of region `$1` and their groups (distinct names) on the calling thread
//! (`dims`); dense-key checks of customer and supplier keys (`common::dense`); the stored orders range whose date
//! zone maps meet `[$2, $2 + 1 year)` (`plan`); per worker one range of orders (`runner`): when the l_orderkey runs
//! of its two ends belong to their orders, the live-order kernel (`live`: batches of live orders, their runs found
//! through the run starts, dead orders' rows skipped), else the merge scan (`kernel`); the groups with a qualifying
//! row by descending revenue (`output`).
//!
//! Proof: the statement's body is the normal form's result over the product of the stored relations (`sqlink`);
//! its accumulators are sums over lineitem rows of a multiplicity (`algebra`), which the kernel evaluates by key
//! lookups under the declared primary keys (`lookup`, `chain`). An absolute revenue mass beyond `i128::MAX` is
//! Capacity (`capacity`); a failing `$2 + INTERVAL '1' YEAR` is that SQL error on a non-empty product.
use vstd::prelude::*;
pub mod common;
pub mod q5spec;
pub mod sqlrow;
pub mod sqlink;
pub mod algebra;
pub mod lookup;
pub mod chain;
pub mod cmap;
pub mod kernel;
pub mod live;
pub mod hits;
pub mod views_facts;
pub mod views_custpart;
pub mod views_suppliers;
pub mod world;
pub mod setup;
pub mod dims;
pub mod plan;
pub mod runner;
pub mod totals;
pub mod output;
pub mod capacity;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::spec::datetime::*;
use crate::spec::typing::*;
use crate::spec::limits::*;
use crate::spec::relation::*;
use crate::spec::eval::eval_expr;
use crate::schema::schema_spec;
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok, capacity_domain};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::{param_domain, param_typed, query_spec_at};
use crate::exec::value::EVal;
use crate::exec::datetime::{date_from_civil_exec, date_to_ts_exec, ts_add_interval_exec, floor_divmod};
use crate::link::query::*;
use crate::link::join::*;
use crate::link::expr::i128_max;
use crate::agent::q5spec::*;
use crate::agent::sqlrow::*;
use crate::agent::sqlink::*;
use crate::agent::lookup::keys_unique;
use crate::agent::chain::*;
use crate::agent::kernel::*;
use crate::agent::world::*;
use crate::agent::setup::*;
use crate::agent::dims::*;
use crate::agent::plan::*;
use crate::agent::runner::*;
use crate::agent::totals::*;
use crate::agent::output::*;
use crate::agent::capacity::*;
use crate::agent::cmap::build_maps;

verus! {

/// The date parameter is a valid civil date whose day number fits `i32`.
proof fn lemma_date_param(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        ps[1] is Date,
        1 <= ps[1]->Date_m <= 12,
        1 <= ps[1]->Date_d <= 31,
        i32::MIN <= date_from_civil(ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d) <= i32::MAX,
{
    let (y, m, d) = (ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d);
    assert(valid_ymd(y, m, d));
    assert(date_valid(date_from_civil(y, m, d)));
}

/// `hi_day` is the first day whose midnight is at or after `hi`.
proof fn lemma_hi_day(hi: int, q: int, r: int)
    requires q * usecs_per_day() + r == hi - 1, 0 <= r < usecs_per_day(),
    ensures (q + 1) * usecs_per_day() >= hi, q * usecs_per_day() < hi,
{
    let u = usecs_per_day();
    assert((q + 1) * u == q * u + u) by (nonlinear_arith);
}

/// The FROM product has a row exactly when every table has one.
proof fn lemma_full_len(db: Database, rs: Rels)
    requires db.tables.len() == 8, rels_of_db(db) == rs,
    ensures
        (full_rows(db).len() > 0) == (rs.c.len() > 0 && rs.o.len() > 0 && rs.l.len() > 0 && rs.s.len() > 0
            && rs.n.len() > 0 && rs.r.len() > 0),
{
    let t = db.tables;
    lemma_joined6(t, tids());
    let p1 = product_rows(t[2], t[1]);
    let p2 = product_rows(p1, t[0]);
    let p3 = product_rows(p2, t[5]);
    let p4 = product_rows(p3, t[6]);
    lemma_product_index(t[2], t[1]);
    lemma_product_index(p1, t[0]);
    lemma_product_index(p2, t[5]);
    lemma_product_index(p3, t[6]);
    lemma_product_index(p4, t[7]);
    let (a, b, c, d, e, f) = (t[2].len() as int, t[1].len() as int, t[0].len() as int, t[5].len() as int,
        t[6].len() as int, t[7].len() as int);
    assert(rs.c.len() == a && rs.o.len() == b && rs.l.len() == c && rs.s.len() == d && rs.n.len() == e && rs.r.len() == f);
    assert((a * b * c * d * e * f > 0) == (a > 0 && b > 0 && c > 0 && d > 0 && e > 0 && f > 0)) by (nonlinear_arith)
        requires a >= 0, b >= 0, c >= 0, d >= 0, e >= 0, f >= 0;
}

/// An empty body has the empty output as its allowed output.
proof fn lemma_empty_ok(db: Database, oq: OrderedQuery)
    requires denote_body(db, oq) == Ok::<Relation, SqlError>(Seq::<Row>::empty()),
    ensures ordered_ok(db, oq, Ok::<Relation, SqlError>(view_rows(Seq::<Vec<EVal>>::empty()))),
{
    let p = Seq::<Row>::empty();
    assert(view_rows(Seq::<Vec<EVal>>::empty()) =~= p);
    assert(slice_rows(p, oq.offset, oq.limit) =~= p);
    assert(sorted_by(oq.keys, p));
}

/// The kernel context built from the readers is well formed.
proof fn lemma_ctx_wf(t: ScanCtx, lc: LineCols, oc: OrdCols, cc: CustCols, sc: SuppCols, rs: Rels, prm: Prm,
    cflag: bool, sv_l: Seq<Row>, sv_o: Seq<Row>)
    requires
        line_cols_ok(lc, rs), ord_cols_ok(oc, rs), cust_cols_ok(cc, rs),
        supp_cols_ok(sc, rs, Seq::<u32>::empty(), Seq::<u64>::empty()),
        keys_unique(rs.o), keys_unique(rs.c), keys_unique(rs.s), keys_unique(rs.n),
        lc.lrows@ == sv_l, oc.orows@ == sv_o,
        cflag ==> crate::stores::facts::interface::cluster::clustered(sv_l, sv_o),
        t.lk_c == lc.lk_c && t.lk_b == lc.lk_b && t.ls_c == lc.ls_c && t.ls_b == lc.ls_b,
        t.le_c == lc.le_c && t.le_b == lc.le_b && t.ld_c == lc.ld_c && t.ld_b == lc.ld_b,
        t.ok_c == oc.ok_c && t.ok_b == oc.ok_b && t.oc_c == oc.oc_c && t.oc_b == oc.oc_b,
        t.od_c == oc.od_c && t.od_b == oc.od_b && t.oi_c == oc.oi_c && t.oi_b == oc.oi_b && t.okind == oc.okind,
        t.ck_c == cc.ck_c && t.ck_b == cc.ck_b && t.ckind == cc.ckind && t.cn_c == cc.cn_c && t.cn_b == cc.cn_b,
        t.sk_c == sc.sk_c && t.sk_b == sc.sk_b && t.skind == sc.skind && t.sn_c == sc.sn_c && t.sn_b == sc.sn_b,
        t.e32 == cc.e32 && t.e64 == cc.e64, t.st == lc.st, t.st_n == lc.st@.len(),
        t.n_l == lc.n_l && t.n_o == oc.n_o && t.n_c == cc.n_c && t.n_s == sc.n_s,
        t.ldiv == lc.div && t.odiv == oc.div && t.cdiv == cc.div && t.sdiv == sc.div,
        t.ok_exact == oc.exact && t.ck_exact == cc.exact && t.sk_exact == sc.exact,
        t.clustered == cflag,
        t.cdense ==> forall|c: int| 0 <= c < t.n_c ==> #[trigger] crate::agent::common::forview::fv32(t.ck_c@, t.ck_b@, t.cdiv.bs as int, c) == c + 1,
        t.sdense ==> forall|s: int| 0 <= s < t.n_s ==> #[trigger] crate::agent::common::forview::fv32(t.sk_c@, t.sk_b@, t.sdiv.bs as int, s) == s + 1,
        t.rs@ == rs, t.prm@ == prm, t.lrows@ == sv_l, t.orows@ == sv_o, t.omap@ == oc.omap@,
        t.lo_day as int == prm.lo,
        t.hi_day as int * usecs_per_day() >= prm.hi,
        (t.hi_day as int - 1) * usecs_per_day() < prm.hi,
    ensures t.wf(),
{
    assert forall|j: int| 0 <= j < t.n_l implies #[trigger] t.lrow_ok(j) by {
        assert(line_row_ok(lc, j));
    }
    assert forall|p: int| 0 <= p < t.n_o implies #[trigger] t.orow_ok(p) by {
        assert(ord_row_ok(oc, rs, p));
    }
    assert forall|c: int| 0 <= c < t.n_c implies #[trigger] t.crow_ok(c) by {
        assert(cust_row_ok(cc, rs, c));
    }
    assert forall|s: int| 0 <= s < t.n_s implies #[trigger] t.srow_ok(s) by {
        assert(supp_row_ok(sc, rs, s));
    }
    assert forall|i: int| 0 <= i < rs.o.len() implies #[trigger] t.o_covered(i) by {
        assert(ord_cov(oc, i));
    }
}

/// The scan totals are the normal form's accumulators; every group key is a computed group; inside the mass
/// condition the groups are within `group_caps`.
proof fn lemma_totals_nf(t: ScanCtx, tot: Totals, rs: Rels, prm: Prm, qkey: Seq<i64>, qgrp: Seq<usize>)
    requires
        t.wf(), t.rs@ == rs, t.prm@ == prm,
        rels_widths(rs),
        t.lrows@.to_multiset() == rs.l.to_multiset(),
        qlist_ok(rs, prm, qkey, qgrp, t.qrow@, t.gnames@),
        totals_on(t, tot, 0, t.n_l as int),
    ensures
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] gabs(q5_g(prm), xs_of(rs), gkey(t.gnames@, gi), 0) == t.lsum(gi, 2, 0, t.n_l as int),
        (forall|gi: int| 0 <= gi < t.gnames@.len() ==> !#[trigger] tot.ovf@[gi]) ==> {
            &&& groups_nf(q5_g(prm), xs_of(rs), t.gnames@, tot.cnt@, tot.sum@)
            &&& group_caps(q5_g(prm), xs_of(rs))
        },
{
    let g = q5_g(prm);
    let xs = xs_of(rs);
    let gn = t.gnames@;
    let n = t.n_l as int;
    assert forall|gi: int| 0 <= gi < gn.len() implies
        #[trigger] gcount(g, xs, gkey(gn, gi)) == t.lsum(gi, 0, 0, n)
        && gsum(g, xs, gkey(gn, gi), 0) == t.lsum(gi, 1, 0, n)
        && gabs(g, xs, gkey(gn, gi), 0) == t.lsum(gi, 2, 0, n) by {
        lemma_acc_nf(rs, prm, gkey(gn, gi));
        lemma_acc_rows(rs, t.lrows@, prm, gkey(gn, gi), 0);
        lemma_acc_rows(rs, t.lrows@, prm, gkey(gn, gi), 1);
        lemma_acc_rows(rs, t.lrows@, prm, gkey(gn, gi), 2);
    }
    assert forall|gi: int| 0 <= gi < gn.len() implies
        #[trigger] gabs(g, xs, gkey(gn, gi), 0) == t.lsum(gi, 2, 0, n) by {
        assert(gcount(g, xs, gkey(gn, gi)) == t.lsum(gi, 0, 0, n));
    }
    if forall|gi: int| 0 <= gi < gn.len() ==> !#[trigger] tot.ovf@[gi] {
        assert forall|gi: int| 0 <= gi < gn.len() implies #[trigger] gcount(g, xs, gkey(gn, gi)) == tot.cnt@[gi]
            && gsum(g, xs, gkey(gn, gi), 0) == tot.sum@[gi] by {
            assert(gcount(g, xs, gkey(gn, gi)) == t.lsum(gi, 0, 0, n));
            assert(t.acc_ok(gi, 0, n, tot.cnt@[gi], tot.sum@[gi], tot.abs@[gi], tot.ovf@[gi]));
            assert(!tot.ovf@[gi]);
        }
        assert forall|k: Row| #[trigger] gcount(g, xs, k) > 0 implies exists|gi: int| 0 <= gi < gn.len() && k == #[trigger] gkey(gn, gi) by {
            lemma_group_witness(rs, prm, qkey, qgrp, t.qrow@, gn, k);
        }
        assert(groups_nf(g, xs, gn, tot.cnt@, tot.sum@));
        assert forall|k: Row, j: int| 0 <= j < g.aggs.len() && !(g.aggs[j] is Count) implies #[trigger] gabs(g, xs, k, j) <= i128_max() by {
            assert(j == 0);
            if gcount(g, xs, k) > 0 {
                lemma_group_witness(rs, prm, qkey, qgrp, t.qrow@, gn, k);
                let gi = choose|gi: int| 0 <= gi < gn.len() && k == #[trigger] gkey(gn, gi);
                assert(gcount(g, xs, gkey(gn, gi)) == t.lsum(gi, 0, 0, n));
                assert(t.acc_ok(gi, 0, n, tot.cnt@[gi], tot.sum@[gi], tot.abs@[gi], tot.ovf@[gi]));
                assert(!tot.ovf@[gi]);
            } else {
                lemma_zero_count(g, xs, k, 0);
            }
        }
        assert(group_caps(g, xs));
    }
}

/// Rows answer: inside `group_caps`, an allowed output of the normal form is an allowed output of the statement
/// for every database bound to the parts.
proof fn lemma_answer_rows(sv: crate::gendb_entry::stores::StoresView, ps: Seq<Literal>, rs: Rels, part: Seq<Row>,
    psupp: Seq<Row>, prm: Prm, t0: int, out: Seq<Vec<EVal>>)
    requires
        parts_rep(sv, rs, part, psupp),
        param_domain(ps),
        prm == prm_of(ps, prm.hi),
        date_to_ts(prm.lo) == Ok::<int, SqlError>(t0),
        ts_add_interval(t0, 12, 0, 0) == Ok::<int, SqlError>(prm.hi),
        group_caps(q5_g(prm), xs_of(rs)),
        result_ok(q5_g(prm), q5_order(), 0, None, xs_of(rs), view_rows(out)),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(out))),
{
    lemma_query_shape(ps);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(out))) by {
        lemma_rels_determined(sv, db, rs, part, psupp);
        lemma_body_ok(db, ps, prm, t0);
        lemma_ordered_link(db, query_spec_at(ps), q5_g(prm), xs_of(rs), view_rows(out));
    }
}

/// Capacity answer: a group's absolute mass beyond `i128::MAX` puts every bound database outside capacity.
proof fn lemma_answer_capacity(sv: crate::gendb_entry::stores::StoresView, ps: Seq<Literal>, rs: Rels, part: Seq<Row>,
    psupp: Seq<Row>, prm: Prm, t0: int, k: Row)
    requires
        parts_rep(sv, rs, part, psupp),
        param_domain(ps),
        prm == prm_of(ps, prm.hi),
        date_to_ts(prm.lo) == Ok::<int, SqlError>(t0),
        ts_add_interval(t0, 12, 0, 0) == Ok::<int, SqlError>(prm.hi),
        gabs(q5_g(prm), xs_of(rs), k, 0) > i128_max(),
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> !capacity_domain(db, query_spec_at(ps)),
{
    lemma_query_shape(ps);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies !capacity_domain(db, query_spec_at(ps)) by {
        lemma_rels_determined(sv, db, rs, part, psupp);
        lemma_capacity(db, ps, prm, t0, k);
    }
}

/// Error answer: when `$2 + INTERVAL '1' YEAR` fails with `e`, the statement is `e` on a non-empty product and has no
/// rows on an empty one, for every bound database.
proof fn lemma_answer_err(sv: crate::gendb_entry::stores::StoresView, ps: Seq<Literal>, rs: Rels, part: Seq<Row>,
    psupp: Seq<Row>, e: SqlError, nonempty: bool)
    requires
        parts_rep(sv, rs, part, psupp),
        param_domain(ps),
        match date_to_ts(date_from_civil(ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d)) {
            Err(e1) => e1 == e,
            Ok(t0) => ts_add_interval(t0, 12, 0, 0) == Err::<int, SqlError>(e),
        },
        nonempty == (rs.c.len() > 0 && rs.o.len() > 0 && rs.l.len() > 0 && rs.s.len() > 0 && rs.n.len() > 0 && rs.r.len() > 0),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> if nonempty {
            ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e))
        } else {
            ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(Seq::<Vec<EVal>>::empty())))
        },
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies if nonempty {
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e))
    } else {
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(Seq::<Vec<EVal>>::empty())))
    } by {
        lemma_rels_determined(sv, db, rs, part, psupp);
        assert(db.tables.len() == 8) by {
            assert(schema_spec().len() == 8) by (compute);
        }
        assert forall|env: Row| eval_expr(db, env, #[trigger] hi_expr(ps)) == Err::<Val, SqlError>(e) by {
            lemma_hi_err(db, env, ps, e);
        }
        lemma_body_err(db, ps, e);
        lemma_full_len(db, rs);
        if !nonempty {
            lemma_empty_ok(db, query_spec_at(ps));
        }
    }
}

/// The first overflowed group, if any.
fn first_ovf(ovf: &Vec<bool>) -> (r: Option<usize>)
    ensures
        r matches Some(i) ==> i < ovf@.len() && ovf@[i as int],
        r is None ==> forall|i: int| 0 <= i < ovf@.len() ==> !#[trigger] ovf@[i],
{
    let mut i: usize = 0;
    while i < ovf.len()
        invariant i <= ovf@.len(), forall|h: int| 0 <= h < i ==> !#[trigger] ovf@[h],
        decreases ovf@.len() - i,
    {
        if ovf[i] {
            return Some(i);
        }
        i = i + 1;
    }
    None
}

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost db0 = choose|db: Database| bound_db(sv, db);
    let ghost rs = rels_of_db(db0);
    let ghost part = other_rels(db0).0;
    let ghost psupp = other_rels(db0).1;
    proof {
        lemma_bound_rep(sv, db0);
        lemma_rels_shapes(db0);
        lemma_rels_keys(db0);
        lemma_query_shape(ps);
    }
    // ---- the stored columns
    let lc = read_lineitem(&mut stores.li_okruns, Ghost(rs));
    let oc = read_orders(&mut stores.li_okruns, Ghost(rs));
    let cflag = read_cluster(&mut stores.li_okruns, Ghost(rs));
    let cc = read_customers(&mut stores.custpart, Ghost(rs), Ghost(part));
    let sc = read_suppliers(&mut stores.suppliers, Ghost(rs), Ghost(psupp));
    let dc = read_dims(&mut stores.suppliers, Ghost(rs), Ghost(psupp));
    // ---- the date window [lo_day, hi_day)
    proof {
        lemma_date_param(ps);
    }
    let lo_day = date_from_civil_exec(params.p1.y as i64, params.p1.m as i64, params.p1.d as i64);
    let ghost lo = lo_day as int;
    let t0r = date_to_ts_exec(lo_day as i32);
    let t1r = match t0r {
        Ok(t0) => ts_add_interval_exec(t0, 12, 0, 0),
        Err(e) => Err(e),
    };
    let hi = match t1r {
        Ok(h) => h,
        Err(e) => {
            // `$2 + INTERVAL '1' YEAR` fails: the error on a non-empty product, else no rows
            let nonempty = lc.n_l > 0 && oc.n_o > 0 && cc.n_c > 0 && sc.n_s > 0 && dc.n_n > 0 && dc.n_r > 0;
            let empty: Vec<Vec<EVal>> = Vec::new();
            proof {
                lemma_answer_err(sv, ps, rs, part, psupp, e, nonempty);
                assert(empty@ =~= Seq::<Vec<EVal>>::empty());
            }
            if nonempty {
                return Ok(Answer::SqlError(e));
            } else {
                return Ok(Answer::Rows(empty));
            }
        },
    };
    let ghost t0 = match t0r { Ok(x) => x as int, Err(_) => 0 };
    let ghost prm = Prm { name: params.p0@, lo, hi: hi as int };
    proof {
        assert(prm == prm_of(ps, prm.hi));
        assert(date_to_ts(prm.lo) == Ok::<int, SqlError>(t0));
        assert(ts_valid(hi as int));
    }
    let (qd, qr) = floor_divmod(hi - 1, 86_400_000_000i64);
    let hi_day = qd + 1;
    proof {
        lemma_hi_day(hi as int, qd as int, qr as int);
    }
    // ---- the qualifying nations and their groups
    let ql = build_qlist(&dc, params.p0, Ghost(rs), Ghost(prm));
    let ng = ql.gnames.len();
    // ---- dense keys and the packed customer and supplier maps (one dispatch)
    let pp = match build_maps(cc.cn_c, cc.cn_b, cc.ck_c, cc.ck_b, cc.div, cc.n_c,
        sc.sn_c, sc.sn_b, sc.sk_c, sc.sk_b, sc.div, sc.n_s, &ql.qkey, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let cdense = pp.cdense;
    let sdense = pp.sdense;
    // ---- the orders range of the window
    let (p0, p1) = candidate_range(&oc, lo_day, hi_day, Ghost(rs));
    let t = ScanCtx {
        lk_c: lc.lk_c, lk_b: lc.lk_b, ls_c: lc.ls_c, ls_b: lc.ls_b, le_c: lc.le_c, le_b: lc.le_b,
        ld_c: lc.ld_c, ld_b: lc.ld_b,
        ok_c: oc.ok_c, ok_b: oc.ok_b, oc_c: oc.oc_c, oc_b: oc.oc_b, od_c: oc.od_c, od_b: oc.od_b,
        oi_c: oc.oi_c, oi_b: oc.oi_b, okind: oc.okind,
        ck_c: cc.ck_c, ck_b: cc.ck_b, ckind: cc.ckind, cn_c: cc.cn_c, cn_b: cc.cn_b,
        sk_c: sc.sk_c, sk_b: sc.sk_b, skind: sc.skind, sn_c: sc.sn_c, sn_b: sc.sn_b,
        e32: cc.e32, e64: cc.e64, st: lc.st, st_n: lc.st.len(),
        n_l: lc.n_l, n_o: oc.n_o, n_c: cc.n_c, n_s: sc.n_s,
        ldiv: lc.div, odiv: oc.div, cdiv: cc.div, sdiv: sc.div,
        ok_exact: oc.exact, ck_exact: cc.exact, sk_exact: sc.exact,
        clustered: cflag, cdense, sdense,
        lo_day, hi_day,
        rs: Ghost(rs), prm: Ghost(prm), lrows: Ghost(lc.lrows@), orows: Ghost(oc.orows@), omap: Ghost(oc.omap@),
        qrow: Ghost(ql.qrow@), gnames: Ghost(names_view(ql.gnames@)),
    };
    proof {
        lemma_ctx_wf(t, lc, oc, cc, sc, rs, prm, cflag, lc.lrows@, oc.orows@);
    }
    // ---- the scan
    let tot = match run_scan(t, &ql.qkey, &ql.qgrp, &oc, p0, p1, ng, pp.cm, pp.cmd, pp.sm, pp.smd, pp.use_map, workers, dispatch) {
        Ok(x) => x,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        lemma_totals_nf(t, tot, rs, prm, ql.qkey@, ql.qgrp@);
    }
    // ---- Capacity: some group's absolute revenue mass exceeds i128::MAX
    match first_ovf(&tot.ovf) {
        Some(gi) => {
            proof {
                assert(t.acc_ok(gi as int, 0, t.n_l as int, tot.cnt@[gi as int], tot.sum@[gi as int], tot.abs@[gi as int], tot.ovf@[gi as int]));
                let k = gkey(t.gnames@, gi as int);
                assert(gabs(q5_g(prm), xs_of(rs), k, 0) == t.lsum(gi as int, 2, 0, t.n_l as int));
                lemma_answer_capacity(sv, ps, rs, part, psupp, prm, t0, k);
            }
            return Ok(Answer::Capacity);
        },
        None => {},
    }
    // ---- the result rows
    let rows = build_rows(&tot.cnt, &tot.sum, &ql.gnames, Ghost(prm), Ghost(xs_of(rs)));
    proof {
        lemma_answer_rows(sv, ps, rs, part, psupp, prm, t0, rows@);
    }
    Ok(Answer::Rows(rows))
}

} // verus!
