//! The kept rows' weighted sum as a sum over the executable contributions.
//!
//! A contribution (`CS`) is what the join emits for one filing (sub row `fil[f]`) and one of its qualifying pre rows:
//! the tlabel slot of the pre row's tag row and the matched num rows (pair code `nq` inside the filing's run
//! `[rs, re)`). Its weight under `w` (`csum`) is `w` of the output fields (sic, tlabel, `$2`, cik, value) summed over
//! the matched num rows. `filing_cs` lists a filing's contributions in the executable order (sub-runs, then rows);
//! `lemma_filing` proves that the nested sum of one qualifying sub row equals its contributions' weight, and
//! `lemma_all` that the kept rows' weighted sum equals the weight of all filings' contributions.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::typing::db_wf;
use crate::spec::constraints::constraints_hold;
use crate::schema::schema_spec;
use crate::gendb_constraints::declared_db;
use crate::gendb_entry::layout::PartView;
use crate::link::join::{sum_of, keep, lemma_sum_of_ext};
use crate::stores::num::interface as N;
use crate::stores::pre::interface as P;
use crate::stores::sub_sic::interface as S;
use crate::stores::tag_tv::interface as T;
use crate::agent::common::sums::*;
use crate::agent::sem::*;
use crate::agent::group::{num4, coeff};
use crate::agent::chain::*;
use crate::agent::levels::*;

verus! {

// ------------------------------------------------------------------------------------------------ context

/// Ghost context of one call: the binding, the four storages' parts, the executable lookups and maps.
pub struct Cx {
    pub b0: Seq<u8>,
    pub b1: Seq<u8>,
    pub lo: int,
    pub hi: int,
    pub num: Seq<PartView>,
    pub sub: Seq<PartView>,
    pub tag: Seq<PartView>,
    pub pre: Seq<PartView>,
    /// uom code of `$1` (or -1), stmt code of `$2` (or -1).
    pub u: int,
    pub sc: int,
    /// Per pre pair: the num pair code and the tag row of its (tag, version), -1 when absent.
    pub t3: Seq<int>,
    pub t6: Seq<int>,
    /// The qualifying sub rows (filings) in executable order, with each one's num run and pre adsh code.
    pub fil: Seq<int>,
    pub runs: Seq<int>,
    pub pcs: Seq<int>,
}

pub open spec fn txt(v: Val) -> Seq<u8> { match v { Val::Text(b) => b, _ => Seq::empty() } }

/// A sub row qualifies: sic not NULL and inside `[$3, $4]`.
pub open spec fn sub_qual(cx: Cx, s: Row) -> bool { s[3] is Int && cx.lo <= ival(s[3]) <= cx.hi }

pub open spec fn srow_of(db: Database, cx: Cx, f: int) -> Row { db.tables[0][cx.fil[f]] }
pub open spec fn sic_of(db: Database, cx: Cx, f: int) -> int { ival(srow_of(db, cx, f)[3]) }
pub open spec fn cik_of(db: Database, cx: Cx, f: int) -> int { ival(srow_of(db, cx, f)[1]) }
pub open spec fn adsh_of(db: Database, cx: Cx, f: int) -> Seq<u8> { txt(srow_of(db, cx, f)[0]) }

pub open spec fn pu64s(cx: Cx, k: usize) -> Seq<u64> { pre_u64s(cx.pre, k) }

/// Bytes of pre pair `q`.
pub open spec fn ptag(cx: Cx, q: int) -> Seq<u8> {
    crate::stores::pre::interface::common::cols::list_entry(cx.pre, P::P_TAG_OFF, pu64s(cx, P::P_PAIR_TAG)[q] as int)
}

pub open spec fn pver(cx: Cx, q: int) -> Seq<u8> {
    crate::stores::pre::interface::common::cols::list_entry(cx.pre, P::P_VERSION_OFF, pu64s(cx, P::P_PAIR_VERSION)[q] as int)
}

pub open spec fn tu64s(cx: Cx, k: usize) -> Seq<u64> { crate::stores::tag_tv::interface::common::cols::u64s(cx.tag, k) }

/// The null tlabel slot (one past the tlabel dictionary).
pub open spec fn ntl(cx: Cx) -> int { crate::stores::tag_tv::interface::common::cols::text_count(cx.tag, T::P_TLABEL_OFF as int) }

/// Tlabel slot of tag row `tr`: its tlabel code, or the null slot.
pub open spec fn slot_of(cx: Cx, tr: int) -> int {
    if crate::stores::tag_tv::interface::common::text::u8_part(cx.tag[T::P_TLABEL_VALID as int])[tr] == 0 { ntl(cx) } else { tu64s(cx, T::P_TLABEL_CODES)[tr] as int }
}

/// Tlabel value of a slot.
pub open spec fn tl_val(cx: Cx, slot: int) -> Val {
    if slot == ntl(cx) { Val::Null } else { Val::Text(crate::stores::tag_tv::interface::common::cols::list_entry(cx.tag, T::P_TLABEL_OFF, slot)) }
}

/// The context's facts.
pub open spec fn cx_ok(db: Database, cx: Cx) -> bool {
    &&& db.schema == schema_spec()
    &&& db_wf(db)
    &&& constraints_hold(declared_db(db))
    &&& N::represents(cx.num, seq![db.tables[1]])
    &&& S::represents(cx.sub, seq![db.tables[0]])
    &&& T::represents(cx.tag, seq![db.tables[2]])
    &&& P::represents(cx.pre, seq![db.tables[3]])
    &&& (cx.sc >= 0 ==> cx.sc < P::stmt_count(cx.pre) && pstmt_entry(cx.pre, cx.sc) == cx.b1)
    &&& (cx.sc < 0 ==> forall|k: int| 0 <= k < P::stmt_count(cx.pre) ==> #[trigger] pstmt_entry(cx.pre, k) != cx.b1)
    &&& cx.t3.len() == P::pair_count(cx.pre) && cx.t6.len() == P::pair_count(cx.pre)
    &&& forall|q: int| 0 <= q < P::pair_count(cx.pre) ==>
            pair_found(cx.num, ptag(cx, q), pver(cx, q), #[trigger] cx.t3[q]) && tag_found(cx.tag, ptag(cx, q), pver(cx, q), cx.t6[q])
    &&& cx.runs.len() == cx.fil.len() && cx.pcs.len() == cx.fil.len()
    &&& cx.fil.no_duplicates()
    &&& forall|f: int| 0 <= f < cx.fil.len() ==> 0 <= #[trigger] cx.fil[f] < db.tables[0].len()
    &&& forall|f: int| 0 <= f < cx.fil.len() ==> sub_qual(cx, #[trigger] srow_of(db, cx, f))
    &&& forall|i: int| 0 <= i < db.tables[0].len() && sub_qual(cx, #[trigger] db.tables[0][i]) ==> cx.fil.contains(i)
    &&& forall|f: int| 0 <= f < cx.fil.len() ==> run_found(cx.num, cx.b0, adsh_of(db, cx, f), cx.u, #[trigger] cx.runs[f])
    &&& forall|f: int| 0 <= f < cx.fil.len() && cx.runs[f] >= 0 ==> pre_found(cx.pre, adsh_of(db, cx, f), cx.b1, #[trigger] cx.pcs[f], cx.sc)
}

// ------------------------------------------------------------------------------------------------ contributions

/// One contribution: filing `f`, tlabel slot, the filing's run `[rs, re)` and the num pair code `nq`.
pub struct CS {
    pub f: int,
    pub slot: int,
    pub rs: int,
    pub re: int,
    pub nq: int,
}

/// The weight of a value at the filing's output fields.
pub open spec fn phi_of(b1: Seq<u8>, sic: int, tl: Val, cik: int, w: spec_fn(Row) -> int) -> spec_fn(Val) -> int {
    |v: Val| w(seq![Val::Int(sic), tl, Val::Text(b1), Val::Int(cik), v])
}

pub open spec fn const1() -> spec_fn(Val) -> int { |v: Val| 1int }

/// Matched num rows of a run and pair code.
pub open spec fn run_pair_cnt(num: Seq<PartView>, rs: int, re: int, nq: int) -> int {
    run_pair_sum(num, rs, re, nq, const1())
}

/// The weight of one contribution.
pub open spec fn csum(db: Database, cx: Cx, c: CS, w: spec_fn(Row) -> int) -> int {
    run_pair_sum(cx.num, c.rs, c.re, c.nq, phi_of(cx.b1, sic_of(db, cx, c.f), tl_val(cx, c.slot), cik_of(db, cx, c.f), w))
}

pub open spec fn lsum(db: Database, cx: Cx, cs: Seq<CS>, w: spec_fn(Row) -> int) -> int
    decreases cs.len(),
{
    if cs.len() == 0 { 0 } else { lsum(db, cx, cs.drop_last(), w) + csum(db, cx, cs.last(), w) }
}

pub open spec fn rs_of(cx: Cx, f: int) -> int { N::u64s(cx.num, N::P_RUN_START)[cx.runs[f]] as int }
pub open spec fn re_of(cx: Cx, f: int) -> int { N::u64s(cx.num, N::P_RUN_START)[cx.runs[f] + 1] as int }

/// The contribution of stored pre row `j` of filing `f`, if any.
pub open spec fn row_cs(cx: Cx, f: int, j: int) -> Seq<CS> {
    let q = pu64s(cx, P::P_TV)[j] as int;
    let nq = cx.t3[q];
    let tr = cx.t6[q];
    if nq >= 0 && tr >= 0 && tag_abstract(cx.tag, tr) == 0 && run_pair_cnt(cx.num, rs_of(cx, f), re_of(cx, f), nq) > 0 {
        seq![CS { f, slot: slot_of(cx, tr), rs: rs_of(cx, f), re: re_of(cx, f), nq }]
    } else {
        Seq::empty()
    }
}

/// Contributions of the stored pre rows `[j0, j1)` of filing `f`.
pub open spec fn rows_cs(cx: Cx, f: int, j0: int, j1: int) -> Seq<CS>
    decreases j1 - j0,
{
    if j1 <= j0 { Seq::empty() } else { rows_cs(cx, f, j0, j1 - 1) + row_cs(cx, f, j1 - 1) }
}

/// Contributions of sub-run `s` of filing `f` (none unless its group has stmt `$2`).
pub open spec fn sub_cs(cx: Cx, f: int, s: int) -> Seq<CS> {
    if gq(cx.pre, cx.sc, pu64s(cx, P::P_SUB_GROUP)[s] as int) {
        rows_cs(cx, f, pu64s(cx, P::P_SUB_START)[s] as int, pu64s(cx, P::P_SUB_START)[s + 1] as int)
    } else {
        Seq::empty()
    }
}

pub open spec fn subs_cs(cx: Cx, f: int, s0: int, s1: int) -> Seq<CS>
    decreases s1 - s0,
{
    if s1 <= s0 { Seq::empty() } else { subs_cs(cx, f, s0, s1 - 1) + sub_cs(cx, f, s1 - 1) }
}

/// Contributions of filing `f`, in executable order.
pub open spec fn filing_cs(cx: Cx, f: int) -> Seq<CS> {
    if cx.runs[f] >= 0 && cx.pcs[f] >= 0 {
        subs_cs(cx, f, pu64s(cx, P::P_ADSH_SUBS)[cx.pcs[f]] as int, pu64s(cx, P::P_ADSH_SUBS)[cx.pcs[f] + 1] as int)
    } else {
        Seq::empty()
    }
}

/// Contributions of filings `[0, n)`.
pub open spec fn all_cs(cx: Cx, n: int) -> Seq<CS>
    decreases n,
{
    if n <= 0 { Seq::empty() } else { all_cs(cx, n - 1) + filing_cs(cx, n - 1) }
}

pub proof fn lemma_lsum_append(db: Database, cx: Cx, a: Seq<CS>, b: Seq<CS>, w: spec_fn(Row) -> int)
    ensures lsum(db, cx, a + b, w) == lsum(db, cx, a, w) + lsum(db, cx, b, w),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_lsum_append(db, cx, a, b.drop_last(), w);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

// ------------------------------------------------------------------------------------------------ the flat condition

pub open spec fn wqc(cx: Cx, w: spec_fn(Row) -> int) -> spec_fn(Row) -> int { wq(cx.b0, cx.b1, cx.lo, cx.hi, w) }

/// The kept-row condition of `n ++ s ++ t ++ p`, level by level.
pub open spec fn flat(cx: Cx, n: Row, s: Row, t: Row, p: Row) -> bool {
    &&& sub_qual(cx, s)
    &&& pmatch(p, txt(s[0]), cx.b1)
    &&& tmatch(t, txt(p[6]), txt(p[7]))
    &&& nmatch(n, cx.b0, txt(s[0]), txt(p[6]), txt(p[7]))
}

/// On typed rows, `qual` of the joined row is `flat`, and its output fields are (sic, tlabel, stmt, cik, value).
pub proof fn lemma_flat(cx: Cx, n: Row, s: Row, t: Row, p: Row)
    requires num_ok(n), sub_ok(s), tag_ok(t), pre_ok(p),
    ensures
        qual(cx.b0, cx.b1, cx.lo, cx.hi, n + s + t + p) == flat(cx, n, s, t, p),
        mini(n + s + t + p) == seq![s[3], t[7], p[3], s[1], n[7]],
{
    let x = n + s + t + p;
    assert(x.len() == 48);
    assert(crate::link::join::left_of(x, 38) =~= n + s + t);
    assert(crate::link::join::right_of(x, 38) =~= p);
    assert(crate::link::join::left_of(n + s + t, 29) =~= n + s);
    assert(crate::link::join::right_of(n + s + t, 29) =~= t);
    assert(crate::link::join::left_of(n + s, 9) =~= n);
    assert(crate::link::join::right_of(n + s, 9) =~= s);
    assert(x[0] == n[0] && x[1] == n[1] && x[2] == n[2] && x[5] == n[5] && x[7] == n[7]);
    assert(x[9] == s[0] && x[10] == s[1] && x[12] == s[3]);
    assert(x[29] == t[0] && x[30] == t[1] && x[32] == t[3] && x[36] == t[7]);
    assert(x[38] == p[0] && x[41] == p[3] && x[44] == p[6] && x[45] == p[7]);
    assert(mini(x) =~= seq![s[3], t[7], p[3], s[1], n[7]]);
}

// ------------------------------------------------------------------------------------------------ one filing

/// The tag-level weight of a tlabel at the filing's fields (its num rows of one (tag, version)).
pub open spec fn psi_of(db: Database, cx: Cx, a: Seq<u8>, tg: Seq<u8>, vr: Seq<u8>, sic: int, cik: int, w: spec_fn(Row) -> int) -> spec_fn(Val) -> int {
    |tl: Val| sum_of(db.tables[1], nfun(cx.b0, a, tg, vr, phi_of(cx.b1, sic, tl, cik, w)))
}

/// The pre-level weight of a pre row at the filing's fields.
pub open spec fn yfun(db: Database, cx: Cx, a: Seq<u8>, sic: int, cik: int, w: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |p: Row| sum_of(db.tables[2], tfun(txt(p[6]), txt(p[7]), psi_of(db, cx, a, txt(p[6]), txt(p[7]), sic, cik, w)))
}

/// One tag row's level: zero unless the pre row and the tag row match.
proof fn lemma_ftx(db: Database, cx: Cx, w: spec_fn(Row) -> int, s: Row, p: Row, t: Row)
    requires
        db.schema == schema_spec(), db_wf(db),
        sub_ok(s), pre_ok(p), tag_ok(t), sub_qual(cx, s),
    ensures
        ftx(db, wqc(cx, w), s, p)(t) == if pmatch(p, txt(s[0]), cx.b1) && tmatch(t, txt(p[6]), txt(p[7])) {
            psi_of(db, cx, txt(s[0]), txt(p[6]), txt(p[7]), ival(s[3]), ival(s[1]), w)(t[7])
        } else { 0 },
{
    lemma_rows_typed(db);
    let num = db.tables[1];
    let (a, tg, vr, sic, cik) = (txt(s[0]), txt(p[6]), txt(p[7]), ival(s[3]), ival(s[1]));
    let fx = fnx(wqc(cx, w), s, t, p);
    if pmatch(p, a, cx.b1) && tmatch(t, tg, vr) {
        let g = nfun(cx.b0, a, tg, vr, phi_of(cx.b1, sic, t[7], cik, w));
        assert forall|i: int| 0 <= i < num.len() implies #[trigger] fx(num[i]) == g(num[i]) by {
            let n = num[i];
            lemma_flat(cx, n, s, t, p);
            assert(s[3] == Val::Int(sic) && s[1] == Val::Int(cik) && p[3] == Val::Text(cx.b1));
            assert(seq![s[3], t[7], p[3], s[1], n[7]] =~= seq![Val::Int(sic), t[7], Val::Text(cx.b1), Val::Int(cik), n[7]]);
        }
        lemma_sum_of_ext(num, fx, g);
    } else {
        assert forall|i: int| 0 <= i < num.len() implies #[trigger] fx(num[i]) == 0 by {
            lemma_flat(cx, num[i], s, t, p);
        }
        crate::link::join::lemma_sum_of_zero(num, fx);
    }
}

/// One pre row's level, as `pfun` of `yfun`.
proof fn lemma_fpx(db: Database, cx: Cx, w: spec_fn(Row) -> int, s: Row, p: Row)
    requires
        db.schema == schema_spec(), db_wf(db),
        sub_ok(s), pre_ok(p), sub_qual(cx, s),
    ensures
        fpx(db, wqc(cx, w), s)(p) == pfun(txt(s[0]), cx.b1, yfun(db, cx, txt(s[0]), ival(s[3]), ival(s[1]), w))(p),
{
    lemma_rows_typed(db);
    let tag = db.tables[2];
    let (a, tg, vr, sic, cik) = (txt(s[0]), txt(p[6]), txt(p[7]), ival(s[3]), ival(s[1]));
    let ft = ftx(db, wqc(cx, w), s, p);
    if pmatch(p, a, cx.b1) {
        let g = tfun(tg, vr, psi_of(db, cx, a, tg, vr, sic, cik, w));
        assert forall|i: int| 0 <= i < tag.len() implies #[trigger] ft(tag[i]) == g(tag[i]) by {
            lemma_ftx(db, cx, w, s, p, tag[i]);
        }
        lemma_sum_of_ext(tag, ft, g);
    } else {
        assert forall|i: int| 0 <= i < tag.len() implies #[trigger] ft(tag[i]) == 0 by {
            lemma_ftx(db, cx, w, s, p, tag[i]);
        }
        crate::link::join::lemma_sum_of_zero(tag, ft);
    }
}

/// A sub row that does not qualify contributes nothing.
proof fn lemma_fsx_unqual(db: Database, cx: Cx, w: spec_fn(Row) -> int, s: Row)
    requires db.schema == schema_spec(), db_wf(db), sub_ok(s), !sub_qual(cx, s),
    ensures fsx(db, wqc(cx, w))(s) == 0,
{
    lemma_rows_typed(db);
    let (num, tag, pre) = (db.tables[1], db.tables[2], db.tables[3]);
    let fp = fpx(db, wqc(cx, w), s);
    assert forall|k: int| 0 <= k < pre.len() implies #[trigger] fp(pre[k]) == 0 by {
        let p = pre[k];
        let ft = ftx(db, wqc(cx, w), s, p);
        assert forall|j: int| 0 <= j < tag.len() implies #[trigger] ft(tag[j]) == 0 by {
            let t = tag[j];
            let fx = fnx(wqc(cx, w), s, t, p);
            assert forall|i: int| 0 <= i < num.len() implies #[trigger] fx(num[i]) == 0 by {
                lemma_flat(cx, num[i], s, t, p);
            }
            crate::link::join::lemma_sum_of_zero(num, fx);
        }
        crate::link::join::lemma_sum_of_zero(tag, ft);
    }
    crate::link::join::lemma_sum_of_zero(pre, fp);
}

/// A run and pair code without matched rows weigh nothing under any weight.
pub proof fn lemma_cnt_zero(num: Seq<PartView>, rs: int, re: int, nq: int, phi: spec_fn(Val) -> int)
    requires run_pair_cnt(num, rs, re, nq) == 0,
    ensures run_pair_sum(num, rs, re, nq, phi) == 0,
{
    let c = run_pair_term(num, nq, const1());
    let h = run_pair_term(num, nq, phi);
    assert forall|i: int| rs <= i < re implies #[trigger] c(i) >= 0 by {}
    assert forall|i: int| rs <= i < re implies #[trigger] h(i) == 0 by {
        lemma_rsum_nonneg_zero(rs, re, c, i);
    }
    lemma_rsum_zero(rs, re, h);
}

/// One stored pre row of a filing with a run: its weight is its contribution's.
proof fn lemma_row(db: Database, cx: Cx, w: spec_fn(Row) -> int, f: int, j: int)
    requires
        cx_ok(db, cx), 0 <= f < cx.fil.len(), cx.runs[f] >= 0, 0 <= j < P::row_count(cx.pre),
    ensures
        yfun(db, cx, adsh_of(db, cx, f), sic_of(db, cx, f), cik_of(db, cx, f), w)(prow(db, cx.pre, j))
            == lsum(db, cx, row_cs(cx, f, j), w),
{
    let p = prow(db, cx.pre, j);
    let rels = seq![db.tables[3]];
    assert(P::stored_cols_ok(cx.pre, P::stored_row(cx.pre, rels, j), j));
    assert(p == P::stored_row(cx.pre, rels, j));
    let q = pu64s(cx, P::P_TV)[j] as int;
    assert(q < P::pair_count(cx.pre));
    let (tg, vr) = (ptag(cx, q), pver(cx, q));
    assert(txt(p[6]) == tg && txt(p[7]) == vr);
    let (a, sic, cik) = (adsh_of(db, cx, f), sic_of(db, cx, f), cik_of(db, cx, f));
    let nq = cx.t3[q];
    let tr = cx.t6[q];
    let psi = psi_of(db, cx, a, tg, vr, sic, cik, w);
    assert(pair_found(cx.num, tg, vr, nq) && tag_found(cx.tag, tg, vr, tr));
    lemma_tag_level(db, cx.tag, tg, vr, tr, psi);
    let run = cx.runs[f];
    assert(run_found(cx.num, cx.b0, a, cx.u, run));
    let (rs, re) = (rs_of(cx, f), re_of(cx, f));
    if tr >= 0 && tag_abstract(cx.tag, tr) == 0 {
        let tl = db.tables[2][tr][7];
        assert(T::tag_row_ok(cx.tag, db.tables[2][tr], tr));
        assert(tl == tl_val(cx, slot_of(cx, tr))) by {
            let tlc = tu64s(cx, T::P_TLABEL_CODES);
            let valid = crate::stores::tag_tv::interface::common::text::u8_part(cx.tag[T::P_TLABEL_VALID as int]);
            if valid[tr] != 0 {
                assert(tlc[tr] < ntl(cx));
            }
        }
        let phi = phi_of(cx.b1, sic, tl, cik, w);
        lemma_num_level(db, cx.num, cx.b0, a, tg, vr, cx.u, run, nq, phi);
        if nq >= 0 {
            assert(run_pair_cnt(cx.num, rs, re, nq) >= 0) by {
                lemma_rsum_nonneg(rs, re, run_pair_term(cx.num, nq, const1()));
            }
            if run_pair_cnt(cx.num, rs, re, nq) > 0 {
                let c = CS { f, slot: slot_of(cx, tr), rs, re, nq };
                assert(row_cs(cx, f, j) == seq![c]);
                assert(seq![c].drop_last() =~= Seq::<CS>::empty());
                assert(lsum(db, cx, Seq::<CS>::empty(), w) == 0);
                assert(seq![c].last() == c);
                assert(lsum(db, cx, seq![c], w) == lsum(db, cx, seq![c].drop_last(), w) + csum(db, cx, seq![c].last(), w));
                assert(lsum(db, cx, seq![c], w) == csum(db, cx, c, w));
                assert(csum(db, cx, c, w) == run_pair_sum(cx.num, rs, re, nq, phi));
            } else {
                lemma_cnt_zero(cx.num, rs, re, nq, phi);
                assert(row_cs(cx, f, j) == Seq::<CS>::empty());
            }
        } else {
            assert(row_cs(cx, f, j) == Seq::<CS>::empty());
        }
        assert(psi(tl) == sum_of(db.tables[1], nfun(cx.b0, a, tg, vr, phi)));
    } else {
        assert(row_cs(cx, f, j) == Seq::<CS>::empty());
    }
    assert(yfun(db, cx, a, sic, cik, w)(p) == sum_of(db.tables[2], tfun(tg, vr, psi)));
}

/// The stored pre rows `[j0, j1)` of a filing with a run.
proof fn lemma_rows(db: Database, cx: Cx, w: spec_fn(Row) -> int, f: int, j0: int, j1: int)
    requires
        cx_ok(db, cx), 0 <= f < cx.fil.len(), cx.runs[f] >= 0, 0 <= j0 <= j1 <= P::row_count(cx.pre),
    ensures
        rsum(j0, j1, yrow(db, cx.pre, yfun(db, cx, adsh_of(db, cx, f), sic_of(db, cx, f), cik_of(db, cx, f), w)))
            == lsum(db, cx, rows_cs(cx, f, j0, j1), w),
    decreases j1 - j0,
{
    if j1 > j0 {
        lemma_rows(db, cx, w, f, j0, j1 - 1);
        lemma_row(db, cx, w, f, j1 - 1);
        lemma_lsum_append(db, cx, rows_cs(cx, f, j0, j1 - 1), row_cs(cx, f, j1 - 1), w);
    }
}

/// The sub-runs `[s0, s1)` of a filing with a run.
proof fn lemma_subs(db: Database, cx: Cx, w: spec_fn(Row) -> int, f: int, s0: int, s1: int)
    requires
        cx_ok(db, cx), 0 <= f < cx.fil.len(), cx.runs[f] >= 0, 0 <= s0 <= s1 <= P::sub_count(cx.pre),
    ensures
        subs_sum(cx.pre, cx.sc, s0, s1, yrow(db, cx.pre, yfun(db, cx, adsh_of(db, cx, f), sic_of(db, cx, f), cik_of(db, cx, f), w)))
            == lsum(db, cx, subs_cs(cx, f, s0, s1), w),
    decreases s1 - s0,
{
    if s1 > s0 {
        let y = yrow(db, cx.pre, yfun(db, cx, adsh_of(db, cx, f), sic_of(db, cx, f), cik_of(db, cx, f), w));
        lemma_subs(db, cx, w, f, s0, s1 - 1);
        let s = s1 - 1;
        let start = pu64s(cx, P::P_SUB_START);
        let ns = P::sub_count(cx.pre);
        assert(start[0] == 0 && start[ns] == P::row_count(cx.pre));
        assert(0 <= start[s] <= start[s + 1] <= P::row_count(cx.pre)) by {
            if s > 0 { assert(start[0] < start[s]); }
            if s + 1 < ns { assert(start[s + 1] < start[ns]); }
            assert(start[s] < start[s + 1]);
        }
        if gq(cx.pre, cx.sc, pu64s(cx, P::P_SUB_GROUP)[s] as int) {
            lemma_rows(db, cx, w, f, start[s] as int, start[s + 1] as int);
        }
        lemma_lsum_append(db, cx, subs_cs(cx, f, s0, s1 - 1), sub_cs(cx, f, s), w);
        assert(subs_sum(cx.pre, cx.sc, s0, s1, y) == subs_sum(cx.pre, cx.sc, s0, s1 - 1, y) + sub_term(cx.pre, cx.sc, y)(s));
    }
}

/// One filing: its nested sum is its contributions' weight.
pub proof fn lemma_filing(db: Database, cx: Cx, w: spec_fn(Row) -> int, f: int)
    requires cx_ok(db, cx), 0 <= f < cx.fil.len(),
    ensures fsx(db, wqc(cx, w))(srow_of(db, cx, f)) == lsum(db, cx, filing_cs(cx, f), w),
{
    lemma_rows_typed(db);
    let s = srow_of(db, cx, f);
    let pre = db.tables[3];
    let (a, sic, cik) = (adsh_of(db, cx, f), sic_of(db, cx, f), cik_of(db, cx, f));
    let y = yfun(db, cx, a, sic, cik, w);
    let fp = fpx(db, wqc(cx, w), s);
    let pf = pfun(a, cx.b1, y);
    assert forall|k: int| 0 <= k < pre.len() implies #[trigger] fp(pre[k]) == pf(pre[k]) by {
        lemma_fpx(db, cx, w, s, pre[k]);
    }
    lemma_sum_of_ext(pre, fp, pf);
    let run = cx.runs[f];
    if run < 0 {
        assert forall|k: int| 0 <= k < pre.len() implies #[trigger] pf(pre[k]) == 0 by {
            let p = pre[k];
            let (tg, vr) = (txt(p[6]), txt(p[7]));
            let psi = psi_of(db, cx, a, tg, vr, sic, cik, w);
            let tf = tfun(tg, vr, psi);
            assert forall|i: int| 0 <= i < db.tables[2].len() implies #[trigger] tf(db.tables[2][i]) == 0 by {
                let tl = db.tables[2][i][7];
                lemma_num_level_norun(db, cx.num, cx.b0, a, tg, vr, cx.u, phi_of(cx.b1, sic, tl, cik, w));
            }
            crate::link::join::lemma_sum_of_zero(db.tables[2], tf);
        }
        crate::link::join::lemma_sum_of_zero(pre, pf);
    } else {
        let pc = cx.pcs[f];
        assert(pre_found(cx.pre, a, cx.b1, pc, cx.sc));
        lemma_pre_level(db, cx.pre, a, cx.b1, pc, cx.sc, y);
        if pc >= 0 {
            P::lemma_adsh_subs(cx.pre, pc);
            let s0 = pu64s(cx, P::P_ADSH_SUBS)[pc] as int;
            let s1 = pu64s(cx, P::P_ADSH_SUBS)[pc + 1] as int;
            lemma_subs(db, cx, w, f, s0, s1);
        }
    }
}

/// All filings: the kept rows' weighted sum is the weight of every filing's contributions.
pub proof fn lemma_all(db: Database, cx: Cx, w: spec_fn(Row) -> int)
    requires cx_ok(db, cx),
    ensures
        sum_of(crate::agent::group::qrows(db, cx.b0, cx.b1, cx.lo, cx.hi), |x: Row| w(mini(x)))
            == lsum(db, cx, all_cs(cx, cx.fil.len() as int), w),
{
    lemma_rows_typed(db);
    lemma_sum_kept(db, cx.b0, cx.b1, cx.lo, cx.hi, w);
    assert(wq(cx.b0, cx.b1, cx.lo, cx.hi, w) == wqc(cx, w));
    let sub = db.tables[0];
    let g = fsx(db, wqc(cx, w));
    crate::agent::common::sums::lemma_sum_of_rsum(sub, g);
    let h = |i: int| g(sub[i]);
    let nf = cx.fil.len() as int;
    assert forall|i: int| 0 <= i < sub.len() && h(i) != 0 implies #[trigger] cx.fil.contains(i) by {
        if !sub_qual(cx, sub[i]) {
            lemma_fsx_unqual(db, cx, w, sub[i]);
        }
    }
    lemma_rsum_reindex(sub.len() as int, h, cx.fil);
    lemma_all_filings(db, cx, w, nf);
    let k1 = |k: int| h(cx.fil[k]);
    let k2 = |f: int| fsx(db, wqc(cx, w))(db.tables[0][cx.fil[f]]);
    lemma_rsum_ext(0, nf, k1, k2);
    assert(nested(db, wqc(cx, w)) == sum_of(sub, g));
    assert(sum_of(sub, g) == rsum(0, sub.len() as int, h));
}

proof fn lemma_all_filings(db: Database, cx: Cx, w: spec_fn(Row) -> int, n: int)
    requires cx_ok(db, cx), 0 <= n <= cx.fil.len(),
    ensures rsum(0, n, |f: int| fsx(db, wqc(cx, w))(db.tables[0][cx.fil[f]])) == lsum(db, cx, all_cs(cx, n), w),
    decreases n,
{
    if n > 0 {
        lemma_all_filings(db, cx, w, n - 1);
        lemma_filing(db, cx, w, n - 1);
        lemma_lsum_append(db, cx, all_cs(cx, n - 1), filing_cs(cx, n - 1), w);
    }
}

} // verus!
