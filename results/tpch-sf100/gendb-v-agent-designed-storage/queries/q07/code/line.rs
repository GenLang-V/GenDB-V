//! One lineitem row of the SQL reduction (`reduce::h1`) is the scan model's line term (`lemma_line`): under the
//! table links of `bind`, the key lookups of `h1` (supplier, order, customer, the two nations) are the model's
//! (`s_cls`, `o_cls`, `c_cls`, with the nation classes of the context `ctx_ok`), the WHERE condition holds exactly
//! when the line is in a group (`l_grp >= 0`), and the SELECT list is that group's key row with the line's volume
//! (`lrow7`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::link::join::*;
use super::common::keysum::*;
use super::dates::*;
use super::sqlq::*;
use super::reduce::*;
use super::body::*;
use super::model::*;
use super::bind::*;
use crate::stores::facts::interface::common::colfmt::{covered, is_perm};

verus! {

// ------------------------------------------------------------------------------------------------ classes and keys

/// The class of a nation name: 1 when it is `$1`, plus 2 when it is `$2`.
pub open spec fn name_cls(ps: Seq<Literal>, v: Val) -> int {
    (if v == Val::Text(ltext(ps[0])) { 1int } else { 0 }) + (if v == Val::Text(ltext(ps[1])) { 2int } else { 0 })
}

/// The class of nation key `k` in `db`: its nation's name class, 0 without a nation.
pub open spec fn nat_cls_db(db: Database, ps: Seq<Literal>, k: int) -> int {
    if has_key(t_nat(db), 0, Val::Int(k)) { name_cls(ps, key_row(t_nat(db), 0, Val::Int(k))[1]) } else { 0 }
}

/// The scan's context holds `db`'s nation classes and whether `$1 == $2`.
pub open spec fn ctx_ok(x: Ctx, db: Database, ps: Seq<Literal>) -> bool {
    &&& forall|k: int| #[trigger] nat_cls(x, k) == nat_cls_db(db, ps, k)
    &&& x.same == (ltext(ps[0]) == ltext(ps[1]))
}

/// The key row of group `gi`: the two nation names of its pair and its year.
pub open spec fn krow(ps: Seq<Literal>, gi: int) -> Row {
    let (ta, tb) = if gi < 2 { (ltext(ps[0]), ltext(ps[1])) } else { (ltext(ps[1]), ltext(ps[0])) };
    seq![Val::Text(ta), Val::Text(tb), Val::Num { coeff: 1995 + gi % 2, scale: 0 }]
}

/// The SELECT list of a line of group `gi` and volume `v`.
pub open spec fn lrow7(ps: Seq<Literal>, gi: int, v: int) -> Row {
    krow(ps, gi).push(Val::Num { coeff: v, scale: 4 })
}

/// The model's term of line `j`: `phi` of its SELECT list when it is in a group.
pub open spec fn line_term(c: Cols, x: Ctx, ps: Seq<Literal>, phi: spec_fn(Row) -> int, j: int) -> int {
    if l_grp(c, x, j) >= 0 { phi(lrow7(ps, l_grp(c, x, j), l_vol(c, j))) } else { 0 }
}

/// All the links the reduction needs.
pub open spec fn links(c: Cols, db: Database, lm: Seq<int>, om: Seq<int>) -> bool {
    &&& li_link(c, db, lm)
    &&& ord_link(c, db, om)
    &&& sup_link(c, db)
    &&& cus_link(c, db)
}

// ------------------------------------------------------------------------------------------------ keys

/// The primary keys of orders, supplier and customer make the model's keys distinct.
pub proof fn lemma_keys_ok(db: Database, c: Cols, lm: Seq<int>, om: Seq<int>)
    requires links(c, db, lm, om), red_ok(db),
    ensures keys_ok(c),
{
    assert forall|a: int, b: int| 0 <= a < c.n_o && 0 <= b < c.n_o && #[trigger] okey(c, a) == #[trigger] okey(c, b) implies a == b by {
        assert(t_ord(db)[om[a]][0] == Val::Int(okey(c, a)));
        assert(t_ord(db)[om[b]][0] == Val::Int(okey(c, b)));
        assert(colv(t_ord(db)[om[a]], 0) == colv(t_ord(db)[om[b]], 0));
        assert(om[a] == om[b]);
    }
    assert forall|a: int, b: int| 0 <= a < c.n_s && 0 <= b < c.n_s && #[trigger] skey(c, a) == #[trigger] skey(c, b) implies a == b by {
        assert(colv(t_sup(db)[a], 0) == colv(t_sup(db)[b], 0));
    }
    assert forall|a: int, b: int| 0 <= a < c.n_c && 0 <= b < c.n_c && #[trigger] ckey(c, a) == #[trigger] ckey(c, b) implies a == b by {
        assert(colv(t_cust(db)[a], 0) == colv(t_cust(db)[b], 0));
    }
}

/// The supplier with key `k`: the table lookup is the model's.
proof fn lemma_sup_key(db: Database, c: Cols, k: int)
    requires sup_link(c, db), red_ok(db), keys_ok(c),
    ensures
        has_key(t_sup(db), 0, Val::Int(k)) == has_s(c, k),
        has_s(c, k) ==> key_row(t_sup(db), 0, Val::Int(k)) == t_sup(db)[srow(c, k)] && 0 <= srow(c, k) < c.n_s
            && skey(c, srow(c, k)) == k,
{
    let rows = t_sup(db);
    if has_s(c, k) {
        let r = srow(c, k);
        assert(colv(rows[r], 0) == Val::Int(k));
        lemma_key_row_unique(rows, 0, Val::Int(k), r);
    }
    if has_key(rows, 0, Val::Int(k)) {
        let r = key_pos(rows, 0, Val::Int(k));
        lemma_key_row(rows, 0, Val::Int(k));
        assert(rows[r][0] == Val::Int(skey(c, r)));
        assert(skey(c, r) == k);
    }
}

/// The order with key `k`: the table lookup is the model's, through the row map.
proof fn lemma_ord_key(db: Database, c: Cols, om: Seq<int>, k: int)
    requires ord_link(c, db, om), red_ok(db), keys_ok(c),
    ensures
        has_key(t_ord(db), 0, Val::Int(k)) == has_o(c, k),
        has_o(c, k) ==> key_row(t_ord(db), 0, Val::Int(k)) == t_ord(db)[om[orow(c, k)]] && 0 <= orow(c, k) < c.n_o
            && okey(c, orow(c, k)) == k,
{
    let rows = t_ord(db);
    if has_o(c, k) {
        let p = orow(c, k);
        assert(0 <= om[p] < c.n_o);
        assert(colv(rows[om[p]], 0) == Val::Int(k));
        lemma_key_row_unique(rows, 0, Val::Int(k), om[p]);
    }
    if has_key(rows, 0, Val::Int(k)) {
        let i = key_pos(rows, 0, Val::Int(k));
        lemma_key_row(rows, 0, Val::Int(k));
        assert(covered(om, i));
        let p = choose|p: int| 0 <= p < om.len() && om[p] == i;
        assert(rows[om[p]][0] == Val::Int(okey(c, p)));
        assert(okey(c, p) == k);
    }
}

/// The customer with key `k`: the table lookup is the model's.
proof fn lemma_cus_key(db: Database, c: Cols, k: int)
    requires cus_link(c, db), red_ok(db), keys_ok(c),
    ensures
        has_key(t_cust(db), 0, Val::Int(k)) == has_c(c, k),
        has_c(c, k) ==> key_row(t_cust(db), 0, Val::Int(k)) == t_cust(db)[crow(c, k)] && 0 <= crow(c, k) < c.n_c
            && ckey(c, crow(c, k)) == k,
{
    let rows = t_cust(db);
    if has_c(c, k) {
        let r = crow(c, k);
        assert(colv(rows[r], 0) == Val::Int(k));
        lemma_key_row_unique(rows, 0, Val::Int(k), r);
    }
    if has_key(rows, 0, Val::Int(k)) {
        let r = key_pos(rows, 0, Val::Int(k));
        lemma_key_row(rows, 0, Val::Int(k));
        assert(rows[r][0] == Val::Int(ckey(c, r)));
        assert(ckey(c, r) == k);
    }
}

// ------------------------------------------------------------------------------------------------ the line

/// The names condition and the SELECT list's names through the classes of the two nations.
proof fn lemma_pair(ps: Seq<Literal>, x: Ctx, n1: Val, n2: Val)
    requires
        texts(ps),
        x.same == (ltext(ps[0]) == ltext(ps[1])),
    ensures ({
        let pr = pair_of(x, name_cls(ps, n1), name_cls(ps, n2));
        &&& names_ok(ps, n1, n2) == (pr >= 0)
        &&& pr >= 0 ==> pr <= 1 && n1 == krow(ps, 2 * pr)[0] && n2 == krow(ps, 2 * pr)[1]
    }),
{
}

/// The supplier and order classes of a line through the table lookups.
pub open spec fn chain_ok(db: Database, c: Cols, x: Ctx, ps: Seq<Literal>, lm: Seq<int>, om: Seq<int>) -> bool {
    &&& links(c, db, lm, om)
    &&& red_ok(db)
    &&& keys_ok(c)
    &&& ctx_ok(x, db, ps)
    &&& texts(ps)
    &&& tables_typed(db)
}

/// One lineitem row: the reduction's term `h1` is the model's line term.
pub proof fn lemma_line(db: Database, c: Cols, x: Ctx, ps: Seq<Literal>, phi: spec_fn(Row) -> int, lm: Seq<int>,
    om: Seq<int>, j: int)
    requires chain_ok(db, c, x, ps, lm, om), 0 <= j < c.n_l,
    ensures h1(db, ps, phi)(t_li(db)[lm[j]]) == line_term(c, x, ps, phi, j),
{
    let l = t_li(db)[lm[j]];
    assert(0 <= lm[j] < c.n_l);
    assert(li_typed(l));
    assert(l[0] == Val::Int(lkey(c, j)) && l[2] == Val::Int(lsupp(c, j)));
    let sk = lsupp(c, j);
    let ok = lkey(c, j);
    lemma_sup_key(db, c, sk);
    if !has_s(c, sk) {
        assert(s_cls(c, x, sk) == 0);
        assert(l_grp(c, x, j) == -1);
        return;
    }
    let s = t_sup(db)[srow(c, sk)];
    assert(sup_typed(s));
    let x2 = s + l;
    assert(x2[7] == l[0]);
    lemma_ord_key(db, c, om, ok);
    if !has_o(c, ok) {
        assert(o_cls(c, x, ok) == 0);
        assert(l_grp(c, x, j) == -1);
        return;
    }
    let q = orow(c, ok);
    let o = t_ord(db)[om[q]];
    assert(0 <= om[q] < c.n_o);
    assert(ord_typed(o));
    assert(o[1] == Val::Int(ocust(c, q)));
    let ck = ocust(c, q);
    let x3 = x2 + o;
    assert(x3[24] == o[1]);
    lemma_cus_key(db, c, ck);
    if !has_c(c, ck) {
        assert(c_cls(c, x, ck) == 0);
        assert(o_cls(c, x, ok) == 0);
        assert(l_grp(c, x, j) == -1);
        return;
    }
    let cu = t_cust(db)[crow(c, ck)];
    assert(cust_typed(cu));
    let x4 = x3 + cu;
    let sn = snat(c, srow(c, sk));
    let cn = cnat(c, crow(c, ck));
    assert(s[3] == Val::Int(sn) && cu[3] == Val::Int(cn));
    assert(x4[3] == s[3]);
    assert(nat_cls(x, sn) == nat_cls_db(db, ps, sn));
    assert(nat_cls(x, cn) == nat_cls_db(db, ps, cn));
    if !has_key(t_nat(db), 0, Val::Int(sn)) {
        assert(s_cls(c, x, sk) == 0);
        assert(l_grp(c, x, j) == -1);
        return;
    }
    let n1 = key_row(t_nat(db), 0, Val::Int(sn));
    lemma_key_row(t_nat(db), 0, Val::Int(sn));
    assert(nat_typed(n1));
    let x5 = x4 + n1;
    assert(x5[35] == cu[3]);
    if !has_key(t_nat(db), 0, Val::Int(cn)) {
        assert(c_cls(c, x, ck) == 0);
        assert(o_cls(c, x, ok) == 0);
        assert(l_grp(c, x, j) == -1);
        return;
    }
    let n2 = key_row(t_nat(db), 0, Val::Int(cn));
    lemma_key_row(t_nat(db), 0, Val::Int(cn));
    assert(nat_typed(n2));
    let full = x5 + n2;
    assert(h1(db, ps, phi)(l) == h6(ps, phi)(full));
    // the joined row: the joins hold by construction
    assert(full.len() == 48);
    assert(full[0] == s[0] && full[9] == l[2] && full[23] == o[0] && full[7] == l[0]);
    assert(full[32] == cu[0] && full[24] == o[1] && full[3] == s[3] && full[40] == n1[0]);
    assert(full[35] == cu[3] && full[44] == n2[0] && full[41] == n1[1] && full[45] == n2[1]);
    assert(full[17] == l[10] && full[12] == l[5] && full[13] == l[6]);
    assert(s[0] == Val::Int(skey(c, srow(c, sk))));
    assert(o[0] == Val::Int(okey(c, q)));
    assert(cu[0] == Val::Int(ckey(c, crow(c, ck))));
    let sc = name_cls(ps, n1[1]);
    let cc = name_cls(ps, n2[1]);
    assert(s_cls(c, x, sk) == sc);
    assert(c_cls(c, x, ck) == cc);
    assert(o_cls(c, x, ok) == cc);
    lemma_pair(ps, x, n1[1], n2[1]);
    let d = lship(c, j);
    assert(l[10] == Val::Date(d));
    assert(jq(ps, full) == (names_ok(ps, n1[1], n2[1]) && win_lo() <= d <= win_hi()));
    if jq(ps, full) {
        let gi = l_grp(c, x, j);
        let pr = pair_of(x, sc, cc);
        assert(gi == 2 * pr + yslot(d));
        lemma_win_year(d);
        assert(year_of(dday(full[17])) == 1995 + gi % 2) by {
            reveal(year_of);
            assert(dday(full[17]) == d);
        }
        assert(vol_of(ncoef(full[12]), ncoef(full[13])) == l_vol(c, j)) by {
            reveal(vol_of);
            assert(l[5] == (Val::Num { coeff: lprice(c, j), scale: 2 }));
            assert(l[6] == (Val::Num { coeff: ldisc(c, j), scale: 2 }));
        }
        assert(krow(ps, gi)[0] == krow(ps, 2 * pr)[0] && krow(ps, gi)[1] == krow(ps, 2 * pr)[1]);
        assert(px(full) =~= lrow7(ps, gi, l_vol(c, j)));
    } else {
        assert(l_grp(c, x, j) == -1);
    }
}

} // verus!
