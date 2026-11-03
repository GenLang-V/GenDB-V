//! The statement's output: the candidates whose s_acctbal reaches a threshold `thr` are built, sorted and cut to
//! 100 rows. `lemma_final` proves that this is an allowed output whenever at least 100 candidates reach `thr` or
//! all of them do: the sorted selected rows followed by the sorted rest form a sorted permutation of the body
//! (every selected row's s_acctbal exceeds every other one's, and s_acctbal DESC is the first ORDER BY key).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::compare;
use crate::spec::order::*;
use crate::query::query_spec_at;
use crate::exec::value::EVal;
use crate::exec::value::view_row;
use crate::bridge::order::{keys_ok, key_ok, all_keys_ok, lemma_sort_rows};
use crate::bridge::typing::val_family;
use crate::link::query::proj_all;
use crate::link::join::keep;
use crate::link::outcome::lemma_outcome_sorted;
use crate::stores::suppliers::interface::common::read::text_slice;
use vstd::slice::slice_to_vec;
use super::common::relops::*;
use super::tables::*;
use super::q2spec::*;
use super::sqlq::*;
use super::sqlrel::*;
use super::scan::grp;

verus! {

/// Candidates reaching / not reaching the threshold.
pub open spec fn ge_f(thr: int) -> spec_fn(Cand) -> bool {
    |c: Cand| c.acct >= thr
}

pub open spec fn lt_f(thr: int) -> spec_fn(Cand) -> bool {
    |c: Cand| c.acct < thr
}

pub open spec fn row_f(t: Tabs, m: Prm) -> spec_fn(Cand) -> Row {
    |c: Cand| out_row_spec(t, m, c)
}

/// Comparison families of the ORDER BY keys: s_acctbal (numeric), n_name, s_name (text), p_partkey (integer).
pub open spec fn q_fams() -> Seq<int> {
    seq![1int, 3, 3, 1]
}

proof fn lemma_row_keys_ok(t: Tabs, m: Prm, c: Cand)
    requires tabs_typed(t), cand_ok(t, m, c),
    ensures
        keys_ok(q_keys(), q_fams(), out_row_spec(t, m, c)),
        out_row_spec(t, m, c)[0] == (Val::Num { coeff: c.acct as int, scale: 2 }),
        out_row_spec(t, m, c).len() == 8,
{
    lemma_out_row(t, m, c);
    let r = out_row_spec(t, m, c);
    assert(s_typed(t.s[c.supp as int]) && n_typed(t.n[c.nation as int]) && p_typed(t.p[c.part as int]));
    assert forall|i: int| 0 <= i < 4 implies #[trigger] key_ok(q_keys()[i], q_fams()[i], r) by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else {}
    }
}

/// A row of a larger s_acctbal comes first.
proof fn lemma_cross(t: Tabs, m: Prm, c1: Cand, c2: Cand)
    requires tabs_typed(t), cand_ok(t, m, c1), cand_ok(t, m, c2), c1.acct > c2.acct,
    ensures keys_cmp(q_keys(), out_row_spec(t, m, c1), out_row_spec(t, m, c2)) < 0,
{
    lemma_row_keys_ok(t, m, c1);
    lemma_row_keys_ok(t, m, c2);
    let (r1, r2) = (out_row_spec(t, m, c1), out_row_spec(t, m, c2));
    crate::link::expr::lemma_compare_num(c1.acct as int, 2, c2.acct as int, 2);
    crate::link::expr::lemma_align_same(c1.acct as int, 2);
    crate::link::expr::lemma_align_same(c2.acct as int, 2);
    assert(crate::spec::numeric::max_nat(2, 2) == 2);
    assert(compare(r1[0], r2[0]) == Some(1int));
    assert(key_cmp(q_keys()[0], r1, r2) == -1);
}

/// The output rows built from the candidates reaching `thr`, sorted and cut to 100, are an allowed output, when at
/// least 100 candidates reach `thr` or all of them do.
pub proof fn lemma_final(db: Database, ps: Seq<Literal>, cs: Seq<Cand>, thr: int)
    requires
        db.tables.len() == 8,
        tabs_typed(tabs_of(db)), tabs_nodup(tabs_of(db)), keys_unique(tabs_of(db)),
        params_ok(ps),
        like_all_ok(tabs_of(db), prm_of(ps)) || prod5(tabs_of(db)).len() == 0,
        cands_ok(tabs_of(db), prm_of(ps), cs),
        select(cs, ge_f(thr)).len() >= 100 || select(cs, lt_f(thr)).len() == 0,
    ensures
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(slice_rows(
            sort_rows(q_keys(), select(cs, ge_f(thr)).map_values(row_f(tabs_of(db), prm_of(ps)))), 0, Some(100nat)))),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    broadcast use vstd::multiset::group_multiset_axioms;
    let t = tabs_of(db);
    let m = prm_of(ps);
    let keys = q_keys();
    let fams = q_fams();
    let oq = query_spec_at(ps);
    lemma_query_shape(ps);
    lemma_eval_body_ok(db, ps);
    let body = proj_all(keep(prod5(t), q_f(t, m)), out_cols());
    assert(denote_body(db, oq) == Ok::<Relation, SqlError>(body));
    lemma_body_multiset(t, m, cs);
    assert(cs.map_values(|c: Cand| out_row_spec(t, m, c)) =~= cs.map_values(row_f(t, m)));
    let (a, b) = (select(cs, ge_f(thr)), select(cs, lt_f(thr)));
    let (ar, br) = (a.map_values(row_f(t, m)), b.map_values(row_f(t, m)));
    lemma_select_split_map(cs, ge_f(thr), lt_f(thr), row_f(t, m));
    lemma_select_members(cs, ge_f(thr));
    lemma_select_members(cs, lt_f(thr));
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] cand_ok(t, m, a[i]) && a[i].acct >= thr by {
        let x = choose|x: int| 0 <= x < cs.len() && cs[x] == a[i];
        assert(cand_ok(t, m, cs[x]));
    }
    assert forall|i: int| 0 <= i < b.len() implies #[trigger] cand_ok(t, m, b[i]) && b[i].acct < thr by {
        let x = choose|x: int| 0 <= x < cs.len() && cs[x] == b[i];
        assert(cand_ok(t, m, cs[x]));
    }
    assert(all_keys_ok(keys, fams, ar)) by {
        assert forall|i: int| 0 <= i < ar.len() implies keys_ok(keys, fams, #[trigger] ar[i]) by {
            assert(cand_ok(t, m, a[i]));
            lemma_row_keys_ok(t, m, a[i]);
        }
    }
    assert(all_keys_ok(keys, fams, br)) by {
        assert forall|i: int| 0 <= i < br.len() implies keys_ok(keys, fams, #[trigger] br[i]) by {
            assert(cand_ok(t, m, b[i]));
            lemma_row_keys_ok(t, m, b[i]);
        }
    }
    lemma_sort_rows(keys, fams, ar);
    lemma_sort_rows(keys, fams, br);
    let (sa, sb) = (sort_rows(keys, ar), sort_rows(keys, br));
    let p = sa + sb;
    assert(p.to_multiset() == body.to_multiset()) by {
        vstd::seq_lib::lemma_multiset_commutative(sa, sb);
    }
    assert(sorted_by(keys, p)) by {
        assert forall|i: int, j: int| 0 <= i < j < p.len() implies keys_cmp(keys, #[trigger] p[i], #[trigger] p[j]) <= 0 by {
            if j < sa.len() {
                assert(p[i] == sa[i] && p[j] == sa[j]);
            } else if i >= sa.len() {
                assert(p[i] == sb[i - sa.len()] && p[j] == sb[j - sa.len()]);
            } else {
                let (x, y) = (sa[i], sb[j - sa.len()]);
                assert(p[i] == x && p[j] == y);
                assert(sa.contains(x));
                assert(sa.to_multiset().count(x) > 0);
                assert(ar.contains(x));
                let ia = choose|ia: int| 0 <= ia < ar.len() && ar[ia] == x;
                assert(sb.contains(y));
                assert(sb.to_multiset().count(y) > 0);
                assert(br.contains(y));
                let ib = choose|ib: int| 0 <= ib < br.len() && br[ib] == y;
                assert(cand_ok(t, m, a[ia]) && cand_ok(t, m, b[ib]));
                lemma_cross(t, m, a[ia], b[ib]);
            }
        }
    }
    lemma_outcome_sorted(db, oq, body, p);
    assert(sa.len() == a.len() && sb.len() == b.len()) by {
        assert(sa.to_multiset().len() == ar.to_multiset().len());
        assert(sb.to_multiset().len() == br.to_multiset().len());
    }
    if a.len() >= 100 {
        assert(slice_rows(p, 0, Some(100nat)) =~= slice_rows(sa, 0, Some(100nat)));
    } else {
        assert(sb.len() == 0);
        assert(p =~= sa);
    }
}

// ------------------------------------------------------------------------------------------------ exec rows

/// Text value `j` of offsets `o` and bytes `y`, copied.
pub fn text_val(o: &[u64], y: &[u8], j: usize) -> (v: EVal)
    requires j + 1 < o@.len(), o@[j as int] <= o@[j + 1], o@[j + 1] <= y@.len(),
    ensures v@ == Val::Text(txt(o@, y@, j as int)),
{
    EVal::Text(slice_to_vec(text_slice(o, y, j)))
}

/// The output row of candidate `x`: s_acctbal, s_name, n_name, p_partkey, p_mfgr, s_address, s_phone, s_comment.
pub fn out_row(c: &Cols, x: Cand, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (r: Vec<EVal>)
    requires cols_ok(*c, t), cand_ok(t, m, x),
    ensures view_row(r@) == out_row_spec(t, m, x),
{
    proof { lemma_tabs_typed(*c, t); }
    let (i, j, n) = (x.part, x.supp, x.nation);
    assert(part_row_ok(c.p, t.p[i as int], i as int));
    assert(supp_row_ok(c.s, t.s[j as int], j as int));
    assert(nat_row_ok(c.n, t.n[n as int], n as int));
    let mut r: Vec<EVal> = Vec::new();
    r.push(EVal::Num { coeff: x.acct as i128, scale: 2 });
    r.push(text_val(c.s.name_o, c.s.name_y, j));
    r.push(text_val(c.n.name_o, c.n.name_y, n));
    proof { lemma_grp_bound(c.p.n as int, c.p.bs as int, c.p.ng as int, i as int); }
    let g = grp(i, c.p.bs);
    let pk = c.p.key_b[g] + c.p.key_c[i] as i64;
    r.push(EVal::Int(pk));
    let e = (c.p.mfgr_b[g] + c.p.mfgr_c[i] as u64) as usize;
    r.push(text_val(c.p.mfgr_o, c.p.mfgr_y, e));
    r.push(text_val(c.s.addr_o, c.s.addr_y, j));
    r.push(text_val(c.s.phone_o, c.s.phone_y, j));
    r.push(text_val(c.s.comm_o, c.s.comm_y, j));
    proof {
        lemma_out_row(t, m, x);
        assert(view_row(r@) =~= out_row_spec(t, m, x));
    }
    r
}

} // verus!
