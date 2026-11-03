//! The result rows from the supplier columns: per supplier row in stored (canonical) order, its output row
//! `[s_suppkey, s_name, s_address, s_phone, M]` when its key is a group of sum `M` (`answer::res_rows`).
//!
//! The hits come as a flag per supplier row (`emit_rows`) or as the increasing list of the hit rows (`emit_list`,
//! which visits only the listed rows; rows between two listed rows add nothing, `lemma_res_skip`).
//!
//! `mrow(s, j)` is supplier row `j` as far as the result reads it (columns 0, 1, 2 and 4; the others NULL); the
//! result over these rows is the result over every bound database's supplier rows (`lemma_res_db`).
use vstd::prelude::*;
use vstd::slice::slice_to_vec;
use crate::spec::value::*;
use crate::spec::limits::{int8_min, int8_max};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::bound_db;
use crate::exec::value::{EVal, view_row};
use crate::link::query::{view_rows, QuerySpec};
use crate::link::expr::ival;
use crate::stores::suppliers::interface::common::colfmt as sc;
use crate::stores::suppliers::interface::common::read as sr;
use super::model::*;
use super::body::*;
use super::answer::*;

verus! {

/// Supplier row `j` as far as the result reads it.
pub open spec fn mrow(s: Su, j: int) -> Row {
    seq![
        Val::Int(skey_v(s, j)),
        Val::Text(sc::text_of(s.name_o@, s.name_y@, j)),
        Val::Text(sc::text_of(s.addr_o@, s.addr_y@, j)),
        Val::Null,
        Val::Text(sc::text_of(s.phone_o@, s.phone_y@, j)),
        Val::Null,
        Val::Null
    ]
}

/// The supplier rows as far as the result reads them.
pub open spec fn mrows(s: Su) -> Seq<Row> {
    Seq::new(s.ns as nat, |j: int| mrow(s, j))
}

/// The result depends only on columns 0, 1, 2 and 4 of the supplier rows.
pub proof fn lemma_res_cols(a: Seq<Row>, b: Seq<Row>, g: QuerySpec, xs: Seq<Row>, m: int)
    requires
        a.len() == b.len(),
        forall|j: int| 0 <= j < a.len() ==> (#[trigger] a[j])[0] == b[j][0] && a[j][1] == b[j][1] && a[j][2] == b[j][2] && a[j][4] == b[j][4],
    ensures res_rows(a, g, xs, m) == res_rows(b, g, xs, m),
    decreases a.len(),
{
    if a.len() > 0 {
        let (ai, bi) = (a.drop_last(), b.drop_last());
        assert forall|j: int| 0 <= j < ai.len() implies (#[trigger] ai[j])[0] == bi[j][0] && ai[j][1] == bi[j][1] && ai[j][2] == bi[j][2] && ai[j][4] == bi[j][4] by {
            assert(ai[j] == a[j] && bi[j] == b[j]);
        }
        lemma_res_cols(ai, bi, g, xs, m);
        assert(a[a.len() - 1] == a.last() && b[b.len() - 1] == b.last());
        assert(seq![a.last()[0]] =~= seq![b.last()[0]]);
        let mv = Val::Num { coeff: m, scale: 4 };
        assert(res_row(a.last(), mv) =~= res_row(b.last(), mv));
    }
}

/// For every bound database: the result over its supplier rows is the result over `mrows`, and every supplier
/// key is a bigint.
pub proof fn lemma_res_db(s: Su, sv: StoresView, db: Database, g: QuerySpec, xs: Seq<Row>, m: int)
    requires
        bound_db(sv, db),
        su_link(s, sv.suppliers),
    ensures
        su_shape(s),
        res_rows(db.tables[5], g, xs, m) == res_rows(mrows(s), g, xs, m),
        forall|j: int| 0 <= j < s.ns ==> int8_min() <= #[trigger] skey_v(s, j) <= int8_max(),
{
    lemma_su_db(s, sv, db);
    lemma_supp_typed(db);
    let t5 = db.tables[5];
    let ms = mrows(s);
    assert forall|j: int| 0 <= j < t5.len() implies (#[trigger] t5[j])[0] == ms[j][0] && t5[j][1] == ms[j][1] && t5[j][2] == ms[j][2] && t5[j][4] == ms[j][4] by {
        assert(su_row_ok(s, t5[j], j));
    }
    lemma_res_cols(t5, ms, g, xs, m);
    assert forall|j: int| 0 <= j < s.ns implies int8_min() <= #[trigger] skey_v(s, j) <= int8_max() by {
        assert(su_row_ok(s, t5[j], j));
        assert(supp_typed(t5[j]));
    }
}

/// The key of supplier row `j`.
pub fn skey_at(s: &Su, j: usize) -> (k: i128)
    requires su_shape(*s), j < s.ns,
    ensures k == skey_v(*s, j as int),
{
    proof {
        crate::stores::suppliers::interface::common::read::lemma_div_lt(j as int, s.bs as int, s.key_base@.len() as int);
    }
    let b = (j as u64 / s.bs) as usize;
    s.key_base[b] as i128 + s.key[j] as i128
}

/// The output row of supplier row `j` with revenue `m` (scale 4).
fn out_row_exec(s: &Su, j: usize, m: i128) -> (row: Vec<EVal>)
    requires
        su_shape(*s), j < s.ns,
        int8_min() <= skey_v(*s, j as int) <= int8_max(),
    ensures view_row(row@) == res_row(mrow(*s, j as int), Val::Num { coeff: m as int, scale: 4 }),
{
    proof {
        // instantiate `su_shape`'s text ranges at row `j` (all three columns at once)
        assert(sc::text_range_ok(s.name_o@, s.name_y@, j as int));
        assert(sc::text_range_ok(s.addr_o@, s.addr_y@, j as int));
        assert(sc::text_range_ok(s.phone_o@, s.phone_y@, j as int));
    }
    let k = skey_at(s, j);
    let name = slice_to_vec(sr::text_slice(s.name_o, s.name_y, j));
    let addr = slice_to_vec(sr::text_slice(s.addr_o, s.addr_y, j));
    let phone = slice_to_vec(sr::text_slice(s.phone_o, s.phone_y, j));
    let row = vec![EVal::Int(k as i64), EVal::Text(name), EVal::Text(addr), EVal::Text(phone), EVal::Num { coeff: m, scale: 4 }];
    proof {
        assert(view_row(row@) =~= res_row(mrow(*s, j as int), Val::Num { coeff: m as int, scale: 4 }));
    }
    row
}

/// The result rows of the hits (`hits[j]`: supplier row `j`'s key is a group of sum `m`).
pub fn emit_rows(s: &Su, m: i128, hits: &Vec<bool>, Ghost(g): Ghost<QuerySpec>, Ghost(xs): Ghost<Seq<Row>>) -> (rows: Vec<Vec<EVal>>)
    requires
        su_shape(*s),
        hits@.len() == s.ns,
        forall|j: int| 0 <= j < s.ns ==> #[trigger] hits@[j] == hit_m(g, xs, m as int, mrow(*s, j)),
        forall|j: int| 0 <= j < s.ns ==> int8_min() <= #[trigger] skey_v(*s, j) <= int8_max(),
    ensures view_rows(rows@) == res_rows(mrows(*s), g, xs, m as int),
{
    let ghost ms = mrows(*s);
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut j: usize = 0;
    proof {
        assert(ms.take(0) =~= Seq::<Row>::empty());
        assert(view_rows(rows@) =~= Seq::<Row>::empty());
    }
    while j < s.ns
        invariant
            su_shape(*s),
            hits@.len() == s.ns,
            forall|j: int| 0 <= j < s.ns ==> #[trigger] hits@[j] == hit_m(g, xs, m as int, mrow(*s, j)),
            forall|j: int| 0 <= j < s.ns ==> int8_min() <= #[trigger] skey_v(*s, j) <= int8_max(),
            ms == mrows(*s),
            j <= s.ns,
            view_rows(rows@) == res_rows(ms.take(j as int), g, xs, m as int),
        decreases s.ns - j,
    {
        proof {
            assert(ms.take(j + 1).drop_last() =~= ms.take(j as int));
            assert(ms.take(j + 1).last() == mrow(*s, j as int));
        }
        if hits[j] {
            let row = out_row_exec(s, j, m);
            proof {
                crate::link::outcome::lemma_view_rows_push(rows@, row);
            }
            rows.push(row);
        } else {
            proof {
                assert(res_rows(ms.take(j as int), g, xs, m as int) + Seq::<Row>::empty() =~= res_rows(ms.take(j as int), g, xs, m as int));
            }
        }
        j = j + 1;
    }
    proof {
        assert(ms.take(s.ns as int) =~= ms);
    }
    rows
}

/// Supplier row `j` is among the entries of `l`.
pub open spec fn listed_row(l: Seq<usize>, j: int) -> bool {
    exists|i: int| 0 <= i < l.len() && l[i] as int == j
}

/// `l` lists, in increasing order, exactly the supplier rows whose key is a group of sum `m`.
pub open spec fn lists_hits(l: Seq<usize>, s: Su, g: QuerySpec, xs: Seq<Row>, m: int) -> bool {
    &&& forall|i: int| 0 <= i < l.len() ==> (#[trigger] l[i]) < s.ns
    &&& forall|i1: int, i2: int| #![trigger l[i1], l[i2]] 0 <= i1 < i2 < l.len() ==> l[i1] < l[i2]
    &&& forall|j: int| 0 <= j < s.ns ==> (hit_m(g, xs, m, mrow(s, j)) <==> #[trigger] listed_row(l, j))
}

/// The hits of a plan: a flag per supplier row, or the increasing list of the hit rows.
pub enum Hits {
    Dense(Vec<bool>),
    List(Vec<usize>),
}

/// The hits are exactly the supplier rows whose key is a group of sum `m`.
pub open spec fn hits_ok(h: Hits, s: Su, g: QuerySpec, xs: Seq<Row>, m: int) -> bool {
    match h {
        Hits::Dense(v) => v@.len() == s.ns && forall|j: int| 0 <= j < s.ns ==> #[trigger] v@[j] == hit_m(g, xs, m, mrow(s, j)),
        Hits::List(l) => lists_hits(l@, s, g, xs, m),
    }
}

/// Rows `[a, b)` without a hit add no result row.
pub proof fn lemma_res_skip(ms: Seq<Row>, g: QuerySpec, xs: Seq<Row>, m: int, a: int, b: int)
    requires
        0 <= a <= b <= ms.len(),
        forall|j: int| a <= j < b ==> !hit_m(g, xs, m, #[trigger] ms[j]),
    ensures res_rows(ms.take(b), g, xs, m) == res_rows(ms.take(a), g, xs, m),
    decreases b - a,
{
    if a < b {
        lemma_res_skip(ms, g, xs, m, a, b - 1);
        assert(ms.take(b).drop_last() =~= ms.take(b - 1));
        assert(ms.take(b).last() == ms[b - 1]);
        assert(res_rows(ms.take(b - 1), g, xs, m) + Seq::<Row>::empty() =~= res_rows(ms.take(b - 1), g, xs, m));
    }
}

/// The result rows of an increasing list of the hit rows: only the listed rows are visited.
pub fn emit_list(s: &Su, m: i128, l: &Vec<usize>, Ghost(g): Ghost<QuerySpec>, Ghost(xs): Ghost<Seq<Row>>) -> (rows: Vec<Vec<EVal>>)
    requires
        su_shape(*s),
        lists_hits(l@, *s, g, xs, m as int),
        forall|j: int| 0 <= j < s.ns ==> int8_min() <= #[trigger] skey_v(*s, j) <= int8_max(),
    ensures view_rows(rows@) == res_rows(mrows(*s), g, xs, m as int),
{
    let ghost ms = mrows(*s);
    let ghost lv = l@;
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let n = l.len();
    let mut i: usize = 0;
    // the rows below `p` are emitted; the listed rows from entry `i` on are at least `p`
    let mut p: usize = 0;
    proof {
        assert(ms.take(0) =~= Seq::<Row>::empty());
        assert(view_rows(rows@) =~= Seq::<Row>::empty());
    }
    while i < n
        invariant
            su_shape(*s),
            lists_hits(lv, *s, g, xs, m as int),
            forall|j: int| 0 <= j < s.ns ==> int8_min() <= #[trigger] skey_v(*s, j) <= int8_max(),
            ms == mrows(*s),
            l@ == lv,
            n == lv.len(),
            i <= n,
            p <= s.ns,
            forall|i2: int| 0 <= i2 < i ==> #[trigger] lv[i2] < p,
            i < n ==> p <= lv[i as int],
            view_rows(rows@) == res_rows(ms.take(p as int), g, xs, m as int),
        decreases n - i,
    {
        let h = l[i];
        proof {
            assert(h < s.ns);
            assert forall|j: int| p <= j < h implies !hit_m(g, xs, m as int, #[trigger] ms[j]) by {
                assert(ms[j] == mrow(*s, j));
                if hit_m(g, xs, m as int, mrow(*s, j)) {
                    assert(listed_row(lv, j));
                    let i2 = choose|i2: int| 0 <= i2 < lv.len() && lv[i2] as int == j;
                    if i2 < i {
                        assert(lv[i2] < p);
                    } else if i2 > i {
                        assert(lv[i as int] < lv[i2]);
                    }
                }
            }
            lemma_res_skip(ms, g, xs, m as int, p as int, h as int);
            assert(listed_row(lv, h as int));
            assert(hit_m(g, xs, m as int, mrow(*s, h as int)));
            assert(ms.take(h + 1).drop_last() =~= ms.take(h as int));
            assert(ms.take(h + 1).last() == mrow(*s, h as int));
        }
        let row = out_row_exec(s, h, m);
        proof {
            crate::link::outcome::lemma_view_rows_push(rows@, row);
        }
        rows.push(row);
        p = h + 1;
        i = i + 1;
        proof {
            if i < n {
                assert(lv[i - 1] < lv[i as int]);
            }
        }
    }
    proof {
        assert forall|j: int| p <= j < s.ns implies !hit_m(g, xs, m as int, #[trigger] ms[j]) by {
            assert(ms[j] == mrow(*s, j));
            if hit_m(g, xs, m as int, mrow(*s, j)) {
                assert(listed_row(lv, j));
                let i2 = choose|i2: int| 0 <= i2 < lv.len() && lv[i2] as int == j;
                assert(lv[i2] < p);
            }
        }
        lemma_res_skip(ms, g, xs, m as int, p as int, s.ns as int);
        assert(ms.take(s.ns as int) =~= ms);
    }
    rows
}

/// The result rows of the hits, either form.
pub fn emit_hits(s: &Su, m: i128, hits: &Hits, Ghost(g): Ghost<QuerySpec>, Ghost(xs): Ghost<Seq<Row>>) -> (rows: Vec<Vec<EVal>>)
    requires
        su_shape(*s),
        hits_ok(*hits, *s, g, xs, m as int),
        forall|j: int| 0 <= j < s.ns ==> int8_min() <= #[trigger] skey_v(*s, j) <= int8_max(),
    ensures view_rows(rows@) == res_rows(mrows(*s), g, xs, m as int),
{
    match hits {
        Hits::Dense(v) => emit_rows(s, m, v, Ghost(g), Ghost(xs)),
        Hits::List(l) => emit_list(s, m, l, Ghost(g), Ghost(xs)),
    }
}

} // verus!
