//! The answer's rows `s_name, s_address`, built in the body's order (supplier-major, then nation, as in
//! `FROM supplier, nation`) as two text columns (`build_output`): for a supplier with a nation row named `$3`
//! holding its nation key (`nation_rows`, `find_nation`, tested first) and a qualifying supplier key
//! (`supp::SuppSet`), its one row (nation keys are unique). They are exactly `out_rows` (`out_ok`). `names_sorted`
//! checks that the names do not decrease (then the body's order is already the `ORDER BY s_name` order); `rows_of`
//! turns the columns into rows for the sort of the general case.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::{Literal, OrderKey};
use crate::spec::relation::product_rows;
use crate::spec::order::*;
use crate::spec::text::lex_cmp;
use crate::spec::scalar::compare;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::results::*;
use crate::exec::value::{EVal, view_row};
use crate::link::query::{text_at, view_rows};
use crate::link::join::{keep, lemma_keep_push, lemma_keep_append, lemma_keep_none, lemma_product_append};
use crate::link::expr::ival;
use crate::bridge::order::lemma_lex_cmp_trans;
use crate::agent::tables::*;
use crate::agent::ast::q_keys;
use crate::agent::params::nat_of;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::supp::{SuppSet, supp_ok, supp_has};
use crate::agent::den_body::lemma_joined_row;

verus! {

// ------------------------------------------------------------------------------------------------ nations

/// Whether the bytes `[s, e)` of `b` are `w`.
fn range_eq(b: &[u8], s: usize, e: usize, w: &[u8]) -> (r: bool)
    requires s <= e <= b@.len(),
    ensures r == (b@.subrange(s as int, e as int) == w@),
{
    let ghost v = b@.subrange(s as int, e as int);
    if e - s != w.len() {
        return false;
    }
    let mut j: usize = 0;
    while j < w.len()
        invariant s <= e <= b@.len(), e - s == w@.len(), j <= w@.len(), v == b@.subrange(s as int, e as int),
            forall|t: int| 0 <= t < j ==> v[t] == w@[t],
        decreases w@.len() - j,
    {
        if b[s + j] != w[j] {
            proof { assert(v[j as int] != w@[j as int]); }
            return false;
        }
        j = j + 1;
    }
    proof { assert(v =~= w@); }
    true
}

/// `ma` lists exactly the nation rows named `$3`.
pub open spec fn nations_ok(ma: Seq<usize>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& forall|i: int| 0 <= i < ma.len() ==> (#[trigger] ma[i]) < n_n(sv) && nname(sv, ma[i] as int) == nat_of(ps)
    &&& forall|a: int| 0 <= a < n_n(sv) && nname(sv, a) == nat_of(ps) ==> exists|i: int| 0 <= i < ma.len() && #[trigger] ma[i] == a
}

/// The nation rows named `$3`.
pub fn nation_rows(c: &Cols, want: &[u8], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (ma: Vec<usize>)
    requires cols_ok(*c, sv), want@ == nat_of(ps),
    ensures nations_ok(ma@, sv, ps),
{
    let nn = c.nn;
    let mut ma: Vec<usize> = Vec::new();
    let mut a: usize = 0;
    while a < nn
        invariant cols_ok(*c, sv), nn == c.nn, a <= nn, want@ == nat_of(ps),
            forall|i: int| 0 <= i < ma@.len() ==> (#[trigger] ma@[i]) < a && nname(sv, ma@[i] as int) == nat_of(ps),
            forall|a2: int| 0 <= a2 < a && nname(sv, a2) == nat_of(ps) ==> exists|i: int| 0 <= i < ma@.len() && #[trigger] ma@[i] == a2,
        decreases nn - a,
    {
        let (s, e) = text_range(c.nname, a, Ghost(nname_col(sv)), Ghost(n_n(sv) as int));
        let m = range_eq(c.nname.bytes, s, e, want);
        let ghost m0 = ma@;
        if m {
            ma.push(a);
        }
        proof {
            assert forall|a2: int| 0 <= a2 < a + 1 && nname(sv, a2) == nat_of(ps) implies exists|i: int| 0 <= i < ma@.len() && #[trigger] ma@[i] == a2 by {
                if a2 < a {
                    let i = choose|i: int| 0 <= i < m0.len() && #[trigger] m0[i] == a2;
                    assert(ma@[i] == m0[i]);
                } else {
                    assert(ma@[m0.len() as int] == a2);
                }
            }
        }
        a = a + 1;
    }
    ma
}

// ------------------------------------------------------------------------------------------------ the rows

/// The rows of the suppliers `0..r` (all nation rows), in the body's order.
#[verifier::opaque]
pub open spec fn rows_upto(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, r: int) -> Seq<Row> {
    keep(product_rows(supp_rows(sv).take(r), nat_rows(sv)), out_f(sv, ps, lo, hi)).map_values(|x: Row| out_proj(x))
}

/// The rows of supplier row `r` with all nation rows.
#[verifier::opaque]
pub open spec fn rows_of_supp(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, r: int) -> Seq<Row> {
    keep(nat_rows(sv).map_values(|y: Row| supp_rows(sv)[r] + y), out_f(sv, ps, lo, hi)).map_values(|z: Row| out_proj(z))
}

/// No supplier yet: no rows; all suppliers: the body's rows.
proof fn lemma_rows_upto_ends(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int)
    ensures
        rows_upto(sv, ps, lo, hi, 0) == Seq::<Row>::empty(),
        rows_upto(sv, ps, lo, hi, n_s(sv) as int) == out_rows(sv, ps, lo, hi),
{
    reveal(rows_upto);
    assert(supp_rows(sv).take(0) =~= Seq::<Row>::empty());
    assert(product_rows(Seq::<Row>::empty(), nat_rows(sv)) == Seq::<Row>::empty());
    assert(rows_upto(sv, ps, lo, hi, 0) =~= Seq::<Row>::empty());
    assert(supp_rows(sv).take(n_s(sv) as int) =~= supp_rows(sv));
}

/// One supplier row more: its rows with all nations follow.
proof fn lemma_rows_upto_step(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, r: int)
    requires 0 <= r < n_s(sv),
    ensures rows_upto(sv, ps, lo, hi, r + 1) == rows_upto(sv, ps, lo, hi, r) + rows_of_supp(sv, ps, lo, hi, r),
{
    reveal(rows_upto);
    reveal(rows_of_supp);
    let s = supp_rows(sv);
    let n = nat_rows(sv);
    let x = s[r];
    let f = out_f(sv, ps, lo, hi);
    assert(s.take(r + 1) =~= s.take(r) + seq![x]);
    lemma_product_append(s.take(r), seq![x], n);
    let one = product_rows(seq![x], n);
    assert(seq![x].drop_last() =~= Seq::<Row>::empty());
    assert(product_rows(Seq::<Row>::empty(), n) == Seq::<Row>::empty());
    assert(one =~= n.map_values(|y: Row| x + y));
    lemma_keep_append(product_rows(s.take(r), n), one, f);
    let ka = keep(product_rows(s.take(r), n), f);
    let kb = keep(one, f);
    assert((ka + kb).map_values(|z: Row| out_proj(z)) =~= ka.map_values(|z: Row| out_proj(z)) + kb.map_values(|z: Row| out_proj(z)));
}

/// The output condition on supplier row `r` with nation row `a`.
proof fn lemma_out_f_at(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, r: int, a: int)
    requires stores_wf(sv), 0 <= r < n_s(sv), 0 <= a < n_n(sv),
    ensures ({
        let x = supp_rows(sv)[r] + nat_rows(sv)[a];
        &&& out_f(sv, ps, lo, hi)(x) == (in_supp(sv, ps, lo, hi, sk(sv)[r] as int) && snk(sv)[r] == nk(sv)[a] && nname(sv, a) == nat_of(ps))
        &&& out_proj(x) == seq![Val::Text(sname(sv, r)), Val::Text(saddr(sv, r))]
    }),
{
    lemma_joined_row(sv, r, a);
    let x = supp_rows(sv)[r] + nat_rows(sv)[a];
    assert(ival(x[0]) == sk(sv)[r] as int);
    assert((x[3] == x[7]) == (snk(sv)[r] == nk(sv)[a]));
    assert((x[8] == Val::Text(nat_of(ps))) == (nname(sv, a) == nat_of(ps)));
    assert(out_proj(x) =~= seq![Val::Text(sname(sv, r)), Val::Text(saddr(sv, r))]);
}

/// The rows of supplier row `r`: none when it is not in `in_supp` or no nation row named `$3` has its nation key;
/// otherwise exactly one (nation keys are unique).
proof fn lemma_rows_of_supp(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, r: int, found: Option<int>)
    requires
        stores_wf(sv), keys_unique(nk(sv)), 0 <= r < n_s(sv),
        found matches Some(a) ==> 0 <= a < n_n(sv) && in_supp(sv, ps, lo, hi, sk(sv)[r] as int) && snk(sv)[r] == nk(sv)[a]
            && nname(sv, a) == nat_of(ps),
        found is None ==> !in_supp(sv, ps, lo, hi, sk(sv)[r] as int)
            || forall|a: int| 0 <= a < n_n(sv) ==> !(snk(sv)[r] == #[trigger] nk(sv)[a] && nname(sv, a) == nat_of(ps)),
    ensures rows_of_supp(sv, ps, lo, hi, r) == match found {
        Some(a) => seq![seq![Val::Text(sname(sv, r)), Val::Text(saddr(sv, r))]],
        None => Seq::<Row>::empty(),
    },
{
    reveal(rows_of_supp);
    let x = supp_rows(sv)[r];
    let f = out_f(sv, ps, lo, hi);
    let ms = nat_rows(sv).map_values(|y: Row| x + y);
    assert forall|i: int| 0 <= i < ms.len() implies (#[trigger] ms[i]) == x + nat_rows(sv)[i] by {}
    match found {
        Some(a) => {
            let pos = seq![a];
            assert forall|i: int| 0 <= i < ms.len() && f(#[trigger] ms[i]) implies exists|t: int| 0 <= t < pos.len() && pos[t] == i by {
                lemma_out_f_at(sv, ps, lo, hi, r, i);
                assert(nk(sv)[i] == nk(sv)[a]);
                assert(i == a);
                assert(pos[0] == i);
            }
            lemma_out_f_at(sv, ps, lo, hi, r, a);
            crate::link::join::lemma_keep_positions(ms, f, pos);
            assert(pos.map_values(|p: int| ms[p]) =~= seq![ms[a]]);
            assert(seq![ms[a]].map_values(|z: Row| out_proj(z)) =~= seq![out_proj(ms[a])]);
        },
        None => {
            assert forall|i: int| 0 <= i < ms.len() implies !f(#[trigger] ms[i]) by {
                lemma_out_f_at(sv, ps, lo, hi, r, i);
            }
            lemma_keep_none(ms, f);
            assert(Seq::<Row>::empty().map_values(|z: Row| out_proj(z)) =~= Seq::<Row>::empty());
        },
    }
}

/// A text column under construction holds the texts `ts`.
#[verifier::opaque]
pub open spec fn col_holds(offs: Seq<usize>, bytes: Seq<u8>, ts: Seq<Seq<u8>>) -> bool {
    &&& offs.len() == ts.len() + 1 && offs.last() == bytes.len() && offs[0] == 0
    &&& forall|i: int| 0 <= i < ts.len() ==> #[trigger] offs[i] <= offs[i + 1] && offs[i + 1] <= bytes.len()
    &&& forall|i: int| 0 <= i < ts.len() ==> #[trigger] bytes.subrange(offs[i] as int, offs[i + 1] as int) == ts[i]
}

/// Append one text to a column.
fn col_push(offs: &mut Vec<usize>, bytes: &mut Vec<u8>, src: &[u8], s: usize, e: usize, Ghost(ts): Ghost<Seq<Seq<u8>>>)
    requires col_holds(old(offs)@, old(bytes)@, ts), s <= e <= src@.len(), old(bytes)@.len() + (e - s) <= usize::MAX,
    ensures
        col_holds(final(offs)@, final(bytes)@, ts.push(src@.subrange(s as int, e as int))),
        final(bytes)@.len() == old(bytes)@.len() + (e - s),
{
    let ghost (o0, b0) = (offs@, bytes@);
    proof { reveal(col_holds); }
    let value = vstd::slice::slice_subrange(src, s, e);
    push_text(offs, bytes, value);
    proof {
        reveal(col_holds);
        let t2 = ts.push(src@.subrange(s as int, e as int));
        assert forall|i: int| 0 <= i < t2.len() implies #[trigger] offs@[i] <= offs@[i + 1] && offs@[i + 1] <= bytes@.len() by {
            if i < ts.len() {
                assert(offs@[i] == o0[i] && offs@[i + 1] == o0[i + 1]);
            }
        }
        assert forall|i: int| 0 <= i < t2.len() implies #[trigger] bytes@.subrange(offs@[i] as int, offs@[i + 1] as int) == t2[i] by {
            if i < ts.len() {
                assert(offs@[i] == o0[i] && offs@[i + 1] == o0[i + 1]);
                assert(bytes@.subrange(o0[i] as int, o0[i + 1] as int) =~= b0.subrange(o0[i] as int, o0[i + 1] as int));
            } else {
                assert(offs@[i] == b0.len());
                assert(bytes@.subrange(b0.len() as int, bytes@.len() as int) =~= value@);
            }
        }
    }
}

/// An empty column holds no text.
proof fn lemma_col_empty(offs: Seq<usize>, bytes: Seq<u8>)
    requires offs == seq![0usize], bytes == Seq::<u8>::empty(),
    ensures col_holds(offs, bytes, Seq::empty()),
{
    reveal(col_holds);
}

/// A finished column: well formed for its row count, value `i` is text `i`.
proof fn lemma_col_done(offs: Vec<usize>, bytes: Vec<u8>, ts: Seq<Seq<u8>>)
    requires col_holds(offs@, bytes@, ts),
    ensures
        column_wf(ResultColumn::Text { offsets: offs, bytes }, ts.len()),
        forall|i: int| 0 <= i < ts.len() ==> #[trigger] column_value(ResultColumn::Text { offsets: offs, bytes }, i) == Val::Text(ts[i]),
{
    reveal(col_holds);
    assert forall|i: int| 0 <= i < ts.len() implies #[trigger] offs@[i] <= offs@[i + 1] && offs@[i + 1] <= bytes@.len() by {
        assert(ts[i] == ts[i]);
    }
}

/// The columns' rows are `rows`: names and addresses of two-value text rows.
pub open spec fn out_ok(rc: ResultColumns, rows: Seq<Row>) -> bool {
    &&& columns_wf(rc) && columns_view(rc) == rows
    &&& rc.columns@.len() == 2 && rc.columns@[0] is Text && rc.columns@[1] is Text
    &&& forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == 2 && rows[i][0] is Text && rows[i][1] is Text
}

/// Offsets of a well-formed text column do not decrease.
proof fn lemma_offs_mono(t: crate::link::query::TextView, n: int, a: int, b: int)
    requires crate::link::query::text_wf(t, n), 0 <= a <= b <= n, n > 0,
    ensures 0 <= t.offsets[a] <= t.offsets[b] <= t.bytes.len(),
    decreases b - a,
{
    if a < b {
        lemma_offs_mono(t, n, a, b - 1);
        assert(t.offsets[b - 1] <= t.offsets[b]);
    } else if a < n {
        assert(0 <= t.offsets[a] <= t.offsets[a + 1]);
    } else {
        assert(0 <= t.offsets[n - 1] <= t.offsets[n] <= t.bytes.len());
    }
}

/// A nation row named `$3` with key `v`, if any.
fn find_nation(c: &Cols, ma: &Vec<usize>, v: i64, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Option<usize>)
    requires cols_ok(*c, sv), nations_ok(ma@, sv, ps),
    ensures
        r matches Some(a) ==> a < n_n(sv) && nk(sv)[a as int] == v && nname(sv, a as int) == nat_of(ps),
        r is None ==> forall|a: int| 0 <= a < n_n(sv) ==> !(v == #[trigger] nk(sv)[a] && nname(sv, a) == nat_of(ps)),
{
    let k = ma.len();
    let mut i: usize = 0;
    while i < k
        invariant cols_ok(*c, sv), nations_ok(ma@, sv, ps), k == ma@.len(), i <= k,
            forall|i2: int| 0 <= i2 < i ==> nk(sv)[#[trigger] ma@[i2] as int] != v,
        decreases k - i,
    {
        let a = ma[i];
        if c.nkey[a] == v {
            return Some(a);
        }
        i = i + 1;
    }
    proof {
        assert forall|a: int| 0 <= a < n_n(sv) implies !(v == #[trigger] nk(sv)[a] && nname(sv, a) == nat_of(ps)) by {
            if nname(sv, a) == nat_of(ps) {
                let i2 = choose|i2: int| 0 <= i2 < ma@.len() && #[trigger] ma@[i2] == a;
                assert(nk(sv)[ma@[i2] as int] != v);
            }
        }
    }
    None
}

/// The columns built so far hold the rows of the suppliers `0..r`, within the stored text sizes.
pub open spec fn out_inv(c: Cols, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, r: int, no: Seq<usize>, nb: Seq<u8>,
    ao: Seq<usize>, ab: Seq<u8>, rows: int, names: Seq<Seq<u8>>, addrs: Seq<Seq<u8>>) -> bool {
    &&& 0 <= r <= n_s(sv)
    &&& col_holds(no, nb, names) && col_holds(ao, ab, addrs) && names.len() == rows && addrs.len() == rows && rows <= r
    &&& rows_upto(sv, ps, lo, hi, r).len() == rows
    &&& forall|i: int| 0 <= i < rows ==> #[trigger] rows_upto(sv, ps, lo, hi, r)[i] == seq![Val::Text(names[i]), Val::Text(addrs[i])]
    &&& n_s(sv) > 0 ==> nb.len() <= sname_col(sv).offsets[r] - sname_col(sv).offsets[0]
        && ab.len() <= saddr_col(sv).offsets[r] - saddr_col(sv).offsets[0]
}

/// The output rows of supplier row `r`: one row when a nation row named `$3` has its key and its key qualifies.
fn emit_supplier(c: &Cols, ss: &SuppSet, ma: &Vec<usize>, r: usize, no: &mut Vec<usize>, nb: &mut Vec<u8>,
    ao: &mut Vec<usize>, ab: &mut Vec<u8>, rows: &mut usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>,
    Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>, Ghost(names): Ghost<Seq<Seq<u8>>>, Ghost(addrs): Ghost<Seq<Seq<u8>>>)
    -> (out: Ghost<(Seq<Seq<u8>>, Seq<Seq<u8>>)>)
    requires
        cols_ok(*c, sv), stores_wf(sv), keys_unique(nk(sv)), supp_ok(*ss, sv, ps, lo, hi), r < c.ns, nations_ok(ma@, sv, ps),
        out_inv(*c, sv, ps, lo, hi, r as int, old(no)@, old(nb)@, old(ao)@, old(ab)@, *old(rows) as int, names, addrs),
    ensures
        out_inv(*c, sv, ps, lo, hi, r + 1, final(no)@, final(nb)@, final(ao)@, final(ab)@, *final(rows) as int, out@.0, out@.1),
{
    let ghost (tn, ta) = (sname_col(sv), saddr_col(sv));
    let ghost base = rows_upto(sv, ps, lo, hi, r as int);
    let ns = c.ns;
    proof {
        lemma_rows_upto_step(sv, ps, lo, hi, r as int);
        lemma_offs_mono(tn, ns as int, 0, r as int);
        lemma_offs_mono(tn, ns as int, r as int, r as int + 1);
        lemma_offs_mono(ta, ns as int, 0, r as int);
        lemma_offs_mono(ta, ns as int, r as int, r as int + 1);
    }
    // the nation first (few rows match), then the supplier key
    let nation = find_nation(c, ma, c.snk[r], Ghost(sv), Ghost(ps));
    let found = match nation {
        Some(a) => if supp_has(ss, c.skey[r], Ghost(sv), Ghost(ps), Ghost(lo), Ghost(hi)) { Some(a) } else { None },
        None => None,
    };
    proof {
        let fg = match found { Some(a) => Some(a as int), None => None };
        lemma_rows_of_supp(sv, ps, lo, hi, r as int, fg);
    }
    if found.is_some() {
        let (s1, e1) = text_range(c.sname, r, Ghost(tn), Ghost(n_s(sv) as int));
        let (s2, e2) = text_range(c.saddr, r, Ghost(ta), Ghost(n_s(sv) as int));
        proof {
            assert(c.sname.bytes@.len() == c.sname.blen && c.saddr.bytes@.len() == c.saddr.blen);
        }
        col_push(no, nb, c.sname.bytes, s1, e1, Ghost(names));
        col_push(ao, ab, c.saddr.bytes, s2, e2, Ghost(addrs));
        let ghost names2 = names.push(sname(sv, r as int));
        let ghost addrs2 = addrs.push(saddr(sv, r as int));
        *rows = *rows + 1;
        proof {
            let after = rows_upto(sv, ps, lo, hi, r as int + 1);
            assert(after =~= base.push(seq![Val::Text(sname(sv, r as int)), Val::Text(saddr(sv, r as int))]));
            assert forall|i: int| 0 <= i < *rows implies #[trigger] after[i] == seq![Val::Text(names2[i]), Val::Text(addrs2[i])] by {
                if i < *rows - 1 {
                    assert(after[i] == base[i]);
                }
            }
        }
        Ghost((names2, addrs2))
    } else {
        proof {
            assert(rows_upto(sv, ps, lo, hi, r as int + 1) =~= base);
        }
        Ghost((names, addrs))
    }
}

/// Two well-formed columns of `n` rows make well-formed result columns.
proof fn lemma_output_wf(rc: ResultColumns, c0: ResultColumn, c1: ResultColumn)
    requires rc.columns@ == seq![c0, c1], column_wf(c0, rc.rows as nat), column_wf(c1, rc.rows as nat),
    ensures columns_wf(rc),
{
    hide(column_wf);
    assert forall|k: int| 0 <= k < rc.columns@.len() implies column_wf(#[trigger] rc.columns@[k], rc.rows as nat) by {
        if k == 0 { assert(rc.columns@[k] == c0); } else { assert(rc.columns@[k] == c1); }
    }
}

/// The finished columns are the body's rows.
proof fn lemma_output_done(rc: ResultColumns, c0: ResultColumn, c1: ResultColumn, out: Seq<Row>, names: Seq<Seq<u8>>, addrs: Seq<Seq<u8>>)
    requires
        rc.columns@ == seq![c0, c1], rc.rows as int == names.len(), names.len() == addrs.len(), c0 is Text, c1 is Text,
        column_wf(c0, names.len()), column_wf(c1, addrs.len()),
        forall|i: int| 0 <= i < names.len() ==> #[trigger] column_value(c0, i) == Val::Text(names[i]),
        forall|i: int| 0 <= i < addrs.len() ==> #[trigger] column_value(c1, i) == Val::Text(addrs[i]),
        out.len() == names.len(),
        forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == seq![Val::Text(names[i]), Val::Text(addrs[i])],
    ensures out_ok(rc, out),
{
    hide(column_wf);
    lemma_output_wf(rc, c0, c1);
    assert(rc.columns@[0] == c0 && rc.columns@[1] == c1 && rc.columns@.len() == 2);
    assert forall|i: int, k: int| 0 <= i < out.len() && 0 <= k < rc.columns@.len() implies #[trigger] out[i][k] == column_value(rc.columns@[k], i) by {
        assert(out[i] == seq![Val::Text(names[i]), Val::Text(addrs[i])]);
        if k == 0 { assert(column_value(c0, i) == Val::Text(names[i])); } else { assert(column_value(c1, i) == Val::Text(addrs[i])); }
    }
    assert forall|i: int| 0 <= i < out.len() implies (#[trigger] out[i]).len() == rc.columns@.len() && out[i][0] is Text && out[i][1] is Text by {
        assert(out[i] == seq![Val::Text(names[i]), Val::Text(addrs[i])]);
    }
    lemma_columns_view_eq(rc, out);
}

/// The answer's columns: the body's rows in its order.
pub fn build_output(c: &Cols, ss: &SuppSet, ma: &Vec<usize>, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>,
    Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>) -> (rc: ResultColumns)
    requires
        cols_ok(*c, sv), stores_wf(sv), keys_unique(nk(sv)), supp_ok(*ss, sv, ps, lo, hi), nations_ok(ma@, sv, ps),
    ensures out_ok(rc, out_rows(sv, ps, lo, hi)),
{
    let ns = c.ns;
    let (mut no, mut nb) = text_column();
    let (mut ao, mut ab) = text_column();
    let mut rows: usize = 0;
    let ghost mut names: Seq<Seq<u8>> = Seq::empty();
    let ghost mut addrs: Seq<Seq<u8>> = Seq::empty();
    let mut r: usize = 0;
    proof {
        lemma_rows_upto_ends(sv, ps, lo, hi);
        lemma_col_empty(no@, nb@);
        lemma_col_empty(ao@, ab@);
        if ns > 0 { lemma_offs_mono(sname_col(sv), ns as int, 0, 0); lemma_offs_mono(saddr_col(sv), ns as int, 0, 0); }
    }
    while r < ns
        invariant
            cols_ok(*c, sv), stores_wf(sv), keys_unique(nk(sv)), supp_ok(*ss, sv, ps, lo, hi), ns == c.ns, r <= ns,
            nations_ok(ma@, sv, ps),
            out_inv(*c, sv, ps, lo, hi, r as int, no@, nb@, ao@, ab@, rows as int, names, addrs),
        decreases ns - r,
    {
        let g = emit_supplier(c, ss, ma, r, &mut no, &mut nb, &mut ao, &mut ab, &mut rows, Ghost(sv), Ghost(ps),
            Ghost(lo), Ghost(hi), Ghost(names), Ghost(addrs));
        proof {
            names = g@.0;
            addrs = g@.1;
        }
        r = r + 1;
    }
    proof {
        lemma_col_done(no, nb, names);
        lemma_col_done(ao, ab, addrs);
    }
    let c0 = ResultColumn::Text { offsets: no, bytes: nb };
    let c1 = ResultColumn::Text { offsets: ao, bytes: ab };
    let mut cols: Vec<ResultColumn> = Vec::new();
    cols.push(c0);
    cols.push(c1);
    let rc = ResultColumns { rows, columns: cols };
    proof {
        let out = out_rows(sv, ps, lo, hi);
        assert(out == rows_upto(sv, ps, lo, hi, n_s(sv) as int));
        assert(rc.columns@ =~= seq![c0, c1]);
        lemma_output_done(rc, c0, c1, out, names, addrs);
    }
    rc
}

// ------------------------------------------------------------------------------------------------ the order

/// `lex_cmp(b[s1..e1], b[s2..e2]) <= 0`.
fn range_lex_le(b: &Vec<u8>, s1: usize, e1: usize, s2: usize, e2: usize) -> (r: bool)
    requires s1 <= e1 <= b@.len(), s2 <= e2 <= b@.len(),
    ensures r == (lex_cmp(b@.subrange(s1 as int, e1 as int), b@.subrange(s2 as int, e2 as int)) <= 0),
{
    let ghost x = b@.subrange(s1 as int, e1 as int);
    let ghost y = b@.subrange(s2 as int, e2 as int);
    let mut j: usize = 0;
    proof {
        assert(x.subrange(0, x.len() as int) =~= x);
        assert(y.subrange(0, y.len() as int) =~= y);
    }
    loop
        invariant
            s1 <= e1 <= b@.len(), s2 <= e2 <= b@.len(), j <= e1 - s1, j <= e2 - s2,
            x == b@.subrange(s1 as int, e1 as int), y == b@.subrange(s2 as int, e2 as int),
            lex_cmp(x, y) == lex_cmp(x.subrange(j as int, x.len() as int), y.subrange(j as int, y.len() as int)),
        decreases e1 - s1 - j,
    {
        let ghost xj = x.subrange(j as int, x.len() as int);
        let ghost yj = y.subrange(j as int, y.len() as int);
        if s1 + j == e1 {
            proof { assert(xj.len() == 0); }
            return true;
        }
        if s2 + j == e2 {
            proof { assert(yj.len() == 0 && xj.len() > 0); }
            return false;
        }
        let u = b[s1 + j];
        let w = b[s2 + j];
        proof { assert(xj[0] == u && yj[0] == w); }
        if u < w {
            return true;
        }
        if u > w {
            return false;
        }
        proof {
            assert(xj.drop_first() =~= x.subrange(j + 1, x.len() as int));
            assert(yj.drop_first() =~= y.subrange(j + 1, y.len() as int));
        }
        j = j + 1;
    }
}

/// The ORDER BY comparison of two rows whose first values are texts is their byte order.
proof fn lemma_keys_cmp_text(r1: Row, r2: Row, a: Seq<u8>, b: Seq<u8>)
    requires r1.len() > 0, r2.len() > 0, r1[0] == Val::Text(a), r2[0] == Val::Text(b),
    ensures keys_cmp(q_keys(), r1, r2) == lex_cmp(a, b),
{
    let ks = q_keys();
    assert(ks.drop_first() =~= Seq::<OrderKey>::empty());
    assert(keys_cmp(ks.drop_first(), r1, r2) == 0);
    assert(compare(Val::Text(a), Val::Text(b)) == Some(lex_cmp(a, b)));
    assert(key_cmp(ks[0], r1, r2) == lex_cmp(a, b));
}

/// The names of the column of the rows `out` (position 0 of every row).
pub open spec fn name_of(out: Seq<Row>, i: int) -> Seq<u8> { out[i][0]->Text_0 }

/// Whether the rows' names do not decrease (then they are in `ORDER BY s_name` order).
pub fn names_sorted(rc: &ResultColumns, Ghost(out): Ghost<Seq<Row>>) -> (r: bool)
    requires out_ok(*rc, out),
    ensures r ==> sorted_by(q_keys(), out),
{
    let n = rc.rows;
    match &rc.columns[0] {
        ResultColumn::Text { offsets, bytes } => {
            proof {
                assert(column_wf(rc.columns@[0], n as nat));
                assert forall|i: int| 0 <= i < n implies #[trigger] name_of(out, i) == bytes@.subrange(offsets@[i] as int, offsets@[i + 1] as int) by {
                    lemma_columns_view(*rc, i, 0);
                }
            }
            if n == 0 {
                return true;
            }
            let mut i: usize = 1;
            while i < n
                invariant
                    out_ok(*rc, out), n == rc.rows, 1 <= i <= n, offsets@.len() == n + 1,
                    rc.columns@[0] == (ResultColumn::Text { offsets: *offsets, bytes: *bytes }),
                    forall|k: int| 0 <= k < n ==> #[trigger] offsets@[k] <= offsets@[k + 1] && offsets@[k + 1] <= bytes@.len(),
                    forall|k: int| 0 <= k < n ==> #[trigger] name_of(out, k) == bytes@.subrange(offsets@[k] as int, offsets@[k + 1] as int),
                    forall|u: int, w: int| 0 <= u < w < i ==> lex_cmp(#[trigger] name_of(out, u), #[trigger] name_of(out, w)) <= 0,
                decreases n - i,
            {
                proof {
                    assert(offsets@[i - 1] <= offsets@[i as int] && offsets@[i as int] <= bytes@.len());
                    assert(offsets@[i as int] <= offsets@[i + 1] && offsets@[i + 1] <= bytes@.len());
                }
                if !range_lex_le(bytes, offsets[i - 1], offsets[i], offsets[i], offsets[i + 1]) {
                    return false;
                }
                proof {
                    let prev = name_of(out, i - 1);
                    let cur = name_of(out, i as int);
                    assert(lex_cmp(prev, cur) <= 0);
                    assert forall|u: int, w: int| 0 <= u < w < i + 1 implies lex_cmp(#[trigger] name_of(out, u), #[trigger] name_of(out, w)) <= 0 by {
                        if w == i && u < i - 1 {
                            lemma_lex_cmp_trans(name_of(out, u), prev, cur);
                        }
                    }
                }
                i = i + 1;
            }
            proof {
                assert forall|u: int, w: int| 0 <= u < w < out.len() implies keys_cmp(q_keys(), #[trigger] out[u], #[trigger] out[w]) <= 0 by {
                    assert(out[u][0] == Val::Text(name_of(out, u)));
                    assert(out[w][0] == Val::Text(name_of(out, w)));
                    lemma_keys_cmp_text(out[u], out[w], name_of(out, u), name_of(out, w));
                }
            }
            true
        },
        _ => {
            proof { assert(false); }
            false
        },
    }
}

/// Byte range `k` of an offset column is ordered and inside `l` bytes. A function of its own, so the facts about
/// ranges trigger on it and never chain from offset `k` to offset `k + 1`.
pub open spec fn rng(o: Seq<usize>, l: int, k: int) -> bool { o[k] <= o[k + 1] && o[k + 1] <= l }

/// Every byte range of a well-formed text column.
proof fn lemma_text_ranges(rows: nat, offs: Vec<usize>, bytes: Vec<u8>)
    requires column_wf(ResultColumn::Text { offsets: offs, bytes }, rows),
    ensures offs@.len() == rows + 1, forall|k: int| 0 <= k < rows ==> #[trigger] rng(offs@, bytes@.len() as int, k),
{
    assert(offs@.len() == rows + 1);
    reveal(column_wf);
    assert(forall|i: int| 0 <= i < rows ==> #[trigger] offs@[i] <= offs@[i + 1] && offs@[i + 1] <= bytes@.len());
    assert forall|k: int| 0 <= k < rows implies #[trigger] rng(offs@, bytes@.len() as int, k) by {}
}

/// The rows of the columns as their byte ranges.
proof fn lemma_rows_ranges(rc: ResultColumns, out: Seq<Row>, o0: Vec<usize>, b0: Vec<u8>, o1: Vec<usize>, b1: Vec<u8>)
    requires
        out_ok(rc, out),
        rc.columns@[0] == (ResultColumn::Text { offsets: o0, bytes: b0 }),
        rc.columns@[1] == (ResultColumn::Text { offsets: o1, bytes: b1 }),
    ensures
        out.len() == rc.rows, o0@.len() == rc.rows + 1, o1@.len() == rc.rows + 1,
        forall|k: int| 0 <= k < rc.rows ==> #[trigger] rng(o0@, b0@.len() as int, k) && rng(o1@, b1@.len() as int, k),
        forall|k: int| 0 <= k < rc.rows ==> #[trigger] out[k] == seq![Val::Text(b0@.subrange(o0@[k] as int, o0@[k + 1] as int)),
            Val::Text(b1@.subrange(o1@[k] as int, o1@[k + 1] as int))],
{
    assert(column_wf(rc.columns@[0], rc.rows as nat) && column_wf(rc.columns@[1], rc.rows as nat));
    lemma_text_ranges(rc.rows as nat, o0, b0);
    lemma_text_ranges(rc.rows as nat, o1, b1);
    assert forall|k: int| 0 <= k < rc.rows implies #[trigger] out[k] == seq![Val::Text(b0@.subrange(o0@[k] as int, o0@[k + 1] as int)),
        Val::Text(b1@.subrange(o1@[k] as int, o1@[k + 1] as int))] by {
        lemma_columns_view(rc, k, 0);
        lemma_columns_view(rc, k, 1);
        assert(out[k] =~= seq![Val::Text(b0@.subrange(o0@[k] as int, o0@[k + 1] as int)),
            Val::Text(b1@.subrange(o1@[k] as int, o1@[k + 1] as int))]);
    }
    assert forall|k: int| 0 <= k < rc.rows implies #[trigger] rng(o0@, b0@.len() as int, k) && rng(o1@, b1@.len() as int, k) by {
        assert(rng(o0@, b0@.len() as int, k));
        assert(rng(o1@, b1@.len() as int, k));
    }
}

/// The rows of the columns, one `Vec` per row (for the sort of the general case).
pub fn rows_of(rc: &ResultColumns, Ghost(out): Ghost<Seq<Row>>) -> (rows: Vec<Vec<EVal>>)
    requires out_ok(*rc, out),
    ensures view_rows(rows@) == out,
{
    let n = rc.rows;
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    match (&rc.columns[0], &rc.columns[1]) {
        (ResultColumn::Text { offsets: o0, bytes: b0 }, ResultColumn::Text { offsets: o1, bytes: b1 }) => {
            proof { lemma_rows_ranges(*rc, out, *o0, *b0, *o1, *b1); }
            let mut i: usize = 0;
            while i < n
                invariant
                    n == rc.rows, i <= n, rows@.len() == i, out.len() == n, o0@.len() == n + 1, o1@.len() == n + 1,
                    forall|k: int| 0 <= k < n ==> #[trigger] rng(o0@, b0@.len() as int, k) && rng(o1@, b1@.len() as int, k),
                    forall|k: int| 0 <= k < n ==> #[trigger] out[k] == seq![Val::Text(b0@.subrange(o0@[k] as int, o0@[k + 1] as int)),
                        Val::Text(b1@.subrange(o1@[k] as int, o1@[k + 1] as int))],
                    forall|k: int| 0 <= k < i ==> view_row(#[trigger] rows@[k]@) == out[k],
                decreases n - i,
            {
                proof { assert(rng(o0@, b0@.len() as int, i as int) && rng(o1@, b1@.len() as int, i as int)); }
                let name = crate::agent::partpass::copy_bytes(b0.as_slice(), o0[i], o0[i + 1]);
                let addr = crate::agent::partpass::copy_bytes(b1.as_slice(), o1[i], o1[i + 1]);
                let mut row: Vec<EVal> = Vec::new();
                row.push(EVal::Text(name));
                row.push(EVal::Text(addr));
                proof {
                    assert(view_row(row@) =~= out[i as int]);
                }
                rows.push(row);
                i = i + 1;
            }
            proof {
                assert(view_rows(rows@) =~= out) by {
                    assert forall|k: int| 0 <= k < out.len() implies view_rows(rows@)[k] == out[k] by {}
                }
            }
        },
        _ => {
            proof { assert(false); }
        },
    }
    rows
}

} // verus!
