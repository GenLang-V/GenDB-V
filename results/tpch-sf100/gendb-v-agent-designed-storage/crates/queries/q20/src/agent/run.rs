//! Calling-thread steps: the days `$2` and `$2 + 1 year` (`dates`), the nation keys named `$3` (`nation_keys`), the
//! merge of the tasks' supplier flags (`merge`), the output columns in supplier order with a check of the s_name
//! order (`build_output`), and the sort of the rows when that check fails (`sorted_rows`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::{Literal, OrderKey};
use crate::spec::text::lex_cmp;
use crate::spec::datetime::*;
use crate::spec::order::{sorted_by, keys_cmp, key_cmp, sort_rows};
use crate::gendb_abi::CivilDate;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::results::*;
use crate::exec::value::{EVal, ERow};
use crate::exec::ast::EOrderKey;
use crate::exec::datetime::*;
use crate::exec::relational::order::{sort_rows_exec, view_keys};
use crate::link::query::view_rows;
use crate::link::expr::tval;
use crate::query::param_domain;
use crate::stores::suppliers::interface::common::colfmt as cf;
use crate::stores::suppliers::interface::common::read::{text_slice, bytes_cmp, for_get_u8, lemma_div_lt};
use super::nf::*;
use super::ast::q_keys;
use super::bind_sp::*;
use super::sl::*;
use super::kern::*;
use super::bits::*;
use vstd::std_specs::bits::{u64_trailing_zeros, axiom_u64_trailing_zeros};

verus! {

/// `$2` and the day `d1` of `$2 + 1 year`.
pub fn dates(p1: CivilDate, Ghost(ps): Ghost<Seq<Literal>>) -> (r: (i64, i64))
    requires
        param_domain(ps),
        ps[1] == (Literal::Date { y: p1.y as int, m: p1.m as int, d: p1.d as int }),
    ensures
        r.0 == d0_of(ps),
        d1_ok(ps, r.1 as int),
        -0x1_0000_0000 <= r.0 <= 0x1_0000_0000,
        -0x1_0000_0000 <= r.1 <= 0x1_0000_0000,
{
    proof {
        assert(crate::query::param_typed(ps));
        super::datewin::lemma_domain_days();
        super::datewin::lemma_hi_ts_ok(ps);
    }
    assert(1 <= p1.d <= days_in_month(p1.y as int, p1.m as int));
    assert(days_in_month(p1.y as int, p1.m as int) <= 31);
    let d0 = date_from_civil_exec(p1.y as i64, p1.m as i64, p1.d as i64);
    assert(d0 == d0_of(ps));
    let t0 = match date_to_ts_exec(d0 as i32) {
        Ok(t) => t,
        Err(_) => {
            assert(false);
            return (0, 0);
        },
    };
    assert(ts_valid(t0 as int));
    let t1 = match ts_add_interval_exec(t0, 12, 0, 0) {
        Ok(t) => t,
        Err(_) => {
            assert(false);
            return (0, 0);
        },
    };
    assert(hi_ts(ps) == Ok::<int, SqlError>(t1 as int));
    assert(ts_valid(t1 as int));
    let (day, tod) = ts_day_and_time_exec(t1);
    proof {
        let u = usecs_per_day();
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t1 as int, u);
        assert(t1 as int == day * u) by (nonlinear_arith)
            requires t1 as int == u * (t1 as int / u) + t1 as int % u, t1 as int % u == 0, day == t1 as int / u;
    }
    (d0, day)
}

/// The keys of the nation rows named `name`.
pub fn nation_keys(nk: &[u8], nkb: &[i64], nbs: usize, noffs: &[u64], nbytes: &[u8], nn: usize, name: &[u8],
    Ghost(sp): Ghost<Seq<PartView>>) -> (v: Vec<i64>)
    requires
        sp_ok(sp),
        nn == tn(sp, 30), nbs as int == super::kctx::bmin(tbs(sp, 30)),
        nk@ == cf::u8s(sp[32]), nkb@ == cf::i64s(sp[33]),
        noffs@ == cf::u64s(sp[34]), nbytes@ == cf::u8s(sp[35]),
    ensures
        forall|i: int| 0 <= i < v@.len() ==> #[trigger] sl_nat_ok(sp, name@, v@[i] as int),
        forall|y: int| 0 <= y < tn(sp, 30) && nan(sp, y) == name@
            ==> exists|i: int| 0 <= i < v@.len() && #[trigger] v@[i] == nak(sp, y),
{
    let mut v: Vec<i64> = Vec::new();
    let mut y: usize = 0;
    while y < nn
        invariant
            sp_ok(sp),
            nn == tn(sp, 30), nbs as int == super::kctx::bmin(tbs(sp, 30)),
            nk@ == cf::u8s(sp[32]), nkb@ == cf::i64s(sp[33]),
            noffs@ == cf::u64s(sp[34]), nbytes@ == cf::u8s(sp[35]),
            y <= nn,
            forall|i: int| 0 <= i < v@.len() ==> #[trigger] sl_nat_ok(sp, name@, v@[i] as int),
            forall|z: int| 0 <= z < y && nan(sp, z) == name@ ==> exists|i: int| 0 <= i < v@.len() && #[trigger] v@[i] == nak(sp, z),
        decreases nn - y,
    {
        assert(cf::text_range_ok(noffs@, nbytes@, y as int));
        let s = text_slice(noffs, nbytes, y);
        let c = bytes_cmp(s, s.len(), name, name.len());
        proof {
            crate::bridge::equality::lemma_lex_cmp_zero(s@, name@);
            super::kctx::lemma_bmin(y as int, tbs(sp, 30), nkb@.len() as int, nn as int);
            lemma_div_lt(y as int, nbs as int, nkb@.len() as int);
            assert(i64r(nak(sp, y as int)));
        }
        let key = for_get_u8(nk, nkb, nbs, y);
        assert(key == nak(sp, y as int));
        let ghost v0 = v@;
        if c == 0 {
            v.push(key);
            proof {
                assert(sl_nat_ok(sp, name@, key as int));
                assert forall|i: int| 0 <= i < v@.len() implies #[trigger] sl_nat_ok(sp, name@, v@[i] as int) by {
                    if i < v0.len() {
                        assert(v@[i] == v0[i]);
                    }
                }
                assert forall|z: int| 0 <= z < y + 1 && nan(sp, z) == name@ implies exists|i: int| 0 <= i < v@.len() && #[trigger] v@[i] == nak(sp, z) by {
                    if z < y {
                        let i = choose|i: int| 0 <= i < v0.len() && #[trigger] v0[i] == nak(sp, z);
                        assert(v@[i] == v0[i]);
                    } else {
                        assert(v@[v0.len() as int] == nak(sp, z));
                    }
                }
            }
        }
        y = y + 1;
    }
    v
}

/// The supplier rows some task found.
pub open spec fn flagged(outs: Seq<Emit>, w: int, x: int) -> bool {
    exists|i: int| 0 <= i < w && #[trigger] has(outs[i], x)
}

/// One bit per supplier row: set when some task found the row.
pub fn merge(outs: &Vec<Emit>, ns: usize) -> (g: Vec<u64>)
    requires
        forall|i: int| 0 <= i < outs@.len() ==> (#[trigger] outs@[i]).wf(ns as int),
        forall|i: int| 0 <= i < outs@.len() ==> !lost(#[trigger] outs@[i]),
    ensures
        g@.len() == ns / 64 + 1,
        holds(g@, ns as int),
        forall|x: int| 0 <= x < ns ==> #[trigger] bit(g@, x) == flagged(outs@, outs@.len() as int, x),
{
    let nw = ns / 64 + 1;
    let mut g: Vec<u64> = vec![0u64; nw];
    proof {
        assert(ns < nw * 64) by (nonlinear_arith) requires nw == ns / 64 + 1;
        lemma_zero_bits(g@, ns as int);
    }
    let mut w: usize = 0;
    while w < outs.len()
        invariant
            forall|i: int| 0 <= i < outs@.len() ==> (#[trigger] outs@[i]).wf(ns as int),
            forall|i: int| 0 <= i < outs@.len() ==> !lost(#[trigger] outs@[i]),
            w <= outs@.len(),
            g@.len() == nw, nw == ns / 64 + 1, holds(g@, ns as int),
            forall|x: int| 0 <= x < ns ==> #[trigger] bit(g@, x) == flagged(outs@, w as int, x),
        decreases outs@.len() - w,
    {
        let e = &outs[w];
        assert(e.wf(ns as int) && !lost(*e));
        let ghost g0 = g@;
        if !e.ovf {
            let mut i: usize = 0;
            while i < e.cnt
                invariant
                    e.wf(ns as int), !e.ovf, e == outs@[w as int],
                    i <= e.cnt, g@.len() == nw, nw == ns / 64 + 1, holds(g@, ns as int),
                    forall|x: int| 0 <= x < ns ==> #[trigger] bit(g@, x)
                        == (bit(g0, x) || exists|t: int| 0 <= t < i && e.out@[t] == x),
                decreases e.cnt - i,
            {
                let x = e.out[i];
                assert(x < ns);
                proof {
                    lemma_div_lt(x as int, 64, nw as int);
                }
                let ghost gb = g@;
                set_bit(&mut g, x);
                proof {
                    assert forall|z: int| 0 <= z < ns implies #[trigger] bit(g@, z)
                        == (bit(g0, z) || exists|t: int| 0 <= t < i + 1 && e.out@[t] == z) by {
                        assert(bit(g@, z) == (z == x || bit(gb, z)));
                        if exists|t: int| 0 <= t < i + 1 && e.out@[t] == z {
                            let t = choose|t: int| 0 <= t < i + 1 && e.out@[t] == z;
                            if t < i {
                                assert(exists|t2: int| 0 <= t2 < i && e.out@[t2] == z);
                            }
                        }
                        if z == x {
                            assert(e.out@[i as int] == z);
                        }
                    }
                }
                i = i + 1;
            }
            proof {
                assert forall|x: int| 0 <= x < ns implies #[trigger] bit(g@, x) == flagged(outs@, w + 1, x) by {
                    let inl = exists|t: int| 0 <= t < e.cnt && e.out@[t] == x;
                    if e.fm {
                        if bit(e.sf@, x) {
                            let t = choose|t: int| 0 <= t < e.cnt && e.out@[t] == x;
                        }
                        if inl {
                            let t = choose|t: int| 0 <= t < e.cnt && e.out@[t] == x;
                            assert(bit(e.sf@, e.out@[t] as int));
                        }
                    } else {
                        if has(*e, x) {
                            let t = choose|t: int| 0 <= t < e.cnt && #[trigger] e.out@[t] == x;
                            assert(inl);
                        }
                        if inl {
                            let t = choose|t: int| 0 <= t < e.cnt && e.out@[t] == x;
                            assert(has(*e, x));
                        }
                    }
                    assert(has(*e, x) == inl);
                    if flagged(outs@, w + 1, x) {
                        let i2 = choose|i2: int| 0 <= i2 < w + 1 && #[trigger] has(outs@[i2], x);
                        if i2 < w {
                            assert(flagged(outs@, w as int, x));
                        }
                    }
                    if flagged(outs@, w as int, x) {
                        let i2 = choose|i2: int| 0 <= i2 < w && #[trigger] has(outs@[i2], x);
                        assert(0 <= i2 < w + 1);
                    }
                    if has(*e, x) {
                        assert(has(outs@[w as int], x));
                    }
                }
            }
        } else {
            assert(e.fm);
            let mut x: usize = 0;
            while x < ns
                invariant
                    e.wf(ns as int), e.fm, e == outs@[w as int],
                    x <= ns, g@.len() == nw, nw == ns / 64 + 1, holds(g@, ns as int),
                    forall|z: int| 0 <= z < ns ==> #[trigger] bit(g@, z) == (bit(g0, z) || (z < x && bit(e.sf@, z))),
                decreases ns - x,
            {
                proof {
                    lemma_div_lt(x as int, 64, e.sf@.len() as int);
                    lemma_div_lt(x as int, 64, nw as int);
                }
                let ghost gb = g@;
                if get_bit(&e.sf, x) {
                    set_bit(&mut g, x);
                }
                proof {
                    assert forall|z: int| 0 <= z < ns implies #[trigger] bit(g@, z) == (bit(g0, z) || (z < x + 1 && bit(e.sf@, z))) by {
                        if bit(e.sf@, x as int) {
                            assert(bit(g@, z) == (z == x || bit(gb, z)));
                        }
                    }
                }
                x = x + 1;
            }
            proof {
                assert forall|z: int| 0 <= z < ns implies #[trigger] bit(g@, z) == flagged(outs@, w + 1, z) by {
                    assert(has(*e, z) == bit(e.sf@, z));
                    if flagged(outs@, w + 1, z) {
                        let i2 = choose|i2: int| 0 <= i2 < w + 1 && #[trigger] has(outs@[i2], z);
                        if i2 < w {
                            assert(flagged(outs@, w as int, z));
                        }
                    }
                    if flagged(outs@, w as int, z) {
                        let i2 = choose|i2: int| 0 <= i2 < w && #[trigger] has(outs@[i2], z);
                        assert(0 <= i2 < w + 1);
                    }
                    if bit(e.sf@, z) {
                        assert(has(outs@[w as int], z));
                    }
                }
            }
        }
        w = w + 1;
    }
    g
}

/// For rows whose first value is text, the ORDER BY s_name comparison is the bytewise order of the names.
pub proof fn lemma_keys_text(r1: Row, r2: Row)
    requires r1.len() >= 1, r2.len() >= 1, r1[0] is Text, r2[0] is Text,
    ensures keys_cmp(q_keys(), r1, r2) == lex_cmp(tval(r1[0]), tval(r2[0])),
{
    let ks = q_keys();
    assert(ks.drop_first() =~= Seq::<OrderKey>::empty());
    assert(keys_cmp(ks.drop_first(), r1, r2) == 0);
}

/// The text value `i` of a column under construction.
pub open spec fn tcol_at(offs: Seq<usize>, bytes: Seq<u8>, i: int) -> Seq<u8> {
    bytes.subrange(offs[i] as int, offs[i + 1] as int)
}

/// Value `i`'s range of a text column lies inside its bytes.
pub open spec fn rng_ok(offs: Seq<usize>, blen: int, i: int) -> bool {
    offs[i] <= offs[i + 1] && offs[i + 1] <= blen
}

/// A text column under construction holds the values `vals`.
pub open spec fn tcol_ok(offs: Seq<usize>, bytes: Seq<u8>, vals: Seq<Seq<u8>>) -> bool {
    &&& offs.len() == vals.len() + 1
    &&& offs.last() == bytes.len()
    &&& forall|i: int| 0 <= i < vals.len() ==> #[trigger] rng_ok(offs, bytes.len() as int, i)
        && tcol_at(offs, bytes, i) == vals[i]
}

pub proof fn lemma_tcol_push(offs: Seq<usize>, bytes: Seq<u8>, vals: Seq<Seq<u8>>, v: Seq<u8>, offs2: Seq<usize>, bytes2: Seq<u8>)
    requires
        tcol_ok(offs, bytes, vals),
        bytes2 == bytes + v,
        offs2 == offs.push(bytes2.len() as usize),
        bytes2.len() <= usize::MAX,
    ensures tcol_ok(offs2, bytes2, vals.push(v)),
{
    let n = vals.len() as int;
    assert forall|i: int| 0 <= i < n + 1 implies #[trigger] rng_ok(offs2, bytes2.len() as int, i)
        && tcol_at(offs2, bytes2, i) == vals.push(v)[i] by {
        if i < n {
            assert(rng_ok(offs, bytes.len() as int, i));
            assert(offs2[i] == offs[i] && offs2[i + 1] == offs[i + 1]);
            assert(tcol_at(offs2, bytes2, i) =~= tcol_at(offs, bytes, i));
        } else {
            assert(offs2[i] == bytes.len());
            assert(tcol_at(offs2, bytes2, i) =~= v);
        }
    }
}

/// `results::push_text` with one bulk copy.
pub fn push_bytes(offsets: &mut Vec<usize>, bytes: &mut Vec<u8>, value: &[u8])
    requires
        old(offsets)@.len() >= 1,
        old(offsets)@.last() == old(bytes)@.len(),
        old(bytes)@.len() + value@.len() <= usize::MAX,
    ensures
        final(bytes)@ == old(bytes)@ + value@,
        final(offsets)@ == old(offsets)@.push(final(bytes)@.len() as usize),
        final(offsets)@.last() == final(bytes)@.len(),
{
    bytes.extend_from_slice(value);
    let n = bytes.len();
    offsets.push(n);
}

/// The names and addresses of the rows.
pub open spec fn names_of(rows: Seq<Row>) -> Seq<Seq<u8>> {
    rows.map_values(|r: Row| tval(r[0]))
}

pub open spec fn addrs_of(rows: Seq<Row>) -> Seq<Seq<u8>> {
    rows.map_values(|r: Row| tval(r[1]))
}

/// At most one result row per supplier row.
pub proof fn lemma_sel_len(sv: StoresView, ps: Seq<Literal>, d1: int, m: int)
    requires m >= 0,
    ensures sel_rows(sv, ps, d1, m).len() <= m,
    decreases m,
{
    if m > 0 {
        lemma_sel_len(sv, ps, d1, m - 1);
    }
}

/// Output of `build_output`: the two text columns of `rows` rows, and whether the rows are in s_name order.
pub struct Built {
    pub no: Vec<usize>,
    pub nb: Vec<u8>,
    pub ao: Vec<usize>,
    pub ab: Vec<u8>,
    pub rows: usize,
    pub sorted: bool,
}

/// The columns of `Built` hold the rows `rs`.
pub open spec fn built_ok(b: Built, rs: Seq<Row>) -> bool {
    &&& rs.len() == b.rows
    &&& two_cols(b.no@, b.nb@, b.ao@, b.ab@, b.rows as int)
    &&& forall|i: int| 0 <= i < b.rows ==> #[trigger] rs[i] == trow(b.no@, b.nb@, b.ao@, b.ab@, i)
}

/// A text column whose ranges lie inside its bytes is well formed.
proof fn lemma_text_col_wf(o: Vec<usize>, b: Vec<u8>, n: nat)
    requires o@.len() == n + 1, forall|i: int| 0 <= i < n ==> #[trigger] rng_ok(o@, b@.len() as int, i),
    ensures column_wf(ResultColumn::Text { offsets: o, bytes: b }, n),
{
    assert forall|i: int| 0 <= i < n implies #[trigger] o@[i] <= o@[i + 1] && o@[i + 1] <= b@.len() by {
        assert(rng_ok(o@, b@.len() as int, i));
    }
}

/// The columnar answer of two text columns.
pub fn make_cols(b: Built, Ghost(rs): Ghost<Seq<Row>>) -> (c: ResultColumns)
    requires built_ok(b, rs),
    ensures columns_wf(c), columns_view(c) == rs,
{
    hide(columns_view);
    hide(column_wf);
    let Built { no, nb, ao, ab, rows, sorted: _ } = b;
    let ghost (o0, b0, o1, b1) = (no@, nb@, ao@, ab@);
    let mut columns: Vec<ResultColumn> = Vec::new();
    columns.push(ResultColumn::Text { offsets: no, bytes: nb });
    columns.push(ResultColumn::Text { offsets: ao, bytes: ab });
    let ghost c0 = columns@[0];
    let ghost c1 = columns@[1];
    let c = ResultColumns { rows, columns };
    proof {
        assert(c0 == (ResultColumn::Text { offsets: no, bytes: nb }));
        assert(c1 == (ResultColumn::Text { offsets: ao, bytes: ab }));
        assert forall|i: int| 0 <= i < rows implies #[trigger] rng_ok(o1, b1.len() as int, i) by {
            assert(rng_ok(o0, b0.len() as int, i));
        }
        lemma_text_col_wf(no, nb, rows as nat);
        lemma_text_col_wf(ao, ab, rows as nat);
        assert forall|k: int| 0 <= k < c.columns@.len() implies column_wf(#[trigger] c.columns@[k], c.rows as nat) by {
            if k == 0 { assert(c.columns@[k] == c0); } else { assert(c.columns@[k] == c1); }
        }
        assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i].len() == c.columns@.len() by {
            assert(rs[i] == trow(o0, b0, o1, b1, i));
        }
        assert forall|i: int, k: int| 0 <= i < rs.len() && 0 <= k < c.columns@.len()
            implies #[trigger] rs[i][k] == column_value(c.columns@[k], i) by {
            assert(rs[i] == trow(o0, b0, o1, b1, i));
            if k == 0 { assert(c.columns@[k] == c0); } else { assert(c.columns@[k] == c1); }
        }
        lemma_columns_view_eq(c, rs);
    }
    c
}

/// No supplier row of `[a, b)` qualifies: the result rows do not grow.
pub proof fn lemma_sel_none(sv: StoresView, ps: Seq<Literal>, d1: int, a: int, b: int)
    requires 0 <= a <= b, forall|z: int| a <= z < b ==> !#[trigger] sl_s_qual(sv, ps, d1, z),
    ensures sel_rows(sv, ps, d1, b) == sel_rows(sv, ps, d1, a),
    decreases b - a,
{
    if b > a {
        lemma_sel_none(sv, ps, d1, a, b - 1);
        assert(!sl_s_qual(sv, ps, d1, b - 1));
    }
}

/// Text offsets never decrease.
pub proof fn lemma_offs_mono(offs: Seq<u64>, bytes: Seq<u8>, n: int, a: int, b: int)
    requires cf::text_parts_wf(offs, bytes, n), 0 <= a <= b <= n,
    ensures offs[a] <= offs[b],
    decreases b - a,
{
    if a < b {
        lemma_offs_mono(offs, bytes, n, a, b - 1);
        assert(cf::text_range_ok(offs, bytes, b - 1));
    }
}

/// Bit `d - 1` of a word shifted past bit `c` is bit `c + d` of the word.
proof fn lemma_shift_bit(wv: u64, c: u64, d: u64)
    requires c + d < 64, d >= 1,
    ensures ((wv >> add(c, 1u64)) >> sub(d, 1u64)) & 1u64 == (wv >> add(c, d)) & 1u64,
{
    assert(((wv >> add(c, 1u64)) >> sub(d, 1u64)) & 1u64 == (wv >> add(c, d)) & 1u64) by (bit_vector)
        requires c + d < 64, d >= 1;
}

/// Position `64 * w + c + d` is bit `c + d` of word `w`.
proof fn lemma_word_pos(x: int, w: int, c: int, d: int)
    requires 0 <= w, 0 <= c, 0 <= d, c + d < 64, x == 64 * w + c,
    ensures (x + d) / 64 == w, (x + d) % 64 == c + d,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x + d, 64, w, c + d);
}

/// Touch, for the flagged rows of `[lo, hi)`, their name and address offsets, then their first bytes, so that the
/// cache misses of many rows overlap; returns a mix of the values read.
fn touch_out(g: &Vec<u64>, ns: usize, lo: usize, hi: usize, sno: &[u64], snb: &[u8], sao: &[u64], sab: &[u8]) -> (t: u64)
    requires holds(g@, ns as int), lo <= hi <= ns, ns + 64 <= usize::MAX, sno@.len() == ns + 1, sao@.len() == ns + 1,
{
    broadcast use axiom_u64_trailing_zeros;
    let mut t: u64 = 0;
    let mut pass: usize = 0;
    while pass < 2
        invariant holds(g@, ns as int), lo <= hi <= ns, ns + 64 <= usize::MAX, sno@.len() == ns + 1, sao@.len() == ns + 1,
        decreases 2 - pass,
    {
        let mut w = lo / 64;
        while w < g.len() && w <= hi / 64
            invariant holds(g@, ns as int), lo <= hi <= ns, ns + 64 <= usize::MAX, sno@.len() == ns + 1, sao@.len() == ns + 1,
            decreases g@.len() - w,
        {
            let mut v = g[w];
            while v != 0
                invariant holds(g@, ns as int), lo <= hi <= ns, ns + 64 <= usize::MAX, sno@.len() == ns + 1,
                    sao@.len() == ns + 1, w < g@.len(), w <= hi / 64,
                decreases v,
            {
                let b = v.trailing_zeros() as usize;
                assert(v & sub(v, 1u64) < v) by (bit_vector) requires v != 0;
                let x = w * 64 + b;
                if x < hi {
                    let a = sno[x];
                    let c = sao[x];
                    if pass == 0 {
                        t = t ^ a ^ c;
                    } else {
                        if a < snb.len() as u64 {
                            t = t ^ (snb[a as usize] as u64);
                        }
                        if c < sab.len() as u64 {
                            t = t ^ (sab[c as usize] as u64);
                        }
                    }
                }
                v = v & (v - 1);
            }
            w = w + 1;
        }
        pass = pass + 1;
    }
    t
}

/// The result rows of the flagged supplier rows, in supplier order.
pub fn build_output(g: &Vec<u64>, ns: usize, sno: &[u64], snb: &[u8], sao: &[u64], sab: &[u8],
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(d1): Ghost<int>) -> (r: Built)
    requires
        sp_ok(sv.suppliers),
        ns == tn(sv.suppliers, 13),
        sno@ == cf::u64s(sv.suppliers[17]), snb@ == cf::u8s(sv.suppliers[18]),
        sao@ == cf::u64s(sv.suppliers[19]), sab@ == cf::u8s(sv.suppliers[20]),
        holds(g@, ns as int),
        forall|x: int| 0 <= x < ns ==> #[trigger] bit(g@, x) == sl_s_qual(sv, ps, d1, x),
    ensures
        built_ok(r, sel_rows(sv, ps, d1, ns as int)),
        r.sorted ==> sorted_by(q_keys(), sel_rows(sv, ps, d1, ns as int)),
{
    let ghost sp = sv.suppliers;
    let mut no: Vec<usize> = Vec::with_capacity(65536);
    no.push(0);
    let mut nb: Vec<u8> = Vec::with_capacity(1048576);
    let mut ao: Vec<usize> = Vec::with_capacity(65536);
    ao.push(0);
    let mut ab: Vec<u8> = Vec::with_capacity(1048576);
    proof {
        assert(no@ =~= seq![0usize]);
        assert(ao@ =~= seq![0usize]);
        assert(nb@ =~= Seq::<u8>::empty());
        assert(ab@ =~= Seq::<u8>::empty());
    }
    let mut rows: usize = 0;
    // the touch loads feed the sortedness flag (a match of this constant only means sorting afterwards)
    let mut tch: u64 = 0;
    let mut tnext: usize = 0;
    let mut sorted = true;
    let mut prev: &[u8] = snb;
    let nby = snb.len();
    let aby = sab.len();
    proof {
        assert(names_of(sel_rows(sv, ps, d1, 0)) =~= Seq::<Seq<u8>>::empty());
        assert(addrs_of(sel_rows(sv, ps, d1, 0)) =~= Seq::<Seq<u8>>::empty());
    }
    let mut x: usize = 0;
    while x < ns
        invariant
            sp_ok(sp), sp == sv.suppliers,
            ns == tn(sp, 13),
            sno@ == cf::u64s(sp[17]), snb@ == cf::u8s(sp[18]),
            sao@ == cf::u64s(sp[19]), sab@ == cf::u8s(sp[20]),
            nby == snb@.len(), aby == sab@.len(),
            holds(g@, ns as int),
            forall|z: int| 0 <= z < ns ==> #[trigger] bit(g@, z) == sl_s_qual(sv, ps, d1, z),
            x <= ns,
            rows == sel_rows(sv, ps, d1, x as int).len(),
            tcol_ok(no@, nb@, names_of(sel_rows(sv, ps, d1, x as int))),
            tcol_ok(ao@, ab@, addrs_of(sel_rows(sv, ps, d1, x as int))),
            nb@.len() <= (if x < ns { sno@[x as int] as int } else { nby as int }),
            ab@.len() <= (if x < ns { sao@[x as int] as int } else { aby as int }),
            sorted ==> sorted_by(q_keys(), sel_rows(sv, ps, d1, x as int)),
            rows > 0 ==> prev@ == tval(sel_rows(sv, ps, d1, x as int)[rows - 1][0]),
            forall|i: int| 0 <= i < rows ==> (#[trigger] sel_rows(sv, ps, d1, x as int)[i]).len() == 2
                && sel_rows(sv, ps, d1, x as int)[i][0] is Text && sel_rows(sv, ps, d1, x as int)[i][1] is Text,
        decreases ns - x,
    {
        let ghost r0 = sel_rows(sv, ps, d1, x as int);
        proof {
            lemma_sel_len(sv, ps, d1, x as int);
            assert(cf::text_range_ok(sno@, snb@, x as int));
            assert(cf::text_range_ok(sao@, sab@, x as int));
            if x + 1 < ns {
                assert(cf::text_range_ok(sno@, snb@, x + 1));
                assert(cf::text_range_ok(sao@, sab@, x + 1));
            }
        }
        if x >= tnext && ns < usize::MAX - 64 {
            let te = if ns - x > 16384 { x + 16384 } else { ns };
            tch = tch ^ touch_out(g, ns, x, te, sno, snb, sao, sab);
            tnext = te;
        }
        proof {
            lemma_div_lt(x as int, 64, g@.len() as int);
        }
        if get_bit(g, x) {
            let nm = text_slice(sno, snb, x);
            let ad = text_slice(sao, sab, x);
            let row = Ghost(orow(sp, x as int));
            proof {
                assert(sel_rows(sv, ps, d1, x + 1) == r0.push(row@));
                assert(nm@ == sun(sp, x as int) && ad@ == sua(sp, x as int));
            }
            if sorted && rows > 0 {
                let c = bytes_cmp(prev, prev.len(), nm, nm.len());
                if c > 0 {
                    sorted = false;
                } else {
                    proof {
                        let r1 = r0.push(row@);
                        assert forall|i: int| 0 <= i < r0.len() implies keys_cmp(q_keys(), #[trigger] r0[i], row@) <= 0 by {
                            if i < rows - 1 {
                                assert(keys_cmp(q_keys(), r0[i], r0[rows - 1]) <= 0);
                            }
                            lemma_keys_text(r0[i], r0[rows - 1]);
                            lemma_keys_text(r0[rows - 1], row@);
                            lemma_keys_text(r0[i], row@);
                            if i < rows - 1 {
                                crate::bridge::order::lemma_lex_cmp_trans(tval(r0[i][0]), tval(r0[rows - 1][0]), tval(row@[0]));
                            } else {
                                assert(r0[i] == r0[rows - 1]);
                            }
                        }
                        crate::bridge::order::lemma_sorted_push(q_keys(), r0, row@);
                    }
                }
            } else if sorted {
                proof {
                    crate::bridge::order::lemma_sorted_push(q_keys(), r0, row@);
                }
            }
            let ghost no0 = no@;
            let ghost nb0 = nb@;
            let ghost ao0 = ao@;
            let ghost ab0 = ab@;
            push_bytes(&mut no, &mut nb, nm);
            push_bytes(&mut ao, &mut ab, ad);
            proof {
                lemma_tcol_push(no0, nb0, names_of(r0), nm@, no@, nb@);
                lemma_tcol_push(ao0, ab0, addrs_of(r0), ad@, ao@, ab@);
                assert(names_of(r0).push(nm@) =~= names_of(r0.push(row@)));
                assert(addrs_of(r0).push(ad@) =~= addrs_of(r0.push(row@)));
                let r1 = r0.push(row@);
                assert forall|i: int| 0 <= i < rows + 1 implies (#[trigger] r1[i]).len() == 2 && r1[i][0] is Text && r1[i][1] is Text by {
                    if i < rows {
                        assert(r1[i] == r0[i]);
                    }
                }
            }
            prev = nm;
            rows = rows + 1;
            x = x + 1;
        } else {
            // not flagged: jump to the next flagged row of this word, or to the word's end
            let w = x / 64;
            let c = (x % 64) as u64;
            proof {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, 64);
            }
            let wv = g[w];
            let rest: u64 = if c >= 63 { 0 } else { wv >> (c + 1) };
            let step: usize = if rest == 0 { (64 - c) as usize } else { rest.trailing_zeros() as usize + 1 };
            proof {
                axiom_u64_trailing_zeros(rest);
                if rest != 0 {
                    let tz = u64_trailing_zeros(rest) as u64;
                    if tz >= 63 - c {
                        assert(((wv >> add(c, 1u64)) >> tz) & 1u64 == 0u64) by (bit_vector)
                            requires c < 63, tz >= sub(63u64, c), tz < 64;
                    }
                }
            }
            let nx = if ns - x > step { x + step } else { ns };
            proof {
                assert forall|z: int| x <= z < nx implies !#[trigger] sl_s_qual(sv, ps, d1, z) by {
                    if z > x {
                        let d = (z - x) as u64;
                        lemma_word_pos(x as int, w as int, c as int, d as int);
                        lemma_shift_bit(wv, c, d);
                        assert(bit(g@, z) == sl_s_qual(sv, ps, d1, z));
                        if rest != 0 {
                            assert((rest >> sub(d, 1u64)) & 1u64 == 0u64);
                        } else {
                            assert((0u64 >> sub(d, 1u64)) & 1u64 == 0u64) by (bit_vector);
                        }
                    }
                }
                lemma_sel_none(sv, ps, d1, x as int, nx as int);
                lemma_offs_mono(sno@, snb@, ns as int, x as int, nx as int);
                lemma_offs_mono(sao@, sab@, ns as int, x as int, nx as int);
            }
            x = nx;
        }
    }
    if tch == 0x9E37_79B9_7F4A_7C15 {
        sorted = false;
    }
    let ghost rs = sel_rows(sv, ps, d1, ns as int);
    proof {
        assert forall|i: int| 0 <= i < rows implies #[trigger] rs[i] == trow(no@, nb@, ao@, ab@, i) by {
            assert(rng_ok(no@, nb@.len() as int, i));
            assert(rng_ok(ao@, ab@.len() as int, i));
            assert(names_of(rs)[i] == tval(rs[i][0]));
            assert(addrs_of(rs)[i] == tval(rs[i][1]));
            assert(rs[i].len() == 2 && rs[i][0] is Text && rs[i][1] is Text);
            assert(rs[i] =~= trow(no@, nb@, ao@, ab@, i));
        }
        assert forall|i: int| 0 <= i < rows implies #[trigger] rng_ok(no@, nb@.len() as int, i)
            && rng_ok(ao@, ab@.len() as int, i) by {
            assert(names_of(rs)[i] == tval(rs[i][0]));
            assert(rng_ok(ao@, ab@.len() as int, i));
        }
    }
    Built { no, nb, ao, ab, rows, sorted }
}

/// Row `i` of two text columns.
pub open spec fn trow(o0: Seq<usize>, b0: Seq<u8>, o1: Seq<usize>, b1: Seq<u8>, i: int) -> Row {
    seq![Val::Text(tcol_at(o0, b0, i)), Val::Text(tcol_at(o1, b1, i))]
}

/// Two text columns of `n` rows.
pub open spec fn two_cols(o0: Seq<usize>, b0: Seq<u8>, o1: Seq<usize>, b1: Seq<u8>, n: int) -> bool {
    &&& o0.len() == n + 1 && o1.len() == n + 1
    &&& forall|i: int| 0 <= i < n ==> #[trigger] rng_ok(o0, b0.len() as int, i) && rng_ok(o1, b1.len() as int, i)
}

/// A copy of `b[a .. z]`.
fn copy_range(b: &Vec<u8>, a: usize, z: usize) -> (v: Vec<u8>)
    requires a <= z <= b@.len(),
    ensures v@ == b@.subrange(a as int, z as int),
{
    let mut v: Vec<u8> = Vec::new();
    let mut t = a;
    while t < z
        invariant a <= t <= z, z <= b@.len(), v@ == b@.subrange(a as int, t as int),
        decreases z - t,
    {
        v.push(b[t]);
        proof { assert(v@ =~= b@.subrange(a as int, t + 1)); }
        t = t + 1;
    }
    v
}

/// The rows of two text columns as `EVal` rows, sorted by the first (the fallback when supplier order is not).
pub fn sorted_rows(o0: &Vec<usize>, b0: &Vec<u8>, o1: &Vec<usize>, b1: &Vec<u8>, n: usize, Ghost(rs): Ghost<Seq<Row>>) -> (out: Vec<ERow>)
    requires
        two_cols(o0@, b0@, o1@, b1@, n as int),
        rs.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] rs[i] == trow(o0@, b0@, o1@, b1@, i),
    ensures
        view_rows(out@) == sort_rows(q_keys(), rs),
        sorted_by(q_keys(), view_rows(out@)),
        view_rows(out@).to_multiset() == rs.to_multiset(),
{
    let mut rows: Vec<ERow> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            two_cols(o0@, b0@, o1@, b1@, n as int),
            rs.len() == n,
            forall|j: int| 0 <= j < n ==> #[trigger] rs[j] == trow(o0@, b0@, o1@, b1@, j),
            i <= n,
            view_rows(rows@) == rs.subrange(0, i as int),
        decreases n - i,
    {
        assert(rng_ok(o0@, b0@.len() as int, i as int));
        let v0 = copy_range(b0, o0[i], o0[i + 1]);
        let v1 = copy_range(b1, o1[i], o1[i + 1]);
        let mut row: ERow = Vec::new();
        row.push(EVal::Text(v0));
        row.push(EVal::Text(v1));
        let ghost rows0 = rows@;
        rows.push(row);
        proof {
            assert(crate::exec::value::view_row(row@) =~= rs[i as int]);
            assert(view_rows(rows@) =~= view_rows(rows0).push(crate::exec::value::view_row(row@)));
            assert(rs.subrange(0, i + 1) =~= rs.subrange(0, i as int).push(rs[i as int]));
        }
        i = i + 1;
    }
    proof {
        assert(rs.subrange(0, n as int) =~= rs);
    }
    let mut keys: Vec<EOrderKey> = Vec::new();
    keys.push(EOrderKey { col: 0, desc: false, nulls_first: false });
    proof {
        assert(view_keys(keys@) =~= q_keys());
    }
    let out = sort_rows_exec(&keys, rows);
    proof {
        let fams = seq![3int];
        assert forall|i: int| 0 <= i < rs.len() implies crate::bridge::order::keys_ok(q_keys(), fams, #[trigger] rs[i]) by {
            assert(rs[i] == trow(o0@, b0@, o1@, b1@, i));
            assert(crate::bridge::order::key_ok(q_keys()[0], fams[0], rs[i]));
        }
        crate::bridge::order::lemma_sort_rows(q_keys(), fams, rs);
    }
    out
}

} // verus!

