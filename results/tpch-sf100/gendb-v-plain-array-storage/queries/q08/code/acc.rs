//! Per-year accumulators of the lineitem scan, the per-row join check, and one accumulation step.
//!
//! `Dir` holds everything the scan reads besides the columns (part bits, coarse filter, nation directory);
//! `scan_ok` collects the facts the scan relies on. `line_eval` decides `line::line_q` for a lineitem row whose
//! part matches and whose order (row `j`) is dated inside the window, and names whether it counts for `$1`.
//! An `Acc` holds the totals of both years over a range of lineitem rows exactly while their volume masses fit
//! `i128` (`acc_ok`); once a mass leaves it, `over` records that and the totals are no longer kept.
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::link::expr::i128_max;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::cols::*;
use crate::agent::lookup::*;
use crate::agent::partpass::*;
use crate::agent::common::bits::word_bit;

verus! {

// ------------------------------------------------------------------------------------------------ the directory

/// What the scan reads besides the columns.
pub struct Dir {
    pub pbits: Vec<u64>,
    pub coarse: Box<[u64; CW]>,
    pub pos: bool,
    pub nat: NatDir,
}

pub open spec fn dir_ok(d: Dir, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& pbits_ok(d.pbits@, sv, typ_of(ps))
    &&& coarse_ok((*d.coarse)@, d.pbits@, n_p(sv) as int)
    &&& d.pos ==> pos_ok(sv, typ_of(ps)) && n_p(sv) < 0x4000_0000_0000_0000
    &&& natdir_ok(d.nat, sv, ps)
}

/// The facts the scan relies on.
pub open spec fn scan_ok(c: Cols, d: Dir, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& cols_ok(c, sv)
    &&& dir_ok(d, sv, ps)
    &&& keys_ok(sv)
    &&& domains_ok(sv)
}

/// Some part row of type `$3` joins lineitem row `l`.
pub open spec fn part_q(sv: StoresView, ps: Seq<Literal>, l: int) -> bool {
    exists|p: int| 0 <= p < n_p(sv) && #[trigger] part_hit(sv, ps, p, l)
}

/// A qualifying row's part matches.
pub proof fn lemma_q_part(sv: StoresView, ps: Seq<Literal>, l: int)
    requires line_q(sv, ps, l),
    ensures part_q(sv, ps, l),
{
    let t = line_tup(sv, ps, l);
    assert(tup_ok(sv, ps, l, t));
    assert(part_hit(sv, ps, t.p, l));
}

// ------------------------------------------------------------------------------------------------ the join check

/// The qualifying tuple of row `l` uses orders row `j` when `j` holds its order key.
proof fn lemma_q_order(sv: StoresView, ps: Seq<Literal>, l: int, j: int)
    requires keys_ok(sv), line_q(sv, ps, l), 0 <= j < n_o(sv), o_key(sv)[j] == l_okey(sv)[l],
    ensures line_tup(sv, ps, l).o == j, tup_ok(sv, ps, l, line_tup(sv, ps, l)),
{
    let t = line_tup(sv, ps, l);
    assert(tup_ok(sv, ps, l, t));
    assert(o_key(sv)[t.o] == o_key(sv)[j]);
}

/// Lineitem row `i` (part matching, order row `j` inside the window): whether it qualifies, and whether it counts
/// for `$1`.
pub fn line_eval(c: &Cols, d: &Dir, i: usize, j: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (bool, bool))
    requires
        scan_ok(*c, *d, sv, ps), i < c.nl, j < c.no,
        part_q(sv, ps, i as int), o_key(sv)[j as int] == l_okey(sv)[i as int], date_in(o_date(sv)[j as int]),
    ensures
        r.0 == line_q(sv, ps, i as int),
        r.0 ==> r.1 == line_then(sv, ps, i as int) && line_tup(sv, ps, i as int).o == j,
    no_unwind
{
    let ghost l = i as int;
    proof {
        if line_q(sv, ps, l) {
            lemma_q_order(sv, ps, l, j as int);
        }
    }
    let ck = c.o_cust[j];
    let cr = match cust_row(c, ck, Ghost(sv)) {
        Some(x) => x,
        None => {
            proof {
                if line_q(sv, ps, l) {
                    let t = line_tup(sv, ps, l);
                    assert(c_key(sv)[t.c] == ck);
                }
            }
            return (false, false);
        },
    };
    let n1 = match nat_row(c, &d.nat, c.c_nat[cr], Ghost(sv), Ghost(ps)) {
        Some(x) => x,
        None => {
            proof {
                if line_q(sv, ps, l) {
                    let t = line_tup(sv, ps, l);
                    assert(c_key(sv)[t.c] == c_key(sv)[cr as int]);
                    assert(n_key(sv)[t.n1] == c_nat(sv)[cr as int]);
                }
            }
            return (false, false);
        },
    };
    if !d.nat.rin[n1] {
        proof {
            if line_q(sv, ps, l) {
                let t = line_tup(sv, ps, l);
                assert(c_key(sv)[t.c] == c_key(sv)[cr as int]);
                assert(n_key(sv)[t.n1] == n_key(sv)[n1 as int]);
                assert(reg_hit(sv, ps, t.r, t.n1));
                assert(in_region(sv, ps, n1 as int));
            }
        }
        return (false, false);
    }
    let sr = match supp_row(c, c.l_sk[i], Ghost(sv)) {
        Some(x) => x,
        None => {
            proof {
                if line_q(sv, ps, l) {
                    let t = line_tup(sv, ps, l);
                    assert(s_key(sv)[t.s] == l_skey(sv)[l]);
                }
            }
            return (false, false);
        },
    };
    let n2 = match nat_row(c, &d.nat, c.s_nat[sr], Ghost(sv), Ghost(ps)) {
        Some(x) => x,
        None => {
            proof {
                if line_q(sv, ps, l) {
                    let t = line_tup(sv, ps, l);
                    assert(s_key(sv)[t.s] == s_key(sv)[sr as int]);
                    assert(n_key(sv)[t.n2] == s_nat(sv)[sr as int]);
                }
            }
            return (false, false);
        },
    };
    let th = d.nat.rthen[n2];
    proof {
        let p = choose|p: int| 0 <= p < n_p(sv) && #[trigger] part_hit(sv, ps, p, l);
        assert(in_region(sv, ps, n1 as int));
        let r = choose|r: int| 0 <= r < n_r(sv) && #[trigger] reg_hit(sv, ps, r, n1 as int);
        let t = Tup { p, s: sr as int, o: j as int, c: cr as int, n1: n1 as int, n2: n2 as int, r };
        assert(tup_ok(sv, ps, l, t));
        lemma_tup_is(sv, ps, l, t);
    }
    (true, th)
}

// ------------------------------------------------------------------------------------------------ accumulators

/// The totals of one year, as machine integers.
#[derive(Clone, Copy)]
pub struct YAcc {
    pub cnt: u64,
    pub s_all: i128,
    pub a_all: u128,
    pub n_then: u64,
    pub s_then: i128,
    pub a_then: u128,
}

/// The totals of both years over a range, or `over` once a volume mass left `i128`.
#[derive(Clone, Copy)]
pub struct Acc {
    pub y95: YAcc,
    pub y96: YAcc,
    pub over: bool,
}

/// `a` holds the totals `t`, whose volume mass fits `i128`.
pub open spec fn yacc_is(a: YAcc, t: Tot) -> bool {
    &&& a.cnt as int == t.cnt
    &&& a.s_all as int == t.s_all
    &&& a.a_all as int == t.a_all
    &&& a.n_then as int == t.n_then
    &&& a.s_then as int == t.s_then
    &&& a.a_then as int == t.a_then
    &&& t.a_all <= i128_max()
}

/// `a` holds the totals of the lineitem rows `lo..hi`.
pub open spec fn acc_ok(a: Acc, sv: StoresView, ps: Seq<Literal>, lo: int, hi: int) -> bool {
    &&& lo <= hi
    &&& if a.over {
        tot(sv, ps, 1995, lo, hi).a_all > i128_max() || tot(sv, ps, 1996, lo, hi).a_all > i128_max()
    } else {
        yacc_is(a.y95, tot(sv, ps, 1995, lo, hi)) && yacc_is(a.y96, tot(sv, ps, 1996, lo, hi))
    }
}

pub fn yacc_zero() -> (a: YAcc)
    ensures yacc_is(a, tot_zero()),
    no_unwind
{
    YAcc { cnt: 0, s_all: 0, a_all: 0, n_then: 0, s_then: 0, a_then: 0 }
}

pub fn acc_zero(Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(lo): Ghost<int>) -> (a: Acc)
    ensures acc_ok(a, sv, ps, lo, lo),
    no_unwind
{
    Acc { y95: yacc_zero(), y96: yacc_zero(), over: false }
}

/// The mass of a range only grows when the range grows.
pub proof fn lemma_mass_mono(sv: StoresView, ps: Seq<Literal>, y: int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures tot(sv, ps, y, lo, mid).a_all <= tot(sv, ps, y, lo, hi).a_all,
{
    lemma_tot_split(sv, ps, y, lo, mid, hi);
    lemma_tot_bounds(sv, ps, y, mid, hi);
}

/// Rows without qualifying rows between `mid` and `hi` keep the totals.
pub proof fn lemma_acc_gap(a: Acc, sv: StoresView, ps: Seq<Literal>, lo: int, mid: int, hi: int)
    requires acc_ok(a, sv, ps, lo, mid), mid <= hi, forall|l: int| mid <= l < hi ==> !#[trigger] line_q(sv, ps, l),
    ensures acc_ok(a, sv, ps, lo, hi),
{
    lemma_tot_split(sv, ps, 1995, lo, mid, hi);
    lemma_tot_split(sv, ps, 1996, lo, mid, hi);
    lemma_tot_gap(sv, ps, 1995, mid, hi);
    lemma_tot_gap(sv, ps, 1996, mid, hi);
    assert(tot(sv, ps, 1995, lo, hi) =~= tot(sv, ps, 1995, lo, mid));
    assert(tot(sv, ps, 1996, lo, hi) =~= tot(sv, ps, 1996, lo, mid));
}

/// One year's contribution of a row of volume `v` (counting for `$1` when `th`).
pub open spec fn contrib(v: int, th: bool) -> Tot {
    Tot {
        cnt: 1,
        s_all: v,
        a_all: abs(v),
        n_then: if th { 1 } else { 0 },
        s_then: if th { v } else { 0 },
        a_then: if th { abs(v) } else { 0 },
    }
}

/// Add a row's volume: the new totals, or `None` when the volume mass leaves `i128`.
pub fn yacc_add(a: YAcc, v: i128, th: bool, Ghost(t): Ghost<Tot>, Ghost(bound): Ghost<int>) -> (r: Option<YAcc>)
    requires
        yacc_is(a, t),
        0 <= t.n_then <= t.cnt, 0 <= t.a_then <= t.a_all,
        -t.a_all <= t.s_all <= t.a_all, -t.a_then <= t.s_then <= t.a_then,
        t.cnt < bound <= u64::MAX,
        -0x1_0000_0000_0000_0000_0000_0000_0000 < v < 0x1_0000_0000_0000_0000_0000_0000_0000,
    ensures
        match r {
            Some(b) => yacc_is(b, tot_plus(t, contrib(v as int, th))),
            None => tot_plus(t, contrib(v as int, th)).a_all > i128_max(),
        },
    no_unwind
{
    let av: u128 = if v >= 0 { v as u128 } else { (-v) as u128 };
    assert(av as int == abs(v as int));
    let na = a.a_all + av;
    if na > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff {
        return None;
    }
    let s_all = a.s_all + v;
    if th {
        Some(YAcc {
            cnt: a.cnt + 1, s_all, a_all: na,
            n_then: a.n_then + 1, s_then: a.s_then + v, a_then: a.a_then + av,
        })
    } else {
        Some(YAcc { cnt: a.cnt + 1, s_all, a_all: na, n_then: a.n_then, s_then: a.s_then, a_then: a.a_then })
    }
}

/// One step of the scan: lineitem row `i` (part matching, order row `j` inside the window) is added to the totals
/// of the rows `lo..i`.
pub fn acc_step(acc: Acc, c: &Cols, d: &Dir, i: usize, j: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>,
    Ghost(lo): Ghost<int>) -> (r: Acc)
    requires
        scan_ok(*c, *d, sv, ps), acc_ok(acc, sv, ps, lo, i as int), 0 <= lo, i < c.nl, j < c.no,
        part_q(sv, ps, i as int), o_key(sv)[j as int] == l_okey(sv)[i as int], date_in(o_date(sv)[j as int]),
    ensures acc_ok(r, sv, ps, lo, i + 1),
    no_unwind
{
    let ghost l = i as int;
    proof {
        lemma_tot_step(sv, ps, 1995, lo, l);
        lemma_tot_step(sv, ps, 1996, lo, l);
        lemma_tot_bounds(sv, ps, 1995, lo, l);
        lemma_tot_bounds(sv, ps, 1996, lo, l);
        lemma_tot_bounds(sv, ps, 1995, l, l + 1);
        lemma_tot_bounds(sv, ps, 1996, l, l + 1);
    }
    if acc.over {
        proof {
            lemma_mass_mono(sv, ps, 1995, lo, l, l + 1);
            lemma_mass_mono(sv, ps, 1996, lo, l, l + 1);
        }
        return acc;
    }
    let (q, th) = line_eval(c, d, i, j, Ghost(sv), Ghost(ps));
    if !q {
        proof { lemma_acc_gap(acc, sv, ps, lo, l, l + 1); }
        return acc;
    }
    let price = c.l_price[i];
    let disc = c.l_disc[i];
    proof {
        assert(num15(l_price(sv)[l]) && num15(l_disc(sv)[l]));
        let (pp, dd) = (price as int, 100 - disc as int);
        assert(-0x1_0000_0000_0000_0000_0000_0000_0000 < pp * dd < 0x1_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
            requires -1_000_000_000_000_000 < pp < 1_000_000_000_000_000, -999_999_999_999_900 < dd < 1_000_000_000_000_100;
    }
    let v: i128 = price * (100 - disc);
    proof {
        assert(v as int == line_vol(sv, l));
        assert(line_year(sv, ps, l) == year_of_day(o_date(sv)[j as int]));
        assert(line_then(sv, ps, l) == th);
    }
    if c.o_date[j] < 9496 {
        proof {
            assert(line_tot(sv, ps, 1995, l) == contrib(v as int, th));
            assert(line_tot(sv, ps, 1996, l) == tot_zero());
            assert(tot(sv, ps, 1996, lo, l + 1) =~= tot(sv, ps, 1996, lo, l));
        }
        match yacc_add(acc.y95, v, th, Ghost(tot(sv, ps, 1995, lo, l)), Ghost(c.nl as int)) {
            Some(y) => Acc { y95: y, y96: acc.y96, over: false },
            None => Acc { y95: acc.y95, y96: acc.y96, over: true },
        }
    } else {
        proof {
            assert(line_tot(sv, ps, 1996, l) == contrib(v as int, th));
            assert(line_tot(sv, ps, 1995, l) == tot_zero());
            assert(tot(sv, ps, 1995, lo, l + 1) =~= tot(sv, ps, 1995, lo, l));
        }
        match yacc_add(acc.y96, v, th, Ghost(tot(sv, ps, 1996, lo, l)), Ghost(c.nl as int)) {
            Some(y) => Acc { y95: acc.y95, y96: y, over: false },
            None => Acc { y95: acc.y95, y96: acc.y96, over: true },
        }
    }
}

/// Totals of adjacent ranges add (or are `over` when a mass leaves `i128`).
pub fn yacc_merge(a: YAcc, b: YAcc, Ghost(ta): Ghost<Tot>, Ghost(tb): Ghost<Tot>, Ghost(bound): Ghost<int>) -> (r: Option<YAcc>)
    requires
        yacc_is(a, ta), yacc_is(b, tb),
        0 <= ta.a_then <= ta.a_all, 0 <= tb.a_then <= tb.a_all,
        -ta.a_all <= ta.s_all <= ta.a_all, -tb.a_all <= tb.s_all <= tb.a_all,
        -ta.a_then <= ta.s_then <= ta.a_then, -tb.a_then <= tb.s_then <= tb.a_then,
        0 <= ta.n_then <= ta.cnt, 0 <= tb.n_then <= tb.cnt, ta.cnt + tb.cnt <= bound <= u64::MAX,
    ensures
        match r {
            Some(c) => yacc_is(c, tot_plus(ta, tb)),
            None => tot_plus(ta, tb).a_all > i128_max(),
        },
    no_unwind
{
    let na = a.a_all + b.a_all;
    if na > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff {
        return None;
    }
    Some(YAcc {
        cnt: a.cnt + b.cnt,
        s_all: a.s_all + b.s_all,
        a_all: na,
        n_then: a.n_then + b.n_then,
        s_then: a.s_then + b.s_then,
        a_then: a.a_then + b.a_then,
    })
}

/// The totals of adjacent ranges `lo..mid` and `mid..hi` give those of `lo..hi`.
pub fn acc_merge(a: Acc, b: Acc, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(lo): Ghost<int>,
    Ghost(mid): Ghost<int>, Ghost(hi): Ghost<int>) -> (r: Acc)
    requires acc_ok(a, sv, ps, lo, mid), acc_ok(b, sv, ps, mid, hi), 0 <= lo, hi - lo <= u64::MAX,
    ensures acc_ok(r, sv, ps, lo, hi),
{
    proof {
        lemma_tot_split(sv, ps, 1995, lo, mid, hi);
        lemma_tot_split(sv, ps, 1996, lo, mid, hi);
        lemma_tot_bounds(sv, ps, 1995, lo, mid);
        lemma_tot_bounds(sv, ps, 1996, lo, mid);
        lemma_tot_bounds(sv, ps, 1995, mid, hi);
        lemma_tot_bounds(sv, ps, 1996, mid, hi);
    }
    if a.over || b.over {
        return Acc { y95: a.y95, y96: a.y96, over: true };
    }
    let y95 = yacc_merge(a.y95, b.y95, Ghost(tot(sv, ps, 1995, lo, mid)), Ghost(tot(sv, ps, 1995, mid, hi)), Ghost(hi - lo));
    let y96 = yacc_merge(a.y96, b.y96, Ghost(tot(sv, ps, 1996, lo, mid)), Ghost(tot(sv, ps, 1996, mid, hi)), Ghost(hi - lo));
    match (y95, y96) {
        (Some(x), Some(y)) => Acc { y95: x, y96: y, over: false },
        _ => Acc { y95: a.y95, y96: a.y96, over: true },
    }
}

} // verus!
