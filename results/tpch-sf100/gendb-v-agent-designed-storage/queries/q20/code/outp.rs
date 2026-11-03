//! The output columns built in parallel: tasks over ranges of supplier rows (`OutTask`) write the s_name and
//! s_address of their result rows (`seg`) into preallocated buffers; the calling thread appends the pieces in range
//! order (`par_output`). A piece whose buffers are too small reports an overflow; then the calling thread builds the
//! whole output itself (`run::build_output`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::text::lex_cmp;
use crate::spec::order::{sorted_by, keys_cmp};
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::link::expr::tval;
use crate::stores::suppliers::interface::common::colfmt as cf;
use crate::stores::suppliers::interface::common::read::{text_slice, bytes_cmp, lemma_div_lt};
use super::nf::*;
use super::ast::q_keys;
use super::bind_sp::*;
use super::sl::*;
use super::run::*;
use super::bits::*;
use crate::gendb_entry::runtime::WorkerFailure;

verus! {

/// The result rows of the supplier rows `[y0, y)`, in order.
pub open spec fn seg(sv: StoresView, ps: Seq<Literal>, d1: int, y0: int, y: int) -> Seq<Row>
    decreases y - y0,
{
    if y <= y0 {
        Seq::empty()
    } else if sl_s_qual(sv, ps, d1, y - 1) {
        seg(sv, ps, d1, y0, y - 1).push(orow(sv.suppliers, y - 1))
    } else {
        seg(sv, ps, d1, y0, y - 1)
    }
}

/// The result rows of the first `y` supplier rows split at `y0`.
pub proof fn lemma_sel_split(sv: StoresView, ps: Seq<Literal>, d1: int, y0: int, y: int)
    requires 0 <= y0 <= y,
    ensures sel_rows(sv, ps, d1, y) == sel_rows(sv, ps, d1, y0) + seg(sv, ps, d1, y0, y),
    decreases y - y0,
{
    if y == y0 {
        assert(sel_rows(sv, ps, d1, y0) + seg(sv, ps, d1, y0, y) =~= sel_rows(sv, ps, d1, y0));
    } else {
        lemma_sel_split(sv, ps, d1, y0, y - 1);
        let a = sel_rows(sv, ps, d1, y0);
        let b = seg(sv, ps, d1, y0, y - 1);
        if sl_s_qual(sv, ps, d1, y - 1) {
            assert((a + b).push(orow(sv.suppliers, y - 1)) =~= a + b.push(orow(sv.suppliers, y - 1)));
        }
    }
}

/// No row of `[a, b)` qualifies: the segment does not grow.
proof fn lemma_seg_none(sv: StoresView, ps: Seq<Literal>, d1: int, y0: int, a: int, b: int)
    requires y0 <= a <= b, forall|z: int| a <= z < b ==> !#[trigger] sl_s_qual(sv, ps, d1, z),
    ensures seg(sv, ps, d1, y0, b) == seg(sv, ps, d1, y0, a),
    decreases b - a,
{
    if b > a {
        lemma_seg_none(sv, ps, d1, y0, a, b - 1);
        assert(!sl_s_qual(sv, ps, d1, b - 1));
    }
}

/// Touch the offsets, then the first name and address bytes, of the rows `x + c` (`c < 64`, below `y1`) whose
/// bit `c` of `wv` is set, so that their cache misses overlap; returns a mix of the values read.
/// Pass 0 touches the offsets only, pass 1 the bytes only (their offsets are then cached).
fn touch_rows(sno: &[u64], snb: &[u8], sao: &[u64], sab: &[u8], nbl: usize, abl: usize, wv: u64, x: usize, y1: usize,
    pass: usize, Ghost(sp): Ghost<Seq<PartView>>) -> (t: u64)
    requires
        sp_ok(sp), text_views(sp, sno@, snb@, sao@, sab@),
        x <= y1 <= tn(sp, 13), nbl == snb@.len(), abl == sab@.len(),
    no_unwind
{
    let mut t: u64 = 0;
    let e = if y1 - x < 64 { y1 } else { x + 64 };
    let mut z = if pass == 0 { x } else { e };
    while z < e
        invariant x <= z <= e <= y1 <= tn(sp, 13), e - x <= 64, sp_ok(sp), text_views(sp, sno@, snb@, sao@, sab@),
        decreases e - z,
    {
        let c = (z - x) as u64;
        if (wv >> c) & 1u64 == 1u64 {
            proof {
                assert(cf::text_range_ok(sno@, snb@, z as int));
                assert(cf::text_range_ok(sao@, sab@, z as int));
            }
            t = t ^ sno[z] ^ sao[z];
        }
        z = z + 1;
    }
    z = if pass == 1 { x } else { e };
    while z < e
        invariant x <= z <= e <= y1 <= tn(sp, 13), e - x <= 64, sp_ok(sp), text_views(sp, sno@, snb@, sao@, sab@),
            nbl == snb@.len(), abl == sab@.len(),
        decreases e - z,
    {
        let c = (z - x) as u64;
        if (wv >> c) & 1u64 == 1u64 {
            proof {
                assert(cf::text_range_ok(sno@, snb@, z as int));
                assert(cf::text_range_ok(sao@, sab@, z as int));
            }
            let na = sno[z];
            let aa = sao[z];
            if na < nbl as u64 {
                t = t ^ (snb[na as usize] as u64);
            }
            if aa < abl as u64 {
                t = t ^ (sab[aa as usize] as u64);
            }
        }
        z = z + 1;
    }
    t
}

/// Touch the result rows of the supplier rows `[x, x + 4096)` (below `y1`; flag bit `i` is row `fo + i`): first
/// the offsets of every flagged row, then their name and address bytes, so that many cache misses overlap.
fn touch_span(fl: &Vec<u64>, fo: usize, x: usize, y1: usize, sno: &[u64], snb: &[u8], sao: &[u64], sab: &[u8],
    nbl: usize, abl: usize, Ghost(sp): Ghost<Seq<PartView>>) -> (t: u64)
    requires
        sp_ok(sp), text_views(sp, sno@, snb@, sao@, sab@),
        fo <= x <= y1 <= tn(sp, 13), (x - fo) % 64 == 0, holds(fl@, y1 - fo),
        nbl == snb@.len(), abl == sab@.len(),
    no_unwind
{
    let mut t: u64 = 0;
    let e = if y1 - x < 4096 { y1 } else { x + 4096 };
    let mut pass: usize = 0;
    while pass < 2
        invariant
            sp_ok(sp), text_views(sp, sno@, snb@, sao@, sab@),
            fo <= x <= e <= y1 <= tn(sp, 13), (x - fo) % 64 == 0, holds(fl@, y1 - fo),
            nbl == snb@.len(), abl == sab@.len(),
        decreases 2 - pass,
    {
        let mut z = x;
        while z < e
            invariant
                sp_ok(sp), text_views(sp, sno@, snb@, sao@, sab@),
                fo <= x <= z <= e <= y1 <= tn(sp, 13), z < e ==> (z - fo) % 64 == 0, holds(fl@, y1 - fo),
                nbl == snb@.len(), abl == sab@.len(),
            decreases e - z,
        {
            proof {
                lemma_div_lt((z - fo) as int, 64, fl@.len() as int);
            }
            let wv = fl[(z - fo) / 64];
            if wv != 0 {
                t = t ^ touch_rows(sno, snb, sao, sab, nbl, abl, wv, z, y1, pass, Ghost(sp));
            }
            if e - z > 64 {
                proof {
                    vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish((z - fo) as int, 64);
                }
                z = z + 64;
            } else {
                z = e;
            }
        }
        pass = pass + 1;
    }
    t
}

/// Rows of a segment are `orow`s of supplier rows in `[y0, y)`.
pub proof fn lemma_seg_rows(sv: StoresView, ps: Seq<Literal>, d1: int, y0: int, y: int)
    ensures
        forall|i: int| 0 <= i < seg(sv, ps, d1, y0, y).len() ==> (#[trigger] seg(sv, ps, d1, y0, y)[i]).len() == 2
            && seg(sv, ps, d1, y0, y)[i][0] is Text && seg(sv, ps, d1, y0, y)[i][1] is Text,
    decreases y - y0,
{
    if y > y0 {
        lemma_seg_rows(sv, ps, d1, y0, y - 1);
        let b = seg(sv, ps, d1, y0, y - 1);
        if sl_s_qual(sv, ps, d1, y - 1) {
            assert forall|i: int| 0 <= i < b.len() + 1 implies (#[trigger] b.push(orow(sv.suppliers, y - 1))[i]).len() == 2
                && b.push(orow(sv.suppliers, y - 1))[i][0] is Text && b.push(orow(sv.suppliers, y - 1))[i][1] is Text by {
                if i < b.len() {
                    assert(b.push(orow(sv.suppliers, y - 1))[i] == b[i]);
                }
            }
        }
    }
}

/// A piece: the first `rows + 1` offsets and the first `used` bytes of each column hold the rows `vals`.
pub open spec fn piece_ok(no: Seq<usize>, nb: Seq<u8>, ao: Seq<usize>, ab: Seq<u8>, rows: int, nused: int, aused: int,
    vals: Seq<Row>) -> bool {
    &&& rows == vals.len()
    &&& rows < no.len() && rows < ao.len()
    &&& no[0] == 0 && ao[0] == 0
    &&& 0 <= nused <= nb.len() && 0 <= aused <= ab.len()
    &&& tcol_ok(no.take(rows + 1), nb.take(nused), names_of(vals))
    &&& tcol_ok(ao.take(rows + 1), ab.take(aused), addrs_of(vals))
}

/// The output of a task.
pub struct Piece {
    pub no: Vec<usize>,
    pub nb: Vec<u8>,
    pub ao: Vec<usize>,
    pub ab: Vec<u8>,
    pub rows: usize,
    pub nused: usize,
    pub aused: usize,
    pub ovf: bool,
    pub sorted: bool,
    pub tch: u64,
    pub first: usize,
    pub last: usize,
}

/// The output task over supplier rows `[y0, y1)`.
pub struct OutTask {
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
    pub d1: Ghost<int>,
    pub y0: usize,
    pub y1: usize,
    pub fo: usize,
    pub fl: Vec<u64>,
    pub sno: &'static [u64],
    pub snb: &'static [u8],
    pub sao: &'static [u64],
    pub sab: &'static [u8],
    pub no: Vec<usize>,
    pub nb: Vec<u8>,
    pub ao: Vec<usize>,
    pub ab: Vec<u8>,
    pub rcap: usize,
    pub ncap: usize,
    pub acap: usize,
    pub nbl: usize,
    pub abl: usize,
}

/// The views of the supplier text slices.
pub open spec fn text_views(sp: Seq<PartView>, sno: Seq<u64>, snb: Seq<u8>, sao: Seq<u64>, sab: Seq<u8>) -> bool {
    &&& sno == cf::u64s(sp[17]) && snb == cf::u8s(sp[18])
    &&& sao == cf::u64s(sp[19]) && sab == cf::u8s(sp[20])
}

/// Copy `src[a .. b]` into `dst` from position `pos` (`no_unwind`).
fn copy_into(dst: &mut Vec<u8>, pos: usize, src: &[u8], a: usize, b: usize, Ghost(cap): Ghost<usize>)
    requires a <= b <= src@.len(), pos + (b - a) <= old(dst)@.len(), old(dst)@.len() == cap,
    ensures
        final(dst)@.len() == old(dst)@.len(),
        final(dst)@.take(pos as int) == old(dst)@.take(pos as int),
        final(dst)@.subrange(pos as int, pos + (b - a)) == src@.subrange(a as int, b as int),
    no_unwind
{
    let ghost d0 = dst@;
    let mut i = a;
    while i < b
        invariant
            a <= i <= b <= src@.len(), pos + (b - a) <= d0.len(), d0.len() == cap,
            dst@.len() == d0.len(),
            dst@.take(pos as int) == d0.take(pos as int),
            dst@.subrange(pos as int, pos + (i - a)) == src@.subrange(a as int, i as int),
        decreases b - i,
    {
        let ghost dd = dst@;
        dst[pos + (i - a)] = src[i];
        proof {
            assert(dst@.take(pos as int) =~= dd.take(pos as int));
            assert(dst@.subrange(pos as int, pos + (i + 1 - a)) =~= src@.subrange(a as int, i + 1));
        }
        i = i + 1;
    }
}

impl WorkerTask for OutTask {
    type Output = Piece;

    open spec fn pre(&self) -> bool {
        let sp = self.sv@.suppliers;
        &&& sp_ok(sp)
        &&& text_views(sp, self.sno@, self.snb@, self.sao@, self.sab@)
        &&& self.y0 <= self.y1 <= tn(sp, 13)
        &&& self.fo <= self.y0
        &&& holds(self.fl@, self.y1 - self.fo)
        &&& forall|i: int| self.y0 - self.fo <= i < self.y1 - self.fo ==> #[trigger] bit(self.fl@, i)
            == sl_s_qual(self.sv@, self.ps@, self.d1@, self.fo + i)
        &&& self.no@.len() == self.rcap + 1 && self.ao@.len() == self.rcap + 1
        &&& self.nb@.len() == self.ncap && self.ab@.len() == self.acap
        &&& self.no@[0] == 0 && self.ao@[0] == 0
        &&& self.nbl == self.snb@.len() && self.abl == self.sab@.len()
    }

    open spec fn post(&self, out: Piece) -> bool {
        let vals = seg(self.sv@, self.ps@, self.d1@, self.y0 as int, self.y1 as int);
        let sp = self.sv@.suppliers;
        !out.ovf ==> {
            &&& piece_ok(out.no@, out.nb@, out.ao@, out.ab@, out.rows as int, out.nused as int, out.aused as int, vals)
            &&& out.sorted ==> sorted_by(q_keys(), vals)
            &&& out.rows > 0 ==> {
                &&& out.first < tn(sp, 13) && out.last < tn(sp, 13)
                &&& vals[0] == orow(sp, out.first as int)
                &&& vals[out.rows - 1] == orow(sp, out.last as int)
            }
        }
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.y0 as u64, self.y1 as u64)
    }

    fn run(self) -> (out: Piece) {
        let OutTask { sv, ps, d1, y0, y1, fo, fl, sno, snb, sao, sab, no, nb, ao, ab, rcap, ncap, acap, nbl, abl } = self;
        let ghost (sv, ps, d1) = (sv@, ps@, d1@);
        let ghost sp = sv.suppliers;
        let mut no = no;
        let mut nb = nb;
        let mut ao = ao;
        let mut ab = ab;
        let mut rows: usize = 0;
        let mut nused: usize = 0;
        let mut aused: usize = 0;
        let mut ovf = false;
        let mut sorted = true;
        let mut first: usize = 0;
        let mut last: usize = 0;
        proof {
            assert(no@.take(1) =~= seq![0usize]);
            assert(ao@.take(1) =~= seq![0usize]);
            assert(nb@.take(0) =~= Seq::<u8>::empty());
            assert(ab@.take(0) =~= Seq::<u8>::empty());
            assert(names_of(seg(sv, ps, d1, y0 as int, y0 as int)) =~= Seq::<Seq<u8>>::empty());
            assert(addrs_of(seg(sv, ps, d1, y0 as int, y0 as int)) =~= Seq::<Seq<u8>>::empty());
        }
        let mut tch: u64 = 0;
        let mut x = y0;
        while x < y1 && !ovf
            invariant
                sp_ok(sp), sp == sv.suppliers,
                text_views(sp, sno@, snb@, sao@, sab@),
                y0 <= x <= y1 <= tn(sp, 13),
                fo <= y0, holds(fl@, y1 - fo),
                forall|i: int| y0 - fo <= i < y1 - fo ==> #[trigger] bit(fl@, i) == sl_s_qual(sv, ps, d1, fo + i),
                no@.len() == rcap + 1 && ao@.len() == rcap + 1,
                nb@.len() == ncap && ab@.len() == acap,
                nbl == snb@.len() && abl == sab@.len(),
                !ovf ==> {
                    &&& piece_ok(no@, nb@, ao@, ab@, rows as int, nused as int, aused as int, seg(sv, ps, d1, y0 as int, x as int))
                    &&& sorted ==> sorted_by(q_keys(), seg(sv, ps, d1, y0 as int, x as int))
                    &&& rows > 0 ==> {
                        &&& first < tn(sp, 13) && y0 <= last < x
                        &&& seg(sv, ps, d1, y0 as int, x as int)[0] == orow(sp, first as int)
                        &&& seg(sv, ps, d1, y0 as int, x as int)[rows - 1] == orow(sp, last as int)
                    }
                },
            decreases y1 - x, (if ovf { 0int } else { 1int }),
        {
            // at a word of flags: skip it if clear, else touch its rows
            let bo = x - fo;
            if bo % 4096 == 0 {
                tch = tch ^ touch_span(&fl, fo, x, y1, sno, snb, sao, sab, nbl, abl, Ghost(sp));
            }
            if bo % 64 == 0 {
                proof {
                    lemma_div_lt(bo as int, 64, fl@.len() as int);
                }
                let wv = fl[bo / 64];
                if wv == 0 && y1 - x >= 64 {
                    proof {
                        assert forall|z: int| x <= z < x + 64 implies !#[trigger] sl_s_qual(sv, ps, d1, z) by {
                            lemma_zero_word(fl@, bo as int, z - fo);
                            assert(bit(fl@, z - fo) == sl_s_qual(sv, ps, d1, fo + (z - fo)));
                        }
                        lemma_seg_none(sv, ps, d1, y0 as int, x as int, x + 64);
                    }
                    x = x + 64;
                    continue;
                }
            }
            let ghost r0 = seg(sv, ps, d1, y0 as int, x as int);
            proof {
                lemma_seg_rows(sv, ps, d1, y0 as int, x as int);
                assert(cf::text_range_ok(sno@, snb@, x as int));
                assert(cf::text_range_ok(sao@, sab@, x as int));
            }
            proof {
                lemma_div_lt((x - fo) as int, 64, fl@.len() as int);
            }
            if get_bit(&fl, x - fo) {
                assert(sno@[x + 1] <= nbl && sao@[x + 1] <= abl);
                let na = sno[x] as usize;
                let nz = sno[x + 1] as usize;
                let aa = sao[x] as usize;
                let az = sao[x + 1] as usize;
                if rows < rcap && nz - na <= ncap - nused && az - aa <= acap - aused {
                    let row = Ghost(orow(sp, x as int));
                    proof {
                        assert(seg(sv, ps, d1, y0 as int, x + 1) == r0.push(row@));
                    }
                    if sorted && rows > 0 {
                        assert(cf::text_range_ok(sno@, snb@, last as int));
                        assert(sno@[last + 1] <= nbl);
                        let pa = sno[last] as usize;
                        let pz = sno[last + 1] as usize;
                        let pv = text_slice(sno, snb, last);
                        let cv = text_slice(sno, snb, x);
                        let c = bytes_cmp(pv, pz - pa, cv, nz - na);
                        if c > 0 {
                            sorted = false;
                        } else {
                            proof {
                                assert(pv@ == tval(r0[rows - 1][0]));
                                assert(cv@ == tval(row@[0]));
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
                    copy_into(&mut nb, nused, snb, na, nz, Ghost(ncap));
                    copy_into(&mut ab, aused, sab, aa, az, Ghost(acap));
                    let nu2 = nused + (nz - na);
                    let au2 = aused + (az - aa);
                    no[rows + 1] = nu2;
                    ao[rows + 1] = au2;
                    proof {
                        let nm = snb@.subrange(na as int, nz as int);
                        let ad = sab@.subrange(aa as int, az as int);
                        assert(nm == sun(sp, x as int) && ad == sua(sp, x as int));
                        assert(nb@.take(nu2 as int) =~= nb0.take(nused as int) + nm) by {
                            assert(nb@.take(nused as int) == nb0.take(nused as int));
                            assert(nb@.subrange(nused as int, nu2 as int) == nm);
                        }
                        assert(ab@.take(au2 as int) =~= ab0.take(aused as int) + ad) by {
                            assert(ab@.take(aused as int) == ab0.take(aused as int));
                            assert(ab@.subrange(aused as int, au2 as int) == ad);
                        }
                        assert(no@.take(rows + 2) =~= no0.take(rows + 1).push(nu2));
                        assert(ao@.take(rows + 2) =~= ao0.take(rows + 1).push(au2));
                        lemma_tcol_push(no0.take(rows + 1), nb0.take(nused as int), names_of(r0), nm, no@.take(rows + 2), nb@.take(nu2 as int));
                        lemma_tcol_push(ao0.take(rows + 1), ab0.take(aused as int), addrs_of(r0), ad, ao@.take(rows + 2), ab@.take(au2 as int));
                        assert(names_of(r0).push(nm) =~= names_of(r0.push(row@)));
                        assert(addrs_of(r0).push(ad) =~= addrs_of(r0.push(row@)));
                        if rows > 0 {
                            assert(r0.push(row@)[0] == r0[0]);
                        }
                    }
                    if rows == 0 {
                        first = x;
                    }
                    last = x;
                    rows = rows + 1;
                    nused = nu2;
                    aused = au2;
                } else {
                    ovf = true;
                }
            } else {
                proof {
                    assert(seg(sv, ps, d1, y0 as int, x + 1) == r0);
                }
            }
            if !ovf {
                x = x + 1;
            }
        }
        Piece { no, nb, ao, ab, rows, nused, aused, ovf, sorted, tch, first, last }
    }
}


/// Boundary `t` of `nt` ranges over `n` rows.
pub open spec fn yb(n: int, t: int, nt: int) -> int {
    (n * t) / nt
}

proof fn lemma_yb(n: int, t: int, nt: int)
    requires 0 <= t < nt, n >= 0,
    ensures 0 <= yb(n, t, nt) <= yb(n, t + 1, nt) <= n, t + 1 == nt ==> yb(n, t + 1, nt) == n, yb(n, 0, nt) == 0,
{
    assert(0 <= n * t <= n * (t + 1) <= n * nt) by (nonlinear_arith) requires 0 <= t < nt, n >= 0;
    vstd::arithmetic::div_mod::lemma_div_is_ordered(n * t, n * (t + 1), nt);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(n * (t + 1), n * nt, nt);
    vstd::arithmetic::div_mod::lemma_div_by_multiple(n, nt);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(n * t, nt);
    assert(n * 0 == 0);
}

/// Two sorted sequences of text-keyed rows, the last of the first not above the first of the second: sorted.
proof fn lemma_sorted_concat(a: Seq<Row>, b: Seq<Row>)
    requires
        sorted_by(q_keys(), a), sorted_by(q_keys(), b),
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == 2 && a[i][0] is Text,
        forall|i: int| 0 <= i < b.len() ==> (#[trigger] b[i]).len() == 2 && b[i][0] is Text,
        a.len() > 0 && b.len() > 0 ==> lex_cmp(tval(a[a.len() - 1][0]), tval(b[0][0])) <= 0,
    ensures sorted_by(q_keys(), a + b),
{
    let c = a + b;
    let n = a.len() as int;
    assert forall|i: int, j: int| 0 <= i < j < c.len() implies keys_cmp(q_keys(), #[trigger] c[i], #[trigger] c[j]) <= 0 by {
        if j < n {
            assert(c[i] == a[i] && c[j] == a[j]);
        } else if i >= n {
            assert(c[i] == b[i - n] && c[j] == b[j - n]);
        } else {
            assert(c[i] == a[i] && c[j] == b[j - n]);
            let (x, l, f, y) = (a[i], a[n - 1], b[0], b[j - n]);
            lemma_keys_text(x, l);
            lemma_keys_text(f, y);
            lemma_keys_text(x, y);
            if i < n - 1 {
                assert(keys_cmp(q_keys(), a[i], a[n - 1]) <= 0);
            } else {
                crate::bridge::equality::lemma_lex_cmp_zero(tval(x[0]), tval(l[0]));
            }
            if j - n > 0 {
                assert(keys_cmp(q_keys(), b[0], b[j - n]) <= 0);
            } else {
                crate::bridge::equality::lemma_lex_cmp_zero(tval(f[0]), tval(y[0]));
            }
            crate::bridge::order::lemma_lex_cmp_trans(tval(x[0]), tval(l[0]), tval(f[0]));
            crate::bridge::order::lemma_lex_cmp_trans(tval(x[0]), tval(f[0]), tval(y[0]));
        }
    }
}

/// The calling thread's facts about output task `w` of `nt`.
pub open spec fn otask_ok(t: OutTask, sv: StoresView, ps: Seq<Literal>, d1: int, ns: int, w: int, nt: int) -> bool {
    &&& t.pre()
    &&& t.sv@ == sv && t.ps@ == ps && t.d1@ == d1
    &&& t.y0 == yb(ns, w, nt) && t.y1 == yb(ns, w + 1, nt)
}

/// The set bits of `v` (an estimate only: no specification).
fn popcnt(v: u64) -> usize {
    let a = v.wrapping_sub((v >> 1) & 0x5555_5555_5555_5555u64);
    let b = (a & 0x3333_3333_3333_3333u64).wrapping_add((a >> 2) & 0x3333_3333_3333_3333u64);
    let c = b.wrapping_add(b >> 4) & 0x0f0f_0f0f_0f0f_0f0fu64;
    (c.wrapping_mul(0x0101_0101_0101_0101u64) >> 56u64) as usize
}

/// Bits set in words `[w0, w1)` of `g`, at most `m` (an estimate of the rows of a range).
fn count_flags(g: &Vec<u64>, w0: usize, w1: usize, m: usize) -> (c: usize)
    requires w0 <= w1 <= g@.len(),
    ensures c <= m,
{
    let mut c: usize = 0;
    let mut w = w0;
    while w < w1
        invariant w0 <= w <= w1 <= g@.len(), c <= m,
        decreases w1 - w,
    {
        let k = popcnt(g[w]);
        if k <= m - c {
            c = c + k;
        } else {
            c = m;
        }
        w = w + 1;
    }
    c
}

/// A copy of words `[w0, w1)` of `g`.
fn copy_flags(g: &Vec<u64>, w0: usize, w1: usize) -> (r: Vec<u64>)
    requires w0 <= w1 <= g@.len(),
    ensures r@ == g@.subrange(w0 as int, w1 as int),
{
    let mut r: Vec<u64> = Vec::with_capacity(w1 - w0);
    let (_, t) = g.as_slice().split_at(w0);
    let (m, _) = t.split_at(w1 - w0);
    r.extend_from_slice(m);
    proof {
        assert(r@ =~= g@.subrange(w0 as int, w1 as int));
    }
    r
}

/// Buffer size for `cnt` rows of a column whose rows `[y0, y1)` take `span` bytes: the average row plus 8 bytes per
/// row, at most `span`.
fn est_cap(cnt: usize, span: usize, y0: usize, y1: usize) -> (c: usize)
    ensures c <= span,
{
    if y1 <= y0 {
        return 0;
    }
    let avg = span / (y1 - y0);
    if cnt > 0x8000_0000 || avg > 0x8000_0000 {
        return span;
    }
    let a8 = avg as u64 + 8;
    assert((cnt as u64) * a8 <= 0x8000_0000 * 0x8000_0008) by (nonlinear_arith)
        requires cnt <= 0x8000_0000, a8 <= 0x8000_0008;
    let e = (cnt as u64) * a8;
    if (e as u128) < span as u128 { e as usize } else { span }
}

/// The output task over supplier rows `[y0, y1)`.
fn make_otask(g: &Vec<u64>, y0: usize, y1: usize, sno: &'static [u64], snb: &'static [u8], sao: &'static [u64],
    sab: &'static [u8], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(d1): Ghost<int>) -> (t: OutTask)
    requires
        sp_ok(sv.suppliers),
        text_views(sv.suppliers, sno@, snb@, sao@, sab@),
        y0 <= y1 <= tn(sv.suppliers, 13),
        holds(g@, tn(sv.suppliers, 13)),
        forall|x: int| 0 <= x < tn(sv.suppliers, 13) ==> #[trigger] bit(g@, x) == sl_s_qual(sv, ps, d1, x),
    ensures
        t.pre(), t.sv@ == sv, t.ps@ == ps, t.d1@ == d1, t.y0 == y0, t.y1 == y1,
{
    let ghost sp = sv.suppliers;
    proof {
        assert(cf::text_range_ok(sno@, snb@, y0 as int) || y0 == y1);
    }
    let w0 = y0 / 64;
    let w1 = if y1 / 64 < g.len() { y1 / 64 + 1 } else { g.len() };
    let fo = w0 * 64;
    let cnt = count_flags(g, w0, w1, y1 - y0);
    let fl = copy_flags(g, w0, w1);
    let nbl = snb.len();
    let abl = sab.len();
    let nspan: usize = if y0 < y1 {
        assert(cf::text_range_ok(sno@, snb@, (y1 - 1) as int));
        if sno[y1] >= sno[y0] && sno[y1] <= nbl as u64 { (sno[y1] - sno[y0]) as usize } else { nbl }
    } else { 0 };
    let aspan: usize = if y0 < y1 {
        assert(cf::text_range_ok(sao@, sab@, (y1 - 1) as int));
        if sao[y1] >= sao[y0] && sao[y1] <= abl as u64 { (sao[y1] - sao[y0]) as usize } else { abl }
    } else { 0 };
    let ncap = est_cap(cnt, nspan, y0, y1);
    let acap = est_cap(cnt, aspan, y0, y1);
    let no: Vec<usize> = vec![0usize; cnt + 1];
    let ao: Vec<usize> = vec![0usize; cnt + 1];
    let nb: Vec<u8> = vec![0u8; ncap];
    let ab: Vec<u8> = vec![0u8; acap];
    let t = OutTask {
        sv: Ghost(sv), ps: Ghost(ps), d1: Ghost(d1), y0, y1, fo, fl, sno, snb, sao, sab, no, nb, ao, ab,
        rcap: cnt, ncap, acap, nbl, abl,
    };
    proof {
        assert(y1 <= w1 * 64);
        assert forall|i: int| y0 - fo <= i < y1 - fo implies #[trigger] bit(t.fl@, i) == sl_s_qual(sv, ps, d1, fo + i) by {
            lemma_div_lt(i, 64, (w1 - w0) as int);
            lemma_bit_words(t.fl@, g@, w0 as int, i);
        }
    }
    t
}

/// Append a piece's text column (offsets `po`, bytes `pb[.. used]`) to a column: one bulk copy of the bytes, then
/// the shifted offsets. `false` (nothing appended) if the bytes would not fit.
fn append_col(offs: &mut Vec<usize>, bytes: &mut Vec<u8>, po: &Vec<usize>, pb: &Vec<u8>, rows: usize, used: usize,
    Ghost(pre): Ghost<Seq<Seq<u8>>>, Ghost(vals): Ghost<Seq<Seq<u8>>>) -> (ok: bool)
    requires
        tcol_ok(old(offs)@, old(bytes)@, pre),
        rows < po@.len(), used <= pb@.len(), po@[0] == 0,
        tcol_ok(po@.take(rows + 1), pb@.take(used as int), vals),
    ensures
        ok ==> tcol_ok(final(offs)@, final(bytes)@, pre + vals),
        !ok ==> final(offs)@ == old(offs)@ && final(bytes)@ == old(bytes)@,
{
    if used > usize::MAX - bytes.len() {
        return false;
    }
    let ghost o0 = offs@;
    let ghost b0 = bytes@;
    let ghost pos = po@.take(rows + 1);
    let ghost pbs = pb@.take(used as int);
    let base = bytes.len();
    let (m, _) = pb.as_slice().split_at(used);
    bytes.extend_from_slice(m);
    proof {
        assert(m@ =~= pbs);
        assert forall|k: int| 0 <= k < pre.len() implies #[trigger] rng_ok(offs@, bytes@.len() as int, k)
            && tcol_at(offs@, bytes@, k) == pre[k] by {
            assert(rng_ok(o0, b0.len() as int, k));
            assert(tcol_at(offs@, bytes@, k) =~= tcol_at(o0, b0, k));
        }
        assert(pos[0] == 0);
    }
    let mut i: usize = 0;
    while i < rows
        invariant
            rows < po@.len(), used <= pb@.len(), pos == po@.take(rows + 1), pbs == pb@.take(used as int),
            tcol_ok(pos, pbs, vals),
            i <= rows, base == b0.len(), bytes@ == b0 + pbs, base + used <= usize::MAX,
            offs@.len() == pre.len() + i + 1,
            offs@[pre.len() + i] == base + pos[i as int],
            forall|k: int| 0 <= k < pre.len() ==> #[trigger] rng_ok(offs@, bytes@.len() as int, k)
                && tcol_at(offs@, bytes@, k) == pre[k],
            forall|k: int| pre.len() <= k < pre.len() + i ==> #[trigger] rng_ok(offs@, bytes@.len() as int, k)
                && tcol_at(offs@, bytes@, k) == vals[k - pre.len()],
        decreases rows - i,
    {
        proof {
            assert(rng_ok(pos, pbs.len() as int, i as int));
            assert(po@[i + 1] == pos[i + 1]);
        }
        let v = po[i + 1];
        let ghost of = offs@;
        offs.push(base + v);
        proof {
            assert forall|k: int| 0 <= k < pre.len() implies #[trigger] rng_ok(offs@, bytes@.len() as int, k)
                && tcol_at(offs@, bytes@, k) == pre[k] by {
                assert(rng_ok(of, bytes@.len() as int, k));
                assert(offs@[k] == of[k] && offs@[k + 1] == of[k + 1]);
            }
            assert forall|k: int| pre.len() <= k < pre.len() + i + 1 implies #[trigger] rng_ok(offs@, bytes@.len() as int, k)
                && tcol_at(offs@, bytes@, k) == vals[k - pre.len()] by {
                if k < pre.len() + i {
                    assert(rng_ok(of, bytes@.len() as int, k));
                    assert(offs@[k] == of[k] && offs@[k + 1] == of[k + 1]);
                } else {
                    assert(rng_ok(pos, pbs.len() as int, i as int));
                    assert(offs@[k] == base + pos[i as int]);
                    assert(offs@[k + 1] == base + pos[i + 1]);
                    assert(tcol_at(offs@, bytes@, k) =~= tcol_at(pos, pbs, i as int));
                    assert(tcol_at(pos, pbs, i as int) == vals[i as int]);
                }
            }
        }
        i = i + 1;
    }
    proof {
        let all = pre + vals;
        assert(pos.len() == rows + 1 && vals.len() == rows);
        assert(pos[rows as int] == pbs.len());
        assert(offs@.last() == bytes@.len());
        assert forall|k: int| 0 <= k < all.len() implies #[trigger] rng_ok(offs@, bytes@.len() as int, k)
            && tcol_at(offs@, bytes@, k) == all[k] by {
            assert(vals.len() == rows);
            if k >= pre.len() {
                assert(pre.len() <= k < pre.len() + i);
                assert(rng_ok(offs@, bytes@.len() as int, k));
                assert(tcol_at(offs@, bytes@, k) == vals[k - pre.len()]);
                assert(all[k] == vals[k - pre.len()]);
            } else {
                assert(rng_ok(offs@, bytes@.len() as int, k));
                assert(tcol_at(offs@, bytes@, k) == pre[k]);
                assert(all[k] == pre[k]);
            }
        }
    }
    true
}

/// The output columns, built by `nt` tasks (or, if a piece overflows, by the calling thread).
pub fn par_output(g: &Vec<u64>, ns: usize, sno: &'static [u64], snb: &'static [u8], sao: &'static [u64], sab: &'static [u8],
    nt: usize, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(d1): Ghost<int>)
    -> (r: Result<Built, WorkerFailure>)
    requires
        sp_ok(sv.suppliers),
        ns == tn(sv.suppliers, 13),
        text_views(sv.suppliers, sno@, snb@, sao@, sab@),
        holds(g@, ns as int),
        forall|x: int| 0 <= x < ns ==> #[trigger] bit(g@, x) == sl_s_qual(sv, ps, d1, x),
        1 <= nt <= MAX_WORKERS,
    ensures
        r matches Ok(b) ==> built_ok(b, sel_rows(sv, ps, d1, ns as int))
            && (b.sorted ==> sorted_by(q_keys(), sel_rows(sv, ps, d1, ns as int))),
{
    let ghost sp = sv.suppliers;
    let mut tasks: Vec<OutTask> = Vec::new();
    let mut t: usize = 0;
    let mut prev: usize = 0;
    while t < nt
        invariant
            sp_ok(sp), sp == sv.suppliers, ns == tn(sp, 13),
            text_views(sp, sno@, snb@, sao@, sab@),
            holds(g@, ns as int),
            forall|x: int| 0 <= x < ns ==> #[trigger] bit(g@, x) == sl_s_qual(sv, ps, d1, x),
            1 <= nt <= MAX_WORKERS, t <= nt,
            tasks@.len() == t,
            prev as int == yb(ns as int, t as int, nt as int), prev <= ns,
            forall|w: int| 0 <= w < t ==> #[trigger] otask_ok(tasks@[w], sv, ps, d1, ns as int, w, nt as int),
        decreases nt - t,
    {
        proof {
            lemma_yb(ns as int, t as int, nt as int);
            assert(ns as int * (t + 1) <= 0x1_0000_0000_0000_0000 * 64) by (nonlinear_arith)
                requires ns as int <= 0xffff_ffff_ffff_ffff, t + 1 <= 64;
        }
        let y1 = ((ns as u128 * (t as u128 + 1)) / nt as u128) as usize;
        let task = make_otask(g, prev, y1, sno, snb, sao, sab, Ghost(sv), Ghost(ps), Ghost(d1));
        let ghost tasks0 = tasks@;
        tasks.push(task);
        proof {
            assert forall|w: int| 0 <= w < t + 1 implies #[trigger] otask_ok(tasks@[w], sv, ps, d1, ns as int, w, nt as int) by {
                if w < t {
                    assert(tasks@[w] == tasks0[w]);
                }
            }
        }
        prev = y1;
        t = t + 1;
    }
    let ghost ts = tasks@;
    proof {
        assert forall|i: int| 0 <= i < tasks@.len() implies #[trigger] tasks@[i].pre() by {
            assert(otask_ok(tasks@[i], sv, ps, d1, ns as int, i, nt as int));
        }
    }
    let pieces = match fork_join(dispatch, tasks) {
        Ok(p) => p,
        Err(e) => return Err(e),
    };
    // any overflow: build on the calling thread
    let mut w: usize = 0;
    let mut ovf = false;
    while w < pieces.len()
        invariant w <= pieces@.len(), !ovf ==> forall|i: int| 0 <= i < w ==> !(#[trigger] pieces@[i]).ovf,
        decreases pieces@.len() - w,
    {
        if pieces[w].ovf {
            ovf = true;
        }
        w = w + 1;
    }
    if ovf {
        return Ok(build_output(g, ns, sno, snb, sao, sab, Ghost(sv), Ghost(ps), Ghost(d1)));
    }
    // exact capacities: the total rows and bytes of the pieces
    let mut tr: usize = 0;
    let mut tnb: usize = 0;
    let mut tab: usize = 0;
    w = 0;
    while w < pieces.len()
        invariant w <= pieces@.len(), tr < 0x4000_0000, tnb < 0x4000_0000, tab < 0x4000_0000,
        decreases pieces@.len() - w,
    {
        let p = &pieces[w];
        tr = if p.rows < 0x2000_0000 && tr < 0x2000_0000 { tr + p.rows } else { 0 };
        tnb = if p.nused < 0x2000_0000 && tnb < 0x2000_0000 { tnb + p.nused } else { 0 };
        tab = if p.aused < 0x2000_0000 && tab < 0x2000_0000 { tab + p.aused } else { 0 };
        w = w + 1;
    }
    let mut no: Vec<usize> = Vec::with_capacity(tr + 1);
    no.push(0);
    let mut nb: Vec<u8> = Vec::with_capacity(tnb);
    let mut ao: Vec<usize> = Vec::with_capacity(tr + 1);
    ao.push(0);
    let mut ab: Vec<u8> = Vec::with_capacity(tab);
    let mut rows: usize = 0;
    let mut sorted = true;
    let mut lastx: usize = 0;
    proof {
        assert(no@ =~= seq![0usize]);
        assert(ao@ =~= seq![0usize]);
        assert(nb@ =~= Seq::<u8>::empty());
        assert(ab@ =~= Seq::<u8>::empty());
        lemma_yb(ns as int, 0, nt as int);
        assert(names_of(sel_rows(sv, ps, d1, 0)) =~= Seq::<Seq<u8>>::empty());
        assert(addrs_of(sel_rows(sv, ps, d1, 0)) =~= Seq::<Seq<u8>>::empty());
    }
    let mut t: usize = 0;
    while t < nt
        invariant
            sp_ok(sp), sp == sv.suppliers, ns == tn(sp, 13),
            text_views(sp, sno@, snb@, sao@, sab@),
            1 <= nt <= MAX_WORKERS, t <= nt,
            pieces@.len() == nt, ts.len() == nt,
            forall|i: int| 0 <= i < nt ==> !(#[trigger] pieces@[i]).ovf,
            forall|i: int| 0 <= i < nt ==> #[trigger] otask_ok(ts[i], sv, ps, d1, ns as int, i, nt as int) && ts[i].post(pieces@[i]),
            rows == sel_rows(sv, ps, d1, yb(ns as int, t as int, nt as int)).len(),
            tcol_ok(no@, nb@, names_of(sel_rows(sv, ps, d1, yb(ns as int, t as int, nt as int)))),
            tcol_ok(ao@, ab@, addrs_of(sel_rows(sv, ps, d1, yb(ns as int, t as int, nt as int)))),
            sorted ==> sorted_by(q_keys(), sel_rows(sv, ps, d1, yb(ns as int, t as int, nt as int))),
            holds(g@, ns as int),
            forall|x: int| 0 <= x < ns ==> #[trigger] bit(g@, x) == sl_s_qual(sv, ps, d1, x),
            rows > 0 ==> lastx < ns && sel_rows(sv, ps, d1, yb(ns as int, t as int, nt as int))[rows - 1] == orow(sp, lastx as int),
            forall|i: int| 0 <= i < rows ==> (#[trigger] sel_rows(sv, ps, d1, yb(ns as int, t as int, nt as int))[i]).len() == 2
                && sel_rows(sv, ps, d1, yb(ns as int, t as int, nt as int))[i][0] is Text
                && sel_rows(sv, ps, d1, yb(ns as int, t as int, nt as int))[i][1] is Text,
            nb@.len() <= usize::MAX, ab@.len() <= usize::MAX,
        decreases nt - t,
    {
        let ghost ya = yb(ns as int, t as int, nt as int);
        let ghost yz = yb(ns as int, t + 1, nt as int);
        let ghost acc = sel_rows(sv, ps, d1, ya);
        let ghost sg = seg(sv, ps, d1, ya, yz);
        proof {
            lemma_yb(ns as int, t as int, nt as int);
            lemma_sel_split(sv, ps, d1, ya, yz);
            lemma_seg_rows(sv, ps, d1, ya, yz);
            assert(otask_ok(ts[t as int], sv, ps, d1, ns as int, t as int, nt as int) && ts[t as int].post(pieces@[t as int]));
            assert(!pieces@[t as int].ovf);
        }
        let p = &pieces[t];
        // boundary order
        if sorted {
            if !p.sorted {
                sorted = false;
            } else if rows > 0 && p.rows > 0 {
                assert(cf::text_range_ok(sno@, snb@, lastx as int));
                assert(cf::text_range_ok(sno@, snb@, p.first as int));
                let pv = text_slice(sno, snb, lastx);
                let cv = text_slice(sno, snb, p.first);
                let c = bytes_cmp(pv, pv.len(), cv, cv.len());
                if c > 0 {
                    sorted = false;
                } else {
                    proof {
                        lemma_sorted_concat(acc, sg);
                    }
                }
            } else {
                proof {
                    lemma_sorted_concat(acc, sg);
                }
            }
        }
        proof {
            assert(p.no@.take(p.rows + 1)[0] == 0 && p.ao@.take(p.rows + 1)[0] == 0);
        }
        if !append_col(&mut no, &mut nb, &p.no, &p.nb, p.rows, p.nused, Ghost(names_of(acc)), Ghost(names_of(sg))) {
            return Ok(build_output(g, ns, sno, snb, sao, sab, Ghost(sv), Ghost(ps), Ghost(d1)));
        }
        if !append_col(&mut ao, &mut ab, &p.ao, &p.ab, p.rows, p.aused, Ghost(addrs_of(acc)), Ghost(addrs_of(sg))) {
            return Ok(build_output(g, ns, sno, snb, sao, sab, Ghost(sv), Ghost(ps), Ghost(d1)));
        }
        proof {
            lemma_sel_len(sv, ps, d1, yz);
        }
        rows = rows + p.rows;
        proof {
            assert(names_of(acc + sg) =~= names_of(acc) + names_of(sg));
            assert(addrs_of(acc + sg) =~= addrs_of(acc) + addrs_of(sg));
        }
        proof {
            assert(sg.take(sg.len() as int) =~= sg);
            let r1 = acc + sg;
            assert forall|k: int| 0 <= k < rows implies (#[trigger] r1[k]).len() == 2 && r1[k][0] is Text && r1[k][1] is Text by {
                if k < acc.len() {
                    assert(r1[k] == acc[k]);
                } else {
                    assert(r1[k] == sg[k - acc.len()]);
                }
            }
        }
        if p.rows > 0 {
            lastx = p.last;
            proof {
                let r1 = acc + sg;
                assert(r1[rows - 1] == sg[p.rows - 1]);
            }
        }
        t = t + 1;
    }
    let ghost rs = sel_rows(sv, ps, d1, ns as int);
    proof {
        lemma_yb(ns as int, (nt - 1) as int, nt as int);
        assert forall|i: int| 0 <= i < rows implies #[trigger] rs[i] == trow(no@, nb@, ao@, ab@, i) by {
            assert(rng_ok(no@, nb@.len() as int, i));
            assert(rng_ok(ao@, ab@.len() as int, i));
            assert(names_of(rs)[i] == tval(rs[i][0]));
            assert(addrs_of(rs)[i] == tval(rs[i][1]));
            assert(rs[i] =~= trow(no@, nb@, ao@, ab@, i));
        }
        assert forall|i: int| 0 <= i < rows implies #[trigger] rng_ok(no@, nb@.len() as int, i)
            && rng_ok(ao@, ab@.len() as int, i) by {
            assert(names_of(rs)[i] == tval(rs[i][0]));
            assert(rng_ok(ao@, ab@.len() as int, i));
        }
    }
    Ok(Built { no, nb, ao, ab, rows, sorted })
}

} // verus!
