//! The read-only context of a worker task (`Ctx`): the slices of every part the kernel reads, their meaning
//! (`Ctx::wf`: the slices are the parts of `sv`, whose `sl_ok` holds), and `no_unwind` readers of single values:
//! a part row's key, partsupp / lineitem / supplier values, the supplier row of a key and the nation test.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::stores::part_nameidx::interface as pi;
use crate::stores::li_pkdate::interface as li;
use crate::stores::suppliers::interface::common::colfmt as cf;
use crate::stores::suppliers::interface::common::read::{lemma_div_lt, find_key_u32, key_u32_at};
use vstd::arithmetic::power2::pow2;
use super::typed::p15;
use super::nf::*;
use super::bind_sp::*;
use super::bind_pl::*;
use super::sl::*;

verus! {

/// A block size as a `usize` (larger ones only ever divide row numbers below them).
pub open spec fn bmin(b: int) -> int {
    if b > usize::MAX { usize::MAX as int } else { b }
}

/// `bmin` changes no quotient of a row number and still covers the rows with the bases.
pub proof fn lemma_bmin(j: int, b: int, len: int, n: int)
    requires 0 <= j < n <= usize::MAX, b >= 1, len >= 0, len * b >= n,
    ensures j / bmin(b) == j / b, len * bmin(b) >= n, bmin(b) >= 1,
{
    if b > usize::MAX {
        let m = usize::MAX as int;
        assert(len >= 1) by (nonlinear_arith) requires len * b >= n, n > j, j >= 0, len >= 0;
        assert(len * m >= m) by (nonlinear_arith) requires len >= 1, m >= 0;
        vstd::arithmetic::div_mod::lemma_basic_div(j, m);
        vstd::arithmetic::div_mod::lemma_basic_div(j, b);
    }
}

/// The `usize` block size of a stored `u64` block size.
pub fn bsize_of(b: u64) -> (r: usize)
    ensures r as int == bmin(b as int),
{
    if b > usize::MAX as u64 { usize::MAX } else { b as usize }
}

/// `v` clamped to `[-1, 65536]` (a date offset compared with U16 date codes).
pub open spec fn clampd(v: int) -> int {
    if v < -1 { -1 } else if v > 65536 { 65536 } else { v }
}

/// `sh` serves blocks of `bs` rows: `bs == 2^sh` when `sh < 64` (a shift replaces the division); 64 means divide.
pub open spec fn sh_ok(bs: usize, sh: u64) -> bool {
    sh <= 64 && (sh < 64 ==> bs as nat == pow2(sh as nat))
}

/// The shift of a block size (64 when it is not a power of two).
pub fn shift_of(bs: usize) -> (sh: u64)
    ensures sh_ok(bs, sh),
{
    let mut s: u64 = 0;
    while s < 63
        invariant s <= 63,
        decreases 63 - s,
    {
        proof {
            vstd::bits::lemma_u64_pow2_no_overflow(s as nat);
            vstd::bits::lemma_u64_shl_is_mul(1u64, s);
        }
        if (bs as u64) == (1u64 << s) {
            return s;
        }
        s = s + 1;
    }
    64
}

/// `j / bs` (a shift when `sh < 64`).
pub fn bdiv(j: usize, bs: usize, sh: u64) -> (q: usize)
    requires bs >= 1, sh_ok(bs, sh),
    ensures q as int == (j as int) / (bs as int),
    no_unwind
{
    if sh < 64 {
        proof {
            vstd::bits::lemma_u64_shr_is_div(j as u64, sh);
        }
        ((j as u64) >> sh) as usize
    } else {
        j / bs
    }
}

/// Value of row `j` of a FOR column with U32 codes and I64 bases (groups of `bs` rows).
pub fn fget_u32(codes: &[u32], bases: &[i64], bs: usize, sh: u64, j: usize) -> (v: i64)
    requires
        bs >= 1, sh_ok(bs, sh),
        j < codes@.len(),
        (j as int) / (bs as int) < bases@.len(),
        i64::MIN <= bases@[(j as int) / (bs as int)] + codes@[j as int] <= i64::MAX,
    ensures v == bases@[(j as int) / (bs as int)] + codes@[j as int],
    no_unwind
{
    bases[bdiv(j, bs, sh)] + codes[j] as i64
}

/// Value of row `j` of a FOR column with U16 codes and I64 bases.
pub fn fget_u16(codes: &[u16], bases: &[i64], bs: usize, sh: u64, j: usize) -> (v: i64)
    requires
        bs >= 1, sh_ok(bs, sh),
        j < codes@.len(),
        (j as int) / (bs as int) < bases@.len(),
        i64::MIN <= bases@[(j as int) / (bs as int)] + codes@[j as int] <= i64::MAX,
    ensures v == bases@[(j as int) / (bs as int)] + codes@[j as int],
    no_unwind
{
    bases[bdiv(j, bs, sh)] + codes[j] as i64
}

/// Value of row `j` of a FOR column with U8 codes and I64 bases.
pub fn fget_u8(codes: &[u8], bases: &[i64], bs: usize, sh: u64, j: usize) -> (v: i64)
    requires
        bs >= 1, sh_ok(bs, sh),
        j < codes@.len(),
        (j as int) / (bs as int) < bases@.len(),
        i64::MIN <= bases@[(j as int) / (bs as int)] + codes@[j as int] <= i64::MAX,
    ensures v == bases@[(j as int) / (bs as int)] + codes@[j as int],
    no_unwind
{
    bases[bdiv(j, bs, sh)] + codes[j] as i64
}

pub struct Ctx {
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
    pub d1g: Ghost<int>,
    // part
    pub np: usize,
    pub pbs: usize,
    pub psh: u64,
    pub pk: &'static [u32],
    pub pkb: &'static [i64],
    // partsupp
    pub nps: usize,
    pub psbs: usize,
    pub pssh: u64,
    pub sorted: bool,
    /// Position guess for a key `k` (any values are correct): `(k - gk0) * gnum / gden`.
    pub gk0: i64,
    pub gnum: u64,
    pub gden: u64,
    /// `gnum / gden` when it divides exactly (the guess is then a multiplication), else 0.
    pub gmul: u64,
    /// The partsupp run layout holds (`suppliers_psrun`): row `j` has key `first + j / ratio`.
    pub runok: bool,
    pub ratio: usize,
    pub first: i64,
    pub spk: &'static [u32],
    pub spkb: &'static [i64],
    pub ssk: &'static [u32],
    pub sskb: &'static [i64],
    pub sav: &'static [u16],
    pub savb: &'static [i64],
    // lineitem
    pub nl: usize,
    pub lbs: usize,
    pub lsh: u64,
    pub idx: bool,
    pub kmin: i64,
    pub nkeys: usize,
    pub offs: &'static [u32],
    pub irows: &'static [u32],
    pub idates: &'static [u16],
    pub dlo: i64,
    pub dhi: i64,
    pub lkey: &'static [u32],
    pub lkeyb: &'static [i64],
    pub lsk: &'static [u32],
    pub lskb: &'static [i64],
    pub lq: &'static [u16],
    pub lqb: &'static [i64],
    pub ldt: &'static [u16],
    pub ldtb: &'static [i64],
    pub d0: i64,
    pub d1: i64,
    // supplier
    pub ns: usize,
    pub sbs: usize,
    pub ssh: u64,
    pub sbase: i64,
    /// Supplier keys are dense: row `x` has key `sbase + x`.
    pub dense: bool,
    pub suk: &'static [u32],
    pub sukb: &'static [i64],
    pub snk: &'static [u8],
    pub snkb: &'static [i64],
    // nation keys named $3
    pub natk: Vec<i64>,
    pub natn: usize,
}

impl Ctx {
    pub open spec fn pp(&self) -> Seq<PartView> { self.sv@.part_nameidx }
    pub open spec fn lp(&self) -> Seq<PartView> { self.sv@.li_pkdate }
    pub open spec fn sp(&self) -> Seq<PartView> { self.sv@.suppliers }
    pub open spec fn pat(&self) -> Seq<u8> { pat_of(self.ps@) }
    pub open spec fn nname(&self) -> Seq<u8> { nname_of(self.ps@) }

    pub open spec fn wf_part(&self) -> bool {
        let pp = self.pp();
        &&& pp_ok(pp)
        &&& self.np == pi::n_rows(pp)
        &&& self.pbs as int == bmin(pi::bsize(pp))
        &&& sh_ok(self.pbs, self.psh)
        &&& self.pk@ == pi::u32s(pp[pi::PA_PARTKEY_CODES as int])
        &&& self.pkb@ == pi::i64s(pp[pi::PA_PARTKEY_BASE as int])
    }

    pub open spec fn wf_ps(&self) -> bool {
        let sp = self.sp();
        &&& sp_ok(sp)
        &&& self.nps == tn(sp, 0)
        &&& self.psbs as int == bmin(tbs(sp, 0))
        &&& sh_ok(self.psbs, self.pssh)
        &&& self.spk@ == cf::u32s(sp[2])
        &&& self.spkb@ == cf::i64s(sp[3])
        &&& self.ssk@ == cf::u32s(sp[4])
        &&& self.sskb@ == cf::i64s(sp[5])
        &&& self.sav@ == u16s(sp[6])
        &&& self.savb@ == cf::i64s(sp[7])
        &&& (self.sorted ==> ps_kind(sp) == 1)
        &&& (self.runok ==> self.ratio >= 1 && forall|j: int| 0 <= j < self.nps
            ==> #[trigger] psk(sp, j) == self.first + j / (self.ratio as int))
    }

    pub open spec fn wf_li(&self) -> bool {
        let lp = self.lp();
        &&& lp_ok(lp)
        &&& self.nl == li::n_rows(lp)
        &&& self.lbs as int == bmin(li::bsize(lp))
        &&& sh_ok(self.lbs, self.lsh)
        &&& self.idx == li::has_idx(lp)
        &&& self.lkey@ == li::u32s(lp[li::LI_PARTKEY_CODES as int])
        &&& self.lkeyb@ == li::i64s(lp[li::LI_PARTKEY_BASE as int])
        &&& self.lsk@ == li::u32s(lp[li::LI_SUPPKEY_CODES as int])
        &&& self.lskb@ == li::i64s(lp[li::LI_SUPPKEY_BASE as int])
        &&& self.lq@ == li::u16s(lp[li::LI_QUANTITY_CODES as int])
        &&& self.lqb@ == li::i64s(lp[li::LI_QUANTITY_BASE as int])
        &&& self.ldt@ == li::u16s(lp[li::LI_SHIPDATE_CODES as int])
        &&& self.ldtb@ == li::i64s(lp[li::LI_SHIPDATE_BASE as int])
        &&& self.d0 == d0_of(self.ps@)
        &&& self.d1 == self.d1g@
        &&& -0x1_0000_0000 <= self.d0 <= 0x1_0000_0000
        &&& -0x1_0000_0000 <= self.d1 <= 0x1_0000_0000
        &&& self.idx ==> {
            &&& self.kmin == li::idx_kmin(lp)
            &&& self.nkeys == li::idx_nkeys(lp)
            &&& self.offs@ == li::idx_offs(lp)
            &&& self.irows@ == li::idx_rows(lp)
            &&& self.idates@ == li::idx_dates(lp)
            &&& self.dlo == clampd(self.d0 - li::idx_dbase(lp))
            &&& self.dhi == clampd(self.d1 - li::idx_dbase(lp))
        }
    }

    pub open spec fn wf_su(&self) -> bool {
        let sp = self.sp();
        &&& sp_ok(sp)
        &&& self.ns == tn(sp, 13)
        &&& self.sbs as int == bmin(tbs(sp, 13))
        &&& sh_ok(self.sbs, self.ssh)
        &&& self.suk@ == cf::u32s(sp[15])
        &&& self.sukb@ == cf::i64s(sp[16])
        &&& self.snk@ == cf::u8s(sp[21])
        &&& self.snkb@ == cf::i64s(sp[22])
        &&& (self.dense ==> forall|x: int| 0 <= x < self.ns ==> #[trigger] suk(sp, x) == self.sbase + x)
        &&& self.natn == self.natk@.len()
        &&& forall|i: int| 0 <= i < self.natn ==> #[trigger] sl_nat_ok(sp, self.nname(), self.natk@[i] as int)
        &&& forall|y: int| 0 <= y < tn(sp, 30) && nan(sp, y) == self.nname()
            ==> exists|i: int| 0 <= i < self.natn && #[trigger] self.natk@[i] == nak(sp, y)
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.wf_part()
        &&& self.wf_ps()
        &&& self.wf_li()
        &&& self.wf_su()
    }

    /// The same context.
    pub open spec fn same(&self, o: &Ctx) -> bool {
        &&& self.sv@ == o.sv@ && self.ps@ == o.ps@ && self.d1g@ == o.d1g@
        &&& self.np == o.np && self.pbs == o.pbs && self.psh == o.psh && self.pssh == o.pssh && self.lsh == o.lsh && self.ssh == o.ssh && self.gmul == o.gmul && self.pk == o.pk && self.pkb == o.pkb
        &&& self.nps == o.nps && self.psbs == o.psbs && self.sorted == o.sorted
        &&& self.gk0 == o.gk0 && self.gnum == o.gnum && self.gden == o.gden
        &&& self.spk == o.spk && self.spkb == o.spkb && self.ssk == o.ssk && self.sskb == o.sskb
        &&& self.sav == o.sav && self.savb == o.savb
        &&& self.nl == o.nl && self.lbs == o.lbs && self.idx == o.idx && self.kmin == o.kmin && self.nkeys == o.nkeys
        &&& self.offs == o.offs && self.irows == o.irows && self.idates == o.idates && self.dlo == o.dlo && self.dhi == o.dhi
        &&& self.lkey == o.lkey && self.lkeyb == o.lkeyb && self.lsk == o.lsk && self.lskb == o.lskb
        &&& self.lq == o.lq && self.lqb == o.lqb && self.ldt == o.ldt && self.ldtb == o.ldtb
        &&& self.d0 == o.d0 && self.d1 == o.d1
        &&& self.ns == o.ns && self.sbs == o.sbs && self.sbase == o.sbase && self.dense == o.dense
        &&& self.runok == o.runok && self.ratio == o.ratio && self.first == o.first
        &&& self.suk == o.suk && self.sukb == o.sukb && self.snk == o.snk && self.snkb == o.snkb
        &&& self.natk@ == o.natk@ && self.natn == o.natn
    }

    /// A context equal to a well-formed one is well formed.
    pub proof fn lemma_same_wf(&self, o: &Ctx)
        requires o.wf(), self.same(o),
        ensures self.wf(),
    {
        assert(self.pk@ == o.pk@ && self.pkb@ == o.pkb@);
        assert(self.spk@ == o.spk@ && self.spkb@ == o.spkb@ && self.ssk@ == o.ssk@ && self.sskb@ == o.sskb@);
        assert(self.sav@ == o.sav@ && self.savb@ == o.savb@);
        assert(self.offs@ == o.offs@ && self.irows@ == o.irows@ && self.idates@ == o.idates@);
        assert(self.lkey@ == o.lkey@ && self.lkeyb@ == o.lkeyb@ && self.lsk@ == o.lsk@ && self.lskb@ == o.lskb@);
        assert(self.lq@ == o.lq@ && self.lqb@ == o.lqb@ && self.ldt@ == o.ldt@ && self.ldtb@ == o.ldtb@);
        assert(self.suk@ == o.suk@ && self.sukb@ == o.sukb@ && self.snk@ == o.snk@ && self.snkb@ == o.snkb@);
        assert(self.wf_part());
        assert(self.wf_ps());
        assert(self.wf_li());
        assert forall|i: int| 0 <= i < self.natn implies #[trigger] sl_nat_ok(self.sp(), self.nname(), self.natk@[i] as int) by {
            assert(self.natk@[i] == o.natk@[i]);
            assert(sl_nat_ok(o.sp(), o.nname(), o.natk@[i] as int));
        }
        assert forall|y: int| 0 <= y < tn(self.sp(), 30) && nan(self.sp(), y) == self.nname()
            implies exists|i: int| 0 <= i < self.natn && #[trigger] self.natk@[i] == nak(self.sp(), y) by {
            let i = choose|i: int| 0 <= i < o.natn && #[trigger] o.natk@[i] == nak(o.sp(), y);
            assert(self.natk@[i] == o.natk@[i]);
        }
        assert(self.wf_su());
    }

    /// A copy (the nation keys are copied).
    pub fn copy(&self) -> (r: Ctx)
        ensures r.same(self),
    {
        let mut natk: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < self.natk.len()
            invariant i <= self.natk@.len(), natk@ == self.natk@.subrange(0, i as int),
            decreases self.natk@.len() - i,
        {
            natk.push(self.natk[i]);
            proof { assert(natk@ =~= self.natk@.subrange(0, i + 1)); }
            i = i + 1;
        }
        proof { assert(natk@ =~= self.natk@); }
        Ctx {
            sv: Ghost(self.sv@), ps: Ghost(self.ps@), d1g: Ghost(self.d1g@),
            np: self.np, pbs: self.pbs, psh: self.psh, pssh: self.pssh, lsh: self.lsh, ssh: self.ssh, gmul: self.gmul, pk: self.pk, pkb: self.pkb,
            nps: self.nps, psbs: self.psbs, sorted: self.sorted, gk0: self.gk0, gnum: self.gnum, gden: self.gden,
            spk: self.spk, spkb: self.spkb, ssk: self.ssk, sskb: self.sskb, sav: self.sav, savb: self.savb,
            nl: self.nl, lbs: self.lbs, idx: self.idx, kmin: self.kmin, nkeys: self.nkeys,
            offs: self.offs, irows: self.irows, idates: self.idates, dlo: self.dlo, dhi: self.dhi,
            lkey: self.lkey, lkeyb: self.lkeyb, lsk: self.lsk, lskb: self.lskb, lq: self.lq, lqb: self.lqb,
            ldt: self.ldt, ldtb: self.ldtb, d0: self.d0, d1: self.d1,
            ns: self.ns, sbs: self.sbs, sbase: self.sbase, dense: self.dense, runok: self.runok, ratio: self.ratio, first: self.first, suk: self.suk, sukb: self.sukb, snk: self.snk, snkb: self.snkb,
            natk, natn: self.natn,
        }
    }

    /// The guessed first partsupp row of key `k` (at most `nps`).
    pub fn guess(&self, k: i64) -> (q: usize)
        ensures q <= self.nps,
        no_unwind
    {
        let d = k as i128 - self.gk0 as i128;
        if self.gden == 0 || self.gden > 0x8000_0000 || self.gnum > 0x8000_0000 || d < 0 {
            0
        } else if d >= self.gden as i128 {
            self.nps
        } else {
            let du = d as u64;
            assert(du * self.gnum <= 0x8000_0000 * 0x8000_0000) by (nonlinear_arith)
                requires du < 0x8000_0000, self.gnum <= 0x8000_0000;
            let q = if self.gmul > 0 && self.gmul <= self.gnum {
                assert(du * self.gmul <= du * self.gnum) by (nonlinear_arith)
                    requires self.gmul <= self.gnum;
                du * self.gmul
            } else {
                (du * self.gnum) / self.gden
            };
            if q < self.nps as u64 { q as usize } else { self.nps }
        }
    }

    /// p_partkey of part row `r`.
    pub fn get_pk(&self, r: usize) -> (v: i64)
        requires self.wf_part(), r < self.np,
        ensures v == pi::pkey_at(self.pp(), r as int),
        no_unwind
    {
        proof {
            lemma_bmin(r as int, pi::bsize(self.pp()), self.pkb@.len() as int, self.np as int);
            lemma_div_lt(r as int, self.pbs as int, self.pkb@.len() as int);
            assert(i64r(pi::pkey_at(self.pp(), r as int)));
        }
        fget_u32(self.pk, self.pkb, self.pbs, self.psh, r)
    }

    /// ps_partkey of partsupp row `j`.
    pub fn get_psk(&self, j: usize) -> (v: i64)
        requires self.wf_ps(), j < self.nps,
        ensures v == psk(self.sp(), j as int),
        no_unwind
    {
        proof {
            lemma_bmin(j as int, tbs(self.sp(), 0), self.spkb@.len() as int, self.nps as int);
            lemma_div_lt(j as int, self.psbs as int, self.spkb@.len() as int);
            assert(i64r(psk(self.sp(), j as int)));
        }
        fget_u32(self.spk, self.spkb, self.psbs, self.pssh, j)
    }

    /// ps_suppkey of partsupp row `j`.
    pub fn get_pss(&self, j: usize) -> (v: i64)
        requires self.wf_ps(), j < self.nps,
        ensures v == pss(self.sp(), j as int),
        no_unwind
    {
        proof {
            lemma_bmin(j as int, tbs(self.sp(), 0), self.sskb@.len() as int, self.nps as int);
            lemma_div_lt(j as int, self.psbs as int, self.sskb@.len() as int);
            assert(i64r(psk(self.sp(), j as int)));
        }
        fget_u32(self.ssk, self.sskb, self.psbs, self.pssh, j)
    }

    /// ps_availqty of partsupp row `j`.
    pub fn get_psa(&self, j: usize) -> (v: i64)
        requires self.wf_ps(), j < self.nps,
        ensures v == psa(self.sp(), j as int),
        no_unwind
    {
        proof {
            lemma_bmin(j as int, tbs(self.sp(), 0), self.savb@.len() as int, self.nps as int);
            lemma_div_lt(j as int, self.psbs as int, self.savb@.len() as int);
            assert(i64r(psk(self.sp(), j as int)));
        }
        fget_u16(self.sav, self.savb, self.psbs, self.pssh, j)
    }

    /// s_suppkey of supplier row `x`.
    pub fn get_suk(&self, x: usize) -> (v: i64)
        requires self.wf_su(), x < self.ns,
        ensures v == suk(self.sp(), x as int),
        no_unwind
    {
        proof {
            lemma_bmin(x as int, tbs(self.sp(), 13), self.sukb@.len() as int, self.ns as int);
            lemma_div_lt(x as int, self.sbs as int, self.sukb@.len() as int);
            assert(i64r(suk(self.sp(), x as int)));
        }
        fget_u32(self.suk, self.sukb, self.sbs, self.ssh, x)
    }

    /// s_nationkey of supplier row `x`.
    pub fn get_sunk(&self, x: usize) -> (v: i64)
        requires self.wf_su(), x < self.ns,
        ensures v == sunk(self.sp(), x as int),
        no_unwind
    {
        proof {
            lemma_bmin(x as int, tbs(self.sp(), 13), self.snkb@.len() as int, self.ns as int);
            lemma_div_lt(x as int, self.sbs as int, self.snkb@.len() as int);
            assert(i64r(suk(self.sp(), x as int)));
        }
        fget_u8(self.snk, self.snkb, self.sbs, self.ssh, x)
    }

    /// l_partkey of stored lineitem row `s`.
    pub fn get_lkey(&self, s: usize) -> (v: i64)
        requires self.wf_li(), s < self.nl,
        ensures v == li::key_at(self.lp(), s as int),
        no_unwind
    {
        proof {
            lemma_bmin(s as int, li::bsize(self.lp()), self.lkeyb@.len() as int, self.nl as int);
            lemma_div_lt(s as int, self.lbs as int, self.lkeyb@.len() as int);
            assert(lrow_vals_ok(self.lp(), s as int));
        }
        fget_u32(self.lkey, self.lkeyb, self.lbs, self.lsh, s)
    }

    /// l_suppkey of stored lineitem row `s`.
    pub fn get_lsk(&self, s: usize) -> (v: i64)
        requires self.wf_li(), s < self.nl,
        ensures v == li::supp_at(self.lp(), s as int),
        no_unwind
    {
        proof {
            lemma_bmin(s as int, li::bsize(self.lp()), self.lskb@.len() as int, self.nl as int);
            lemma_div_lt(s as int, self.lbs as int, self.lskb@.len() as int);
            assert(lrow_vals_ok(self.lp(), s as int));
        }
        fget_u32(self.lsk, self.lskb, self.lbs, self.lsh, s)
    }

    /// l_quantity coefficient of stored lineitem row `s`.
    pub fn get_lq(&self, s: usize) -> (v: i64)
        requires self.wf_li(), s < self.nl,
        ensures v == li::qty_at(self.lp(), s as int), -p15() < v < p15(),
        no_unwind
    {
        proof {
            lemma_bmin(s as int, li::bsize(self.lp()), self.lqb@.len() as int, self.nl as int);
            lemma_div_lt(s as int, self.lbs as int, self.lqb@.len() as int);
            assert(lrow_vals_ok(self.lp(), s as int));
        }
        fget_u16(self.lq, self.lqb, self.lbs, self.lsh, s)
    }

    /// l_shipdate of stored lineitem row `s`.
    pub fn get_ldt(&self, s: usize) -> (v: i64)
        requires self.wf_li(), s < self.nl,
        ensures v == li::date_at(self.lp(), s as int),
        no_unwind
    {
        proof {
            lemma_bmin(s as int, li::bsize(self.lp()), self.ldtb@.len() as int, self.nl as int);
            lemma_div_lt(s as int, self.lbs as int, self.ldtb@.len() as int);
            assert(lrow_vals_ok(self.lp(), s as int));
        }
        fget_u16(self.ldt, self.ldtb, self.lbs, self.lsh, s)
    }

    /// The supplier row of supplier key `s`, if any (keys are distinct).
    pub fn find_su(&self, s: i64) -> (r: Option<usize>)
        requires self.wf_su(),
        ensures
            r matches Some(x) ==> x < self.ns && suk(self.sp(), x as int) == s,
            r is None ==> forall|x: int| 0 <= x < self.ns ==> #[trigger] suk(self.sp(), x) != s,
        no_unwind
    {
        let sp = Ghost(self.sp());
        if self.dense {
            let d = s as i128 - self.sbase as i128;
            if d >= 0 && d < self.ns as i128 {
                return Some(d as usize);
            }
            return None;
        }
        // keys that may be dense: the row at the guessed position
        if s >= self.sbase && (s as i128 - self.sbase as i128) < self.ns as i128 {
            let g = (s as i128 - self.sbase as i128) as usize;
            if self.get_suk(g) == s {
                return Some(g);
            }
        }
        proof {
            assert forall|j: int| 0 <= j < self.ns implies #[trigger] key_u32_at(self.suk@, self.sukb@, self.sbs as int, j) == suk(sp@, j) by {
                lemma_bmin(j, tbs(sp@, 13), self.sukb@.len() as int, self.ns as int);
                lemma_div_lt(j, self.sbs as int, self.sukb@.len() as int);
            }
            if self.ns > 0 {
                lemma_bmin(0, tbs(sp@, 13), self.sukb@.len() as int, self.ns as int);
            }
            assert forall|j: int| 0 <= j < self.ns implies i64::MIN <= #[trigger] key_u32_at(self.suk@, self.sukb@, self.sbs as int, j) <= i64::MAX by {
                assert(key_u32_at(self.suk@, self.sukb@, self.sbs as int, j) == suk(sp@, j));
                assert(i64r(suk(sp@, j)));
            }
        }
        let g: usize = if s >= self.sbase && (s as i128 - self.sbase as i128) < self.ns as i128 { (s as i128 - self.sbase as i128) as usize } else { self.ns };
        let r = find_key_u32(self.suk, self.sukb, self.sbs, self.ns, s, g);
        proof {
            if let Some(x) = r {
                assert(key_u32_at(self.suk@, self.sukb@, self.sbs as int, x as int) == suk(sp@, x as int));
            } else {
                assert forall|x: int| 0 <= x < self.ns implies #[trigger] suk(sp@, x) != s by {
                    assert(key_u32_at(self.suk@, self.sukb@, self.sbs as int, x) == suk(sp@, x));
                }
            }
        }
        r
    }

    /// Some nation row of key `kn` is named `$3`.
    pub fn nat_has(&self, kn: i64) -> (b: bool)
        requires self.wf_su(),
        ensures b == sl_nat_ok(self.sp(), self.nname(), kn as int),
        no_unwind
    {
        let mut i: usize = 0;
        while i < self.natn
            invariant
                self.wf_su(),
                i <= self.natn,
                forall|t: int| 0 <= t < i ==> #[trigger] self.natk@[t] != kn,
            decreases self.natn - i,
        {
            if self.natk[i] == kn {
                proof {
                    assert(sl_nat_ok(self.sp(), self.nname(), self.natk@[i as int] as int));
                }
                return true;
            }
            i = i + 1;
        }
        proof {
            if sl_nat_ok(self.sp(), self.nname(), kn as int) {
                let sp = self.sp();
                let y = choose|y: int| 0 <= y < tn(sp, 30) && #[trigger] nak(sp, y) == kn && nan(sp, y) == self.nname();
                let t = choose|t: int| 0 <= t < self.natn && #[trigger] self.natk@[t] == nak(sp, y);
                assert(self.natk@[t] == kn);
            }
        }
        false
    }
}

/// Row `j` lies in band `d` of width `r` exactly when `j / r == d`.
pub proof fn lemma_div_band(j: int, r: int, d: int)
    requires r >= 1, j >= 0, d >= 0,
    ensures (j / r == d) == (d * r <= j < d * r + r),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, r);
    assert(r * (j / r) == (j / r) * r) by (nonlinear_arith);
    if d * r <= j < d * r + r {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j, r, d, j - d * r);
    } else if j / r == d {
        assert((j / r) * r == d * r);
    }
}

/// The partsupp rows of key `k` under the run layout: exactly `[lo, hi)`.
pub open spec fn run_rows(ctx: &Ctx, k: int, lo: int, hi: int) -> bool {
    &&& 0 <= lo <= hi <= ctx.nps
    &&& forall|j: int| 0 <= j < ctx.nps ==> (#[trigger] psk(ctx.sp(), j) == k) == (lo <= j < hi)
}

/// The partsupp rows of key `k` by arithmetic (run layout; no key read).
pub fn run_range(ctx: &Ctx, k: i64) -> (r: (usize, usize))
    requires ctx.wf_ps(), ctx.runok, ctx.ratio <= 0x1_0000,
    ensures run_rows(ctx, k as int, r.0 as int, r.1 as int),
    no_unwind
{
    let ghost sp = ctx.sp();
    let n = ctx.nps;
    let ratio = ctx.ratio;
    let d = k as i128 - ctx.first as i128;
    if d < 0 {
        proof {
            assert forall|j: int| 0 <= j < ctx.nps implies (#[trigger] psk(sp, j) == k) == (0 <= j < 0) by {
                vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, ratio as int);
            }
        }
        return (0, 0);
    }
    assert(d * (ratio as i128) <= 0x1_0000_0000_0000_0000 * 0x1_0000) by (nonlinear_arith)
        requires 0 <= d <= 0x1_0000_0000_0000_0000, ratio <= 0x1_0000;
    let lo = d * (ratio as i128);
    if lo >= n as i128 {
        proof {
            assert forall|j: int| 0 <= j < ctx.nps implies (#[trigger] psk(sp, j) == k) == (n <= j < n) by {
                lemma_div_band(j, ratio as int, d as int);
            }
        }
        return (n, n);
    }
    let lo = lo as usize;
    let hi = if n - lo > ratio { lo + ratio } else { n };
    proof {
        assert forall|j: int| 0 <= j < ctx.nps implies (#[trigger] psk(sp, j) == k) == (lo <= j < hi) by {
            lemma_div_band(j, ratio as int, d as int);
        }
    }
    (lo, hi)
}

/// Sorted, distinct supplier keys from `sbase` to `sbase + n - 1` are dense.
pub proof fn lemma_dense(sp: Seq<PartView>, base: int)
    requires
        su_ok(sp), su_kind(sp) == 1, tn(sp, 13) > 0,
        suk(sp, 0) == base, suk(sp, tn(sp, 13) - 1) == base + tn(sp, 13) - 1,
    ensures forall|x: int| 0 <= x < tn(sp, 13) ==> #[trigger] suk(sp, x) == base + x,
{
    let n = tn(sp, 13);
    assert forall|x: int| 0 <= x < n implies #[trigger] suk(sp, x) == base + x by {
        lemma_dense_up(sp, base, x);
        lemma_dense_down(sp, base, x);
    }
}

proof fn lemma_dense_up(sp: Seq<PartView>, base: int, x: int)
    requires su_ok(sp), su_kind(sp) == 1, 0 <= x < tn(sp, 13), suk(sp, 0) == base,
    ensures suk(sp, x) >= base + x,
    decreases x,
{
    if x > 0 {
        lemma_dense_up(sp, base, x - 1);
        assert(su_le(sp, x - 1));
        assert(suk(sp, x - 1) != suk(sp, x));
    }
}

proof fn lemma_dense_down(sp: Seq<PartView>, base: int, x: int)
    requires su_ok(sp), su_kind(sp) == 1, 0 <= x < tn(sp, 13), suk(sp, tn(sp, 13) - 1) == base + tn(sp, 13) - 1,
    ensures suk(sp, x) <= base + x,
    decreases tn(sp, 13) - x,
{
    if x < tn(sp, 13) - 1 {
        lemma_dense_down(sp, base, x + 1);
        assert(su_le(sp, x));
        assert(suk(sp, x) != suk(sp, x + 1));
    }
}

} // verus!
