//! Scan of `pre` rows `lo..hi` for the entries (`keys::elist`): `stmt = $2` (not NULL) and an adsh with a member.
//! For each entry, in row order, the task writes its row, member, join-key hash, group-key hash and partition into
//! preallocated buffers (at least `hi - lo` slots each, so they never fill up).
use vstd::prelude::*;
use std::sync::Arc;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::gendb_entry::parallel::WorkerTask;
use crate::agent::common::bytes::*;
use crate::agent::common::chain::NONE;
use crate::agent::ctx::*;
use crate::agent::keys::*;
use crate::agent::subidx::*;
use crate::agent::sem::sub_key;

verus! {

pub struct PreTask {
    pub lo: usize,
    pub hi: usize,
    pub stmt: TextCol,
    pub stmtv: &'static [u8],
    pub adsh: TextCol,
    pub tag: TextCol,
    pub ver: TextCol,
    pub plabel: TextCol,
    pub plabelv: &'static [u8],
    pub name: TextCol,
    pub p1: &'static [u8],
    pub p1len: usize,
    pub pbits: u64,
    pub sub: Arc<SubIdx>,
    pub ek: Vec<usize>,
    pub es: Vec<usize>,
    pub ekh: Vec<u64>,
    pub egh: Vec<u64>,
    pub ep: Vec<u8>,
    pub ctx: Ghost<Ctx>,
}

pub struct PreOut {
    pub ek: Vec<usize>,
    pub es: Vec<usize>,
    pub ekh: Vec<u64>,
    pub egh: Vec<u64>,
    pub ep: Vec<u8>,
    pub len: usize,
}

/// The columns and parameters a `pre` scan reads, for the call context `c`.
pub open spec fn pre_cols_ok(t: PreTask, c: Ctx) -> bool {
    &&& ctx_ok(c)
    &&& sub_key(c)
    &&& t.stmt@ == p_stmt_v(c)
    &&& t.stmtv@ == p_stmtv_s(c)
    &&& t.adsh@ == p_adsh_v(c)
    &&& t.tag@ == p_tag_v(c)
    &&& t.ver@ == p_ver_v(c)
    &&& t.plabel@ == p_plabel_v(c)
    &&& t.plabelv@ == p_plabelv_s(c)
    &&& t.name@ == s_name_v(c)
    &&& t.p1@ == c.stmt
    &&& t.p1len as int == c.stmt.len()
    &&& t.pbits <= MAX_PBITS
    &&& sub_idx_wf(*t.sub, c)
}

/// The output lists the entries of `lo..hi` with their member, hashes and partition.
pub open spec fn pre_out_ok(o: PreOut, c: Ctx, pbits: u64, lo: int, hi: int) -> bool {
    let el = elist(c, lo, hi);
    &&& o.len as int == el.len()
    &&& o.len <= o.ek@.len() && o.len <= o.es@.len() && o.len <= o.ekh@.len() && o.len <= o.egh@.len() && o.len <= o.ep@.len()
    &&& forall|j: int| 0 <= j < o.len ==> #[trigger] o.ek@[j] as int == el[j]
    &&& forall|j: int| 0 <= j < o.len ==> #[trigger] o.es@[j] as int == esub(c, el[j])
    &&& forall|j: int| 0 <= j < o.len ==> #[trigger] o.ekh@[j] == ekh(c, el[j])
    &&& forall|j: int| 0 <= j < o.len ==> #[trigger] o.egh@[j] == egh(c, el[j])
    &&& forall|j: int| 0 <= j < o.len ==> #[trigger] o.ep@[j] as int == epart(c, pbits, el[j])
}

impl WorkerTask for PreTask {
    type Output = PreOut;

    open spec fn pre(&self) -> bool {
        &&& pre_cols_ok(*self, self.ctx@)
        &&& self.lo <= self.hi
        &&& self.hi as int <= self.ctx@.q
        &&& self.ek@.len() >= self.hi - self.lo
        &&& self.es@.len() >= self.hi - self.lo
        &&& self.ekh@.len() >= self.hi - self.lo
        &&& self.egh@.len() >= self.hi - self.lo
        &&& self.ep@.len() >= self.hi - self.lo
    }

    open spec fn post(&self, out: PreOut) -> bool {
        pre_out_ok(out, self.ctx@, self.pbits, self.lo as int, self.hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: PreOut) {
        let ghost c = self.ctx@;
        let ghost t0 = self;
        let PreTask { lo, hi, stmt, stmtv, adsh, tag, ver, plabel, plabelv, name, p1, p1len, pbits, sub, mut ek, mut es,
            mut ekh, mut egh, mut ep, ctx } = self;
        let sub: &SubIdx = &*sub;
        proof {
            lemma_views_wf(c);
        }
        let mut len: usize = 0;
        let mut k: usize = lo;
        while k < hi
            invariant
                pre_cols_ok(t0, c), lo <= k <= hi, hi as int <= c.q,
                stmt@ == p_stmt_v(c), stmtv@ == p_stmtv_s(c), adsh@ == p_adsh_v(c), tag@ == p_tag_v(c), ver@ == p_ver_v(c),
                plabel@ == p_plabel_v(c), plabelv@ == p_plabelv_s(c), name@ == s_name_v(c),
                p1@ == c.stmt, p1len as int == c.stmt.len(), pbits <= MAX_PBITS, sub_idx_wf(*sub, c), sub_key(c),
                text_wf(p_stmt_v(c), c.q), p_stmtv_s(c).len() == c.q, text_wf(p_adsh_v(c), c.q), text_wf(p_tag_v(c), c.q),
                text_wf(p_ver_v(c), c.q), text_wf(p_plabel_v(c), c.q), p_plabelv_s(c).len() == c.q, text_wf(s_name_v(c), c.m),
                ek@.len() >= hi - lo, es@.len() >= hi - lo, ekh@.len() >= hi - lo, egh@.len() >= hi - lo, ep@.len() >= hi - lo,
                pre_out_ok(PreOut { ek, es, ekh, egh, ep, len }, c, pbits, lo as int, k as int),
            decreases hi - k,
        {
            proof {
                lemma_elist_step(c, lo as int, k as int);
                lemma_elist_len(c, lo as int, k as int);
            }
            let mut hit = false;
            if stmtv[k] != 0 {
                if text_is(&stmt, k, Ghost(c.q), p1, p1len) {
                    let a = text_of(&adsh, k, Ghost(c.q));
                    let al = text_len(&adsh, k, Ghost(c.q));
                    let s = sub_find(sub, a, al, Ghost(c));
                    if s != NONE {
                        proof {
                            lemma_sub_for(c, p_adsh(c, k as int));
                            assert(s as int == esub(c, k as int));
                            assert(pre_ok(c, k as int));
                        }
                        let tb = text_of(&tag, k, Ghost(c.q));
                        let tl = text_len(&tag, k, Ghost(c.q));
                        let vb = text_of(&ver, k, Ghost(c.q));
                        let vl = text_len(&ver, k, Ghost(c.q));
                        let th = sig(tb, tl);
                        let vh = sig(vb, vl);
                        let nb = text_of(&name, s, Ghost(c.m));
                        let nl = text_len(&name, s, Ghost(c.m));
                        let nh = sig(nb, nl);
                        let lh = if plabelv[k] != 0 {
                            let lb = text_of(&plabel, k, Ghost(c.q));
                            let ll = text_len(&plabel, k, Ghost(c.q));
                            sig(lb, ll)
                        } else {
                            LH_NULL
                        };
                        let p = part_of(th, pbits, Ghost(p_tag(c, k as int)));
                        let khv = kha(th, sig(a, al), vh);
                        let ghv = mix(mix(th, nh), lh);
                        ek[len] = k;
                        es[len] = s;
                        ekh[len] = khv;
                        egh[len] = ghv;
                        ep[len] = p as u8;
                        len = len + 1;
                        hit = true;
                    }
                }
            }
            proof {
                if !hit {
                    assert(!pre_ok(c, k as int));
                }
            }
            k = k + 1;
        }
        PreOut { ek, es, ekh, egh, ep, len }
    }
}

} // verus!
