//! Nation tags (`lines::name_tag`) and the 2-bit nation tags of the supplier and customer rows.
//!
//! `nation_tags` compares every nation name with `$1` and `$2` (25 rows); `nat_tag_of` finds the tag of a nation
//! key (at the position `key - n_nationkey[0]` when that matches, else by a linear search). A `TagTask` builds words
//! of the nation tags of a keyed table's rows (2 bits per row, 32 rows per word, `tags_ok`; used for the suppliers
//! and the customers) and checks that the table's keys are positional (`key[r] == base + r`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::link::query::{text_at, text_wf, TextView};
use crate::agent::tables::*;
use crate::agent::normal_form::*;
use crate::agent::lines::*;
use crate::agent::common::bits::*;

verus! {

/// The nation columns a tag lookup reads.
#[derive(Clone, Copy)]
pub struct NationCols {
    pub nkey: &'static [i64],
    pub offs: &'static [i64],
    pub bytes: &'static [u8],
    pub nn: usize,
}

pub open spec fn nation_cols_ok(c: NationCols, sv: StoresView) -> bool {
    &&& c.nkey@ == nk(sv)
    &&& c.offs@ == nname_col(sv).offsets
    &&& c.bytes@ == nname_col(sv).bytes
    &&& text_wf(nname_col(sv), n_n(sv))
    &&& c.nn as int == n_n(sv)
    &&& keys_unique(nk(sv))
}

/// Every nation's tag.
pub open spec fn ntags_ok(ntag: Seq<u8>, sv: StoresView, ps: Seq<Literal>) -> bool {
    &&& ntag.len() == n_n(sv)
    &&& forall|a: int| 0 <= a < n_n(sv) ==> #[trigger] ntag[a] as int == name_tag(sv, ps, a)
}

/// Nation row `a`'s name is `p`.
fn name_eq(c: &NationCols, a: usize, p: &[u8], Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires nation_cols_ok(*c, sv), a < c.nn,
    ensures r == (nname(sv, a as int) == p@),
{
    let ghost t = nname_col(sv);
    assert(0 <= t.offsets[a as int] <= t.offsets[a + 1] <= t.bytes.len());
    let x0 = c.offs[a];
    let y0 = c.offs[a + 1];
    assert(x0 == t.offsets[a as int] && y0 == t.offsets[a + 1]);
    assert(c.bytes@.len() == t.bytes.len());
    let nb = c.bytes.len();
    assert(y0 <= nb);
    let x = x0 as usize;
    let y = y0 as usize;
    assert(x as int == x0 as int && y as int == y0 as int && x <= y);
    let n = p.len();
    if y - x != n {
        assert(nname(sv, a as int).len() != p@.len());
        return false;
    }
    let mut k: usize = 0;
    while k < n
        invariant
            nation_cols_ok(*c, sv), a < c.nn, t == nname_col(sv),
            k <= n, n == p@.len(), x + n == y, y <= c.bytes@.len(), c.bytes@ == t.bytes,
            x == t.offsets[a as int], y == t.offsets[a + 1],
            nname(sv, a as int) == t.bytes.subrange(x as int, y as int),
            forall|q: int| 0 <= q < k ==> c.bytes@[x + q] == p@[q],
        decreases n - k,
    {
        if c.bytes[x + k] != p[k] {
            assert(nname(sv, a as int)[k as int] == t.bytes[x + k]);
            return false;
        }
        k = k + 1;
    }
    assert(nname(sv, a as int) =~= p@);
    true
}

/// Every nation's tag: 1 if its name is `$1`, plus 2 if it is `$2`.
pub fn nation_tags(c: &NationCols, p1: &[u8], p2: &[u8], Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (ntag: Vec<u8>)
    requires nation_cols_ok(*c, sv), p1@ == p1_of(ps), p2@ == p2_of(ps),
    ensures ntags_ok(ntag@, sv, ps),
{
    let mut ntag: Vec<u8> = Vec::new();
    let mut a: usize = 0;
    while a < c.nn
        invariant
            nation_cols_ok(*c, sv), p1@ == p1_of(ps), p2@ == p2_of(ps), a <= c.nn, ntag@.len() == a,
            forall|q: int| 0 <= q < a ==> #[trigger] ntag@[q] as int == name_tag(sv, ps, q),
        decreases c.nn - a,
    {
        let e1 = name_eq(c, a, p1, Ghost(sv));
        let e2 = name_eq(c, a, p2, Ghost(sv));
        let t: u8 = (if e1 { 1u8 } else { 0u8 }) + (if e2 { 2u8 } else { 0u8 });
        ntag.push(t);
        a = a + 1;
    }
    ntag
}

/// The tag of the nation with key `key` (0 when there is none).
pub fn nat_tag_of(c: &NationCols, ntag: &Vec<u8>, key: i64, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (t: u8)
    requires nation_cols_ok(*c, sv), ntags_ok(ntag@, sv, ps),
    ensures t as int == nat_tag(sv, ps, key), t <= 3,
    no_unwind
{
    proof { lemma_key_row(nk(sv), key); }
    if c.nn > 0 {
        let g = key as i128 - c.nkey[0] as i128;
        if g >= 0 && g < c.nn as i128 {
            let gu = g as usize;
            if c.nkey[gu] == key {
                proof { assert(has_key(nk(sv), key)); }
                return ntag[gu];
            }
        }
    }
    let mut a: usize = 0;
    while a < c.nn
        invariant nation_cols_ok(*c, sv), ntags_ok(ntag@, sv, ps), a <= c.nn,
            forall|q: int| 0 <= q < a ==> nk(sv)[q] != key,
        decreases c.nn - a,
    {
        if c.nkey[a] == key {
            proof { assert(has_key(nk(sv), key)); }
            return ntag[a];
        }
        a = a + 1;
    }
    0
}

// ------------------------------------------------------------------------------------------------ row tags

/// The nation tags of the rows of a table whose nation-key column is `nats`, 2 bits each: row `r` is field `r % 32`
/// of word `r / 32`.
pub open spec fn tags_ok(words: Seq<u64>, nats: Seq<i64>, sv: StoresView, ps: Seq<Literal>, n: int) -> bool {
    &&& words.len() == n / 32 + 1
    &&& forall|r: int| 0 <= r < n ==> #[trigger] field2(words[r / 32], (r % 32) as u64) as int == nat_tag(sv, ps, nats[r])
}

/// Words `wl..wh` of the row tags (`out[w - wl]` is word `w`), and positional keys in their rows when `pos`.
pub open spec fn tags_range_ok(out: Seq<u64>, pos: bool, keys: Seq<i64>, nats: Seq<i64>, sv: StoresView, ps: Seq<Literal>,
    base: int, wl: int, wh: int) -> bool {
    &&& out.len() == wh - wl
    &&& forall|r: int| 32 * wl <= r < 32 * wh && r < nats.len() ==> #[trigger] field2(out[r / 32 - wl], (r % 32) as u64) as int == nat_tag(sv, ps, nats[r])
    &&& pos ==> forall|r: int| 32 * wl <= r < 32 * wh && r < nats.len() ==> #[trigger] keys[r] as int == base + r
}

/// The key and nation-key columns of a keyed table (suppliers or customers) and its first key.
#[derive(Clone, Copy)]
pub struct KeyCols {
    pub keys: &'static [i64],
    pub nats: &'static [i64],
    pub n: usize,
    pub base: i64,
}

pub open spec fn key_cols_ok(c: KeyCols) -> bool {
    &&& c.keys@.len() == c.n && c.nats@.len() == c.n
}

/// Word `w` of the row tags: rows `32 w .. min(32 w + 32, n)`; whether their keys are positional.
fn tag_word(c: &KeyCols, nation: &NationCols, ntag: &Vec<u8>, w: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (u64, bool))
    requires key_cols_ok(*c), nation_cols_ok(*nation, sv), ntags_ok(ntag@, sv, ps), 32 * w + 32 <= usize::MAX,
    ensures
        forall|u: u64| u < 32 && 32 * w + u < c.n ==> #[trigger] field2(r.0, u) as int == nat_tag(sv, ps, c.nats@[32 * w + u]),
        r.1 ==> forall|u: u64| u < 32 && 32 * w + u < c.n ==> #[trigger] c.keys@[32 * w + u] as int == c.base + 32 * w + u,
    no_unwind
{
    let lo = 32 * w;
    let mut m: u64 = 0;
    let mut pos = true;
    let mut k: usize = 0;
    proof {
        assert forall|u: u64| u < 32 implies #[trigger] field2(0u64, u) == 0 by { lemma_field2_zero(u); }
    }
    while k < 32
        invariant
            key_cols_ok(*c), nation_cols_ok(*nation, sv), ntags_ok(ntag@, sv, ps), lo == 32 * w, k <= 32,
            32 * w + 32 <= usize::MAX,
            forall|u: u64| u < k && lo + u < c.n ==> #[trigger] field2(m, u) as int == nat_tag(sv, ps, c.nats@[lo + u]),
            forall|u: u64| k <= u < 32 ==> #[trigger] field2(m, u) == 0,
            pos ==> forall|u: u64| u < k && lo + u < c.n ==> #[trigger] c.keys@[lo + u] as int == c.base + lo + u,
        decreases 32 - k,
    {
        let r = lo + k;
        let mut t: u64 = 0;
        if r < c.n {
            t = nat_tag_of(nation, ntag, c.nats[r], Ghost(sv), Ghost(ps)) as u64;
            if (c.keys[r] as i128) != (c.base as i128) + (r as i128) {
                pos = false;
            }
        }
        let ghost m0 = m;
        m = m | (t << (2 * (k as u64)));
        proof {
            assert forall|u: u64| u < 32 implies #[trigger] field2(m, u) == if u == k as u64 { t } else { field2(m0, u) } by {
                lemma_field2_set(m0, t, k as u64, u);
            }
        }
        k = k + 1;
    }
    (m, pos)
}

/// One task: words `wl..wh` of the row tags of a keyed table.
pub struct TagTask {
    pub cols: KeyCols,
    pub nation: NationCols,
    pub ntag: Arc<Vec<u8>>,
    pub wl: usize,
    pub wh: usize,
    pub out: Vec<u64>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

impl WorkerTask for TagTask {
    type Output = (Vec<u64>, bool);

    open spec fn pre(&self) -> bool {
        &&& key_cols_ok(self.cols)
        &&& nation_cols_ok(self.nation, self.sv@)
        &&& ntags_ok(self.ntag@, self.sv@, self.ps@)
        &&& self.wl <= self.wh && 32 * self.wh <= usize::MAX
        &&& self.out@.len() == self.wh - self.wl
    }

    open spec fn post(&self, out: (Vec<u64>, bool)) -> bool {
        tags_range_ok(out.0@, out.1, self.cols.keys@, self.cols.nats@, self.sv@, self.ps@, self.cols.base as int, self.wl as int,
            self.wh as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.wl as u64, self.wh as u64)
    }

    fn run(self) -> (out: (Vec<u64>, bool)) {
        let ntag: &Vec<u8> = &*self.ntag;
        tag_range(&self.cols, &self.nation, ntag, self.wl, self.wh, self.out, Ghost(self.sv@), Ghost(self.ps@))
    }
}

/// The body of a `TagTask`.
fn tag_range(c: &KeyCols, nation: &NationCols, ntag: &Vec<u8>, wl: usize, wh: usize, out: Vec<u64>,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: (Vec<u64>, bool))
    requires
        key_cols_ok(*c), nation_cols_ok(*nation, sv), ntags_ok(ntag@, sv, ps),
        wl <= wh, 32 * wh <= usize::MAX, out@.len() == wh - wl,
    ensures tags_range_ok(r.0@, r.1, c.keys@, c.nats@, sv, ps, c.base as int, wl as int, wh as int),
    no_unwind
{
    let mut out = out;
    let mut pos = true;
    let mut w = wl;
    while w < wh
        invariant
            key_cols_ok(*c), nation_cols_ok(*nation, sv), ntags_ok(ntag@, sv, ps),
            wl <= w <= wh, 32 * wh <= usize::MAX, out@.len() == wh - wl,
            forall|r: int| 32 * wl <= r < 32 * w && r < c.n ==> #[trigger] field2(out@[r / 32 - wl], (r % 32) as u64) as int == nat_tag(sv, ps, c.nats@[r]),
            pos ==> forall|r: int| 32 * wl <= r < 32 * w && r < c.n ==> #[trigger] c.keys@[r] as int == c.base + r,
        decreases wh - w,
    {
        let (word, p) = tag_word(c, nation, ntag, w, Ghost(sv), Ghost(ps));
        let ghost out0 = out@;
        out[w - wl] = word;
        proof {
            assert forall|r: int| 32 * wl <= r < 32 * (w + 1) && r < c.n implies #[trigger] field2(out@[r / 32 - wl], (r % 32) as u64) as int == nat_tag(sv, ps, c.nats@[r]) by {
                if r < 32 * w {
                    assert(out@[r / 32 - wl] == out0[r / 32 - wl]);
                } else {
                    assert(r / 32 == w);
                    let b = (r % 32) as u64;
                    assert(32 * w + b == r);
                }
            }
            if pos && p {
                assert forall|r: int| 32 * wl <= r < 32 * (w + 1) && r < c.n implies #[trigger] c.keys@[r] as int == c.base + r by {
                    if r >= 32 * w {
                        let b = (r - 32 * w) as u64;
                        assert(c.keys@[32 * w + b] as int == c.base + 32 * w + b);
                    }
                }
            }
        }
        pos = pos && p;
        w = w + 1;
    }
    (out, pos)
}

} // verus!
