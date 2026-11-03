// REGISTRY FILE: the verified read handle of stored parts (`registry/verus/stored.rs`, the one definition).
//
// Copied unchanged into every storage crate and every query crate of the fixed entry v4 as
// `crate::gendb_entry::stored` (assembled by `gendb_verification::obligations`). Authors cannot edit it; storage
// interface readers and query code read stored data only through it. Checked by Verus with `--no-cheating` in every
// such crate; no `assume`, `admit` or `external_body`.
//
// A `StoredParts` is one storage use of a query call: the immutable parts that the storage's builder returned, as the
// host maps them. Its view is the parts' `layout::PartView`s, the same view the builder's `OwnedPart`s have, so "the
// query reads what the builder wrote" stays one equality of views (the trusted storage round trip). The view never
// changes during a call.
//
// Reading is by extent: `extent_<kind>(p, lo, hi)` returns the elements [lo, hi) of part `p` as a `&'static` slice
// (zero-copy; the host maps parts lazily, so only the pages that code touches are read from the device). Nothing
// decodes a whole part or rebuilds canonical columns: a reader can read small metadata parts first and then request
// only the extents of data parts it needs.
//
// Request accounting (descriptive evidence, never a proof input). Every extent call adds one request, `hi - lo`
// elements and `(hi - lo) * width` bytes (`width` = the element size), each counter saturating at `u64::MAX`. They
// count requests: not element accesses (a returned slice may be read any number of times), not distinct bytes
// (extents may overlap or repeat) and not device I/O (the page cache, readahead and the lazy mapping decide what the
// device reads). The fields are private, and the constructor and the counter read are `pub(super)`: visible only
// inside `crate::gendb_entry` (fixed and generated framework files). Author code can therefore neither create, copy,
// reset nor unpack a handle, and every extent it obtains is counted on the handle it came from. Each handle carries
// the position of its storage use, so its counts stay attributed to that use.
use vstd::prelude::*;
use crate::gendb_abi::Part;
use super::layout::{part_view, parts_view, PartView};

verus! {

/// `x` as a `u64` counter value: `x` itself up to `u64::MAX`, else `u64::MAX` (for `x >= 0`).
pub open spec fn saturated(x: int) -> u64 {
    if x <= u64::MAX { x as u64 } else { u64::MAX }
}

/// Request counters `(requests, elements, bytes)` after one more request of `n` elements of `width` bytes each.
pub open spec fn after_request(counters: (u64, u64, u64), n: int, width: int) -> (u64, u64, u64) {
    (saturated(counters.0 + 1), saturated(counters.1 + n), saturated(counters.2 + n * width))
}

/// Number of elements of a part.
pub open spec fn part_len(part: PartView) -> nat {
    match part {
        PartView::I8(s) => s.len(),
        PartView::I16(s) => s.len(),
        PartView::I32(s) => s.len(),
        PartView::I64(s) => s.len(),
        PartView::I128(s) => s.len(),
        PartView::U8(s) => s.len(),
        PartView::U16(s) => s.len(),
        PartView::U32(s) => s.len(),
        PartView::U64(s) => s.len(),
    }
}

/// The request counters of one storage use at the end of a call (descriptive evidence).
pub struct RequestCounts {
    /// Position of the storage use in the query's storage-use list (the order of `abi_query`'s `uses`).
    pub use_index: u64,
    pub requests: u64,
    pub elements: u64,
    pub bytes: u64,
}

/// The stored parts of one storage use, read by extent.
pub struct StoredParts {
    parts: Vec<Part>,
    use_index: u64,
    requests: u64,
    elements: u64,
    bytes: u64,
}

impl View for StoredParts {
    type V = Seq<PartView>;

    closed spec fn view(&self) -> Seq<PartView> {
        parts_view(self.parts@)
    }
}

fn add_saturating(a: u64, b: u64) -> (r: u64)
    ensures r == saturated(a + b),
    no_unwind
{
    if a <= u64::MAX - b { a + b } else { u64::MAX }
}

fn mul_saturating(a: u64, b: u64) -> (r: u64)
    ensures r == saturated(a * b),
    no_unwind
{
    if b == 0 || a <= u64::MAX / b {
        proof {
            if b > 0 {
                assert(a * b <= (u64::MAX / b) * b) by (nonlinear_arith) requires a <= u64::MAX / b, b > 0;
                assert((u64::MAX / b) * b <= u64::MAX) by (nonlinear_arith) requires b > 0;
            }
        }
        a * b
    } else {
        proof {
            assert(a * b > u64::MAX) by (nonlinear_arith) requires a > u64::MAX / b, b > 0;
        }
        u64::MAX
    }
}

impl StoredParts {
    /// `(requests, elements, bytes)` requested so far on this handle.
    pub closed spec fn counters(&self) -> (u64, u64, u64) {
        (self.requests, self.elements, self.bytes)
    }

    /// The handle of storage use `use_index` over `parts`, with zero counters. Framework only (`crate::gendb_entry`).
    pub(super) fn new(parts: Vec<Part>, use_index: u64) -> (s: StoredParts)
        ensures s@ == parts_view(parts@), s.counters() == (0u64, 0u64, 0u64),
    {
        StoredParts { parts, use_index, requests: 0, elements: 0, bytes: 0 }
    }

    /// The counters of this handle and the position of its storage use. Framework only (`crate::gendb_entry`).
    pub(super) fn request_counts(&self) -> (r: RequestCounts)
        ensures (r.requests, r.elements, r.bytes) == self.counters(),
    {
        RequestCounts { use_index: self.use_index, requests: self.requests, elements: self.elements, bytes: self.bytes }
    }

    /// Number of parts.
    pub fn part_count(&self) -> (n: usize)
        ensures n == self@.len(),
    {
        self.parts.len()
    }

    /// Number of elements of part `p`.
    pub fn part_len(&self, p: usize) -> (n: usize)
        requires p < self@.len(),
        ensures n == part_len(self@[p as int]),
    {
        proof {
            assert(self@[p as int] == part_view(self.parts@[p as int]));
        }
        match &self.parts[p] {
            Part::I8(s) => s.len(),
            Part::I16(s) => s.len(),
            Part::I32(s) => s.len(),
            Part::I64(s) => s.len(),
            Part::I128(s) => s.len(),
            Part::U8(s) => s.len(),
            Part::U16(s) => s.len(),
            Part::U32(s) => s.len(),
            Part::U64(s) => s.len(),
        }
    }

    /// Account one request of `n` elements of `width` bytes each.
    fn count_request(&mut self, n: usize, width: u64)
        ensures
            final(self)@ == old(self)@,
            final(self).counters() == after_request(old(self).counters(), n as int, width as int),
        no_unwind
    {
        self.requests = add_saturating(self.requests, 1);
        self.elements = add_saturating(self.elements, n as u64);
        let bytes = mul_saturating(n as u64, width);
        proof {
            // Saturating the product first does not change the saturated total (the old count is nonnegative).
            assert(n as int * width as int >= 0) by (nonlinear_arith) requires n >= 0, width >= 0;
        }
        self.bytes = add_saturating(self.bytes, bytes);
    }

    /// Elements `[lo, hi)` of the `i8` part `p` (one request).
    pub fn extent_i8(&mut self, p: usize, lo: usize, hi: usize) -> (r: &'static [i8])
        requires p < old(self)@.len(), old(self)@[p as int] is I8, lo <= hi <= old(self)@[p as int]->I8_0.len(),
        ensures
            final(self)@ == old(self)@,
            r@ == old(self)@[p as int]->I8_0.subrange(lo as int, hi as int),
            final(self).counters() == after_request(old(self).counters(), hi - lo, 1),
    {
        proof {
            assert(self@[p as int] == part_view(self.parts@[p as int]));
        }
        let all: &'static [i8] = match &self.parts[p] {
            Part::I8(s) => *s,
            _ => vstd::pervasive::unreached(),
        };
        self.count_request(hi - lo, 1);
        let (_, tail) = all.split_at(lo);
        let (r, _) = tail.split_at(hi - lo);
        proof {
            assert(r@ =~= all@.subrange(lo as int, hi as int));
        }
        r
    }

    /// Elements `[lo, hi)` of the `i16` part `p` (one request).
    pub fn extent_i16(&mut self, p: usize, lo: usize, hi: usize) -> (r: &'static [i16])
        requires p < old(self)@.len(), old(self)@[p as int] is I16, lo <= hi <= old(self)@[p as int]->I16_0.len(),
        ensures
            final(self)@ == old(self)@,
            r@ == old(self)@[p as int]->I16_0.subrange(lo as int, hi as int),
            final(self).counters() == after_request(old(self).counters(), hi - lo, 2),
    {
        proof {
            assert(self@[p as int] == part_view(self.parts@[p as int]));
        }
        let all: &'static [i16] = match &self.parts[p] {
            Part::I16(s) => *s,
            _ => vstd::pervasive::unreached(),
        };
        self.count_request(hi - lo, 2);
        let (_, tail) = all.split_at(lo);
        let (r, _) = tail.split_at(hi - lo);
        proof {
            assert(r@ =~= all@.subrange(lo as int, hi as int));
        }
        r
    }

    /// Elements `[lo, hi)` of the `i32` part `p` (one request).
    pub fn extent_i32(&mut self, p: usize, lo: usize, hi: usize) -> (r: &'static [i32])
        requires p < old(self)@.len(), old(self)@[p as int] is I32, lo <= hi <= old(self)@[p as int]->I32_0.len(),
        ensures
            final(self)@ == old(self)@,
            r@ == old(self)@[p as int]->I32_0.subrange(lo as int, hi as int),
            final(self).counters() == after_request(old(self).counters(), hi - lo, 4),
    {
        proof {
            assert(self@[p as int] == part_view(self.parts@[p as int]));
        }
        let all: &'static [i32] = match &self.parts[p] {
            Part::I32(s) => *s,
            _ => vstd::pervasive::unreached(),
        };
        self.count_request(hi - lo, 4);
        let (_, tail) = all.split_at(lo);
        let (r, _) = tail.split_at(hi - lo);
        proof {
            assert(r@ =~= all@.subrange(lo as int, hi as int));
        }
        r
    }

    /// Elements `[lo, hi)` of the `i64` part `p` (one request).
    pub fn extent_i64(&mut self, p: usize, lo: usize, hi: usize) -> (r: &'static [i64])
        requires p < old(self)@.len(), old(self)@[p as int] is I64, lo <= hi <= old(self)@[p as int]->I64_0.len(),
        ensures
            final(self)@ == old(self)@,
            r@ == old(self)@[p as int]->I64_0.subrange(lo as int, hi as int),
            final(self).counters() == after_request(old(self).counters(), hi - lo, 8),
    {
        proof {
            assert(self@[p as int] == part_view(self.parts@[p as int]));
        }
        let all: &'static [i64] = match &self.parts[p] {
            Part::I64(s) => *s,
            _ => vstd::pervasive::unreached(),
        };
        self.count_request(hi - lo, 8);
        let (_, tail) = all.split_at(lo);
        let (r, _) = tail.split_at(hi - lo);
        proof {
            assert(r@ =~= all@.subrange(lo as int, hi as int));
        }
        r
    }

    /// Elements `[lo, hi)` of the `i128` part `p` (one request).
    pub fn extent_i128(&mut self, p: usize, lo: usize, hi: usize) -> (r: &'static [i128])
        requires p < old(self)@.len(), old(self)@[p as int] is I128, lo <= hi <= old(self)@[p as int]->I128_0.len(),
        ensures
            final(self)@ == old(self)@,
            r@ == old(self)@[p as int]->I128_0.subrange(lo as int, hi as int),
            final(self).counters() == after_request(old(self).counters(), hi - lo, 16),
    {
        proof {
            assert(self@[p as int] == part_view(self.parts@[p as int]));
        }
        let all: &'static [i128] = match &self.parts[p] {
            Part::I128(s) => *s,
            _ => vstd::pervasive::unreached(),
        };
        self.count_request(hi - lo, 16);
        let (_, tail) = all.split_at(lo);
        let (r, _) = tail.split_at(hi - lo);
        proof {
            assert(r@ =~= all@.subrange(lo as int, hi as int));
        }
        r
    }

    /// Elements `[lo, hi)` of the `u8` (byte) part `p` (one request).
    pub fn extent_u8(&mut self, p: usize, lo: usize, hi: usize) -> (r: &'static [u8])
        requires p < old(self)@.len(), old(self)@[p as int] is U8, lo <= hi <= old(self)@[p as int]->U8_0.len(),
        ensures
            final(self)@ == old(self)@,
            r@ == old(self)@[p as int]->U8_0.subrange(lo as int, hi as int),
            final(self).counters() == after_request(old(self).counters(), hi - lo, 1),
    {
        proof {
            assert(self@[p as int] == part_view(self.parts@[p as int]));
        }
        let all: &'static [u8] = match &self.parts[p] {
            Part::U8(s) => *s,
            _ => vstd::pervasive::unreached(),
        };
        self.count_request(hi - lo, 1);
        let (_, tail) = all.split_at(lo);
        let (r, _) = tail.split_at(hi - lo);
        proof {
            assert(r@ =~= all@.subrange(lo as int, hi as int));
        }
        r
    }

    /// Elements `[lo, hi)` of the `u16` part `p` (one request).
    pub fn extent_u16(&mut self, p: usize, lo: usize, hi: usize) -> (r: &'static [u16])
        requires p < old(self)@.len(), old(self)@[p as int] is U16, lo <= hi <= old(self)@[p as int]->U16_0.len(),
        ensures
            final(self)@ == old(self)@,
            r@ == old(self)@[p as int]->U16_0.subrange(lo as int, hi as int),
            final(self).counters() == after_request(old(self).counters(), hi - lo, 2),
    {
        proof {
            assert(self@[p as int] == part_view(self.parts@[p as int]));
        }
        let all: &'static [u16] = match &self.parts[p] {
            Part::U16(s) => *s,
            _ => vstd::pervasive::unreached(),
        };
        self.count_request(hi - lo, 2);
        let (_, tail) = all.split_at(lo);
        let (r, _) = tail.split_at(hi - lo);
        proof {
            assert(r@ =~= all@.subrange(lo as int, hi as int));
        }
        r
    }

    /// Elements `[lo, hi)` of the `u32` part `p` (one request).
    pub fn extent_u32(&mut self, p: usize, lo: usize, hi: usize) -> (r: &'static [u32])
        requires p < old(self)@.len(), old(self)@[p as int] is U32, lo <= hi <= old(self)@[p as int]->U32_0.len(),
        ensures
            final(self)@ == old(self)@,
            r@ == old(self)@[p as int]->U32_0.subrange(lo as int, hi as int),
            final(self).counters() == after_request(old(self).counters(), hi - lo, 4),
    {
        proof {
            assert(self@[p as int] == part_view(self.parts@[p as int]));
        }
        let all: &'static [u32] = match &self.parts[p] {
            Part::U32(s) => *s,
            _ => vstd::pervasive::unreached(),
        };
        self.count_request(hi - lo, 4);
        let (_, tail) = all.split_at(lo);
        let (r, _) = tail.split_at(hi - lo);
        proof {
            assert(r@ =~= all@.subrange(lo as int, hi as int));
        }
        r
    }

    /// Elements `[lo, hi)` of the `u64` part `p` (one request).
    pub fn extent_u64(&mut self, p: usize, lo: usize, hi: usize) -> (r: &'static [u64])
        requires p < old(self)@.len(), old(self)@[p as int] is U64, lo <= hi <= old(self)@[p as int]->U64_0.len(),
        ensures
            final(self)@ == old(self)@,
            r@ == old(self)@[p as int]->U64_0.subrange(lo as int, hi as int),
            final(self).counters() == after_request(old(self).counters(), hi - lo, 8),
    {
        proof {
            assert(self@[p as int] == part_view(self.parts@[p as int]));
        }
        let all: &'static [u64] = match &self.parts[p] {
            Part::U64(s) => *s,
            _ => vstd::pervasive::unreached(),
        };
        self.count_request(hi - lo, 8);
        let (_, tail) = all.split_at(lo);
        let (r, _) = tail.split_at(hi - lo);
        proof {
            assert(r@ =~= all@.subrange(lo as int, hi as int));
        }
        r
    }
}

} // verus!
