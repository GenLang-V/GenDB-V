//! Zero-filled vectors allocated in one step (`vec![0; n]`: the allocator hands out zeroed memory, so a large
//! buffer costs no element-by-element initialization on the calling thread).
use vstd::prelude::*;

verus! {

/// `n` zero `i64`s.
pub fn zeros_i64(n: usize) -> (v: Vec<i64>)
    ensures v@ == Seq::new(n as nat, |_i: int| 0i64),
{
    let v = vec![0i64; n];
    proof {
        assert forall|i: int| 0 <= i < n implies v@[i] == 0i64 by {
            assert(vstd::pervasive::cloned(0i64, v@[i]));
        }
        assert(v@ =~= Seq::new(n as nat, |_i: int| 0i64));
    }
    v
}

/// `n` zero `i128`s.
pub fn zeros_i128(n: usize) -> (v: Vec<i128>)
    ensures v@ == Seq::new(n as nat, |_i: int| 0i128),
{
    let v = vec![0i128; n];
    proof {
        assert forall|i: int| 0 <= i < n implies v@[i] == 0i128 by {
            assert(vstd::pervasive::cloned(0i128, v@[i]));
        }
        assert(v@ =~= Seq::new(n as nat, |_i: int| 0i128));
    }
    v
}

/// `n` zero `u64`s.
pub fn zeros_u64(n: usize) -> (v: Vec<u64>)
    ensures v@ == Seq::new(n as nat, |_i: int| 0u64),
{
    let v = vec![0u64; n];
    proof {
        assert forall|i: int| 0 <= i < n implies v@[i] == 0u64 by {
            assert(vstd::pervasive::cloned(0u64, v@[i]));
        }
        assert(v@ =~= Seq::new(n as nat, |_i: int| 0u64));
    }
    v
}

/// `n` zero `u32`s.
pub fn zeros_u32(n: usize) -> (v: Vec<u32>)
    ensures v@ == Seq::new(n as nat, |_i: int| 0u32),
{
    let v = vec![0u32; n];
    proof {
        assert forall|i: int| 0 <= i < n implies v@[i] == 0u32 by {
            assert(vstd::pervasive::cloned(0u32, v@[i]));
        }
        assert(v@ =~= Seq::new(n as nat, |_i: int| 0u32));
    }
    v
}

/// `n` zero `u16`s.
pub fn zeros_u16(n: usize) -> (v: Vec<u16>)
    ensures v@ == Seq::new(n as nat, |_i: int| 0u16),
{
    let v = vec![0u16; n];
    proof {
        assert forall|i: int| 0 <= i < n implies v@[i] == 0u16 by {
            assert(vstd::pervasive::cloned(0u16, v@[i]));
        }
        assert(v@ =~= Seq::new(n as nat, |_i: int| 0u16));
    }
    v
}

/// `n` zero `u8`s.
pub fn zeros_u8(n: usize) -> (v: Vec<u8>)
    ensures v@ == Seq::new(n as nat, |_i: int| 0u8),
{
    let v = vec![0u8; n];
    proof {
        assert forall|i: int| 0 <= i < n implies v@[i] == 0u8 by {
            assert(vstd::pervasive::cloned(0u8, v@[i]));
        }
        assert(v@ =~= Seq::new(n as nat, |_i: int| 0u8));
    }
    v
}

/// `n` zero `usize`s.
pub fn zeros_usize(n: usize) -> (v: Vec<usize>)
    ensures v@ == Seq::new(n as nat, |_i: int| 0usize),
{
    let v = vec![0usize; n];
    proof {
        assert forall|i: int| 0 <= i < n implies v@[i] == 0usize by {
            assert(vstd::pervasive::cloned(0usize, v@[i]));
        }
        assert(v@ =~= Seq::new(n as nat, |_i: int| 0usize));
    }
    v
}

} // verus!
