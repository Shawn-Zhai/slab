// Which std methods the bundled vstd lets verified code call under `--no-cheating`.
// SPEC_REVIEW.md uses this to tell contracts that are missing by choice from contracts that cannot
// be written yet. Run from verus_fixed/:
//
//     verus --no-cheating vstd_probe.rs
//     verus --no-cheating --cfg probe_clone_from vstd_probe.rs
//
// Expected with Verus 0.2026.10.18.7d82994: the first command reports "is not supported" for
// exactly the 8 calls marked UNSUPPORTED below, and none for the 3 marked SUPPORTED. The second
// command stops earlier, at "Verus does not yet support `clone_from`".
use vstd::prelude::*;

verus! {

// UNSUPPORTED: `capacity`, `reserve` and `reserve_exact` of `Slab` need it, and every capacity
// clause of the human spec does.
fn vec_capacity(v: &Vec<u8>) -> usize {
    v.capacity()
}

// UNSUPPORTED: `Slab::reserve_exact`.
fn vec_reserve_exact(v: &mut Vec<u8>) {
    v.reserve_exact(3);
}

// UNSUPPORTED: `Slab::shrink_to_fit` and `Slab::compact`.
fn vec_shrink_to_fit(v: &mut Vec<u8>) {
    v.shrink_to_fit();
}

// UNSUPPORTED (2 errors: the method and the `Drain` type): `Slab::drain` and `Drain`.
fn vec_drain(v: &mut Vec<u8>) {
    let _ = v.drain(..);
}

// UNSUPPORTED: `Slab::get_unchecked` and `Slab::get_unchecked_mut`.
fn slice_get_unchecked(s: &[u8]) -> u8
    requires
        s@.len() > 0,
{
    unsafe { *s.get_unchecked(0) }
}

// UNSUPPORTED: `try_remove` uses the verified stand-in `std_ext::mem_replace` instead.
fn mem_replace(x: &mut u8) {
    let _ = core::mem::replace(x, 3u8);
}

// UNSUPPORTED: vstd's iterator specification has no `size_hint`, so `Iter::size_hint` must state
// its own contract (amendment A1 in SPEC_REVIEW.md).
fn iter_size_hint(v: &Vec<u8>) {
    let it = v.iter();
    let _ = it.size_hint();
}

// SUPPORTED (positive control).
fn vec_reserve(v: &mut Vec<u8>) {
    v.reserve(3);
}

// SUPPORTED (positive control): the `vec_get_mut`/`slice_get_mut` stand-ins are no longer needed.
fn slice_get_mut(s: &mut [u8]) {
    let _ = s.get_mut(0);
}

// SUPPORTED (positive control).
fn vec_clone(w: &Vec<u8>) -> Vec<u8> {
    w.clone()
}

// `Clone for Slab` needs it (with `--cfg probe_clone_from`).
#[cfg(probe_clone_from)]
fn vec_clone_from(v: &mut Vec<u8>, w: &Vec<u8>) {
    v.clone_from(w);
}

fn main() {
}

} // verus!
