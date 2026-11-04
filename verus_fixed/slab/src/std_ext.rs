//! Verified stand-ins for std methods that vstd does not specify (`<[T]>::get_mut` and
//! `core::mem::replace`), written with std methods that it does specify. Each one behaves
//! exactly like the method it replaces.
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// `vec.get_mut(i)`, implemented with `IndexMut` (`&mut vec[i]`).
#[inline]
pub(crate) fn vec_get_mut<E>(vec: &mut Vec<E>, i: usize) -> (r: Option<&mut E>)
    ensures
        i < old(vec)@.len() ==> {
            &&& r is Some
            &&& *r->Some_0 == old(vec)@[i as int]
            &&& final(vec)@ == old(vec)@.update(i as int, *final(r->Some_0))
        },
        i >= old(vec)@.len() ==> r is None && final(vec)@ == old(vec)@,
{
    if i < vec.len() {
        Some(&mut vec[i])
    } else {
        None
    }
}

/// `slice.get_mut(i)`, implemented with `split_at_mut` and `first_mut`.
#[inline]
pub(crate) fn slice_get_mut<E>(slice: &mut [E], i: usize) -> (r: Option<&mut E>)
    ensures
        i < old(slice)@.len() ==> {
            &&& r is Some
            &&& *r->Some_0 == old(slice)@[i as int]
            &&& final(slice)@ == old(slice)@.update(i as int, *final(r->Some_0))
        },
        i >= old(slice)@.len() ==> r is None && final(slice)@ == old(slice)@,
{
    if i < slice.len() {
        slice.split_at_mut(i).1.first_mut()
    } else {
        None
    }
}

/// `core::mem::replace(dest, src)`, implemented with `core::mem::swap`.
#[inline]
pub(crate) fn mem_replace<E>(dest: &mut E, src: E) -> (r: E)
    ensures
        r == *old(dest),
        *final(dest) == src,
{
    let mut src = src;
    core::mem::swap(dest, &mut src);
    src
}

} // verus!
