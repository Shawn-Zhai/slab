//! TRUSTED code: the upstream items that Verus does not verify.
//! Verus skips this module (`#[verifier::external]` on `mod trusted` in `lib.rs`); normal builds
//! compile it like any other module. The items are upstream's code, moved here unchanged, except
//! the `shrink_to_fit` shell (T8), whose logic moved into the verified `remove_vacant_tail`.
//!
//! | id | items | why trusted |
//! |----|-------|-------------|
//! | T1 | `iter_mut`, `drain`, the three `IntoIterator` impls, `IntoIter`, `IterMut` and `Drain` with their `Iterator`, `DoubleEndedIterator`, `ExactSizeIterator` and `FusedIterator` impls | vstd does not specify `Enumerate`, `slice::IterMut::next_back` or `vec::Drain`; `IntoIter` needs `vec::IntoIter::next` to be `no_unwind`; a trait method cannot require `wf()` |
//! | T2 | `get_disjoint_mut`, `get_unchecked`, `get_unchecked_mut`, `get2_unchecked_mut`, `key_of` | raw pointers, `MaybeUninit`, unchecked indexing, pointer-to-integer casts |
//! | T3 | `compact` | a `Drop` guard that repairs the slab if the closure unwinds, `mem::forget` and `Vec::shrink_to_fit` |
//! | T4 | the `Debug` impls, `Display` and `std::error::Error` for `GetDisjointMutError` | formatting is not supported |
//! | T5 | `capacity`, `reserve`, `reserve_exact` | `Vec::capacity` and `Vec::reserve_exact` are unspecified |
//! | T6 | `Clone for Slab` | `Vec::clone_from` is unspecified, and Verus verifies a trait impl all-or-nothing |
//! | T7 | `FromIterator` | iterates an arbitrary `IntoIterator` and calls `size_hint`; it drives the verified `Builder` |
//! | T8 | `shrink_to_fit` | `Vec::shrink_to_fit` is unspecified; the rest is the verified `remove_vacant_tail` |
//!
//! The serde impls are trusted too (T9 in `VERIFICATION.md`), in their own file, `serde.rs`.
//!
//! Obligations, checked by inspection: code here that mutates a slab keeps `wf()`, and calls into
//! verified code meet their preconditions (see `VERIFICATION.md`, "Trusted base").

use crate::{builder, Entry, GetDisjointMutError, Iter, Slab};

use alloc::vec;
use core::iter::{self, FromIterator, FusedIterator};
use core::mem::MaybeUninit;
use core::{fmt, mem, slice};

// ===== T1: iterators other than `Iter` =====

/// A consuming iterator over the values stored in a `Slab`
// T1: wraps std iterator adapters that Verus does not specify.
pub struct IntoIter<T> {
    entries: iter::Enumerate<vec::IntoIter<Entry<T>>>,
    len: usize,
}

/// A mutable iterator over the values stored in the `Slab`
// T1: wraps std iterator adapters that Verus does not specify.
pub struct IterMut<'a, T> {
    entries: iter::Enumerate<slice::IterMut<'a, Entry<T>>>,
    len: usize,
}

/// A draining iterator for `Slab`
// T1: wraps `vec::Drain`, which Verus does not specify.
pub struct Drain<'a, T> {
    inner: vec::Drain<'a, Entry<T>>,
    len: usize,
}

impl<T> Slab<T> {
    /// Return an iterator that allows modifying each value.
    ///
    /// This function should generally be **avoided** as it is not efficient.
    /// Iterators must iterate over every slot in the slab even if it is
    /// vacant. As such, a slab with a capacity of 1 million but only one
    /// stored value must still iterate the million slots.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// let key1 = slab.insert(0);
    /// let key2 = slab.insert(1);
    ///
    /// for (key, val) in slab.iter_mut() {
    ///     if key == key1 {
    ///         *val += 2;
    ///     }
    /// }
    ///
    /// assert_eq!(slab[key1], 2);
    /// assert_eq!(slab[key2], 1);
    /// ```
    // T1: `IterMut` is not verified.
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            entries: self.entries.iter_mut().enumerate(),
            len: self.len,
        }
    }

    /// Return a draining iterator that removes all elements from the slab and
    /// yields the removed items.
    ///
    /// Note: Elements are removed even if the iterator is only partially
    /// consumed or not consumed at all.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// let _ = slab.insert(0);
    /// let _ = slab.insert(1);
    /// let _ = slab.insert(2);
    ///
    /// {
    ///     let mut drain = slab.drain();
    ///
    ///     assert_eq!(Some(0), drain.next());
    ///     assert_eq!(Some(1), drain.next());
    ///     assert_eq!(Some(2), drain.next());
    ///     assert_eq!(None, drain.next());
    /// }
    ///
    /// assert!(slab.is_empty());
    /// ```
    // T1: `Vec::drain` has no Verus specification.
    pub fn drain(&mut self) -> Drain<'_, T> {
        let old_len = self.len;
        self.len = 0;
        self.next = 0;
        Drain {
            inner: self.entries.drain(..),
            len: old_len,
        }
    }
}

// T1: `IntoIter` is not verified.
impl<T> IntoIterator for Slab<T> {
    type Item = (usize, T);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter {
            entries: self.entries.into_iter().enumerate(),
            len: self.len,
        }
    }
}

// T1: a trait method cannot require `wf()`, which the verified `iter` needs.
impl<'a, T> IntoIterator for &'a Slab<T> {
    type Item = (usize, &'a T);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

// T1: `IterMut` is not verified.
impl<'a, T> IntoIterator for &'a mut Slab<T> {
    type Item = (usize, &'a mut T);
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

// T1: `IntoIter` is not verified.
impl<T> Iterator for IntoIter<T> {
    type Item = (usize, T);

    fn next(&mut self) -> Option<Self::Item> {
        for (key, entry) in &mut self.entries {
            if let Entry::Occupied(v) = entry {
                self.len -= 1;
                return Some((key, v));
            }
        }

        debug_assert_eq!(self.len, 0);
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

// T1: `IntoIter` is not verified.
impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some((key, entry)) = self.entries.next_back() {
            if let Entry::Occupied(v) = entry {
                self.len -= 1;
                return Some((key, v));
            }
        }

        debug_assert_eq!(self.len, 0);
        None
    }
}

// T1: `IntoIter` is not verified.
impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.len
    }
}

// T1: `IntoIter` is not verified.
impl<T> FusedIterator for IntoIter<T> {}

// T1: `IterMut` is not verified.
impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (usize, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        for (key, entry) in &mut self.entries {
            if let Entry::Occupied(ref mut v) = *entry {
                self.len -= 1;
                return Some((key, v));
            }
        }

        debug_assert_eq!(self.len, 0);
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

// T1: `IterMut` is not verified.
impl<T> DoubleEndedIterator for IterMut<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some((key, entry)) = self.entries.next_back() {
            if let Entry::Occupied(ref mut v) = *entry {
                self.len -= 1;
                return Some((key, v));
            }
        }

        debug_assert_eq!(self.len, 0);
        None
    }
}

// T1: `IterMut` is not verified.
impl<T> ExactSizeIterator for IterMut<'_, T> {
    fn len(&self) -> usize {
        self.len
    }
}

// T1: `IterMut` is not verified.
impl<T> FusedIterator for IterMut<'_, T> {}

// T1: `Drain` is not verified.
impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        for entry in &mut self.inner {
            if let Entry::Occupied(v) = entry {
                self.len -= 1;
                return Some(v);
            }
        }

        debug_assert_eq!(self.len, 0);
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

// T1: `Drain` is not verified.
impl<T> DoubleEndedIterator for Drain<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some(entry) = self.inner.next_back() {
            if let Entry::Occupied(v) = entry {
                self.len -= 1;
                return Some(v);
            }
        }

        debug_assert_eq!(self.len, 0);
        None
    }
}

// T1: `Drain` is not verified.
impl<T> ExactSizeIterator for Drain<'_, T> {
    fn len(&self) -> usize {
        self.len
    }
}

// T1: `Drain` is not verified.
impl<T> FusedIterator for Drain<'_, T> {}

// ===== T2: raw pointers and unchecked access =====

impl<T> Slab<T> {
    /// Returns mutable references to many indices at once.
    ///
    /// Returns [`GetDisjointMutError`] if the indices are out of bounds,
    /// overlapping, or vacant.
    // T2: raw pointers and `MaybeUninit`.
    pub fn get_disjoint_mut<const N: usize>(
        &mut self,
        keys: [usize; N],
    ) -> Result<[&mut T; N], GetDisjointMutError> {
        // NB: The optimizer should inline the loops into a sequence
        // of instructions without additional branching.
        for (i, &key) in keys.iter().enumerate() {
            for &prev_key in &keys[..i] {
                if key == prev_key {
                    return Err(GetDisjointMutError::OverlappingIndices);
                }
            }
        }

        let entries_ptr = self.entries.as_mut_ptr();
        let entries_len = self.entries.len();

        let mut res = MaybeUninit::<[&mut T; N]>::uninit();
        let res_ptr = res.as_mut_ptr() as *mut &mut T;

        for (i, &key) in keys.iter().enumerate() {
            // `key` won't be greater than `entries_len`.
            if key >= entries_len {
                return Err(GetDisjointMutError::IndexOutOfBounds);
            }
            // SAFETY: we made sure above that this key is in bounds.
            match unsafe { &mut *entries_ptr.add(key) } {
                Entry::Vacant(_) => return Err(GetDisjointMutError::IndexVacant),
                Entry::Occupied(entry) => {
                    // SAFETY: `res` and `keys` both have N elements so `i` must be in bounds.
                    // We checked above that all selected `entry`s are distinct.
                    unsafe { res_ptr.add(i).write(entry) };
                }
            }
        }
        // SAFETY: the loop above only terminates successfully if it initialized
        // all elements of this array.
        Ok(unsafe { res.assume_init() })
    }

    /// Return a reference to the value associated with the given key without
    /// performing bounds checking.
    ///
    /// For a safe alternative see [`get`](Slab::get).
    ///
    /// This function should be used with care.
    ///
    /// # Safety
    ///
    /// The key must be within bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// let key = slab.insert(2);
    ///
    /// unsafe {
    ///     assert_eq!(slab.get_unchecked(key), &2);
    /// }
    /// ```
    // T2: unchecked access (`<[T]>::get_unchecked`).
    pub unsafe fn get_unchecked(&self, key: usize) -> &T {
        match *self.entries.get_unchecked(key) {
            Entry::Occupied(ref val) => val,
            _ => unreachable!(),
        }
    }

    /// Return a mutable reference to the value associated with the given key
    /// without performing bounds checking.
    ///
    /// For a safe alternative see [`get_mut`](Slab::get_mut).
    ///
    /// This function should be used with care.
    ///
    /// # Safety
    ///
    /// The key must be within bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// let key = slab.insert(2);
    ///
    /// unsafe {
    ///     let val = slab.get_unchecked_mut(key);
    ///     *val = 13;
    /// }
    ///
    /// assert_eq!(slab[key], 13);
    /// ```
    // T2: unchecked access (`<[T]>::get_unchecked_mut`).
    pub unsafe fn get_unchecked_mut(&mut self, key: usize) -> &mut T {
        match *self.entries.get_unchecked_mut(key) {
            Entry::Occupied(ref mut val) => val,
            _ => unreachable!(),
        }
    }

    /// Return two mutable references to the values associated with the two
    /// given keys simultaneously without performing bounds checking and safety
    /// condition checking.
    ///
    /// For a safe alternative see [`get2_mut`](Slab::get2_mut).
    ///
    /// This function should be used with care.
    ///
    /// # Safety
    ///
    /// - Both keys must be within bounds.
    /// - The condition `key1 != key2` must hold.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// use std::mem;
    ///
    /// let mut slab = Slab::new();
    /// let key1 = slab.insert(1);
    /// let key2 = slab.insert(2);
    /// let (value1, value2) = unsafe { slab.get2_unchecked_mut(key1, key2) };
    /// mem::swap(value1, value2);
    /// assert_eq!(slab[key1], 2);
    /// assert_eq!(slab[key2], 1);
    /// ```
    // T2: raw pointers.
    pub unsafe fn get2_unchecked_mut(&mut self, key1: usize, key2: usize) -> (&mut T, &mut T) {
        debug_assert_ne!(key1, key2);
        let ptr = self.entries.as_mut_ptr();
        let ptr1 = ptr.add(key1);
        let ptr2 = ptr.add(key2);
        match (&mut *ptr1, &mut *ptr2) {
            (&mut Entry::Occupied(ref mut val1), &mut Entry::Occupied(ref mut val2)) => {
                (val1, val2)
            }
            _ => unreachable!(),
        }
    }

    /// Get the key for an element in the slab.
    ///
    /// The reference must point to an element owned by the slab.
    /// Otherwise this function will panic.
    /// This is a constant-time operation because the key can be calculated
    /// from the reference with pointer arithmetic.
    ///
    /// # Panics
    ///
    /// This function will panic if the reference does not point to an element
    /// of the slab.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    ///
    /// let mut slab = Slab::new();
    /// let key = slab.insert(String::from("foo"));
    /// let value = &slab[key];
    /// assert_eq!(slab.key_of(value), key);
    /// ```
    ///
    /// Values are not compared, so passing a reference to a different location
    /// will result in a panic:
    ///
    /// ```should_panic
    /// # use slab::*;
    ///
    /// let mut slab = Slab::new();
    /// let key = slab.insert(0);
    /// let bad = &0;
    /// slab.key_of(bad); // this will panic
    /// unreachable!();
    /// ```
    // T2: pointer-to-integer casts and `mem::size_of`.
    #[track_caller]
    pub fn key_of(&self, present_element: &T) -> usize {
        let element_ptr = present_element as *const T as usize;
        let base_ptr = self.entries.as_ptr() as usize;
        // Use wrapping subtraction in case the reference is bad
        let byte_offset = element_ptr.wrapping_sub(base_ptr);
        // The division rounds away any offset of T inside Entry
        // The size of Entry<T> is never zero even if T is due to Vacant(usize)
        let key = byte_offset / mem::size_of::<Entry<T>>();
        // Prevent returning unspecified (but out of bounds) values
        if key >= self.entries.len() {
            panic!("The reference points to a value outside this slab");
        }
        // The reference cannot point to a vacant entry, because then it would not be valid
        key
    }
}

// ===== T3: `compact` =====

impl<T> Slab<T> {
    /// Reduce the capacity as much as possible, changing the key for elements when necessary.
    ///
    /// To allow updating references to the elements which must be moved to a new key,
    /// this function takes a closure which is called before moving each element.
    /// The second and third parameters to the closure are the current key and
    /// new key respectively.
    /// In case changing the key for one element turns out not to be possible,
    /// the move can be cancelled by returning `false` from the closure.
    /// In that case no further attempts at relocating elements is made.
    /// If the closure unwinds, the slab will be left in a consistent state,
    /// but the value that the closure panicked on might be removed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    ///
    /// let mut slab = Slab::with_capacity(10);
    /// let a = slab.insert('a');
    /// slab.insert('b');
    /// slab.insert('c');
    /// slab.remove(a);
    /// slab.compact(|&mut value, from, to| {
    ///     assert_eq!((value, from, to), ('c', 2, 0));
    ///     true
    /// });
    /// assert!(slab.capacity() >= 2 && slab.capacity() < 10);
    /// ```
    ///
    /// The value is not moved when the closure returns `Err`:
    ///
    /// ```
    /// # use slab::*;
    ///
    /// let mut slab = Slab::with_capacity(100);
    /// let a = slab.insert('a');
    /// let b = slab.insert('b');
    /// slab.remove(a);
    /// slab.compact(|&mut value, from, to| false);
    /// assert_eq!(slab.iter().next(), Some((b, &'b')));
    /// ```
    // T3: relies on a `Drop` guard for unwinding, `mem::forget` and
    // `Vec::shrink_to_fit`, none of which Verus supports. It calls the verified
    // `recreate_vacant_list`.
    pub fn compact<F>(&mut self, mut rekey: F)
    where
        F: FnMut(&mut T, usize, usize) -> bool,
    {
        // If the closure unwinds, we need to restore a valid list of vacant entries
        struct CleanupGuard<'a, T> {
            slab: &'a mut Slab<T>,
            decrement: bool,
        }
        impl<T> Drop for CleanupGuard<'_, T> {
            fn drop(&mut self) {
                if self.decrement {
                    // Value was popped and not pushed back on
                    self.slab.len -= 1;
                }
                self.slab.recreate_vacant_list();
            }
        }
        let mut guard = CleanupGuard {
            slab: self,
            decrement: true,
        };

        let mut occupied_until = 0;
        // While there are vacant entries
        while guard.slab.entries.len() > guard.slab.len {
            // Find a value that needs to be moved,
            // by popping entries until we find an occupied one.
            // (entries cannot be empty because 0 is not greater than anything)
            if let Some(Entry::Occupied(mut value)) = guard.slab.entries.pop() {
                // Found one, now find a vacant entry to move it to
                while let Some(&Entry::Occupied(_)) = guard.slab.entries.get(occupied_until) {
                    occupied_until += 1;
                }
                // Let the caller try to update references to the key
                if !rekey(&mut value, guard.slab.entries.len(), occupied_until) {
                    // Changing the key failed, so push the entry back on at its old index.
                    guard.slab.entries.push(Entry::Occupied(value));
                    guard.decrement = false;
                    guard.slab.entries.shrink_to_fit();
                    return;
                    // Guard drop handles cleanup
                }
                // Put the value in its new spot
                guard.slab.entries[occupied_until] = Entry::Occupied(value);
                // ... and mark it as occupied (this is optional)
                occupied_until += 1;
            }
        }
        guard.slab.next = guard.slab.len;
        guard.slab.entries.shrink_to_fit();
        // Normal cleanup is not necessary
        mem::forget(guard);
    }
}

// ===== T4: formatting =====

// T4: formatting is not supported by Verus.
impl fmt::Display for GetDisjointMutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            GetDisjointMutError::IndexVacant => "an index is vacant",
            GetDisjointMutError::IndexOutOfBounds => "an index is out of bounds",
            GetDisjointMutError::OverlappingIndices => "there were overlapping indices",
        };
        fmt::Display::fmt(msg, f)
    }
}

// T4: `std::error::Error` is not known to Verus.
#[cfg(feature = "std")]
impl std::error::Error for GetDisjointMutError {}

// T4: formatting is not supported by Verus.
impl<T> fmt::Debug for Slab<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        if fmt.alternate() {
            fmt.debug_map().entries(self.iter()).finish()
        } else {
            fmt.debug_struct("Slab")
                .field("len", &self.len)
                .field("cap", &self.capacity())
                .finish()
        }
    }
}

// T4: formatting is not supported by Verus.
impl<T> fmt::Debug for IntoIter<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("IntoIter")
            .field("remaining", &self.len)
            .finish()
    }
}

// T4: formatting is not supported by Verus.
impl<T> fmt::Debug for Iter<'_, T>
where
    T: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("Iter")
            .field("remaining", &self.len)
            .finish()
    }
}

// T4: formatting is not supported by Verus.
impl<T> fmt::Debug for IterMut<'_, T>
where
    T: fmt::Debug,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("IterMut")
            .field("remaining", &self.len)
            .finish()
    }
}

// T4: formatting is not supported by Verus.
impl<T> fmt::Debug for Drain<'_, T> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("Drain").finish()
    }
}

// ===== T5: capacity =====

impl<T> Slab<T> {
    /// Return the number of values the slab can store without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let slab: Slab<i32> = Slab::with_capacity(10);
    /// assert_eq!(slab.capacity(), 10);
    /// ```
    // T5: `Vec::capacity` has no Verus specification.
    pub fn capacity(&self) -> usize {
        self.entries.capacity()
    }

    /// Reserve capacity for at least `additional` more values to be stored
    /// without allocating.
    ///
    /// `reserve` does nothing if the slab already has sufficient capacity for
    /// `additional` more values. If more capacity is required, a new segment of
    /// memory will be allocated and all existing values will be copied into it.
    /// As such, if the slab is already very large, a call to `reserve` can end
    /// up being expensive.
    ///
    /// The slab may reserve more than `additional` extra space in order to
    /// avoid frequent reallocations. Use `reserve_exact` instead to guarantee
    /// that only the requested space is allocated.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// slab.insert("hello");
    /// slab.reserve(10);
    /// assert!(slab.capacity() >= 11);
    /// ```
    // T5: uses `capacity` (above).
    pub fn reserve(&mut self, additional: usize) {
        if self.capacity() - self.len >= additional {
            return;
        }
        let need_add = additional - (self.entries.len() - self.len);
        self.entries.reserve(need_add);
    }

    /// Reserve the minimum capacity required to store exactly `additional`
    /// more values.
    ///
    /// `reserve_exact` does nothing if the slab already has sufficient capacity
    /// for `additional` more values. If more capacity is required, a new segment
    /// of memory will be allocated and all existing values will be copied into
    /// it.  As such, if the slab is already very large, a call to `reserve` can
    /// end up being expensive.
    ///
    /// Note that the allocator may give the slab more space than it requests.
    /// Therefore capacity can not be relied upon to be precisely minimal.
    /// Prefer `reserve` if future insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// slab.insert("hello");
    /// slab.reserve_exact(10);
    /// assert!(slab.capacity() >= 11);
    /// ```
    // T5: uses `capacity` and `Vec::reserve_exact`, which have no Verus
    // specification.
    pub fn reserve_exact(&mut self, additional: usize) {
        if self.capacity() - self.len >= additional {
            return;
        }
        let need_add = additional - (self.entries.len() - self.len);
        self.entries.reserve_exact(need_add);
    }
}

// ===== T6: `Clone for Slab` =====

// T6: `Vec::clone_from` has no Verus specification, and Verus
// verifies a trait impl as a whole.
impl<T> Clone for Slab<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            entries: self.entries.clone(),
            len: self.len,
            next: self.next,
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.entries.clone_from(&source.entries);
        self.len = source.len;
        self.next = source.next;
    }
}

// ===== T7: `FromIterator` =====

/// Create a slab from an iterator of key-value pairs.
///
/// If the iterator produces duplicate keys, the previous value is replaced with the later one.
/// The keys does not need to be sorted beforehand, and this function always
/// takes O(n) time.
/// Note that the returned slab will use space proportional to the largest key,
/// so don't use `Slab` with untrusted keys.
///
/// # Examples
///
/// ```
/// # use slab::*;
///
/// let vec = vec![(2,'a'), (6,'b'), (7,'c')];
/// let slab = vec.into_iter().collect::<Slab<char>>();
/// assert_eq!(slab.len(), 3);
/// assert!(slab.capacity() >= 8);
/// assert_eq!(slab[2], 'a');
/// ```
///
/// With duplicate and unsorted keys:
///
/// ```
/// # use slab::*;
///
/// let vec = vec![(20,'a'), (10,'b'), (11,'c'), (10,'d')];
/// let slab = vec.into_iter().collect::<Slab<char>>();
/// assert_eq!(slab.len(), 3);
/// assert_eq!(slab[10], 'd');
/// ```
// T7: iterating over an arbitrary `IntoIterator` (and its `size_hint`)
// is not supported by Verus. The `Builder` it drives is verified.
impl<T> FromIterator<(usize, T)> for Slab<T> {
    fn from_iter<I>(iterable: I) -> Self
    where
        I: IntoIterator<Item = (usize, T)>,
    {
        let iterator = iterable.into_iter();
        let mut builder = builder::Builder::with_capacity(iterator.size_hint().0);

        for (key, value) in iterator {
            builder.pair(key, value);
        }
        builder.build()
    }
}

// ===== T8: the `shrink_to_fit` shell =====

impl<T> Slab<T> {
    /// Shrink the capacity of the slab as much as possible without invalidating keys.
    ///
    /// Because values cannot be moved to a different index, the slab cannot
    /// shrink past any stored values.
    /// It will drop down as close as possible to the length but the allocator may
    /// still inform the underlying vector that there is space for a few more elements.
    ///
    /// This function can take O(n) time even when the capacity cannot be reduced
    /// or the allocation is shrunk in place. Repeated calls run in O(1) though.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::with_capacity(10);
    ///
    /// for i in 0..3 {
    ///     slab.insert(i);
    /// }
    ///
    /// slab.shrink_to_fit();
    /// assert!(slab.capacity() >= 3 && slab.capacity() < 10);
    /// ```
    ///
    /// The slab cannot shrink past the last present value even if previous
    /// values are removed:
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::with_capacity(10);
    ///
    /// for i in 0..4 {
    ///     slab.insert(i);
    /// }
    ///
    /// slab.remove(0);
    /// slab.remove(3);
    ///
    /// slab.shrink_to_fit();
    /// assert!(slab.capacity() >= 3 && slab.capacity() < 10);
    /// ```
    // T8: `Vec::shrink_to_fit` has no Verus specification. Everything
    // before that call was moved, unchanged, into the verified `remove_vacant_tail`.
    pub fn shrink_to_fit(&mut self) {
        self.remove_vacant_tail();
        self.entries.shrink_to_fit();
    }
}
