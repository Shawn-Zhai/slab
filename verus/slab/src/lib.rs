#![no_std]
#![warn(
    missing_debug_implementations,
    missing_docs,
    rust_2018_idioms,
    unreachable_pub
)]
#![doc(test(
    no_crate_inject,
    attr(deny(warnings, rust_2018_idioms), allow(dead_code, unused_variables))
))]
#![allow(clippy::incompatible_msrv)] // false positive: https://github.com/rust-lang/rust-clippy/issues/12280
#![cfg_attr(docsrs, feature(doc_cfg))]

//! Pre-allocated storage for a uniform data type.
//!
//! `Slab` provides pre-allocated storage for a single data type. If many values
//! of a single type are being allocated, it can be more efficient to
//! pre-allocate the necessary storage. Since the size of the type is uniform,
//! memory fragmentation can be avoided. Storing, clearing, and lookup
//! operations become very cheap.
//!
//! While `Slab` may look like other Rust collections, it is not intended to be
//! used as a general purpose collection. The primary difference between `Slab`
//! and `Vec` is that `Slab` returns the key when storing the value.
//!
//! It is important to note that keys may be reused. In other words, once a
//! value associated with a given key is removed from a slab, that key may be
//! returned from future calls to `insert`.
//!
//! # Performance notes
//!
//! Methods that remove values and return them, such as [`Slab::remove`] and
//! [`Slab::try_remove`], might copy the removed values to the stack even if
//! their return values are unused. For types that don't have drop glue, the
//! compiler can usually elide these copies.
//!
//! # Examples
//!
//! Basic storing and retrieval.
//!
//! ```
//! # use slab::*;
//! let mut slab = Slab::new();
//!
//! let hello = slab.insert("hello");
//! let world = slab.insert("world");
//!
//! assert_eq!(slab[hello], "hello");
//! assert_eq!(slab[world], "world");
//!
//! slab[world] = "earth";
//! assert_eq!(slab[world], "earth");
//! ```
//!
//! Sometimes it is useful to be able to associate the key with the value being
//! inserted in the slab. This can be done with the `vacant_entry` API as such:
//!
//! ```
//! # use slab::*;
//! let mut slab = Slab::new();
//!
//! let hello = {
//!     let entry = slab.vacant_entry();
//!     let key = entry.key();
//!
//!     entry.insert((key, "hello"));
//!     key
//! };
//!
//! assert_eq!(hello, slab[hello].0);
//! assert_eq!("hello", slab[hello].1);
//! ```
//!
//! It is generally a good idea to specify the desired capacity of a slab at
//! creation time. Note that `Slab` will grow the internal capacity when
//! attempting to insert a new value once the existing capacity has been reached.
//! To avoid this, add a check.
//!
//! ```
//! # use slab::*;
//! let mut slab = Slab::with_capacity(1024);
//!
//! // ... use the slab
//!
//! if slab.len() == slab.capacity() {
//!     panic!("slab full");
//! }
//!
//! slab.insert("the slab is not at capacity yet");
//! ```
//!
//! # Capacity and reallocation
//!
//! The capacity of a slab is the amount of space allocated for any future
//! values that will be inserted in the slab. This is not to be confused with
//! the *length* of the slab, which specifies the number of actual values
//! currently being inserted. If a slab's length is equal to its capacity, the
//! next value inserted into the slab will require growing the slab by
//! reallocating.
//!
//! For example, a slab with capacity 10 and length 0 would be an empty slab
//! with space for 10 more stored values. Storing 10 or fewer elements into the
//! slab will not change its capacity or cause reallocation to occur. However,
//! if the slab length is increased to 11 (due to another `insert`), it will
//! have to reallocate, which can be slow. For this reason, it is recommended to
//! use [`Slab::with_capacity`] whenever possible to specify how many values the
//! slab is expected to store.
//!
//! # Implementation
//!
//! `Slab` is backed by a `Vec` of slots. Each slot is either occupied or
//! vacant. `Slab` maintains a stack of vacant slots using a linked list. To
//! find a vacant slot, the stack is popped. When a slot is released, it is
//! pushed onto the stack.
//!
//! If there are no more available slots in the stack, then `Vec::reserve(1)` is
//! called and a new slot is created.
//!
//! [`Slab::with_capacity`]: struct.Slab.html#with_capacity

#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;
#[cfg(feature = "std")]
extern crate std as alloc;

#[cfg(feature = "serde")]
mod serde;

mod builder;

/// Verus specification of `Slab` (ghost code; compiled only under Verus).
#[cfg(verus_keep_ghost)]
pub mod spec;
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::spec::*;

/// Verified clients of the specification (never called; compiled only under Verus).
#[cfg(verus_keep_ghost)]
mod verified_examples;

mod std_ext;
use crate::std_ext::{mem_replace, slice_get_mut, vec_get_mut};

/// The upstream code that Verus does not verify (compiled in every build; Verus skips it).
#[cfg_attr(verus_keep_ghost, verifier::external)]
mod trusted;
pub use crate::trusted::{Drain, IntoIter, IterMut};

use alloc::vec::Vec;
use core::iter::FusedIterator;
use core::ops;
use vstd::pervasive::{runtime_assert, unreached};
#[allow(unused_imports)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // ghost-only: vstd's `std_specs` exist only under Verus
use vstd::std_specs::iter::IteratorSpec;

verus! {

/// Pre-allocated storage for a uniform data type
///
/// See the [module documentation] for more details.
///
/// [module documentation]: index.html
pub struct Slab<T> {
    // Chunk of memory
    entries: Vec<Entry<T>>,

    // Number of Filled elements currently in the slab
    len: usize,

    // Offset of the next available slot in the slab. Set to the slab's
    // capacity when the slab is full.
    next: usize,
}

impl<T> Default for Slab<T> {
    fn default() -> (slab: Self)
        ensures
            slab.wf(),
            slab@ == Seq::<Option<T>>::empty(),
            slab.vacant_list() == Seq::<usize>::empty(),
    {
        Slab::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// The error type returned by [`Slab::get_disjoint_mut`].
pub enum GetDisjointMutError {
    /// An index provided was not associated with a value.
    IndexVacant,

    /// An index provided was out-of-bounds for the slab.
    IndexOutOfBounds,

    /// Two indices provided were overlapping.
    OverlappingIndices,
}

/// A handle to a vacant entry in a `Slab`.
///
/// `VacantEntry` allows constructing values with the key that they will be
/// assigned to.
///
/// # Examples
///
/// ```
/// # use slab::*;
/// let mut slab = Slab::new();
///
/// let hello = {
///     let entry = slab.vacant_entry();
///     let key = entry.key();
///
///     entry.insert((key, "hello"));
///     key
/// };
///
/// assert_eq!(hello, slab[hello].0);
/// assert_eq!("hello", slab[hello].1);
/// ```
#[derive(Debug)]
pub struct VacantEntry<'a, T> {
    slab: &'a mut Slab<T>,
    key: usize,
}

/// An iterator over the values stored in the `Slab`
pub struct Iter<'a, T> {
    // Upstream: `entries: iter::Enumerate<slice::Iter<'a, Entry<T>>>`. Verus specifies neither
    // `Enumerate` nor `slice::Iter::next_back`, so this holds the entries not yet visited, and
    // `front` is the key of the first of them.
    entries: &'a [Entry<T>],
    front: usize,
    len: usize,
}

impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> (r: Self)
        ensures
            r == *self,
    {
        proof {
            use_type_invariant(self);
        }
        // Upstream: `entries: self.entries.clone()`.
        Self {
            entries: self.entries,
            front: self.front,
            len: self.len,
        }
    }
}

#[derive(Clone)]
enum Entry<T> {
    Vacant(usize),
    Occupied(T),
}

impl<T> Slab<T> {
    /// Construct a new, empty `Slab`.
    ///
    /// The function does not allocate and the returned slab will have no
    /// capacity until `insert` is called or capacity is explicitly reserved.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let slab: Slab<i32> = Slab::new();
    /// ```
    pub const fn new() -> (slab: Self)
        ensures
            slab.wf(),
            slab@ == Seq::<Option<T>>::empty(),
            slab.vacant_list() == Seq::<usize>::empty(),
    {
        let slab = Self {
            entries: Vec::new(),
            next: 0,
            len: 0,
        };
        proof {
            slab.lemma_wf_intro(Seq::empty());
        }
        slab
    }

    /// Construct a new, empty `Slab` with the specified capacity.
    ///
    /// The returned slab will be able to store exactly `capacity` without
    /// reallocating. If `capacity` is 0, the slab will not allocate.
    ///
    /// It is important to note that this function does not specify the *length*
    /// of the returned slab, but only the capacity. For an explanation of the
    /// difference between length and capacity, see [Capacity and
    /// reallocation](index.html#capacity-and-reallocation).
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::with_capacity(10);
    ///
    /// // The slab contains no values, even though it has capacity for more
    /// assert_eq!(slab.len(), 0);
    ///
    /// // These are all done without reallocating...
    /// for i in 0..10 {
    ///     slab.insert(i);
    /// }
    ///
    /// // ...but this may make the slab reallocate
    /// slab.insert(11);
    /// ```
    pub fn with_capacity(capacity: usize) -> (slab: Slab<T>)
        ensures
            slab.wf(),
            slab@ == Seq::<Option<T>>::empty(),
            slab.vacant_list() == Seq::<usize>::empty(),
    {
        let slab = Slab {
            entries: Vec::with_capacity(capacity),
            next: 0,
            len: 0,
        };
        proof {
            slab.lemma_wf_intro(Seq::empty());
        }
        slab
    }
}

impl<T> Slab<T> {
    /// The part of `shrink_to_fit` before the reallocation, moved out of it so that Verus can
    /// check it.
    fn remove_vacant_tail(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@ == trim_vacant_tail(old(self)@),
            final(self)@.len() == old(self)@.len() ==> final(self).vacant_list()
                == old(self).vacant_list(),
            final(self)@.len() < old(self)@.len() ==> final(self).vacant_list() == vacant_keys(
                final(self)@,
            ),
    {
        // Remove all vacant entries after the last occupied one, so that
        // the capacity can be reduced to what is actually needed.
        // If the slab is empty the vector can simply be cleared, but that
        // optimization would not affect time complexity when T: Drop.
        let len_before = self.entries.len();
        while matches!(self.entries.last(), Some(Entry::Vacant(_)))
            invariant
                self.entries@.len() <= len_before == old(self).entries@.len(),
                self.entries@ == old(self).entries@.subrange(0, self.entries@.len() as int),
                trim_vacant_tail(self@) == trim_vacant_tail(old(self)@),
                self.len == old(self).len,
                self.next == old(self).next,
            decreases self.entries@.len(),
        {
            proof {
                lemma_view_drop_last(self.entries@);
            }
            self.entries.pop();
        }
        proof {
            lemma_num_occupied_trim(old(self)@);
            if self.entries@.len() == len_before {
                assert(self.entries@ =~= old(self).entries@);
                self.lemma_wf_intro(old(self).vacant_list());
            }
        }

        // Removing entries breaks the list of vacant entries,
        // so it must be repaired
        if self.entries.len() != len_before {
            // Some vacant entries were removed, so the list now likely¹
            // either contains references to the removed entries, or has an
            // invalid end marker. Fix this by recreating the list.
            self.recreate_vacant_list();
            // ¹: If the removed entries formed the tail of the list, with the
            // most recently popped entry being the head of them, (so that its
            // index is now the end marker) the list is still valid.
            // Checking for that unlikely scenario of this infrequently called
            // is not worth the code complexity.
        }
    }

    /// Iterate through all entries to recreate and repair the vacant list.
    /// self.len must be correct and is not modified.
    fn recreate_vacant_list(&mut self)
        requires
            old(self).len == num_occupied(old(self)@),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@,
            final(self).vacant_list() == vacant_keys(old(self)@),
    {
        let ghost slots = self@;
        let ghost n = self.entries@.len() as int;
        proof {
            self.lemma_len_bound();
            lemma_num_occupied_le(slots);
            lemma_vacant_keys_from(slots, 0);
            assert(slots.subrange(0, n) =~= slots);
        }
        self.next = self.entries.len();
        // We can stop once we've found all vacant entries
        let mut remaining_vacant = self.entries.len() - self.len;
        if remaining_vacant == 0 {
            proof {
                lemma_num_occupied_all_some(slots);
                lemma_vacant_keys_from_skip(slots, 0, n);
                assert forall|k: int| 0 <= k < n implies !(#[trigger] self.entries@[k] is Vacant) by {
                    assert(slots[k] is Some);
                }
                self.lemma_wf_intro(Seq::empty());
            }
            return;
        }

        // Iterate in reverse order so that lower keys are at the start of
        // the vacant list. This way future shrinks are more likely to be
        // able to remove vacant entries.
        let mut i = self.entries.len();
        while i > 0
            invariant_except_break
                remaining_vacant > 0,
                remaining_vacant == i - num_occupied(slots.subrange(0, i as int)),
            invariant
                0 <= i <= n <= usize::MAX,
                n == old(self).entries@.len(),
                self.entries@.len() == n,
                self@ == slots,
                slots == old(self)@,
                self.len == old(self).len,
                is_vacant_chain(self.entries@, self.next, vacant_keys_from(slots, i as int)),
            ensures
                is_vacant_chain(self.entries@, self.next, vacant_keys(slots)),
            decreases i,
        {
            i -= 1;
            let ghost entries0 = self.entries@;
            let ghost next0 = self.next;
            proof {
                assert(slots.subrange(0, i + 1).drop_last() =~= slots.subrange(0, i as int));
                lemma_vacant_keys_from(slots, i + 1);
            }
            if let Entry::Vacant(next) = &mut self.entries[i] {
                *next = self.next;
                self.next = i;
                remaining_vacant -= 1;
                proof {
                    let rest = vacant_keys_from(slots, i + 1);
                    assert(slots[i as int] is None);
                    assert(vacant_keys_from(slots, i as int) == seq![i as usize] + rest);
                    assert forall|j: int| 0 <= j < rest.len() implies #[trigger] rest[j] != i by {}
                    lemma_vacant_chain_prepend(entries0, next0, rest, i);
                    assert(self.entries@ == entries0.update(i as int, Entry::Vacant(next0)));
                }
                if remaining_vacant == 0 {
                    proof {
                        let prefix = slots.subrange(0, i as int);
                        lemma_num_occupied_all_some(prefix);
                        assert forall|k: int| 0 <= k < i implies (#[trigger] slots[k]) is Some by {
                            assert(prefix[k] == slots[k]);
                        }
                        lemma_vacant_keys_from_skip(slots, 0, i as int);
                    }
                    break;
                }
            } else {
                proof {
                    assert(slots[i as int] is Some);
                }
            }
        }
        proof {
            let list = vacant_keys(slots);
            assert forall|k: int| 0 <= k < n && (#[trigger] self.entries@[k]) is Vacant implies list.contains(
                k as usize,
            ) by {
                assert(slots[k] is None);
            }
            self.lemma_wf_intro(list);
        }
    }
}

impl<T> Slab<T> {
    /// Clear the slab of all values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// for i in 0..3 {
    ///     slab.insert(i);
    /// }
    ///
    /// slab.clear();
    /// assert!(slab.is_empty());
    /// ```
    pub fn clear(&mut self)
        ensures
            final(self).wf(),
            final(self)@ == Seq::<Option<T>>::empty(),
            final(self).vacant_list() == Seq::<usize>::empty(),
    {
        self.entries.clear();
        self.len = 0;
        self.next = 0;
        proof {
            self.lemma_wf_intro(Seq::empty());
        }
    }

    /// Return the number of stored values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// for i in 0..3 {
    ///     slab.insert(i);
    /// }
    ///
    /// assert_eq!(3, slab.len());
    /// ```
    pub fn len(&self) -> (len: usize)
        requires
            self.wf(),
        ensures
            len == num_occupied(self@),
    {
        self.len
    }

    /// Return `true` if there are no values stored in the slab.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// assert!(slab.is_empty());
    ///
    /// slab.insert(1);
    /// assert!(!slab.is_empty());
    /// ```
    pub fn is_empty(&self) -> (empty: bool)
        requires
            self.wf(),
        ensures
            empty == (num_occupied(self@) == 0),
    {
        self.len == 0
    }

    /// Return an iterator over the slab.
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
    /// for i in 0..3 {
    ///     slab.insert(i);
    /// }
    ///
    /// let mut iterator = slab.iter();
    ///
    /// assert_eq!(iterator.next(), Some((0, &0)));
    /// assert_eq!(iterator.next(), Some((1, &1)));
    /// assert_eq!(iterator.next(), Some((2, &2)));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn iter(&self) -> (it: Iter<'_, T>)
        requires
            self.wf(),
        ensures
            it.remaining() == ref_pairs(occupied_pairs(self@, 0)),
            it.decrease() is Some,
    {
        proof {
            self.lemma_len_bound();
            lemma_occupied_pairs_len(self@, 0);
        }
        // Upstream: `entries: self.entries.iter().enumerate()`.
        Iter {
            entries: self.entries.as_slice(),
            front: 0,
            len: self.len,
        }
    }
}

impl<T> Slab<T> {
    /// Return a reference to the value associated with the given key.
    ///
    /// If the given key is not associated with a value, then `None` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// let key = slab.insert("hello");
    ///
    /// assert_eq!(slab.get(key), Some(&"hello"));
    /// assert_eq!(slab.get(123), None);
    /// ```
    pub fn get(&self, key: usize) -> (value: Option<&T>)
        ensures
            value == if self.spec_contains(key) {
                Some(&self@[key as int]->Some_0)
            } else {
                None::<&T>
            },
    {
        match self.entries.get(key) {
            Some(Entry::Occupied(val)) => Some(val),
            _ => None,
        }
    }

    /// Return a mutable reference to the value associated with the given key.
    ///
    /// If the given key is not associated with a value, then `None` is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// let key = slab.insert("hello");
    ///
    /// *slab.get_mut(key).unwrap() = "world";
    ///
    /// assert_eq!(slab[key], "world");
    /// assert_eq!(slab.get_mut(123), None);
    /// ```
    pub fn get_mut(&mut self, key: usize) -> (value: Option<&mut T>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).vacant_list() == old(self).vacant_list(),
            match value {
                Some(value) => {
                    &&& old(self).spec_contains(key)
                    &&& *value == old(self)@[key as int]->Some_0
                    &&& final(self)@ == old(self)@.update(key as int, Some(*final(value)))
                },
                None => !old(self).spec_contains(key) && final(self)@ == old(self)@,
            },
    {
        proof {
            self.lemma_same_shape_preserves_wf();
        }
        match vec_get_mut(&mut self.entries, key) {
            Some(Entry::Occupied(val)) => Some(val),
            _ => None,
        }
    }

    /// Return two mutable references to the values associated with the two
    /// given keys simultaneously.
    ///
    /// If any one of the given keys is not associated with a value, then `None`
    /// is returned.
    ///
    /// This function can be used to get two mutable references out of one slab,
    /// so that you can manipulate both of them at the same time, eg. swap them.
    ///
    /// # Panics
    ///
    /// This function will panic if `key1` and `key2` are the same.
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
    /// let (value1, value2) = slab.get2_mut(key1, key2).unwrap();
    /// mem::swap(value1, value2);
    /// assert_eq!(slab[key1], 2);
    /// assert_eq!(slab[key2], 1);
    /// ```
    pub fn get2_mut(&mut self, key1: usize, key2: usize) -> (values: Option<(&mut T, &mut T)>)
        requires
            old(self).wf(),
            key1 != key2,
            // `split_at_mut` panics past the end, so the larger key must not exceed the number of slots.
            key1 <= old(self)@.len(),
            key2 <= old(self)@.len(),
        ensures
            final(self).wf(),
            final(self).vacant_list() == old(self).vacant_list(),
            match values {
                Some((value1, value2)) => {
                    &&& old(self).spec_contains(key1)
                    &&& old(self).spec_contains(key2)
                    &&& *value1 == old(self)@[key1 as int]->Some_0
                    &&& *value2 == old(self)@[key2 as int]->Some_0
                    &&& final(self)@ == old(self)@.update(key1 as int, Some(*final(value1))).update(
                        key2 as int,
                        Some(*final(value2)),
                    )
                },
                None => {
                    &&& !(old(self).spec_contains(key1) && old(self).spec_contains(key2))
                    &&& final(self)@ == old(self)@
                },
            },
    {
        runtime_assert(key1 != key2);
        proof {
            self.lemma_same_shape_preserves_wf();
        }

        let (entry1, entry2);

        if key1 > key2 {
            let (slice1, slice2) = self.entries.as_mut_slice().split_at_mut(key1);
            entry1 = slice_get_mut(slice2, 0);
            entry2 = slice_get_mut(slice1, key2);
        } else {
            let (slice1, slice2) = self.entries.as_mut_slice().split_at_mut(key2);
            entry1 = slice_get_mut(slice1, key1);
            entry2 = slice_get_mut(slice2, 0);
        }

        match (entry1, entry2) {
            (Some(Entry::Occupied(val1)), Some(Entry::Occupied(val2))) => Some((val1, val2)),
            _ => None,
        }
    }
}

impl<T> Slab<T> {
    /// Insert a value in the slab, returning key assigned to the value.
    ///
    /// The returned key can later be used to retrieve or remove the value using indexed
    /// lookup and `remove`. Additional capacity is allocated if needed. See
    /// [Capacity and reallocation](index.html#capacity-and-reallocation).
    ///
    /// # Panics
    ///
    /// Panics if the new storage in the vector exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// let key = slab.insert("hello");
    /// assert_eq!(slab[key], "hello");
    /// ```
    pub fn insert(&mut self, val: T) -> (key: usize)
        requires
            old(self).wf(),
        ensures
            Self::insert_post(*old(self), *final(self), key, val),
    {
        let key = self.next;

        self.insert_at(key, val);

        key
    }

    /// Returns the key of the next vacant entry.
    ///
    /// This function returns the key of the vacant entry which  will be used
    /// for the next insertion. This is equivalent to
    /// `slab.vacant_entry().key()`, but it doesn't require mutable access.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    /// assert_eq!(slab.vacant_key(), 0);
    ///
    /// slab.insert(0);
    /// assert_eq!(slab.vacant_key(), 1);
    ///
    /// slab.insert(1);
    /// slab.remove(0);
    /// assert_eq!(slab.vacant_key(), 0);
    /// ```
    pub fn vacant_key(&self) -> (key: usize)
        requires
            self.wf(),
        ensures
            key == self.next_key(),
    {
        self.next
    }

    /// Return a handle to a vacant entry allowing for further manipulation.
    ///
    /// This function is useful when creating values that must contain their
    /// slab key. The returned `VacantEntry` reserves a slot in the slab and is
    /// able to query the associated key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// let hello = {
    ///     let entry = slab.vacant_entry();
    ///     let key = entry.key();
    ///
    ///     entry.insert((key, "hello"));
    ///     key
    /// };
    ///
    /// assert_eq!(hello, slab[hello].0);
    /// assert_eq!("hello", slab[hello].1);
    /// ```
    pub fn vacant_entry(&mut self) -> (entry: VacantEntry<'_, T>)
        requires
            old(self).wf(),
        ensures
            entry.wf(),
            entry.slab() == *old(self),
            entry.final_slab() == *final(self),
            entry.spec_key() == old(self).next_key(),
    {
        VacantEntry {
            key: self.next,
            slab: self,
        }
    }

    fn insert_at(&mut self, key: usize, val: T)
        requires
            old(self).wf(),
            key == old(self).next_key(),
        ensures
            Self::insert_post(*old(self), *final(self), key, val),
    {
        let ghost pre = *self;
        let ghost list = self.vacant_list();
        proof {
            self.lemma_vacant_list();
            if list.len() > 0 {
                lemma_num_occupied_lt(self@, key as int);
                lemma_vacant_list_pop(pre.entries@, pre.next, list, val);
            }
        }
        if key == self.entries.len() {
            self.entries.push(Entry::Occupied(val));
            proof {
                self.lemma_len_bound();
            }
            self.next = key + 1;
        } else {
            self.next = match self.entries.get(key) {
                Some(Entry::Vacant(next)) => *next,
                _ => unreached(),
            };
            self.entries[key] = Entry::Occupied(val);
        }
        // Moved after the branch (upstream increments first): the branch does not read `len`.
        self.len += 1;
        proof {
            if list.len() > 0 {
                lemma_view_update(pre.entries@, key as int, Entry::Occupied(val));
                lemma_num_occupied_update(pre@, key as int, Some(val));
                self.lemma_wf_intro(list.drop_first());
            } else {
                lemma_view_push(pre.entries@, Entry::Occupied(val));
                assert(self@.drop_last() =~= pre@);
                assert forall|k: int|
                    0 <= k < self.entries@.len() implies !(#[trigger] self.entries@[k] is Vacant) by {
                    if k < pre.entries@.len() && pre.entries@[k] is Vacant {
                        assert(list.contains(k as usize));
                    }
                }
                self.lemma_wf_intro(Seq::empty());
            }
        }
    }

    /// Tries to remove the value associated with the given key,
    /// returning the value if the key existed.
    ///
    /// The key is then released and may be associated with future stored
    /// values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// let hello = slab.insert("hello");
    ///
    /// assert_eq!(slab.try_remove(hello), Some("hello"));
    /// assert!(!slab.contains(hello));
    /// ```
    pub fn try_remove(&mut self, key: usize) -> (value: Option<T>)
        requires
            old(self).wf(),
        ensures
            match value {
                Some(value) => Self::remove_post(*old(self), *final(self), key, value),
                None => !old(self).spec_contains(key) && Self::unchanged(*old(self), *final(self)),
            },
    {
        let ghost pre = *self;
        let ghost list = self.vacant_list();
        proof {
            self.lemma_len_bound();
            if self.spec_contains(key) {
                lemma_num_occupied_pos(self@, key as int);
            }
        }
        if let Some(entry) = vec_get_mut(&mut self.entries, key) {
            if let Entry::Occupied(_) = entry {
                // Here we use `std::mem::replace` to move the entry's value to
                // the stack and set the entry as vacant in one shot. By doing
                // this only when the entry is occupied, the compiler should be
                // able to elide copying the bytes to the stack if the value
                // turns out to be unused.

                let val = match mem_replace(entry, Entry::Vacant(self.next)) {
                    Entry::Occupied(val) => val, // confirmed occupied above
                    _ => unreached(),
                };

                self.len -= 1;
                self.next = key;
                proof {
                    lemma_view_update(pre.entries@, key as int, Entry::Vacant(pre.next));
                    lemma_num_occupied_update(pre@, key as int, None);
                    lemma_vacant_list_push(pre.entries@, pre.next, list, key);
                    self.lemma_wf_intro(seq![key] + list);
                }
                return Some(val);
            }
        }
        proof {
            assert(self.entries@ =~= pre.entries@);
            self.lemma_wf_intro(list);
        }
        None
    }

    /// Remove and return the value associated with the given key.
    ///
    /// The key is then released and may be associated with future stored
    /// values.
    ///
    /// # Panics
    ///
    /// Panics if `key` is not associated with a value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// let hello = slab.insert("hello");
    ///
    /// assert_eq!(slab.remove(hello), "hello");
    /// assert!(!slab.contains(hello));
    /// ```
    #[track_caller]
    pub fn remove(&mut self, key: usize) -> (value: T)
        requires
            old(self).wf(),
            old(self).spec_contains(key),
        ensures
            Self::remove_post(*old(self), *final(self), key, value),
    {
        self.try_remove(key).expect("invalid key")
    }

    /// Return `true` if a value is associated with the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// let hello = slab.insert("hello");
    /// assert!(slab.contains(hello));
    ///
    /// slab.remove(hello);
    ///
    /// assert!(!slab.contains(hello));
    /// ```
    pub fn contains(&self, key: usize) -> (contains: bool)
        ensures
            contains == self.spec_contains(key),
    {
        matches!(self.entries.get(key), Some(Entry::Occupied(_)))
    }

    /// Retain only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(usize, &mut e)`
    /// returns false. This method operates in place and preserves the key
    /// associated with the retained values.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// let k1 = slab.insert(0);
    /// let k2 = slab.insert(1);
    /// let k3 = slab.insert(2);
    ///
    /// slab.retain(|key, val| key == k1 || *val == 1);
    ///
    /// assert!(slab.contains(k1));
    /// assert!(slab.contains(k2));
    /// assert!(!slab.contains(k3));
    ///
    /// assert_eq!(2, slab.len());
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(usize, &mut T) -> bool,
        requires
            old(self).wf(),
            forall|key: usize, value: &mut T| f.requires((key, value)),
        ensures
            final(self).wf(),
            final(self)@.len() == old(self)@.len(),
            forall|k: int|
                0 <= k < old(self)@.len() && (#[trigger] old(self)@[k]) is None ==> final(self)@[k] is None,
            forall|k: int|
                #![trigger final(self)@[k]]
                0 <= k < old(self)@.len() && old(self)@[k] is Some ==> retain_step(
                    f,
                    k as usize,
                    old(self)@[k]->Some_0,
                    final(self)@[k],
                ),
            final(self).vacant_list() == removed_keys_desc(
                old(self)@,
                final(self)@,
                old(self)@.len() as int,
            ) + old(self).vacant_list(),
    {
        let ghost f0 = f;
        let ghost pre = *self;
        proof {
            self.lemma_len_bound();
            assert(removed_keys_desc(pre@, self@, 0) + pre.vacant_list() =~= pre.vacant_list());
        }
        for i in iter: 0..self.entries.len()
            invariant
                iter.snapshot.end == pre@.len(),
                f == f0,
                forall|key: usize, value: &mut T| f.requires((key, value)),
                self.wf(),
                self@.len() == pre@.len(),
                forall|k: int| i <= k < pre@.len() ==> (#[trigger] self@[k]) == pre@[k],
                forall|k: int| 0 <= k < i && (#[trigger] pre@[k]) is None ==> self@[k] is None,
                forall|k: int|
                    0 <= k < i && pre@[k] is Some ==> #[trigger] retain_step(
                        f,
                        k as usize,
                        pre@[k]->Some_0,
                        self@[k],
                    ),
                self.vacant_list() == removed_keys_desc(pre@, self@, i as int) + pre.vacant_list(),
        {
            let ghost cur = *self;
            proof {
                self.lemma_len_bound();
                cur.lemma_same_shape_preserves_wf();
            }
            let keep = match self.entries[i] {
                Entry::Occupied(ref mut v) => f(i, v),
                _ => true,
            };
            proof {
                assert(same_shape(cur, *self));
                assert(self.wf() && self.vacant_list() == cur.vacant_list());
            }

            if !keep {
                self.remove(i);
            }
            proof {
                if pre@[i as int] is Some {
                    assert(retain_step(f, i, pre@[i as int]->Some_0, self@[i as int]));
                }
                lemma_removed_keys_desc_prefix(pre@, cur@, self@, i as int);
                if cur@[i as int] is Some && !keep {
                    assert(removed_keys_desc(pre@, self@, i + 1) == seq![i as usize]
                        + removed_keys_desc(pre@, self@, i as int));
                    assert(seq![i as usize] + (removed_keys_desc(pre@, cur@, i as int)
                        + pre.vacant_list()) =~= (seq![i as usize] + removed_keys_desc(
                        pre@,
                        cur@,
                        i as int,
                    )) + pre.vacant_list());
                }
            }
        }
    }
}

#[cfg(verus_keep_ghost)] // ghost-only: vstd's `std_specs` exist only under Verus
impl<T> vstd::std_specs::core::IndexSpecImpl<usize> for Slab<T> {
    /// `slab[key]` requires `key` to be associated with a value (it panics otherwise).
    open spec fn index_req(&self, key: &usize) -> bool {
        self.spec_contains(*key)
    }
}

impl<T> ops::Index<usize> for Slab<T> {
    type Output = T;

    #[track_caller]
    fn index(&self, key: usize) -> (value: &T)
        ensures
            *value == self@[key as int]->Some_0,
    {
        // Upstream: `match self.entries.get(key) { Some(Entry::Occupied(v)) => v, _ => panic!("invalid key") }`.
        self.get(key).expect("invalid key")
    }
}

// `slab[key] = value` has the precondition of `slab[key]` (vstd's `index_req`, above).
impl<T> ops::IndexMut<usize> for Slab<T> {
    #[track_caller]
    fn index_mut(&mut self, key: usize) -> (value: &mut T)
        ensures
            *value == old(self)@[key as int]->Some_0,
            final(self)@ == old(self)@.update(key as int, Some(*final(value))),
            old(self).wf() ==> final(self).wf() && final(self).vacant_list() == old(
                self,
            ).vacant_list(),
    {
        proof {
            if self.wf() {
                self.lemma_same_shape_preserves_wf();
            }
        }
        // Upstream: `match self.entries.get_mut(key) { Some(&mut Entry::Occupied(ref mut v)) => v,
        // _ => panic!("invalid key") }`.
        let value = match vec_get_mut(&mut self.entries, key) {
            Some(Entry::Occupied(v)) => Some(v),
            _ => None,
        };
        value.expect("invalid key")
    }
}

// ===== VacantEntry =====

impl<'a, T> VacantEntry<'a, T> {
    /// Insert a value in the entry, returning a mutable reference to the value.
    ///
    /// To get the key associated with the value, use `key` prior to calling
    /// `insert`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// let hello = {
    ///     let entry = slab.vacant_entry();
    ///     let key = entry.key();
    ///
    ///     entry.insert((key, "hello"));
    ///     key
    /// };
    ///
    /// assert_eq!(hello, slab[hello].0);
    /// assert_eq!("hello", slab[hello].1);
    /// ```
    pub fn insert(self, val: T) -> (value: &'a mut T)
        requires
            self.wf(),
        ensures
            *value == val,
            Slab::insert_post(self.slab(), self.final_slab(), self.spec_key(), *final(value)),
    {
        let ghost pre = *self.slab;
        self.slab.insert_at(self.key, val);
        proof {
            Slab::<T>::lemma_insert_then_set(pre, *self.slab, self.key, val);
        }

        match vec_get_mut(&mut self.slab.entries, self.key) {
            Some(Entry::Occupied(v)) => v,
            _ => unreached(),
        }
    }

    /// Return the key associated with this entry.
    ///
    /// A value stored in this entry will be associated with this key.
    ///
    /// # Examples
    ///
    /// ```
    /// # use slab::*;
    /// let mut slab = Slab::new();
    ///
    /// let hello = {
    ///     let entry = slab.vacant_entry();
    ///     let key = entry.key();
    ///
    ///     entry.insert((key, "hello"));
    ///     key
    /// };
    ///
    /// assert_eq!(hello, slab[hello].0);
    /// assert_eq!("hello", slab[hello].1);
    /// ```
    pub fn key(&self) -> (key: usize)
        ensures
            key == self.spec_key(),
    {
        self.key
    }
}

} // verus!

// ===== Iter =====

verus! {

impl<'a, T> Iter<'a, T> {
    /// `len` counts the items left, and the keys of the entries left fit in a `usize`.
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.front + self.entries@.len() <= usize::MAX
        &&& self.len == iter_items(self.entries@, self.front).len()
    }
}

#[cfg(verus_keep_ghost)] // ghost-only: vstd's `std_specs` exist only under Verus
impl<'a, T> vstd::std_specs::iter::IteratorSpecImpl for Iter<'a, T> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    /// The `(key, &value)` pairs not yet yielded, in increasing key order.
    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        iter_items(self.entries@, self.front)
    }

    #[verifier::prophetic]
    open spec fn will_return_none(&self) -> bool {
        true
    }

    closed spec fn decrease(&self) -> Option<nat> {
        Some(self.entries@.len())
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        None
    }
}

#[cfg(verus_keep_ghost)]
impl<'a, T> vstd::std_specs::iter::DoubleEndedIteratorSpecImpl for Iter<'a, T> {
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        None
    }
}

#[cfg(verus_keep_ghost)]
impl<'a, T> vstd::std_specs::iter::ExactSizeIteratorSpecImpl for Iter<'a, T> {
    closed spec fn exact_len(&self) -> usize {
        self.len
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (usize, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        proof {
            use_type_invariant(&*self);
        }
        // One call updates the fields, so that the type invariant is checked once, after it.
        iter_next(&mut self.entries, &mut self.front, &mut self.len)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<T> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        proof {
            use_type_invariant(&*self);
        }
        iter_next_back(&mut self.entries, self.front, &mut self.len)
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {
    fn len(&self) -> usize {
        proof {
            use_type_invariant(self);
        }
        self.len
    }
}

impl<T> FusedIterator for Iter<'_, T> {}

/// `Iter::next` on the fields of the iterator. Upstream:
/// `for (key, entry) in &mut self.entries { if let Entry::Occupied(ref v) = *entry {
/// self.len -= 1; return Some((key, v)); } } debug_assert_eq!(self.len, 0); None`.
fn iter_next<'a, T>(entries: &mut &'a [Entry<T>], front: &mut usize, len: &mut usize) -> (item:
    Option<(usize, &'a T)>)
    requires
        *old(front) + (*old(entries))@.len() <= usize::MAX,
        *old(len) == iter_items((*old(entries))@, *old(front)).len(),
    ensures
        *final(front) + (*final(entries))@.len() <= usize::MAX,
        ({
            let items = iter_items((*old(entries))@, *old(front));
            let rest = iter_items((*final(entries))@, *final(front));
            &&& *final(len) == rest.len()
            &&& if items.len() > 0 {
                &&& rest == items.drop_first()
                &&& item == Some(items[0])
                &&& (*final(entries))@.len() < (*old(entries))@.len()
            } else {
                rest == items && item is None
            }
        }),
    no_unwind
{
    let ghost items = iter_items((*entries)@, *front);
    loop
        invariant
            *front + (*entries)@.len() <= usize::MAX,
            iter_items((*entries)@, *front) == items,
            *len == items.len(),
            (*entries)@.len() <= (*old(entries))@.len(),
            items == iter_items((*old(entries))@, *old(front)),
        decreases (*entries)@.len(),
    {
        let slice: &'a [Entry<T>] = *entries;
        match slice.split_first() {
            Some((entry, rest)) => {
                proof {
                    lemma_occupied_pairs_drop_first(entries_view(slice@), *front as int);
                    assert(entries_view(slice@).drop_first() =~= entries_view(rest@));
                }
                let key = *front;
                *entries = rest;
                *front += 1;
                if let Entry::Occupied(ref v) = *entry {
                    *len -= 1;
                    proof {
                        assert(items.drop_first() =~= iter_items((*entries)@, *front));
                    }
                    return Some((key, v));
                }
            },
            None => {
                // Upstream: `debug_assert_eq!(self.len, 0)`, which this proves.
                proof {
                    assert(*len == 0);
                }
                return None;
            },
        }
    }
}

/// `Iter::next_back` on the fields of the iterator. Upstream:
/// `while let Some((key, entry)) = self.entries.next_back() { if let Entry::Occupied(ref v) =
/// *entry { self.len -= 1; return Some((key, v)); } } debug_assert_eq!(self.len, 0); None`.
fn iter_next_back<'a, T>(entries: &mut &'a [Entry<T>], front: usize, len: &mut usize) -> (item:
    Option<(usize, &'a T)>)
    requires
        front + (*old(entries))@.len() <= usize::MAX,
        *old(len) == iter_items((*old(entries))@, front).len(),
    ensures
        front + (*final(entries))@.len() <= usize::MAX,
        ({
            let items = iter_items((*old(entries))@, front);
            let rest = iter_items((*final(entries))@, front);
            &&& *final(len) == rest.len()
            &&& if items.len() > 0 {
                &&& rest == items.drop_last()
                &&& item == Some(items.last())
                &&& (*final(entries))@.len() < (*old(entries))@.len()
            } else {
                rest == items && item is None
            }
        }),
    no_unwind
{
    let ghost items = iter_items((*entries)@, front);
    loop
        invariant
            front + (*entries)@.len() <= usize::MAX,
            iter_items((*entries)@, front) == items,
            *len == items.len(),
            (*entries)@.len() <= (*old(entries))@.len(),
            items == iter_items((*old(entries))@, front),
        decreases (*entries)@.len(),
    {
        let slice: &'a [Entry<T>] = *entries;
        let n = slice.len();
        if n == 0 {
            // Upstream: `debug_assert_eq!(self.len, 0)`, which this proves.
            proof {
                assert(*len == 0);
            }
            return None;
        }
        let (rest, last) = slice.split_at(n - 1);
        proof {
            assert(entries_view(slice@).drop_last() =~= entries_view(rest@));
            assert(last@[0] == slice@.last());
        }
        *entries = rest;
        let key = front + (n - 1);
        if let Entry::Occupied(ref v) = last[0] {
            *len -= 1;
            proof {
                assert(items.drop_last() =~= iter_items((*entries)@, front));
            }
            return Some((key, v));
        }
    }
}

} // verus!
