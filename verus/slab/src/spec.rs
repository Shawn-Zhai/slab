//! Specification of `Slab` for Verus (ghost code only; it is erased from normal builds).
//!
//! The contracts in `lib.rs` and `builder.rs` are stated with the definitions below.
//! Nothing here is trusted: every `spec fn` is a definition and every `proof fn` is
//! checked by Verus.
//!
//! The abstract state of a slab has two parts:
//!
//! * `slab@`, a `Seq<Option<T>>` of slots indexed by key (`Some(value)` when the key is
//!   occupied, `None` when it is vacant), and
//! * `slab.vacant_list()`, the vacant keys in the order in which `insert` reuses them.
//!
//! The internal invariant `slab.wf()` relates the private fields to that state.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::{Entry, Slab, VacantEntry};

verus! {

// =============================================================================== slots

/// The abstract value of a slot: `Some(value)` if it is occupied, `None` if it is vacant.
pub(crate) open spec fn entry_view<T>(entry: Entry<T>) -> Option<T> {
    match entry {
        Entry::Occupied(value) => Some(value),
        Entry::Vacant(_) => None,
    }
}

/// The slots stored in a vector of entries.
pub(crate) open spec fn entries_view<T>(entries: Seq<Entry<T>>) -> Seq<Option<T>> {
    entries.map_values(|entry: Entry<T>| entry_view(entry))
}

impl<T> View for Slab<T> {
    /// The slots of the slab, indexed by key.
    type V = Seq<Option<T>>;

    open(crate) spec fn view(&self) -> Seq<Option<T>> {
        entries_view(self.entries@)
    }
}

/// The number of occupied slots.
pub open spec fn num_occupied<T>(slots: Seq<Option<T>>) -> nat
    decreases slots.len(),
{
    if slots.len() == 0 {
        0
    } else {
        num_occupied(slots.drop_last()) + if slots.last() is Some {
            1nat
        } else {
            0nat
        }
    }
}

/// The vacant keys of `slots[lo..]`, in increasing order.
pub open spec fn vacant_keys_from<T>(slots: Seq<Option<T>>, lo: int) -> Seq<usize>
    decreases slots.len() - lo,
{
    if lo < 0 || lo >= slots.len() {
        Seq::empty()
    } else if slots[lo] is None {
        seq![lo as usize] + vacant_keys_from(slots, lo + 1)
    } else {
        vacant_keys_from(slots, lo + 1)
    }
}

/// All vacant keys of `slots`, in increasing order.
pub open spec fn vacant_keys<T>(slots: Seq<Option<T>>) -> Seq<usize> {
    vacant_keys_from(slots, 0)
}

/// `slots` without its trailing vacant slots.
pub open spec fn trim_vacant_tail<T>(slots: Seq<Option<T>>) -> Seq<Option<T>>
    decreases slots.len(),
{
    if slots.len() > 0 && slots.last() is None {
        trim_vacant_tail(slots.drop_last())
    } else {
        slots
    }
}

// ========================================================================= vacant list

/// `list` is the vacant list threaded through `entries` from `next`: `next` is its head
/// (the end marker `entries.len()` when the list is empty), each listed entry is vacant and
/// links to the next one (the last one to the end marker).
pub(crate) open spec fn is_vacant_chain<T>(
    entries: Seq<Entry<T>>,
    next: usize,
    list: Seq<usize>,
) -> bool {
    &&& next == if list.len() == 0 {
        entries.len() as usize
    } else {
        list[0]
    }
    &&& forall|i: int| 0 <= i < list.len() ==> (#[trigger] list[i] as int) < entries.len()
    &&& forall|i: int|
        #![trigger entries[list[i] as int]]
        0 <= i < list.len() ==> entries[list[i] as int] == Entry::<T>::Vacant(
            if i + 1 < list.len() {
                list[i + 1]
            } else {
                entries.len() as usize
            },
        )
}

/// A vacant chain that, in addition, lists every vacant entry exactly once.
pub(crate) open spec fn is_vacant_list<T>(
    entries: Seq<Entry<T>>,
    next: usize,
    list: Seq<usize>,
) -> bool {
    &&& is_vacant_chain(entries, next, list)
    &&& list.no_duplicates()
    &&& forall|k: int|
        0 <= k < entries.len() && (#[trigger] entries[k]) is Vacant ==> list.contains(k as usize)
}

impl<T> Slab<T> {
    /// The vacant list: the vacant keys, in the order in which `insert` will reuse them.
    pub open(crate) spec fn vacant_list(&self) -> Seq<usize> {
        choose|list: Seq<usize>| is_vacant_list(self.entries@, self.next, list)
    }

    /// The invariant of `Slab`: `len` counts the occupied slots and `next` heads the vacant
    /// list (see `is_vacant_list`).
    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.len == num_occupied(self@)
        &&& is_vacant_list(self.entries@, self.next, self.vacant_list())
    }

    /// The key that the next insertion will use: the head of the vacant list, or the end of
    /// the slab when no slot is vacant.
    pub open spec fn next_key(&self) -> usize {
        if self.vacant_list().len() > 0 {
            self.vacant_list()[0]
        } else {
            self@.len() as usize
        }
    }

    /// `key` is associated with a value.
    pub open spec fn spec_contains(&self, key: usize) -> bool {
        key < self@.len() && self@[key as int] is Some
    }

    /// `post` is `pre` after storing `value` under `key`, the key that `insert` picks: the head
    /// of the vacant list is reused, and the slab grows by one slot only if no slot is vacant.
    pub open spec fn insert_post(pre: Self, post: Self, key: usize, value: T) -> bool {
        &&& post.wf()
        &&& key == pre.next_key()
        &&& if pre.vacant_list().len() > 0 {
            &&& post@ == pre@.update(key as int, Some(value))
            &&& post.vacant_list() == pre.vacant_list().drop_first()
        } else {
            &&& post@ == pre@.push(Some(value))
            &&& post.vacant_list() == Seq::<usize>::empty()
        }
    }

    /// `post` is `pre` after removing `value`, which was stored under `key`; the freed key
    /// becomes the head of the vacant list.
    pub open spec fn remove_post(pre: Self, post: Self, key: usize, value: T) -> bool {
        &&& post.wf()
        &&& pre.spec_contains(key)
        &&& value == pre@[key as int]->Some_0
        &&& post@ == pre@.update(key as int, None)
        &&& post.vacant_list() == seq![key] + pre.vacant_list()
    }

    /// `post` has the same abstract state as `pre`.
    pub open spec fn unchanged(pre: Self, post: Self) -> bool {
        &&& post.wf()
        &&& post@ == pre@
        &&& post.vacant_list() == pre.vacant_list()
    }

    /// Facts about the vacant list that clients may need.
    pub proof fn lemma_vacant_list(&self)
        requires
            self.wf(),
        ensures
            self@.len() <= usize::MAX,
            self.vacant_list().no_duplicates(),
            forall|i: int|
                #![trigger self.vacant_list()[i]]
                0 <= i < self.vacant_list().len() ==> {
                    &&& (self.vacant_list()[i] as int) < self@.len()
                    &&& self@[self.vacant_list()[i] as int] is None
                },
            forall|k: int|
                0 <= k < self@.len() && (#[trigger] self@[k]) is None ==> self.vacant_list().contains(
                    k as usize,
                ),
            num_occupied(self@) <= self@.len(),
            self.vacant_list().len() == 0 <==> num_occupied(self@) == self@.len(),
    {
        self.lemma_len_bound();
        let list = self.vacant_list();
        assert forall|i: int| #![trigger list[i]] 0 <= i < list.len() implies {
            &&& (list[i] as int) < self@.len()
            &&& self@[list[i] as int] is None
        } by {}
        assert forall|k: int| 0 <= k < self@.len() && (#[trigger] self@[k]) is None implies list.contains(
            k as usize,
        ) by {
            assert(self.entries@[k] is Vacant);
        }
        lemma_num_occupied_le(self@);
        if list.len() == 0 {
            assert forall|k: int| 0 <= k < self@.len() implies self@[k] is Some by {
                if self@[k] is None {
                    assert(self.entries@[k] is Vacant);
                }
            }
            lemma_num_occupied_all_some(self@);
        } else {
            lemma_num_occupied_lt(self@, list[0] as int);
        }
    }

    /// The number of slots fits in a `usize` (it is the length of a `Vec`).
    pub(crate) proof fn lemma_len_bound(&self)
        ensures
            self@.len() <= usize::MAX,
            self@.len() == self.entries@.len(),
    {
        assert(self.entries@.len() == self.entries.len());
    }

    /// Establishes the invariant from a concrete vacant list, which is then *the* vacant list.
    pub(crate) proof fn lemma_wf_intro(&self, list: Seq<usize>)
        requires
            self.len == num_occupied(self@),
            is_vacant_list(self.entries@, self.next, list),
        ensures
            self.wf(),
            self.vacant_list() == list,
    {
        self.lemma_len_bound();
        let chosen = self.vacant_list();
        assert(is_vacant_list(self.entries@, self.next, chosen));
        lemma_vacant_chain_unique(self.entries@, self.next, chosen, list);
    }
}

/// The vacant chain from `next` is determined by `entries` and `next`.
pub(crate) proof fn lemma_vacant_chain_unique<T>(
    entries: Seq<Entry<T>>,
    next: usize,
    l1: Seq<usize>,
    l2: Seq<usize>,
)
    requires
        entries.len() <= usize::MAX,
        is_vacant_chain(entries, next, l1),
        is_vacant_chain(entries, next, l2),
    ensures
        l1 == l2,
{
    assert forall|i: int| 0 <= i < l1.len() && i < l2.len() implies l1[i] == l2[i] by {
        lemma_vacant_chain_agree(entries, next, l1, l2, i);
    }
    if l1.len() < l2.len() {
        lemma_vacant_chain_too_short(entries, next, l1, l2);
    } else if l2.len() < l1.len() {
        lemma_vacant_chain_too_short(entries, next, l2, l1);
    }
    assert(l1 =~= l2);
}

proof fn lemma_vacant_chain_agree<T>(
    entries: Seq<Entry<T>>,
    next: usize,
    l1: Seq<usize>,
    l2: Seq<usize>,
    i: int,
)
    requires
        is_vacant_chain(entries, next, l1),
        is_vacant_chain(entries, next, l2),
        0 <= i < l1.len(),
        i < l2.len(),
    ensures
        l1[i] == l2[i],
    decreases i,
{
    if i > 0 {
        lemma_vacant_chain_agree(entries, next, l1, l2, i - 1);
        assert(entries[l1[i - 1] as int] == Entry::<T>::Vacant(l1[i]));
        assert(entries[l2[i - 1] as int] == Entry::<T>::Vacant(l2[i]));
    }
}

/// A vacant chain cannot be a proper prefix of another one.
proof fn lemma_vacant_chain_too_short<T>(
    entries: Seq<Entry<T>>,
    next: usize,
    short: Seq<usize>,
    long: Seq<usize>,
)
    requires
        entries.len() <= usize::MAX,
        is_vacant_chain(entries, next, short),
        is_vacant_chain(entries, next, long),
        short.len() < long.len(),
    ensures
        false,
{
    if short.len() == 0 {
        assert((long[0] as int) < entries.len());
    } else {
        let i = short.len() - 1;
        lemma_vacant_chain_agree(entries, next, short, long, i);
        assert(entries[short[i] as int] == Entry::<T>::Vacant(entries.len() as usize));
        assert(entries[long[i] as int] == Entry::<T>::Vacant(long[i + 1]));
        assert((long[i + 1] as int) < entries.len());
    }
}

/// Linking a vacant entry `key` (not yet on the chain) in front of the chain.
pub(crate) proof fn lemma_vacant_chain_prepend<T>(
    entries: Seq<Entry<T>>,
    next: usize,
    list: Seq<usize>,
    key: usize,
)
    requires
        is_vacant_chain(entries, next, list),
        (key as int) < entries.len(),
        forall|j: int| 0 <= j < list.len() ==> #[trigger] list[j] != key,
    ensures
        is_vacant_chain(entries.update(key as int, Entry::Vacant(next)), key, seq![key] + list),
{
    let e2 = entries.update(key as int, Entry::Vacant(next));
    let l2 = seq![key] + list;
    assert forall|i: int| #![trigger l2[i]] 0 <= i < l2.len() implies {
        &&& (l2[i] as int) < e2.len()
        &&& e2[l2[i] as int] == Entry::<T>::Vacant(
            if i + 1 < l2.len() {
                l2[i + 1]
            } else {
                e2.len() as usize
            },
        )
    } by {
        if i > 0 {
            assert(l2[i] == list[i - 1]);
            assert(list[i - 1] != key);
        }
    }
}

/// `insert` at the head of the vacant list: the head becomes occupied and its link the new head.
pub(crate) proof fn lemma_vacant_list_pop<T>(
    entries: Seq<Entry<T>>,
    next: usize,
    list: Seq<usize>,
    value: T,
)
    requires
        entries.len() <= usize::MAX,
        is_vacant_list(entries, next, list),
        list.len() > 0,
    ensures
        entries[list[0] as int] is Vacant,
        is_vacant_list(
            entries.update(list[0] as int, Entry::Occupied(value)),
            entries[list[0] as int]->Vacant_0,
            list.drop_first(),
        ),
{
    let key = list[0];
    let e2 = entries.update(key as int, Entry::Occupied(value));
    let rest = list.drop_first();
    assert(entries[key as int] is Vacant);
    assert forall|i: int| #![trigger rest[i]] 0 <= i < rest.len() implies {
        &&& (rest[i] as int) < e2.len()
        &&& e2[rest[i] as int] == Entry::<T>::Vacant(
            if i + 1 < rest.len() {
                rest[i + 1]
            } else {
                e2.len() as usize
            },
        )
    } by {
        assert(rest[i] == list[i + 1]);
        assert(list[i + 1] != list[0]);
    }
    assert forall|k: int| 0 <= k < e2.len() && (#[trigger] e2[k]) is Vacant implies rest.contains(
        k as usize,
    ) by {
        assert(entries[k] is Vacant);
        let j = choose|j: int| 0 <= j < list.len() && list[j] == k as usize;
        assert(j != 0);
        assert(rest[j - 1] == k as usize);
    }
}

/// `try_remove`: the freed entry links to the old head and becomes the new head.
pub(crate) proof fn lemma_vacant_list_push<T>(
    entries: Seq<Entry<T>>,
    next: usize,
    list: Seq<usize>,
    key: usize,
)
    requires
        entries.len() <= usize::MAX,
        is_vacant_list(entries, next, list),
        (key as int) < entries.len(),
        entries[key as int] is Occupied,
    ensures
        is_vacant_list(entries.update(key as int, Entry::Vacant(next)), key, seq![key] + list),
{
    let e2 = entries.update(key as int, Entry::Vacant(next));
    let l2 = seq![key] + list;
    assert forall|j: int| 0 <= j < list.len() implies #[trigger] list[j] != key by {
        assert(entries[list[j] as int] is Vacant);
    }
    lemma_vacant_chain_prepend(entries, next, list, key);
    assert forall|a: int, b: int| 0 <= a < l2.len() && 0 <= b < l2.len() && a != b implies l2[a]
        != l2[b] by {
        if a > 0 {
            assert(l2[a] == list[a - 1]);
        }
        if b > 0 {
            assert(l2[b] == list[b - 1]);
        }
    }
    assert forall|k: int| 0 <= k < e2.len() && (#[trigger] e2[k]) is Vacant implies l2.contains(
        k as usize,
    ) by {
        if k == key {
            assert(l2[0] == key);
        } else {
            assert(entries[k] is Vacant);
            let j = choose|j: int| 0 <= j < list.len() && list[j] == k as usize;
            assert(l2[j + 1] == k as usize);
        }
    }
}

/// Replacing the value of an occupied entry keeps the vacant list.
pub(crate) proof fn lemma_vacant_list_set_occupied<T>(
    entries: Seq<Entry<T>>,
    next: usize,
    list: Seq<usize>,
    key: int,
    value: T,
)
    requires
        entries.len() <= usize::MAX,
        is_vacant_list(entries, next, list),
        0 <= key < entries.len(),
        entries[key] is Occupied,
    ensures
        is_vacant_list(entries.update(key, Entry::Occupied(value)), next, list),
{
    let e2 = entries.update(key, Entry::Occupied(value));
    assert forall|i: int| #![trigger list[i]] 0 <= i < list.len() implies list[i] != key by {
        assert(entries[list[i] as int] is Vacant);
    }
    assert forall|k: int| 0 <= k < e2.len() && (#[trigger] e2[k]) is Vacant implies list.contains(
        k as usize,
    ) by {
        assert(entries[k] is Vacant);
    }
}

// ============================================================================== views

/// The slots after changing one entry.
pub(crate) proof fn lemma_view_update<T>(entries: Seq<Entry<T>>, k: int, entry: Entry<T>)
    requires
        0 <= k < entries.len(),
    ensures
        entries_view(entries.update(k, entry)) == entries_view(entries).update(k, entry_view(entry)),
{
    assert(entries_view(entries.update(k, entry)) =~= entries_view(entries).update(
        k,
        entry_view(entry),
    ));
}

/// The slots after appending an entry.
pub(crate) proof fn lemma_view_push<T>(entries: Seq<Entry<T>>, entry: Entry<T>)
    ensures
        entries_view(entries.push(entry)) == entries_view(entries).push(entry_view(entry)),
{
    assert(entries_view(entries.push(entry)) =~= entries_view(entries).push(entry_view(entry)));
}

/// The slots after removing the last entry.
pub(crate) proof fn lemma_view_drop_last<T>(entries: Seq<Entry<T>>)
    requires
        entries.len() > 0,
    ensures
        entries_view(entries.drop_last()) == entries_view(entries).drop_last(),
{
    assert(entries_view(entries.drop_last()) =~= entries_view(entries).drop_last());
}

// ===================================================================== occupied count

/// The count is at most the number of slots.
pub proof fn lemma_num_occupied_le<T>(slots: Seq<Option<T>>)
    ensures
        num_occupied(slots) <= slots.len(),
    decreases slots.len(),
{
    if slots.len() > 0 {
        lemma_num_occupied_le(slots.drop_last());
    }
}

/// Changing one slot changes the count by at most one.
pub proof fn lemma_num_occupied_update<T>(slots: Seq<Option<T>>, k: int, slot: Option<T>)
    requires
        0 <= k < slots.len(),
    ensures
        num_occupied(slots.update(k, slot)) + (if slots[k] is Some {
            1int
        } else {
            0int
        }) == num_occupied(slots) + (if slot is Some {
            1int
        } else {
            0int
        }),
    decreases slots.len(),
{
    let s2 = slots.update(k, slot);
    if k == slots.len() - 1 {
        assert(s2.drop_last() =~= slots.drop_last());
    } else {
        lemma_num_occupied_update(slots.drop_last(), k, slot);
        assert(s2.drop_last() =~= slots.drop_last().update(k, slot));
    }
}

/// A vacant slot leaves room in the count.
pub proof fn lemma_num_occupied_lt<T>(slots: Seq<Option<T>>, k: int)
    requires
        0 <= k < slots.len(),
        slots[k] is None,
    ensures
        num_occupied(slots) < slots.len(),
{
    lemma_num_occupied_update(slots, k, Some(arbitrary()));
    lemma_num_occupied_le(slots.update(k, Some(arbitrary())));
}

/// An occupied slot is counted.
pub proof fn lemma_num_occupied_pos<T>(slots: Seq<Option<T>>, k: int)
    requires
        0 <= k < slots.len(),
        slots[k] is Some,
    ensures
        num_occupied(slots) > 0,
{
    lemma_num_occupied_update(slots, k, None);
}

/// When every slot is occupied, every slot is counted, and conversely.
pub proof fn lemma_num_occupied_all_some<T>(slots: Seq<Option<T>>)
    ensures
        (forall|k: int| 0 <= k < slots.len() ==> (#[trigger] slots[k]) is Some) <==> num_occupied(
            slots,
        ) == slots.len(),
    decreases slots.len(),
{
    if slots.len() > 0 {
        let init = slots.drop_last();
        lemma_num_occupied_all_some(init);
        lemma_num_occupied_le(init);
        if forall|k: int| 0 <= k < slots.len() ==> (#[trigger] slots[k]) is Some {
            assert forall|k: int| 0 <= k < init.len() implies (#[trigger] init[k]) is Some by {
                assert(slots[k] is Some);
            }
        }
        if num_occupied(slots) == slots.len() {
            assert forall|k: int| 0 <= k < slots.len() implies (#[trigger] slots[k]) is Some by {
                if k < init.len() {
                    assert(init[k] is Some);
                }
            }
        }
    }
}

// ======================================================================== vacant keys

/// The keys listed by `vacant_keys_from(slots, lo)`: vacant, increasing, at least `lo`, and all
/// of the vacant keys from `lo` on.
pub proof fn lemma_vacant_keys_from<T>(slots: Seq<Option<T>>, lo: int)
    requires
        0 <= lo <= slots.len(),
        slots.len() <= usize::MAX + 1,
    ensures
        ({
            let keys = vacant_keys_from(slots, lo);
            &&& forall|i: int|
                #![trigger keys[i]]
                0 <= i < keys.len() ==> {
                    &&& lo <= keys[i] < slots.len()
                    &&& slots[keys[i] as int] is None
                }
            &&& forall|i: int, j: int| 0 <= i < j < keys.len() ==> keys[i] < keys[j]
            &&& forall|k: int|
                lo <= k < slots.len() && (#[trigger] slots[k]) is None ==> keys.contains(k as usize)
            &&& keys.no_duplicates()
        }),
    decreases slots.len() - lo,
{
    if lo < slots.len() {
        lemma_vacant_keys_from(slots, lo + 1);
        let rest = vacant_keys_from(slots, lo + 1);
        let keys = vacant_keys_from(slots, lo);
        if slots[lo] is None {
            assert forall|k: int| lo <= k < slots.len() && (#[trigger] slots[k]) is None implies keys.contains(
                k as usize,
            ) by {
                if k == lo {
                    assert(keys[0] == k);
                } else {
                    assert(rest.contains(k as usize));
                    let j = choose|j: int| 0 <= j < rest.len() && rest[j] == k as usize;
                    assert(keys[j + 1] == k);
                }
            }
        }
    }
}

/// No vacant key in `slots[lo..hi]` means the vacant keys from `lo` are those from `hi`.
pub proof fn lemma_vacant_keys_from_skip<T>(slots: Seq<Option<T>>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= slots.len(),
        forall|k: int| lo <= k < hi ==> (#[trigger] slots[k]) is Some,
    ensures
        vacant_keys_from(slots, lo) == vacant_keys_from(slots, hi),
    decreases hi - lo,
{
    if lo < hi {
        assert(slots[lo] is Some);
        lemma_vacant_keys_from_skip(slots, lo + 1, hi);
    }
}

/// Appending a slot appends its key if it is vacant.
pub proof fn lemma_vacant_keys_from_push<T>(slots: Seq<Option<T>>, slot: Option<T>, lo: int)
    requires
        0 <= lo <= slots.len(),
    ensures
        vacant_keys_from(slots.push(slot), lo) == if slot is None {
            vacant_keys_from(slots, lo).push(slots.len() as usize)
        } else {
            vacant_keys_from(slots, lo)
        },
    decreases slots.len() - lo,
{
    let s2 = slots.push(slot);
    if lo < slots.len() {
        lemma_vacant_keys_from_push(slots, slot, lo + 1);
        assert(s2[lo] == slots[lo]);
        if slots[lo] is None {
            let rest = vacant_keys_from(slots, lo + 1);
            if slot is None {
                assert(seq![lo as usize] + rest.push(slots.len() as usize) =~= (seq![lo as usize]
                    + rest).push(slots.len() as usize));
            }
        }
    } else {
        assert(vacant_keys_from(slots, lo) =~= Seq::<usize>::empty());
        assert(vacant_keys_from(s2, lo + 1) =~= Seq::<usize>::empty());
        if slot is None {
            assert(seq![lo as usize] + Seq::<usize>::empty() =~= Seq::<usize>::empty().push(
                slots.len() as usize,
            ));
        }
    }
}

/// The vacant keys only depend on which slots are vacant.
pub proof fn lemma_vacant_keys_from_same_pattern<T>(s1: Seq<Option<T>>, s2: Seq<Option<T>>, lo: int)
    requires
        s1.len() == s2.len(),
        forall|k: int| 0 <= k < s1.len() ==> ((#[trigger] s1[k]) is None <==> s2[k] is None),
    ensures
        vacant_keys_from(s1, lo) == vacant_keys_from(s2, lo),
    decreases s1.len() - lo,
{
    if 0 <= lo < s1.len() {
        lemma_vacant_keys_from_same_pattern(s1, s2, lo + 1);
    }
}

// ===================================================================== trailing vacancy

/// Removing vacant slots does not change the count.
pub proof fn lemma_num_occupied_trim<T>(slots: Seq<Option<T>>)
    ensures
        num_occupied(trim_vacant_tail(slots)) == num_occupied(slots),
    decreases slots.len(),
{
    if slots.len() > 0 && slots.last() is None {
        lemma_num_occupied_trim(slots.drop_last());
    }
}

/// The count only depends on which slots are occupied.
pub proof fn lemma_num_occupied_same_pattern<T>(s1: Seq<Option<T>>, s2: Seq<Option<T>>)
    requires
        s1.len() == s2.len(),
        forall|k: int| 0 <= k < s1.len() ==> ((#[trigger] s1[k]) is Some <==> s2[k] is Some),
    ensures
        num_occupied(s1) == num_occupied(s2),
    decreases s1.len(),
{
    if s1.len() > 0 {
        let (t1, t2) = (s1.drop_last(), s2.drop_last());
        assert forall|k: int| 0 <= k < t1.len() implies ((#[trigger] t1[k]) is Some <==> t2[k] is Some) by {
            assert(s1[k] is Some <==> s2[k] is Some);
        }
        lemma_num_occupied_same_pattern(t1, t2);
        assert(s1.last() is Some <==> s2.last() is Some);
    }
}

// ================================================================ in-place value updates

/// `s` differs from `t` at most in the values held by occupied entries.
pub(crate) open spec fn same_shape<T>(t: Slab<T>, s: Slab<T>) -> bool {
    &&& s.len == t.len
    &&& s.next == t.next
    &&& s.entries@.len() == t.entries@.len()
    &&& forall|k: int|
        0 <= k < t.entries@.len() ==> {
            &&& ((#[trigger] t.entries@[k]) is Vacant ==> s.entries@[k] == t.entries@[k])
            &&& (t.entries@[k] is Occupied ==> s.entries@[k] is Occupied)
        }
}

impl<T> Slab<T> {
    /// A slab that differs from a well-formed one only in the values of occupied entries is
    /// well formed and has the same vacant list. (Stated for all such slabs, so that it applies
    /// to the final value of a slab borrowed through a returned `&mut T`.)
    pub(crate) proof fn lemma_same_shape_preserves_wf(&self)
        requires
            self.wf(),
        ensures
            forall|s: Slab<T>|
                #![trigger s.wf()]
                #![trigger s.vacant_list()]
                same_shape(*self, s) ==> s.wf() && s.vacant_list() == self.vacant_list(),
    {
        assert forall|s: Slab<T>|
            #![trigger s.wf()]
            #![trigger s.vacant_list()]
            same_shape(*self, s) implies s.wf() && s.vacant_list() == self.vacant_list() by {
            let list = self.vacant_list();
            self.lemma_len_bound();
            s.lemma_len_bound();
            assert forall|i: int| #![trigger list[i]] 0 <= i < list.len() implies {
                &&& (list[i] as int) < s.entries@.len()
                &&& s.entries@[list[i] as int] == Entry::<T>::Vacant(
                    if i + 1 < list.len() {
                        list[i + 1]
                    } else {
                        s.entries@.len() as usize
                    },
                )
            } by {
                assert(self.entries@[list[i] as int] is Vacant);
            }
            assert forall|k: int|
                0 <= k < s.entries@.len() && (#[trigger] s.entries@[k]) is Vacant implies list.contains(
                k as usize,
            ) by {
                assert(self.entries@[k] is Vacant);
            }
            assert forall|k: int| 0 <= k < self@.len() implies ((#[trigger] self@[k]) is Some <==> s@[k] is Some) by {
                assert(self.entries@[k] is Occupied <==> s.entries@[k] is Occupied);
            }
            lemma_num_occupied_same_pattern(self@, s@);
            s.lemma_wf_intro(list);
        }
    }

    /// After `insert_post(pre, mid, key, val)`, overwriting the new value with `x` gives
    /// `insert_post(pre, s, key, x)`. (Stated for all such `s` and `x`, as above.)
    pub(crate) proof fn lemma_insert_then_set(pre: Self, mid: Self, key: usize, val: T)
        requires
            pre.wf(),
            Self::insert_post(pre, mid, key, val),
        ensures
            (key as int) < mid.entries@.len(),
            mid.entries@[key as int] == Entry::Occupied(val),
            forall|s: Self, x: T|
                #![trigger Self::insert_post(pre, s, key, x)]
                s.len == mid.len && s.next == mid.next && s.entries@ == mid.entries@.update(
                    key as int,
                    Entry::Occupied(x),
                ) ==> Self::insert_post(pre, s, key, x),
    {
        pre.lemma_vacant_list();
        mid.lemma_len_bound();
        if pre.vacant_list().len() > 0 {
            assert((pre.vacant_list()[0] as int) < pre@.len());
        }
        assert(mid@[key as int] == Some(val));
        assert(mid.entries@[key as int] is Occupied);
        mid.lemma_same_shape_preserves_wf();
        assert forall|s: Self, x: T|
            #![trigger Self::insert_post(pre, s, key, x)]
            s.len == mid.len && s.next == mid.next && s.entries@ == mid.entries@.update(
                key as int,
                Entry::Occupied(x),
            ) implies Self::insert_post(pre, s, key, x) by {
            assert(same_shape(mid, s));
            lemma_view_update(mid.entries@, key as int, Entry::Occupied(x));
            if pre.vacant_list().len() > 0 {
                assert(s@ =~= pre@.update(key as int, Some(x)));
            } else {
                assert(s@ =~= pre@.push(Some(x)));
            }
        }
    }
}

// =========================================================================== VacantEntry

impl<'a, T> VacantEntry<'a, T> {
    /// The key under which the entry will store its value.
    pub open(crate) spec fn spec_key(&self) -> usize {
        self.key
    }

    /// The slab, as it is now.
    pub open(crate) spec fn slab(&self) -> Slab<T> {
        *self.slab
    }

    /// The slab as it will be when the entry, and the reference returned by `insert`, are gone.
    #[verifier::prophetic]
    pub open(crate) spec fn final_slab(&self) -> Slab<T> {
        *final(self.slab)
    }

    /// The entry's invariant: the slab is well formed and `key` is the key it will use next.
    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.slab().wf()
        &&& self.key == self.slab().next_key()
    }
}

// ================================================================================ retain

/// `f` was called with `key` and a reference to `value`, and `slot` is what the slot holds
/// afterwards: the value as `f` left it if `f` returned `true`, nothing if it returned `false`.
#[verifier::prophetic]
pub open spec fn retain_step<T, F: FnMut(usize, &mut T) -> bool>(
    f: F,
    key: usize,
    value: T,
    slot: Option<T>,
) -> bool {
    exists|v: &mut T, keep: bool|
        #![trigger f.ensures((key, v), keep)]
        *v == value && f.ensures((key, v), keep) && slot == if keep {
            Some(*final(v))
        } else {
            None
        }
}

/// The keys below `n` that are occupied in `pre` and vacant in `post`, in decreasing order.
pub open spec fn removed_keys_desc<T>(pre: Seq<Option<T>>, post: Seq<Option<T>>, n: int) -> Seq<
    usize,
>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else if pre[n - 1] is Some && post[n - 1] is None {
        seq![(n - 1) as usize] + removed_keys_desc(pre, post, n - 1)
    } else {
        removed_keys_desc(pre, post, n - 1)
    }
}

/// `removed_keys_desc` only looks at the slots below `n`.
pub proof fn lemma_removed_keys_desc_prefix<T>(
    pre: Seq<Option<T>>,
    s1: Seq<Option<T>>,
    s2: Seq<Option<T>>,
    n: int,
)
    requires
        forall|k: int| 0 <= k < n ==> ((#[trigger] s1[k]) is None <==> s2[k] is None),
    ensures
        removed_keys_desc(pre, s1, n) == removed_keys_desc(pre, s2, n),
    decreases n,
{
    if n > 0 {
        assert(s1[n - 1] is None <==> s2[n - 1] is None);
        lemma_removed_keys_desc_prefix(pre, s1, s2, n - 1);
    }
}

// ============================================================================== iterators

/// The occupied slots of `slots` as `(key, value)` pairs in increasing key order, when the first
/// slot has key `key`. `slab.iter()` yields `ref_pairs(occupied_pairs(slab@, 0))`.
pub open spec fn occupied_pairs<T>(slots: Seq<Option<T>>, key: int) -> Seq<(usize, T)>
    decreases slots.len(),
{
    if slots.len() == 0 {
        Seq::empty()
    } else {
        occupied_pairs(slots.drop_last(), key) + match slots.last() {
            Some(value) => seq![((key + slots.len() - 1) as usize, value)],
            None => Seq::empty(),
        }
    }
}

/// The pairs with each value replaced by a reference to it, as `Iter` yields them.
pub open spec fn ref_pairs<'a, T>(pairs: Seq<(usize, T)>) -> Seq<(usize, &'a T)> {
    Seq::new(pairs.len(), |i: int| (pairs[i].0, &pairs[i].1))
}

/// The items left in an `Iter` whose remaining entries are `entries`, the first with key `front`.
pub(crate) open spec fn iter_items<'a, T>(entries: Seq<Entry<T>>, front: usize) -> Seq<
    (usize, &'a T),
> {
    ref_pairs(occupied_pairs(entries_view(entries), front as int))
}

/// There is one pair per occupied slot.
pub proof fn lemma_occupied_pairs_len<T>(slots: Seq<Option<T>>, key: int)
    ensures
        occupied_pairs(slots, key).len() == num_occupied(slots),
    decreases slots.len(),
{
    if slots.len() > 0 {
        lemma_occupied_pairs_len(slots.drop_last(), key);
    }
}

/// `occupied_pairs` from the front: the first slot gives the first pair if it is occupied.
pub proof fn lemma_occupied_pairs_drop_first<T>(slots: Seq<Option<T>>, key: int)
    requires
        slots.len() > 0,
    ensures
        occupied_pairs(slots, key) == match slots[0] {
            Some(value) => seq![(key as usize, value)],
            None => Seq::empty(),
        } + occupied_pairs(slots.drop_first(), key + 1),
    decreases slots.len(),
{
    let head = match slots[0] {
        Some(value) => seq![(key as usize, value)],
        None => Seq::<(usize, T)>::empty(),
    };
    if slots.len() == 1 {
        assert(slots.drop_last() =~= Seq::<Option<T>>::empty());
        assert(slots.drop_first() =~= Seq::<Option<T>>::empty());
        assert(occupied_pairs(slots.drop_last(), key) == Seq::<(usize, T)>::empty());
        assert(occupied_pairs(slots.drop_first(), key + 1) == Seq::<(usize, T)>::empty());
        assert(slots.last() == slots[0]);
        assert(occupied_pairs(slots, key) =~= head + occupied_pairs(slots.drop_first(), key + 1));
    } else {
        let init = slots.drop_last();
        lemma_occupied_pairs_drop_first(init, key);
        assert(init.drop_first() =~= slots.drop_first().drop_last());
        assert(slots.drop_first().last() == slots.last());
        assert(occupied_pairs(slots, key) =~= head + occupied_pairs(slots.drop_first(), key + 1));
    }
}

/// What the pairs are: each pair `(k, v)` has `slots[k - key] == Some(v)`, the keys increase, and
/// every occupied slot has a pair.
pub proof fn lemma_occupied_pairs<T>(slots: Seq<Option<T>>, key: int)
    requires
        0 <= key,
        key + slots.len() <= usize::MAX + 1,
    ensures
        ({
            let pairs = occupied_pairs(slots, key);
            &&& pairs.len() == num_occupied(slots)
            &&& forall|i: int|
                #![trigger pairs[i]]
                0 <= i < pairs.len() ==> {
                    &&& key <= pairs[i].0 < key + slots.len()
                    &&& slots[pairs[i].0 - key] == Some(pairs[i].1)
                }
            &&& forall|i: int, j: int|
                #![trigger pairs[i], pairs[j]]
                0 <= i < j < pairs.len() ==> pairs[i].0 < pairs[j].0
            &&& forall|k: int|
                0 <= k < slots.len() && (#[trigger] slots[k]) is Some ==> exists|i: int|
                    #![trigger pairs[i]]
                    0 <= i < pairs.len() && pairs[i].0 == key + k
        }),
    decreases slots.len(),
{
    lemma_occupied_pairs_len(slots, key);
    if slots.len() > 0 {
        let init = slots.drop_last();
        lemma_occupied_pairs(init, key);
        let p0 = occupied_pairs(init, key);
        let pairs = occupied_pairs(slots, key);
        assert forall|i: int| #![trigger pairs[i]] 0 <= i < p0.len() implies pairs[i] == p0[i] by {}
        assert forall|i: int|
            #![trigger pairs[i]]
            0 <= i < pairs.len() implies {
            &&& key <= pairs[i].0 < key + slots.len()
            &&& slots[pairs[i].0 - key] == Some(pairs[i].1)
        } by {
            if i < p0.len() {
                assert(init[p0[i].0 - key] == slots[p0[i].0 - key]);
            }
        }
        assert forall|i: int, j: int|
            #![trigger pairs[i], pairs[j]]
            0 <= i < j < pairs.len() implies pairs[i].0 < pairs[j].0 by {
            if j >= p0.len() {
                assert(p0[i].0 < key + init.len());
            }
        }
        assert forall|k: int|
            0 <= k < slots.len() && (#[trigger] slots[k]) is Some implies exists|i: int|
                #![trigger pairs[i]]
                0 <= i < pairs.len() && pairs[i].0 == key + k by {
            if k < init.len() {
                assert(init[k] is Some);
                let i = choose|i: int| #![trigger p0[i]] 0 <= i < p0.len() && p0[i].0 == key + k;
                assert(pairs[i] == p0[i]);
            } else {
                assert(pairs[p0.len() as int].0 == key + k);
            }
        }
    }
}

} // verus!
