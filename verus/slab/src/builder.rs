use crate::{Entry, Slab};
#[cfg(verus_keep_ghost)]
#[allow(unused_imports)]
use crate::spec::*;
use vstd::pervasive::unreached;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// Building `Slab` from pairs (usize, T).
pub(crate) struct Builder<T> {
    slab: Slab<T>,
    vacant_list_broken: bool,
    first_vacant_index: Option<usize>,
}

/// `n` vacant slots.
pub(crate) open spec fn vacant_slots<T>(n: nat) -> Seq<Option<T>> {
    Seq::new(n, |_i: int| None::<T>)
}

/// The slots after `pair(key, value)`: the value goes to slot `key`, after padding with
/// vacant slots if `key` is past the end.
pub(crate) open spec fn pair_slots<T>(slots: Seq<Option<T>>, key: usize, value: T) -> Seq<
    Option<T>,
> {
    if key < slots.len() {
        slots.update(key as int, Some(value))
    } else {
        slots + vacant_slots((key - slots.len()) as nat) + seq![Some(value)]
    }
}

/// While the vacant list is not broken, the vacant entries are exactly the holes that `pair`
/// inserted. Listed in increasing order (`vacant_keys`), they form a chain from `slab.next`
/// down to `first_vacant_index`, each hole linking to the one before it; `build` sets the link
/// of the first hole to the end marker.
pub(crate) open spec fn is_hole_chain<T>(slab: Slab<T>, first_vacant_index: Option<usize>) -> bool {
    let holes = vacant_keys(slab@);
    match first_vacant_index {
        None => holes.len() == 0,
        Some(first) => {
            &&& holes.len() > 0
            &&& first == holes[0]
            &&& slab.next == holes.last()
            &&& forall|j: int|
                #![trigger slab.entries@[holes[j] as int]]
                1 <= j < holes.len() ==> slab.entries@[holes[j] as int] == Entry::<T>::Vacant(
                    holes[j - 1],
                )
        }
    }
}

/// Pushing a hole (linked to the current head) extends the hole chain.
proof fn lemma_push_hole<T>(before: Slab<T>, after: Slab<T>, first: usize)
    requires
        after.entries@ == before.entries@.push(Entry::Vacant(before.next)),
        after.next == before.entries@.len() as usize,
        before.entries@.len() < usize::MAX,
        is_hole_chain(before, Some(first)) || (first == before.entries@.len() && vacant_keys(
            before@,
        ).len() == 0),
    ensures
        is_hole_chain(after, Some(first)),
{
    let h = before.entries@.len() as usize;
    lemma_view_push(before.entries@, Entry::Vacant(before.next));
    lemma_vacant_keys_from_push(before@, None, 0);
    lemma_vacant_keys_from(before@, 0);
    let old_holes = vacant_keys(before@);
    let holes = vacant_keys(after@);
    assert(holes == old_holes.push(h));
    assert forall|j: int|
        #![trigger after.entries@[holes[j] as int]]
        1 <= j < holes.len() implies after.entries@[holes[j] as int] == Entry::<T>::Vacant(
        holes[j - 1],
    ) by {
        if j < old_holes.len() {
            assert(holes[j] == old_holes[j]);
            assert(holes[j - 1] == old_holes[j - 1]);
            assert(old_holes[j] < h);
        } else {
            assert(holes[j - 1] == old_holes.last());
        }
    }
}

impl<T> View for Builder<T> {
    type V = Seq<Option<T>>;

    /// The slots built so far.
    closed spec fn view(&self) -> Seq<Option<T>> {
        self.slab@
    }
}

impl<T> Builder<T> {
    /// Some pair filled a hole, so `build` must recreate the vacant list.
    pub(crate) closed spec fn spec_vacant_list_broken(&self) -> bool {
        self.vacant_list_broken
    }

    /// The invariant of a `Builder`.
    pub(crate) closed spec fn wf(&self) -> bool {
        &&& self.slab.len == num_occupied(self.slab@)
        &&& !self.vacant_list_broken ==> is_hole_chain(self.slab, self.first_vacant_index)
    }

    pub(crate) fn with_capacity(capacity: usize) -> (builder: Self)
        ensures
            builder.wf(),
            builder@ == Seq::<Option<T>>::empty(),
            !builder.spec_vacant_list_broken(),
    {
        let builder = Self {
            slab: Slab::with_capacity(capacity),
            vacant_list_broken: false,
            first_vacant_index: None,
        };
        proof {
            assert(vacant_keys(builder.slab@) =~= Seq::<usize>::empty());
        }
        builder
    }

    pub(crate) fn pair(&mut self, key: usize, value: T)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self)@ == pair_slots(old(self)@, key, value),
            final(self).spec_vacant_list_broken() == (old(self).spec_vacant_list_broken() || (key
                < old(self)@.len() && old(self)@[key as int] is None)),
    {
        let ghost pre = self.slab;
        let ghost first0 = self.first_vacant_index;
        proof {
            pre.lemma_len_bound();
            lemma_num_occupied_le(pre@);
        }
        let slab = &mut self.slab;
        if key < slab.entries.len() {
            // iterator is not sorted, might need to recreate vacant list
            if let Entry::Vacant(_) = slab.entries[key] {
                proof {
                    lemma_num_occupied_lt(pre@, key as int);
                }
                self.vacant_list_broken = true;
                slab.len += 1;
            }
            // if an element with this key already exists, replace it.
            // This is consistent with HashMap and BtreeMap
            slab.entries[key] = Entry::Occupied(value);
            proof {
                lemma_view_update(pre.entries@, key as int, Entry::Occupied(value));
                lemma_num_occupied_update(pre@, key as int, Some(value));
                if !self.vacant_list_broken {
                    // `key` was occupied: the holes and their links are unchanged.
                    assert forall|k: int| 0 <= k < pre@.len() implies ((#[trigger] pre@[k]) is None
                        <==> slab@[k] is None) by {}
                    lemma_vacant_keys_from_same_pattern(pre@, slab@, 0);
                    lemma_vacant_keys_from(pre@, 0);
                    let holes = vacant_keys(pre@);
                    assert forall|j: int| #![trigger holes[j]] 0 <= j < holes.len() implies holes[j]
                        != key by {}
                }
            }
        } else {
            if self.first_vacant_index.is_none() && slab.entries.len() < key {
                self.first_vacant_index = Some(slab.entries.len());
            }
            // insert holes as necessary
            while slab.entries.len() < key
                invariant
                    pre.entries@.len() <= slab.entries@.len() <= key,
                    slab@ == pre@ + vacant_slots((slab@.len() - pre@.len()) as nat),
                    slab.len == pre.len,
                    slab.len == num_occupied(slab@),
                    self.vacant_list_broken == old(self).vacant_list_broken,
                    first0 is Some ==> self.first_vacant_index == first0,
                    slab.entries@.len() < key ==> self.first_vacant_index is Some,
                    !self.vacant_list_broken ==> {
                        ||| is_hole_chain(*slab, self.first_vacant_index)
                        ||| {
                            &&& self.first_vacant_index == Some(slab.entries@.len() as usize)
                            &&& vacant_keys(slab@).len() == 0
                            &&& slab.entries@.len() < key
                        }
                    },
                decreases key - slab.entries@.len(),
            {
                let ghost before = *slab;
                proof {
                    before.lemma_len_bound();
                }
                // add the entry to the start of the vacant list
                let next = slab.next;
                slab.next = slab.entries.len();
                slab.entries.push(Entry::Vacant(next));
                proof {
                    slab.lemma_len_bound();
                    lemma_view_push(before.entries@, Entry::Vacant(next));
                    assert(slab@ =~= pre@ + vacant_slots((slab@.len() - pre@.len()) as nat));
                    assert(slab@.drop_last() =~= before@);
                    if !self.vacant_list_broken {
                        lemma_push_hole(before, *slab, self.first_vacant_index->Some_0);
                    }
                }
            }
            let ghost before = *slab;
            proof {
                before.lemma_len_bound();
                lemma_vacant_keys_from(before@, 0);
            }
            slab.entries.push(Entry::Occupied(value));
            proof {
                slab.lemma_len_bound();
                lemma_num_occupied_le(before@);
            }
            slab.len += 1;
            proof {
                lemma_view_push(before.entries@, Entry::Occupied(value));
                lemma_vacant_keys_from_push(before@, Some(value), 0);
                assert(slab@.drop_last() =~= before@);
                assert(slab@ =~= pair_slots(pre@, key, value));
                let holes = vacant_keys(slab@);
                assert forall|j: int| #![trigger holes[j]] 0 <= j < holes.len() implies holes[j]
                    < before.entries@.len() by {}
            }
        }
        proof {
            if key < pre@.len() {
                assert(slab@ =~= pair_slots(pre@, key, value));
            }
        }
    }

    pub(crate) fn build(self) -> (slab: Slab<T>)
        requires
            self.wf(),
        ensures
            slab.wf(),
            slab@ == self@,
            slab.vacant_list() == if self.spec_vacant_list_broken() {
                vacant_keys(self@)
            } else {
                vacant_keys(self@).reverse()
            },
    {
        let ghost slots = self.slab@;
        proof {
            self.slab.lemma_len_bound();
            lemma_vacant_keys_from(slots, 0);
            lemma_num_occupied_le(slots);
            lemma_num_occupied_all_some(slots);
        }
        let mut slab = self.slab;
        if slab.len == slab.entries.len() {
            // no vacant entries, so next might not have been updated
            slab.next = slab.entries.len();
            proof {
                lemma_vacant_keys_from_skip(slots, 0, slots.len() as int);
                assert forall|k: int| 0 <= k < slab.entries@.len() implies !(#[trigger] slab.entries@[k] is Vacant) by {
                    assert(slots[k] is Some);
                }
                assert(vacant_keys(slots).reverse() =~= Seq::<usize>::empty());
                slab.lemma_wf_intro(Seq::empty());
            }
        } else if self.vacant_list_broken {
            slab.recreate_vacant_list();
        } else if let Some(first_vacant_index) = self.first_vacant_index {
            let ghost before = slab;
            let next = slab.entries.len();
            match &mut slab.entries[first_vacant_index] {
                Entry::Vacant(n) => *n = next,
                _ => unreached(),
            }
            proof {
                let holes = vacant_keys(slots);
                let list = holes.reverse();
                assert(slab.entries@ == before.entries@.update(
                    first_vacant_index as int,
                    Entry::Vacant(next),
                ));
                lemma_view_update(before.entries@, first_vacant_index as int, Entry::Vacant(next));
                assert(slab@ =~= slots);
                assert forall|i: int| #![trigger list[i]] 0 <= i < list.len() implies {
                    &&& (list[i] as int) < slab.entries@.len()
                    &&& slab.entries@[list[i] as int] == Entry::<T>::Vacant(
                        if i + 1 < list.len() {
                            list[i + 1]
                        } else {
                            slab.entries@.len() as usize
                        },
                    )
                } by {
                    let j = holes.len() - 1 - i;
                    assert(list[i] == holes[j]);
                    if i + 1 < list.len() {
                        assert(list[i + 1] == holes[j - 1]);
                        assert(holes[0] < holes[j]);
                    }
                }
                assert forall|a: int, b: int|
                    0 <= a < list.len() && 0 <= b < list.len() && a != b implies list[a]
                    != list[b] by {
                    assert(list[a] == holes[holes.len() - 1 - a]);
                    assert(list[b] == holes[holes.len() - 1 - b]);
                }
                assert forall|k: int|
                    0 <= k < slab.entries@.len() && (#[trigger] slab.entries@[k]) is Vacant implies list.contains(
                    k as usize,
                ) by {
                    assert(slots[k] is None);
                    assert(holes.contains(k as usize));
                    let j = choose|j: int| 0 <= j < holes.len() && holes[j] == k as usize;
                    assert(list[holes.len() - 1 - j] == k as usize);
                }
                slab.lemma_wf_intro(list);
            }
        } else {
            unreached()
        }
        slab
    }
}

} // verus!
