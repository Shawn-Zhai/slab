use vstd::prelude::*;

verus! {

// --- Slab Helpers ---

// spec helper state model for slab
pub ghost struct SlabModel<T> {
    // one entry for every initialized Vec entry
    // `Some(v)` corresponds to Entry::Occupied(v)
    // `None` corresponds to Entry::Vacant(next_index)
    // indices >= slots.len() have never been initialized and are not in free list
    // len() counts Some entries, not this seq's length.
    pub slots: Seq<Option<T>>,

    // vacant indices in insertion-reuse order
    // it is empty until something is removed
    pub free: Seq<int>,

    // capacity of Vec<Entry<T>>, which may exceed slots.len() and is not
    // determined by the current key/value contents
    // allocation growth can increase this even when every logical element is unchanged
    pub capacity: int,
}

// Slab<T> -> GHOST SlabModel<T> BRIDGE
// this is an uninterpreted stand-in, NOT a proven model of Vec::capacity()
// a Vec view gives elements, not the actual allocated capacity
// capacity-specific contracts require a sound specification of Vec allocation
pub uninterp spec fn vec_allocated_capacity<T>(v: &Vec<T>) -> int;

// TRUSTED fact about std, for automated comparison: a Vec's allocated capacity is never below its
// length. It holds for every Vec, and makes the `slots.len() <= capacity` conjunct of
// `SlabModel::valid()` provable. Obligations enable it with
// `broadcast use axiom_vec_len_le_capacity;`.
pub broadcast axiom fn axiom_vec_len_le_capacity<T>(v: &Vec<T>)
    ensures
        v@.len() <= #[trigger] vec_allocated_capacity(v),
;

// Convert concrete entries to abstract slots, preserving every index.
// The Vacant(next) link is discarded here because its ordering is represented
// separately by `free` below.
pub open spec fn slots_from_entries<T>(entries: Seq<crate::Entry<T>>) -> Seq<Option<T>> {
    entries.map_values(|entry: crate::Entry<T>|
        match entry {
            crate::Entry::Occupied(value) => Some(value),
            crate::Entry::Vacant(_) => None,
        }
    )
}

// Follow the REAL intrusive free list, starting at `next`.
// `entries.len()` is the terminal sentinel and is NOT a vacant key.
// Fuel bounds recursion for all states, including malformed/cyclic ones.
// The representation invariant below rules out truncation and cycles.
pub open spec fn follow_free_links<T>(
    entries: Seq<crate::Entry<T>>,
    current: int,
    fuel: nat,
) -> Seq<int>
    decreases fuel,
{
    if current == entries.len() || fuel == 0 {
        Seq::empty()
    } else if 0 <= current < entries.len() {
        match entries[current] {
            crate::Entry::Vacant(next) =>
                seq![current] + follow_free_links(entries, next as int, (fuel - 1) as nat),
            crate::Entry::Occupied(_) => Seq::empty(),
        }
    } else {
        Seq::empty()
    }
}

// Unlike follow_free_links, this predicate rejects a malformed/cyclic chain:
// following at most `entries.len()` vacant nodes must reach the sentinel.
pub open spec fn free_links_terminate<T>(
    entries: Seq<crate::Entry<T>>,
    current: int,
    fuel: nat,
) -> bool
    decreases fuel,
{
    if current == entries.len() {
        true
    } else if fuel == 0 {
        false
    } else if 0 <= current < entries.len() {
        match entries[current] {
            crate::Entry::Vacant(next) =>
                free_links_terminate(entries, next as int, (fuel - 1) as nat),
            crate::Entry::Occupied(_) => false,
        }
    } else {
        false
    }
}

// View is the formal conversion from the *different concrete Rust struct*
// Slab<T> to our *ghost-only* SlabModel<T>. Thus s@ and
// SlabModel::<T>::empty() have the SAME TYPE and can be compared.
//
// This uses the concrete free-list links, not a sorted list of vacant keys;
// sorting would give the wrong key for the next insert() after removals.
impl<T> View for crate::Slab<T> {
    type V = SlabModel<T>;

    closed spec fn view(&self) -> SlabModel<T> {
        let entries = self.entries@;
        SlabModel {
            slots: slots_from_entries(entries),
            free: follow_free_links(entries, self.next as int, entries.len() as nat),
            capacity: vec_allocated_capacity(&self.entries),
        }
    }
}

// Additional CONCRETE representation invariant to maintain in the proofs.
// `SlabModel::valid()` verifies that the abstract free list has exactly the
// vacant keys, but on its own does not guarantee that the concrete next-link
// chain actually reaches the end sentinel. We also connect the concrete
// occupied count and the free-list head to their abstract counterparts.
pub open spec fn slab_rep_ok<T>(s: &crate::Slab<T>) -> bool {
    &&& s@.valid()
    &&& s.len as int == s@.occupied_count()
    &&& s.next as int == s@.vacant_key()
    &&& free_links_terminate(s.entries@, s.next as int, s.entries@.len() as nat)
}

// state view for IntoIter and Iter
// `remaining` gives precisely the elements that future next()/next_back() calls can return
// in ascending-key order
pub ghost struct IteratorModel<T> {
    pub remaining: Seq<(int, T)>,
}

// draining iterators yield T values alone
pub ghost struct DrainModel<T> {
    pub remaining: Seq<T>,
}

// these ghost iterator fields have no proven connection to
// the concrete iterator's internal Enumerate/Drain state yet
// for mutating iterator APIs
// `remaining_keys` tracks keys not yet yielded
// `original_slots` is the borrow-entry snapshot
// `free` and `capacity` are unaffected by ordinary iteration/mutation
// values already lent out must be tracked with their own borrow restoration obligations
// the owning slab view cannot be mutated via non-iterator methods while IterMut exists
pub ghost struct IterMutModel<T> {
    pub remaining_keys: Seq<int>,
    pub original_slots: Seq<Option<T>>,
    pub free: Seq<int>,
    pub capacity: int,
}

// Iterator View bridges (ABSTRACT, UNVERIFIED)
// These uninterpreted observations make it explicit what the
// iterator public contracts mean. They are NOT translators proven from the
// concrete Enumerate<slice/vec::Iter...> or vec::Drain state. For full Verus
// verification, connect each observation to the iterator's actual position,
// length, and remaining occupied elements; preferably use IteratorSpecImpl
// (and DoubleEndedIteratorSpecImpl for next_back) from vstd.
pub uninterp spec fn into_iter_remaining<T>(it: &crate::IntoIter<T>) -> Seq<(int, T)>;
pub uninterp spec fn iter_remaining<'a, T>(it: &crate::Iter<'a, T>) -> Seq<(int, T)>;
pub uninterp spec fn iter_mut_remaining_keys<'a, T>(it: &crate::IterMut<'a, T>) -> Seq<int>;
pub uninterp spec fn iter_mut_original_slots<'a, T>(it: &crate::IterMut<'a, T>) -> Seq<Option<T>>;
pub uninterp spec fn iter_mut_original_free<'a, T>(it: &crate::IterMut<'a, T>) -> Seq<int>;
pub uninterp spec fn iter_mut_original_capacity<'a, T>(it: &crate::IterMut<'a, T>) -> int;
pub uninterp spec fn drain_remaining<'a, T>(it: &crate::Drain<'a, T>) -> Seq<T>;

impl<T> View for crate::IntoIter<T> {
    type V = IteratorModel<T>;
    closed spec fn view(&self) -> IteratorModel<T> {
        IteratorModel { remaining: into_iter_remaining(self) }
    }
}

impl<'a, T> View for crate::Iter<'a, T> {
    type V = IteratorModel<T>;
    closed spec fn view(&self) -> IteratorModel<T> {
        IteratorModel { remaining: iter_remaining(self) }
    }
}

impl<'a, T> View for crate::IterMut<'a, T> {
    type V = IterMutModel<T>;
    closed spec fn view(&self) -> IterMutModel<T> {
        IterMutModel {
            remaining_keys: iter_mut_remaining_keys(self),
            original_slots: iter_mut_original_slots(self),
            free: iter_mut_original_free(self),
            capacity: iter_mut_original_capacity(self),
        }
    }
}

impl<'a, T> View for crate::Drain<'a, T> {
    type V = DrainModel<T>;
    closed spec fn view(&self) -> DrainModel<T> {
        DrainModel { remaining: drain_remaining(self) }
    }
}

// records one callback invocation, including mutations to T
// a `retain` callback receives (key, &mut T), may modify T, and returns bool
// true preserves the modified value, false removes it
pub ghost struct RetainEvent<T> {
    pub after_callback: T,
    pub keep: bool,
}

// describes the corresponding `rekey(&mut T, old, new)` call
// source is the last occupied key, destination is the earliest available hole
// the closure can mutate the moved value before deciding to accept the move
// if accept_move=false, compact stops, the modified value stays at source
pub ghost struct CompactEvent<T> {
    pub source: int,
    pub destination: int,
    pub after_callback: T,
    pub accept_move: bool,
}

impl<T> SlabModel<T> {
    
    // the state of `Slab::new()` / `Default::default()`.
    pub open spec fn empty() -> Self {
        Self { slots: Seq::empty(), free: Seq::empty(), capacity: 0 }
    }

    // The representation invariant shared by every safe public method
    // 1. the initialized length is nonnegative and fits in allocated capacity
    // 2. the ordered free list cannot contain duplicate keys (no cycles)
    // 3. every free key is a valid initialized index holding None
    // 4, every None is reachable through free, and every Some is absent from it
    pub open spec fn valid(&self) -> bool {
        &&& 0 <= self.slots.len() <= self.capacity
        &&& self.free.no_duplicates()
        &&& forall |j: int| 0 <= j < self.free.len() ==> (
            0 <= #[trigger] self.free[j] < self.slots.len()
            && self.slots[self.free[j]].is_none()
        )
        &&& forall |i: int| 0 <= i < self.slots.len() ==> (
            self.slots[i].is_none() <==> self.free.contains(i)
        )
    }

    // logical length of the collection
    // count Some(v) entries, ignoring holes
    // counterpart of the slab's `len` field
    pub open spec fn occupied_count(&self) -> int {
        self.slots.filter(|x: Option<T>| x.is_some()).len() as int
    }

    // whether an index denotes a currently occupied key
    // out-of-bounds indexes and in-bounds vacant indexes both return false
    // matching contains()
    pub open spec fn present(&self, k: int) -> bool {
        0 <= k < self.slots.len() && self.slots[k].is_some()
    }

    // lookup, Some(v) only for an occupied key,
    // None for a vacant or an out-of-range key
    pub open spec fn get(&self, k: int) -> Option<T> {
        if 0 <= k < self.slots.len() { self.slots[k] } else { None }
    }

    // next cell to be inserted, the first free-list node if exists, or append at slots.len()
    pub open spec fn vacant_key(&self) -> int {
        if self.free.len() > 0 { self.free[0] } else { self.slots.len() as int }
    }

    // compute the new slot sequence for an insertion at the required key
    // either append one new occupied cell, or replace an existing None in place
    pub open spec fn append_or_fill(&self, k: int, v: T) -> Seq<Option<T>>
        recommends self.valid(), k == self.vacant_key(),
    {
        if k == self.slots.len() {
            self.slots.push(Some(v))
        } else {
            self.slots.update(k, Some(v))
        }
    }

    // complete insertion, except for the allocator-selected capacity
    // new capacity >= old capacity and >= new slots length
    // when a hole is filled, remove only free[0], otherwise grow the initialized slots by one.
    // The caller supplies the resulting allocator-chosen capacity separately   
    pub open spec fn inserted(&self, v: T, new_cap: int) -> Self
        recommends self.valid(),
    {
        Self {
            slots: self.append_or_fill(self.vacant_key(), v),
            free: if self.free.len() == 0 { self.free } else { self.free.drop_first() },
            capacity: new_cap,
        }
    }

    // helper for get_mut / index_mut
    // same keys, same vacant list and capacity, only the selected value may change
    // Exclusive mutable borrow returns a potentially changed value
    pub open spec fn value_updated(&self, k: int, v: T) -> Self
        recommends self.valid(), self.present(k),
    {
        Self {
            slots: self.slots.update(k, Some(v)),
            free: self.free,
            capacity: self.capacity,
        }
    }

    // combine edits to distinct occupied keys, used for simultaneous borrows (get2_mut)
    // each key is occupied and they must be different to avoid aliasing
    // because indices differ, both updates survive regardless of 
    // the order in which references are released
    pub open spec fn updated_two(
        &self, k1: int, v1: T, k2: int, v2: T,
    ) -> Self
        recommends self.valid(), self.present(k1), self.present(k2), k1 != k2,
    {
        self.value_updated(k1, v1).value_updated(k2, v2)
    }

    // apply a finite sequence of (key, final_value) writes
    // intended for get_disjoint_mut's distinct keys and iterator borrow release
    pub open spec fn updated_many(&self, edits: Seq<(int, T)>) -> Self
        recommends
            self.valid(),
            // every edited key is occupied.
            forall |i: int|
                0 <= i < edits.len() ==> self.present(edits[i].0),
            // all edited keys are pairwise distinct.
            forall |i: int, j: int|
                0 <= i < j < edits.len()
                    ==> edits[i].0 != edits[j].0,
        
        decreases edits.len(),
    {
        if edits.len() == 0 { Self {
            slots: self.slots, free: self.free, capacity: self.capacity,
        } } else {
            self.value_updated(edits[0].0, edits[0].1)
                .updated_many(edits.drop_first())
        }
    }

    // successful removal takes the element out of slot k, records None at k,
    // and pushes k onto the head of the free list 
    pub open spec fn removed(&self, k: int) -> Self
        recommends self.valid(), self.present(k),
    {
        Self {
            slots: self.slots.update(k, None),
            free: seq![k] + self.free,
            capacity: self.capacity,
        }
    }

    // total removal transition, same as removed(k) when occupied
    // otherwise return the unchanged state
    // try_remove can accept invalid or vacant indices
    pub open spec fn tried_remove(&self, k: int) -> Self
        recommends self.valid(),
    {
        if self.present(k) { self.removed(k) } else {
            Self { 
                slots: self.slots, 
                free: self.free, 
                capacity: self.capacity,
            }
        }
    }

    // clear all initialized entries and the free list
    // the underlying allocation capacity is preserved
    pub open spec fn cleared(&self) -> Self {
        Self { 
            slots: Seq::empty(), 
            free: Seq::empty(), 
            capacity: self.capacity,
        }
    }

    // keys of occupied entries in ascending order
    pub open spec fn occupied_keys(&self) -> Seq<int> {
        Seq::new(self.slots.len(), |i: int| i).filter(|i: int| self.slots[i].is_some())
    }

    // iterators yield occupied (key, value) pairs in increasing key order
    // convert sorted occupied keys to (key, value) pairs
    // this is the snapshot yielded by an immutable iterator or an owning IntoIter
    pub open spec fn pairs(&self) -> Seq<(int, T)> {
        self.occupied_keys().map_values(|i: int| (i, self.slots[i].unwrap()))
    }

    // number of initialized slots remaining after shrink_to_fit() strips
    // all trailing vacant entries
    pub open spec fn trimmed_len(&self) -> int {
        let ks = self.occupied_keys();
        if ks.len() == 0 { 0 } else { ks.last() + 1 }
    }

    // vacancies in increasing key order, used whenever slab reconstructs links
    pub open spec fn vacant_keys_ascending_in(slots: Seq<Option<T>>) -> Seq<int> {
        Seq::new(slots.len(), |i: int| i).filter(|i: int| slots[i].is_none())
    }

    // shrink_to_fit rebuilds its free list in ascending index order if it
    // actually removes trailing vacant entries, otherwise it leaves it alone
    // model shrink_to_fit(): 
    // strip only trailing vacant entries. If trailing cells were removed, 
    // the concrete implementation reconstructs the remainingc vacancy links 
    // and this ghost view expresses them in ascending order. Otherwise the original
    // free-list order is kept
    // the allocator can retain more capacity than the new initialized length
    pub open spec fn shrunk(&self, new_cap: int) -> Self
        recommends self.valid(), self.trimmed_len() <= new_cap <= self.capacity,
    {
        let new_len = self.trimmed_len();
        if new_len == self.slots.len() {
            Self { 
                slots: self.slots, 
                free: self.free, 
                capacity: new_cap,
            }
        } else {
            let new_slots = self.slots.subrange(0, new_len);
            Self {
                slots: new_slots,
                free: Self::vacant_keys_ascending_in(new_slots),
                capacity: new_cap,
            }
        }
    }

    // the callback runs once for each originally occupied key in ascending key order
    // it may mutate the value before returning bool
    // each occupied slot needs one Some(event), every original vacant must have None (no callback)
    pub open spec fn retain_events_valid(
        &self, events: Seq<Option<RetainEvent<T>>>,
    ) -> bool {
        events.len() == self.slots.len()
        && forall |k: int| 0 <= k < self.slots.len() ==> (
            self.slots[k].is_some() <==> events[k].is_some()
        )
    }

    // final state after a normal retain() callback trace
    // kept entries use their after-callback values, removed entries become None
    // the new free-list head contains newly removed keys in REVERSE callback order,
    // because remove pushes each freed key onto the front
    // previously vacant indices remain behind these new nodes in their original order
    pub open spec fn retained(
        &self, events: Seq<Option<RetainEvent<T>>>,
    ) -> Self
        recommends self.valid(), self.retain_events_valid(events),
    {
        let removed_keys: Seq<int> = Seq::new(self.slots.len(), |i: int| i)
            .filter(|i: int| self.slots[i].is_some() && !events[i].unwrap().keep);
        let new_slots: Seq<Option<T>> = Seq::new(self.slots.len(), |i: int|
            if self.slots[i].is_some() && events[i].unwrap().keep {
                Some(events[i].unwrap().after_callback)
            } else {
                None
            });
        Self {
            slots: new_slots,
            free: removed_keys.reverse() + self.free,
            capacity: self.capacity,
        }
    }

    // remove trailing vacant slots 
    // corresponds to compact's initial popping loop before it invokes rekey on a rightmost value
    pub open spec fn trim_trailing_vacancies(s: Seq<Option<T>>) -> Seq<Option<T>>
        decreases s.len(),
    {
        if s.len() > 0 && s.last().is_none() {
            Self::trim_trailing_vacancies(s.drop_last())
        } else {
            s
        }
    }

    // return the earliest vacant index (used for each compaction move)
    pub open spec fn first_hole(s: Seq<Option<T>>) -> int
        recommends s.filter(|v: Option<T>| v.is_none()).len() > 0,
    {
        choose |i: int| 0 <= i < s.len() && s[i].is_none()
            && forall |j: int| 0 <= j < i ==> s[j].is_some()
    }

    // complete trace of a normally returning `compact`
    // output is None for an impossible/ill-formed callback trace
    // Some((slots,true)) means full compaction,
    // Some((slots,false)) means the callback refused a move and compaction terminated early
    // Replay every callback event against logical slots. At each step:
    // 1. trim empty suffix entries
    // 2. stop successfully if no holes remain
    // 3. otherwise propose moving the rightmost value into the earliest hole
    // 4. check the event's source/destination and apply the mutated value
    // 5. if rejected, restore the value at its source and stop immediately
    pub open spec fn run_compact_trace(
        s: Seq<Option<T>>,
        events: Seq<CompactEvent<T>>,
    ) -> Option<(Seq<Option<T>>, bool)>
        decreases s.len() via Self::run_compact_trace_decreases
    {
        let short = Self::trim_trailing_vacancies(s);
        if short.len() == short.filter(|v: Option<T>| v.is_some()).len() {
            if events.len() == 0 { Some((short, true)) } else { None }
        } else if events.len() == 0 {
            None
        } else {
            let ev = events[0];
            let src = short.len() - 1;
            let dst = Self::first_hole(short);
            if ev.source != src || ev.destination != dst {
                None
            } else if ev.accept_move {
                let moved = short.drop_last().update(dst, Some(ev.after_callback));
                Self::run_compact_trace(moved, events.drop_first())
            } else if events.len() == 1 {
                Some((short.update(src, Some(ev.after_callback)), false))
            } else {
                None
            }
        }
    }

    // termination of run_compact_trace: trimming never lengthens the sequence, so the
    // recursive call is on a shorter one
    #[via_fn]
    proof fn run_compact_trace_decreases(s: Seq<Option<T>>, events: Seq<CompactEvent<T>>) {
        Self::lemma_trim_len(s);
        reveal(Seq::filter);
    }

    proof fn lemma_trim_len(s: Seq<Option<T>>)
        ensures
            Self::trim_trailing_vacancies(s).len() <= s.len(),
        decreases s.len(),
    {
        if s.len() > 0 && s.last().is_none() {
            Self::lemma_trim_len(s.drop_last());
        }
    }

    // full ghost state for the general compact() transition
    // accepted moves fill vacant slots, a rejected move stops compaction
    // the free list is empty after full compaction or rebuilt in ascending key order
    // after partial compaction
    // capacity may shrink but must remain sufficient for all remaining slots.
    // requires a valid callback trace produced by run_compact_trace()
    pub open spec fn compacted(
        &self,
        events: Seq<CompactEvent<T>>,
        new_cap: int,
    ) -> Self
        recommends
            self.valid(),
            Self::run_compact_trace(self.slots, events).is_some(),
            Self::run_compact_trace(self.slots, events).unwrap().0.len() <= new_cap,
            new_cap <= self.capacity,
    {
        let outcome = Self::run_compact_trace(self.slots, events).unwrap();
        let new_slots = outcome.0;
        let completed = outcome.1;

        Self {
            slots: new_slots,
            free: if completed {
                Seq::empty()
            } else {
                Seq::new(new_slots.len(), |i: int| i)
                    .filter(|i: int| new_slots[i].is_none())
            },
            capacity: new_cap,
        }
    }

    // reconstruct occupied slots from an input stream of (key, value)
    // missing keys become None, repeated keys use the last value in the stream
    // free-list is not specified due to Builder's incidental free-list ordering
    pub open spec fn slots_from_pairs(pairs: Seq<(int, T)>) -> Seq<Option<T>>
        decreases pairs.len(),
    {
        if pairs.len() == 0 {
            Seq::empty()
        } else {
            let prev = Self::slots_from_pairs(pairs.drop_last());
            let key = pairs.last().0;
            let val = pairs.last().1;
            if key < prev.len() {
                prev.update(key, Some(val))
            } else {
                prev + Seq::new((key - prev.len()) as nat, |i: int| None)
                    + seq![Some(val)]
            }
        }
    }
}

// for get_disjoint_mut, pairwise comparison of every requested key
pub open spec fn keys_distinct<const N: usize>(keys: [usize; N]) -> bool {
    forall |i: int, j: int| 0 <= i < N && 0 <= j < N && i != j
        ==> keys[i] != keys[j]
}

// computes exactly the error priority of get_disjoint_mut
// duplicate checking is global and runs before any bounds or vacancy check
// the earliest invalid key determines IndexOutOfBounds versus IndexVacant
// returning None indicates every key is occupied and all returned mutable references can be disjoint
pub open spec fn disjoint_error<T, const N: usize>(
    m: SlabModel<T>, keys: [usize; N],
) -> Option<crate::GetDisjointMutError>
    decreases N,
{
    if !keys_distinct(keys) {
        Some(crate::GetDisjointMutError::OverlappingIndices)
    } else if exists |i: int| 0 <= i < N
        && (keys[i] as int >= m.slots.len() || !m.present(keys[i] as int)) {
        let first = choose |i: int| 0 <= i < N
            && (keys[i] as int >= m.slots.len() || !m.present(keys[i] as int))
            && forall |j: int| 0 <= j < i ==> m.present(keys[j] as int);
        if keys[first] as int >= m.slots.len() {
            Some(crate::GetDisjointMutError::IndexOutOfBounds)
        } else {
            Some(crate::GetDisjointMutError::IndexVacant)
        }
    } else { None }
}

// for key_of (pointer-identity lookup)
// These two declarations are only uninterpreted names
// They are not a sound account of reference identity: ordinary Verus &T
// specifications generally cannot distinguish equal values at different
// addresses.
pub uninterp spec fn owned_reference<T>(slab: &crate::Slab<T>, reference: &T) -> bool;
pub uninterp spec fn reference_is_at<T>(slab: &crate::Slab<T>, reference: &T, key: int) -> bool;

// --- Specs for Public Functions ---

impl<T> Slab<T> {

    // -- Constructors and Capacities --

    // return an empty slab, no occupied keys, no vacant, no capacity
    pub const fn new() -> (s: Self)
        ensures
            s@ == SlabModel::<T>::empty(),
    ;

    // allocate  storage for `capacity` elements
    // no initialized/occupied slots at construction
    pub fn with_capacity(capacity: usize) -> (s: Self)
        ensures
            s@.valid(),
            s@.slots.len() == 0,
            s@.free.len() == 0,
            s@.capacity >= capacity as int,
            capacity == 0 ==> s@.capacity == 0,
    ;

    // report allocated Vec capacity, not occupied length.
    pub fn capacity(&self) -> (n: usize)
        requires self@.valid(),
        ensures n as int == self@.capacity,
    ;

    // increase available space for additional occupied values if needed
    // the previous initialized slots and exact free-list order are unchanged
    pub fn reserve(&mut self, additional: usize)
        requires old(self)@.valid(),
        ensures
            final(self)@.valid(),
            final(self)@.slots == old(self)@.slots,
            final(self)@.free == old(self)@.free,
            final(self)@.capacity >= old(self)@.capacity,
            final(self)@.capacity >= old(self)@.occupied_count() + additional as int,
            (old(self)@.capacity - old(self)@.occupied_count() >= additional as int)
            ==> final(self)@.capacity == old(self)@.capacity,
    ;

    // same observable lower bound as reserve, allocator may round up
    pub fn reserve_exact(&mut self, additional: usize)
        requires old(self)@.valid(),
        ensures
            final(self)@.valid(),
            final(self)@.slots == old(self)@.slots,
            final(self)@.free == old(self)@.free,
            final(self)@.capacity >= old(self)@.capacity,
            final(self)@.capacity >= old(self)@.occupied_count() + additional as int,
            (old(self)@.capacity - old(self)@.occupied_count() >= additional as int)
            ==> final(self)@.capacity == old(self)@.capacity,
    ;

    // -- size and read-only access --

    // count Some entries
    pub fn len(&self) -> (n: usize)
        requires self@.valid(),
        ensures n as int == self@.occupied_count(),
    ;

    // empty means zero occupied values, even if the vec has vacants
    pub fn is_empty(&self) -> (r: bool)
        requires self@.valid(),
        ensures r == (self@.occupied_count() == 0),
    ;

    // invalid and vacant keys are both false, never a panic
    pub fn contains(&self, key: usize) -> (r: bool)
        requires self@.valid(),
        ensures r == self@.present(key as int),
    ;

    // return immutable T reference for occupied key, otherwise None
    // the source slab is read-only and is not mutated
    pub fn get(&self, key: usize) -> (r: Option<&T>)
        requires self@.valid(),
        ensures
            match r {
                Some(v) => self@.present(key as int)
                    && *v == self@.get(key as int).unwrap(),
                None => !self@.present(key as int),
            },
    ;

    // -- insertion / vacant-entry handle --

    // return the next insertion key
    // when free is empty, this equals the current initialized length
    pub fn vacant_key(&self) -> (k: usize)
        requires self@.valid(),
        ensures k as int == self@.vacant_key(),
    ;

    // return the pre-state head of the free list or append index
    pub fn insert(&mut self, val: T) -> (k: usize)
        requires old(self)@.valid(),
        ensures
            k as int == old(self)@.vacant_key(),
            final(self)@.valid(),
            final(self)@ == old(self)@.inserted(val, final(self)@.capacity),
            final(self)@.capacity >= old(self)@.capacity,
    ;

    // return a key in an exclusive handle, without inserting yet
    // e owns an exclusive borrow of this slab
    // the slab's view is UNCHANGED at handle creation
    pub fn vacant_entry(&mut self) -> (e: VacantEntry<'_, T>)
        requires old(self)@.valid(),
        ensures
            e.key as int == old(self)@.vacant_key(),
    ;

    // -- removal --

    // if occupied, return the old T and prepend its key to free
    // if vacant/out-of-bounds, return None and change nothing
    pub fn try_remove(&mut self, key: usize) -> (r: Option<T>)
        requires old(self)@.valid(),
        ensures
            r == old(self)@.get(key as int),
            final(self)@ == old(self)@.tried_remove(key as int),
            final(self)@.valid(),
    ;

    // panic-free usage requires occupied key, unlike try_remove
    // it returns the exact removed value on success 
    pub fn remove(&mut self, key: usize) -> (r: T)
        requires
            old(self)@.valid(),
            old(self)@.present(key as int),
        ensures
            r == old(self)@.get(key as int).unwrap(),
            final(self)@ == old(self)@.removed(key as int),
            final(self)@.valid(),
    ;

    // discard all initialized entries but retain allocation capacity
    pub fn clear(&mut self)
        requires old(self)@.valid(),
        ensures
            final(self)@ == old(self)@.cleared(),
            final(self)@.valid(),
    ;

    // -- Mutable references and unsafe access --

    // on Some, the reference starts at the old T value
    // on reference release, only this occupied slot may be updated
    pub fn get_mut(&mut self, key: usize) -> (r: Option<&mut T>)
        requires old(self)@.valid(),
        ensures
            match r {
                Some(v) =>
                    old(self)@.present(key as int)
                    && *v == old(self)@.get(key as int).unwrap()
                    && final(self)@ == old(self)@.value_updated(
                        key as int, *final(v)),
                None =>
                    !old(self)@.present(key as int)
                    && final(self)@ == old(self)@,
            },
    ;

    // two safe mutable references require different indices
    // a key exactly at slots.len() gives None, a larger key may panic
    pub fn get2_mut(&mut self, key1: usize, key2: usize)
        -> (r: Option<(&mut T, &mut T)>)
        requires
            old(self)@.valid(),
            key1 != key2,
            key1 as int <= old(self)@.slots.len(),
            key2 as int <= old(self)@.slots.len(),
        ensures
            match r {
                Some((a, b)) =>
                    old(self)@.present(key1 as int)
                    && old(self)@.present(key2 as int)
                    && *a == old(self)@.get(key1 as int).unwrap()
                    && *b == old(self)@.get(key2 as int).unwrap()
                    && final(self)@ == old(self)@.updated_two(
                        key1 as int, *final(a), key2 as int, *final(b)),
                None =>
                    !(old(self)@.present(key1 as int)
                    && old(self)@.present(key2 as int))
                    && final(self)@ == old(self)@,
            },
    ;

    // unsafe caller promises the key is occupied, not just in bounds
    pub unsafe fn get_unchecked(&self, key: usize) -> (r: &T)
        requires self@.valid(), self@.present(key as int),
        ensures *r == self@.get(key as int).unwrap(),
    ;

    // unsafe caller promises occupancy, returned &mut can update slot
    pub unsafe fn get_unchecked_mut(&mut self, key: usize) -> (r: &mut T)
        requires old(self)@.valid(), old(self)@.present(key as int),
        ensures
            *r == old(self)@.get(key as int).unwrap(),
            final(self)@ == old(self)@.value_updated(key as int, *final(r)),
    ;

    // unsafe caller promises two distinct, occupied keys
    // the two returned mutable references must never alias
    pub unsafe fn get2_unchecked_mut(&mut self, key1: usize, key2: usize)
        -> (r: (&mut T, &mut T))
        requires
            old(self)@.valid(),
            key1 != key2,
            old(self)@.present(key1 as int),
            old(self)@.present(key2 as int),
        ensures
            *r.0 == old(self)@.get(key1 as int).unwrap(),
            *r.1 == old(self)@.get(key2 as int).unwrap(),
            final(self)@ == old(self)@.updated_two(
                key1 as int, *final(r.0), key2 as int, *final(r.1)),
    ;

    // -- Disjoint Access --

    // validate all keys, reject duplicates before bad occupancy
    pub fn get_disjoint_mut<const N: usize>(
        &mut self, keys: [usize; N],
    ) -> (r: Result<[&mut T; N], GetDisjointMutError>)
        requires old(self)@.valid(),
        ensures
            // disjoint_error is defined in slab_spec_ghost.rs.
            r.is_err() <==> disjoint_error(old(self)@, keys).is_some(),
            // Avoid unwrap_err(), which imposes an unnecessary Debug bound on
            // the Ok type in ordinary Rust.
            match r {
                Err(err) => disjoint_error(old(self)@, keys) == Some(err),
                Ok(_) => disjoint_error(old(self)@, keys).is_none(),
            },
            r.is_err() ==> final(self)@ == old(self)@,
            r.is_ok() ==> keys_distinct(keys),
            r.is_ok() ==> forall |i: int| 0 <= i < N ==>
                old(self)@.present(keys[i] as int),
            r.is_ok() ==> forall |i: int| 0 <= i < N ==>
                *r.unwrap()[i] == old(self)@.get(keys[i] as int).unwrap(),
            // Shape and nonselected entries cannot change through returned refs.
            r.is_ok() ==> final(self)@.valid(),
            r.is_ok() ==> final(self)@.free == old(self)@.free,
            r.is_ok() ==> final(self)@.capacity == old(self)@.capacity,
            r.is_ok() ==> final(self)@.slots.len() == old(self)@.slots.len(),
            r.is_ok() ==> forall |j: int|
                0 <= j < old(self)@.slots.len()
                && !(exists |i: int| 0 <= i < N && keys[i] as int == j)
                ==> final(self)@.slots[j] == old(self)@.slots[j],
            // Need to connect selected final values to updated_many().
            // final() of references nested in Result<[&mut T; N], ...> needs
            // a borrow-aware specification; do not invent arbitrary ghost edits.
    ;

    // -- pointer-identity lookup --
    // (owned_reference and reference_is_at are declared before this impl block)

    // return index based on pointer provenance, not T equality
    // owned_reference/reference_is_at have no definitions
    // they require a pointer-identity model, T-value equality is insufficient
    #[track_caller]
    pub fn key_of(&self, present_element: &T) -> (key: usize)
        requires
            self@.valid(),
            // present_element points to the T payload of a particular occupied slot
            owned_reference(self, present_element),
        ensures
            self@.present(key as int),
            // The reference points specifically to the T stored at slot `key`
            reference_is_at(self, present_element, key as int),
    ;

    // -- compaction, shrinking --

    // remove trailing holes, preserve occupied keys
    // capacity can remain larger than the trimmed slot count
    pub fn shrink_to_fit(&mut self)
        requires old(self)@.valid(),
        ensures
            final(self)@.valid(),
            final(self)@ == old(self)@.shrunk(final(self)@.capacity),
            old(self)@.trimmed_len() <= final(self)@.capacity,
            final(self)@.capacity <= old(self)@.capacity,
    ;

    // relocate values from last occupied key to earliest vacant
    // existential events constrain possible shapes but are not linked to what rekey actually does
    // normal returns only; panic excluded
    pub fn compact<F>(&mut self, rekey: F)
        where F: FnMut(&mut T, usize, usize) -> bool,
        requires old(self)@.valid(),
        ensures
            final(self)@.valid(),
            final(self)@.occupied_count() == old(self)@.occupied_count(),
            final(self)@.capacity <= old(self)@.capacity,
            exists |events: Seq<CompactEvent<T>>|
                #![trigger old(self)@.compacted(events, final(self)@.capacity)]
            {
                let outcome = SlabModel::<T>::run_compact_trace(old(self)@.slots, events);
                &&& outcome.is_some()
                &&& outcome.unwrap().0.len() <= final(self)@.capacity
                &&& final(self)@.capacity <= old(self)@.capacity
                &&& final(self)@ == old(self)@.compacted(events, final(self)@.capacity)
            },
    ;

    // filtering, draining, iteration

    // visit each initially occupied value exactly once, in key order
    // callback can mutate T before choosing whether to keep it
    // events currently existential, not tied to f's results
    pub fn retain<F>(&mut self, f: F)
        where F: FnMut(usize, &mut T) -> bool,
        requires old(self)@.valid(),
        ensures
            final(self)@.valid(),
            final(self)@.slots.len() == old(self)@.slots.len(),
            final(self)@.capacity == old(self)@.capacity,
            final(self)@.occupied_count() <= old(self)@.occupied_count(),
            forall |k: int| final(self)@.present(k) ==>
                old(self)@.present(k),
            exists |events: Seq<Option<RetainEvent<T>>>|
                old(self)@.retain_events_valid(events)
                && final(self)@ == old(self)@.retained(events),
    ;

    // transfer old occupied values to Drain, original slab becomes empty
    // drain sets slab logical len to zero immediately and removes all entries
    // even if the Drain iterator is dropped before it is fully consumed
    // the mutable borrow blocks observing self until Drain ends
    pub fn drain(&mut self) -> (d: Drain<'_, T>)
        requires old(self)@.valid(),
        ensures
            // at creation Drain owns the prior occupied values and lends the slab
            d@.remaining == old(self)@.pairs().map_values(|p: (int, T)| p.1),
            final(self)@ == old(self)@.cleared(),
    ;

    // yield borrowed (key, &T) in ascending-key order
    pub fn iter(&self) -> (it: Iter<'_, T>)
        requires self@.valid(),
        ensures it@.remaining == self@.pairs(),
    ;

    // yield borrowed (key, &T) in ascending-key order
    pub fn iter_mut(&mut self) -> (it: IterMut<'_, T>)
        requires old(self)@.valid(),
        ensures
            it@.remaining_keys == old(self)@.occupied_keys(),
            it@.original_slots == old(self)@.slots,
            it@.free == old(self)@.free,
            it@.capacity == old(self)@.capacity,
    ;

} // end contract-only impl<T> Slab<T>

// -- public trait methods --
impl<T> core::ops::Index<usize> for crate::Slab<T> {
    type Output = T;
    // invalid/vacant keys panic, this is the normal-return contract only
    fn index(&self, key: usize) -> (r: &T)
        requires self@.valid(), self@.present(key as int),
        ensures *r == self@.get(key as int).unwrap(),
    ;
}

impl<T> core::ops::IndexMut<usize> for crate::Slab<T> {
    fn index_mut(&mut self, key: usize) -> (r: &mut T)
        requires old(self)@.valid(), old(self)@.present(key as int),
        ensures
            *r == old(self)@.get(key as int).unwrap(),
            final(self)@ == old(self)@.value_updated(key as int, *final(r)),
    ;
}

// -- public VacantEntry<'a, T> methods --

impl<'a, T> VacantEntry<'a, T> {

    // expose the key chosen when vacant_entry() was created
    pub fn key(&self) -> (k: usize)
        ensures k == self.key,
    ;

    // consumes the handle, inserts at its reserved key and returns a
    // mutable reference to the newly stored value, which the caller can edit
    // need to also specify insertion transition in borrowed slab,
    // and its final value when the returned &'a mut T borrow is released
    pub fn insert(self, val: T) -> (r: &'a mut T)
        requires self.slab@.valid(),
                 self.key as int == self.slab@.vacant_key(),
        ensures
            *r == val,
    ;
}

// A total ordered input trace is needed for FromIterator.
// This uninterpreted observation is a placeholder; it is NOT guaranteed
// to equal the elements consumed by arbitrary IntoIterator implementations.
// A verified iterator spec or explicit trace witness must justify it.
pub uninterp spec fn produced_pairs<I, T>(iterable: &I) -> Seq<(usize, T)>;

// -- Slab trait methods --

impl<T> Default for Slab<T> {
    // same abstract state as `Slab::new()`
    fn default() -> (s: Self)
        ensures s@ == SlabModel::<T>::empty(),
    ;
}

impl<T: Clone> Clone for Slab<T> {
    // duplicates the keys/free order of the original collection
    // semantic equality of each cloned T needs a T::clone interface
    fn clone(&self) -> (s: Self)
        requires self@.valid(),
        ensures
            s@.valid(),
            s@.slots.len() == self@.slots.len(),
            s@.free == self@.free,
            s@.occupied_keys() == self@.occupied_keys(),
            s@.capacity >= s@.slots.len(),
    ;

    // overwrite target structure to match the source
    fn clone_from(&mut self, source: &Self)
        requires old(self)@.valid(), source@.valid(),
        ensures
            final(self)@.valid(),
            final(self)@.slots.len() == source@.slots.len(),
            final(self)@.free == source@.free,
            final(self)@.occupied_keys() == source@.occupied_keys(),
    ;
}

impl<T> FromIterator<(usize, T)> for Slab<T> {
    // produced_pairs(&iterable) represents the complete sequence
    // of elements yielded by iterable, in iteration order
    // requiring an iterator trace interface
    fn from_iter<I>(iterable: I) -> (s: Self)
    where I: IntoIterator<Item = (usize, T)>,
        ensures
            s@.valid(),
            s@.slots == SlabModel::<T>::slots_from_pairs(
                produced_pairs::<I, T>(&iterable).map_values(|p: (usize, T)| (p.0 as int, p.1))),
            s@.capacity >= s@.slots.len(),
    ;
}

impl<T> IntoIterator for Slab<T> {
    type Item = (usize, T);
    type IntoIter = IntoIter<T>;
    // owning iterator transfers T values out, it no longer borrows Slab
    fn into_iter(self) -> (r: IntoIter<T>)
        ensures r@.remaining == self@.pairs(),
    ;
}

impl<'a, T> IntoIterator for &'a Slab<T> {
    type Item = (usize, &'a T);
    type IntoIter = Iter<'a, T>;
    // shared iterator borrows values, its view is the key/value snapshot
    fn into_iter(self) -> (r: Iter<'a, T>)
        ensures r@.remaining == self@.pairs(),
    ;
}

impl<'a, T> IntoIterator for &'a mut Slab<T> {
    type Item = (usize, &'a mut T);
    type IntoIter = IterMut<'a, T>;
    // mutable iterator borrows elements exclusively, one key per token
    fn into_iter(self) -> (r: IterMut<'a, T>)
        ensures r@.remaining_keys == old(self)@.occupied_keys(),
    ;
}

// -- Iterator methods: IntoIter, Iter, IterMut, Drain --

// IntoIter

impl<T> Iterator for IntoIter<T> {
    type Item = (usize, T);
    // return the first pair, or None if exhausted
    // each successful call shortens the ghost `remaining` sequence by exactly one element
    fn next(&mut self) -> (r: Option<(usize, T)>)
        requires old(self)@.remaining.len() >= 0,
        ensures
            r == (if old(self)@.remaining.len() == 0 { None }
                 else { Some((old(self)@.remaining[0].0 as usize,
                              old(self)@.remaining[0].1)) }),
            final(self)@.remaining ==
                (if old(self)@.remaining.len() == 0 { old(self)@.remaining }
                 else { old(self)@.remaining.drop_first() }),
    ;
    fn size_hint(&self) -> (r: (usize, Option<usize>))
        ensures r == (self@.remaining.len() as usize,
                      Some(self@.remaining.len() as usize)),
    ;
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    // remove the final pair, supporting iteration from both ends without yielding a slot twice
    fn next_back(&mut self) -> (r: Option<(usize, T)>)
        ensures
            r == (if old(self)@.remaining.len() == 0 { None }
                 else { Some((old(self)@.remaining.last().0 as usize,
                              old(self)@.remaining.last().1)) }),
            final(self)@.remaining ==
                (if old(self)@.remaining.len() == 0 { old(self)@.remaining }
                 else { old(self)@.remaining.drop_last() }),
    ;
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> (r: usize)
        ensures r as int == self@.remaining.len(),
    ;
}

// Iter

// borrow the next occupied value, its key is the first remaining key
// the returned &T requires a pointer connection to the originating slab
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (usize, &'a T);

    // requires concrete iterator remaining-state view
    fn next(&mut self) -> (r: Option<(usize, &'a T)>)
        ensures
            r.is_some() <==> old(self)@.remaining.len() > 0,
            r.is_some() ==> (
                r.unwrap().0 as int == old(self)@.remaining[0].0
                && *r.unwrap().1 == old(self)@.remaining[0].1),
            final(self)@.remaining ==
                (if old(self)@.remaining.len() == 0 { old(self)@.remaining }
                else { old(self)@.remaining.drop_first() }),
    ;

    fn size_hint(&self) -> (r: (usize, Option<usize>))
        ensures r == (self@.remaining.len() as usize,
                    Some(self@.remaining.len() as usize)),
    ;
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> (r: Option<(usize, &'a T)>)
        ensures
            r.is_some() <==> old(self)@.remaining.len() > 0,
            r.is_some() ==> (
                r.unwrap().0 as int == old(self)@.remaining.last().0
                && *r.unwrap().1 == old(self)@.remaining.last().1),
            final(self)@.remaining ==
                (if old(self)@.remaining.len() == 0 { old(self)@.remaining }
                else { old(self)@.remaining.drop_last() }),
    ;
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> (r: usize)
        ensures r as int == self@.remaining.len(),
    ;
}

impl<'a, T> Clone for Iter<'a, T> {
    fn clone(&self) -> (r: Iter<'a,T>)
        ensures r@.remaining == self@.remaining,
    ;
}

// IterMut

// yield an exclusive reference to a previously unyielded occupied key
// any mutation is reflected when that reference's borrow is resolved
impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (usize, &'a mut T);

    // returned mutable references need restoration semantics
    fn next(&mut self) -> (r: Option<(usize, &'a mut T)>)
        ensures
            r.is_some() <==> old(self)@.remaining_keys.len() > 0,
            r.is_some() ==>
                r.unwrap().0 as int == old(self)@.remaining_keys[0],
            // initially returned_ref equals the current slot value at this key
            // on resolution only that occupied slot can change
            final(self)@.remaining_keys ==
                (if old(self)@.remaining_keys.len() == 0 {
                    old(self)@.remaining_keys
                } else { old(self)@.remaining_keys.drop_first() }),
    ;

    fn size_hint(&self) -> (r: (usize, Option<usize>))
        ensures r == (self@.remaining_keys.len() as usize,
                    Some(self@.remaining_keys.len() as usize)),
    ;
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> (r: Option<(usize, &'a mut T)>)
        ensures
            r.is_some() <==> old(self)@.remaining_keys.len() > 0,
            r.is_some() ==>
                r.unwrap().0 as int == old(self)@.remaining_keys.last(),
            final(self)@.remaining_keys ==
                (if old(self)@.remaining_keys.len() == 0 {
                    old(self)@.remaining_keys
                } else { old(self)@.remaining_keys.drop_last() }),
    ;
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    fn len(&self) -> (r: usize)
        ensures r as int == self@.remaining_keys.len(),
    ;
}

// Drain

// yields owned values, not key/reference pairs
// removing one item from the iterator does not restore that value to the original slab
impl<'a, T> Iterator for Drain<'a, T> {
    type Item = T;

    fn next(&mut self) -> (r: Option<T>)
        ensures
            r == (if old(self)@.remaining.len() == 0 { None }
                else { Some(old(self)@.remaining[0]) }),
            final(self)@.remaining ==
                (if old(self)@.remaining.len() == 0 { old(self)@.remaining }
                else { old(self)@.remaining.drop_first() }),
    ;

    fn size_hint(&self) -> (r: (usize, Option<usize>))
        ensures r == (self@.remaining.len() as usize,
                    Some(self@.remaining.len() as usize)),
    ;
}

impl<'a, T> DoubleEndedIterator for Drain<'a, T> {
    fn next_back(&mut self) -> (r: Option<T>)
        ensures
            r == (if old(self)@.remaining.len() == 0 { None }
                else { Some(old(self)@.remaining.last()) }),
            final(self)@.remaining ==
                (if old(self)@.remaining.len() == 0 { old(self)@.remaining }
                else { old(self)@.remaining.drop_last() }),
    ;
}

impl<'a, T> ExactSizeIterator for Drain<'a, T> {
    fn len(&self) -> (r: usize)
        ensures r as int == self@.remaining.len(),
    ;
}

}