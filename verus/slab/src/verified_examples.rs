//! Verified clients of the specification (compiled only under Verus; never called).
//!
//! Each function replays a documented example or upstream test and proves its expected
//! outcome from the contracts alone. They show that the contracts are strong enough to be
//! used: a vacuous or too-weak specification would make these proofs fail.
#![allow(unused_imports)]

use crate::builder::Builder;
use crate::spec::*;
use crate::Slab;
use vstd::prelude::*;
use vstd::std_specs::iter::IteratorSpec;

verus! {

/// Crate docs, "Basic storing and retrieval" (reading part).
fn example_insert_get() {
    let mut slab: Slab<u64> = Slab::new();

    let hello = slab.insert(1);
    let world = slab.insert(2);
    assert(hello == 0 && world == 1);

    let h = slab[hello];
    let w = slab[world];
    assert(h == 1 && w == 2);

    let g = slab.get(world);
    assert(g == Some(&2u64));
    let missing = slab.get(123);
    assert(missing is None);
}

/// `Slab::vacant_key` docs: keys are reused last-in, first-out.
fn example_vacant_key() {
    let mut slab: Slab<u64> = Slab::new();
    let k = slab.vacant_key();
    assert(k == 0);

    slab.insert(0);
    let k = slab.vacant_key();
    assert(k == 1);

    slab.insert(1);
    slab.remove(0);
    let k = slab.vacant_key();
    assert(k == 0);
}

/// `VacantEntry` docs: the value can contain its own key.
fn example_vacant_entry() {
    let mut slab: Slab<(usize, u64)> = Slab::new();

    let hello = {
        let entry = slab.vacant_entry();
        let key = entry.key();

        entry.insert((key, 7));
        key
    };

    assert(slab@[hello as int] == Some((hello, 7u64)));
    let v = slab[hello];
    assert(v.0 == hello);
}

/// `Slab::get_mut` docs: writing through the returned reference updates the slab.
fn example_get_mut() {
    let mut slab: Slab<u64> = Slab::new();
    let key = slab.insert(5);

    match slab.get_mut(key) {
        Some(v) => *v = 6,
        None => {},
    }
    let v = slab[key];
    assert(v == 6);
}

/// `Slab::try_remove` docs and the upstream `try_remove` test.
fn example_try_remove() {
    let mut slab: Slab<u64> = Slab::new();
    let key = slab.insert(1);

    let first = slab.try_remove(key);
    assert(first == Some(1u64));
    let second = slab.try_remove(key);
    assert(second is None);
    let c = slab.contains(key);
    assert(!c);
}

/// `Slab::retain` docs.
fn example_retain() {
    let mut slab: Slab<u64> = Slab::new();

    let k1 = slab.insert(0);
    let k2 = slab.insert(1);
    let k3 = slab.insert(2);

    let f = |key: usize, val: &mut u64| -> (keep: bool)
        ensures
            keep == (key == k1 || *old(val) == 1),
            *final(val) == *old(val),
        { key == k1 || *val == 1 };
    let ghost pre = slab@;
    slab.retain(f);

    proof {
        assert(pre =~= seq![Some(0u64), Some(1u64), Some(2u64)]);
        assert(retain_step(f, 0, 0, slab@[0]));
        assert(retain_step(f, 1, 1, slab@[1]));
        assert(retain_step(f, 2, 2, slab@[2]));
        assert(slab@ =~= seq![Some(0u64), Some(1u64), None]);
    }
    let c1 = slab.contains(k1);
    let c2 = slab.contains(k2);
    let c3 = slab.contains(k3);
    assert(c1 && c2 && !c3);

    let len = slab.len();
    proof {
        reveal_with_fuel(num_occupied, 4);
        assert(slab@.drop_last() =~= seq![Some(0u64), Some(1u64)]);
        assert(slab@.drop_last().drop_last() =~= seq![Some(0u64)]);
        assert(slab@.drop_last().drop_last().drop_last() =~= Seq::<Option<u64>>::empty());
    }
    assert(len == 2);

    // The removed key is the next to be reused.
    proof {
        reveal_with_fuel(removed_keys_desc, 4);
        assert(removed_keys_desc(pre, slab@, 3) =~= seq![2usize]);
    }
    let k = slab.insert(9);
    assert(k == k3);
}

/// Upstream test `from_iterator_issue_100` (first case): pairs `[(1, ())]`, built through the
/// `Builder` that `FromIterator` uses. Before #102 the first insertion after this returned 0
/// but left the vacant list pointing at 0 again.
fn example_issue_100() {
    let mut builder: Builder<u64> = Builder::with_capacity(1);
    builder.pair(1, 10);
    let mut slab = builder.build();

    proof {
        let slots = seq![None, Some(10u64)];
        assert(slab@ =~= slots);
        reveal_with_fuel(vacant_keys_from, 3);
        assert(vacant_keys(slots) =~= seq![0usize]);
        assert(seq![0usize].reverse() =~= seq![0usize]);
    }

    let a = slab.insert(20);
    let b = slab.insert(30);
    let c = slab.insert(40);
    assert(a == 0 && b == 2 && c == 3);
}

/// `Slab::iter` docs: the values in key order, then `None`.
fn example_iter() {
    let mut slab: Slab<u64> = Slab::new();
    slab.insert(0);
    slab.insert(1);
    slab.insert(2);

    let mut iterator = slab.iter();
    proof {
        let slots = seq![Some(0u64), Some(1u64), Some(2u64)];
        assert(slab@ =~= slots);
        reveal_with_fuel(occupied_pairs, 4);
        assert(slots.drop_last().drop_last().drop_last() =~= Seq::<Option<u64>>::empty());
        assert(slots.drop_last().drop_last() =~= seq![Some(0u64)]);
        assert(slots.drop_last() =~= seq![Some(0u64), Some(1u64)]);
        assert(occupied_pairs(slots, 0) =~= seq![(0usize, 0u64), (1usize, 1u64), (2usize, 2u64)]);
    }
    let a = iterator.next();
    let b = iterator.next();
    let c = iterator.next();
    let d = iterator.next();
    assert(a == Some((0usize, &0u64)));
    assert(b == Some((1usize, &1u64)));
    assert(c == Some((2usize, &2u64)));
    assert(d is None);
}

/// Upstream test `iter_rev`, with `next_back` in place of `rev().collect()`: a removed key is
/// skipped from either end, and `len` counts what is left.
fn example_iter_rev() {
    let mut slab: Slab<u64> = Slab::new();
    slab.insert(0);
    slab.insert(1);
    slab.insert(2);
    slab.insert(3);
    slab.remove(0);

    let mut it = slab.iter();
    proof {
        let slots = seq![None, Some(1u64), Some(2u64), Some(3u64)];
        assert(slab@ =~= slots);
        reveal_with_fuel(occupied_pairs, 5);
        assert(slots.drop_last().drop_last().drop_last().drop_last() =~= Seq::<Option<u64>>::empty());
        assert(slots.drop_last().drop_last().drop_last() =~= seq![None::<u64>]);
        assert(slots.drop_last().drop_last() =~= seq![None, Some(1u64)]);
        assert(slots.drop_last() =~= seq![None, Some(1u64), Some(2u64)]);
        assert(occupied_pairs(slots, 0) =~= seq![(1usize, 1u64), (2usize, 2u64), (3usize, 3u64)]);
    }
    let n = it.len();
    assert(n == 3);
    let a = it.next_back();
    let b = it.next_back();
    let c = it.next_back();
    let d = it.next_back();
    assert(a == Some((3usize, &3u64)));
    assert(b == Some((2usize, &2u64)));
    assert(c == Some((1usize, &1u64)));
    assert(d is None);
    let n = it.len();
    assert(n == 0);
}

/// A `for` loop over `slab.iter()` sees each stored value under its key, and sees `slab.len()`
/// of them.
fn example_iter_for(slab: &Slab<u64>)
    requires
        slab.wf(),
{
    proof {
        slab.lemma_len_bound();
        lemma_num_occupied_le(slab@);
        lemma_occupied_pairs(slab@, 0);
    }
    let mut count: usize = 0;
    for (key, value) in it: slab.iter()
        invariant
            slab.wf(),
            it.seq() == ref_pairs(occupied_pairs(slab@, 0)),
            occupied_pairs(slab@, 0).len() <= usize::MAX,
            count == it.index(),
            forall|i: int|
                #![trigger occupied_pairs(slab@, 0)[i]]
                0 <= i < occupied_pairs(slab@, 0).len() ==> {
                    &&& occupied_pairs(slab@, 0)[i].0 < slab@.len()
                    &&& slab@[occupied_pairs(slab@, 0)[i].0 as int] == Some(
                        occupied_pairs(slab@, 0)[i].1,
                    )
                },
    {
        assert(slab@[key as int] == Some(*value));
        count += 1;
    }
    let len = slab.len();
    assert(count == len);
}

/// `slab[key] = value` stores the value, and the slab stays usable.
fn example_index_mut() {
    let mut slab: Slab<u64> = Slab::new();
    let key = slab.insert(1);

    slab[key] = 2;
    let v = slab[key];
    assert(v == 2);

    let next = slab.insert(3);
    assert(next == 1);
}

} // verus!
