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

} // verus!
