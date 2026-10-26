// Proofs for the obligations that compare_specs.py generates (gold spec vs. verified spec).
//
// This file holds only proof code, checked by Verus:
//   * lemmas: `proof fn` (and helper `spec fn`) items, placed in the generated module, where the
//     gold definitions (SlabModel, slab_rep_ok, ...) and crate::spec are in scope;
//   * hints: a `proof { ... }` block after a marker line
//         // @hint <obligation> before|after
//     which is inserted into that obligation's wrapper before or after the call it checks
//     (`*` as the obligation: every obligation). In a wrapper, `slf` is the receiver, `pre` its
//     value before the call, and `ret` the result. A hint for `X` also applies to its
//     capacity-free variant `X__nocap`;
//   * notes: comment lines after a marker line
//         // @note <obligation>
//     explaining why that obligation stays unproved (the specs differ). The report shows a note
//     next to the failure; notes are not checked.
// assume, admit, external_body, axioms and other trusted constructs are rejected.

// ====================================================================== occupied count

// Claude's occupied count (recursion from the back) is the gold model's filter count.
proof fn lemma_occupied_count<T>(m: SlabModel<T>)
    ensures
        num_occupied(m.slots) == m.occupied_count(),
    decreases m.slots.len(),
{
    reveal(Seq::filter);
    if m.slots.len() > 0 {
        let init = SlabModel { slots: m.slots.drop_last(), free: m.free, capacity: m.capacity };
        lemma_occupied_count(init);
    }
}

// =========================================================================== free list

// Claude's vacant list as gold keys (`int`).
spec fn ints(s: Seq<usize>) -> Seq<int> {
    s.map_values(|x: usize| x as int)
}

// A duplicate-free sequence of keys below `n` has at most `n` elements.
proof fn lemma_unique_keys_len(s: Seq<int>, n: int)
    requires
        0 <= n,
        s.no_duplicates(),
        forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < n,
    ensures
        s.len() <= n,
{
    s.unique_seq_to_set();
    s.to_set_ensures();
    vstd::set_lib::lemma_int_range(0, n);
    assert forall|x: int| #[trigger] s.to_set().contains(x) implies vstd::set_lib::set_int_range(0, n).contains(x) by {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
        assert(s[i] == x);
    }
    vstd::set_lib::lemma_len_subset(s.to_set(), vstd::set_lib::set_int_range(0, n));
}

// Following the gold free links along a chain that Claude's spec describes gives that chain,
// and the links terminate.
proof fn lemma_follow_chain<T>(entries: Seq<Entry<T>>, list: Seq<usize>, i: int, fuel: nat)
    requires
        0 <= i <= list.len(),
        list.len() - i <= fuel,
        entries.len() <= usize::MAX,
        forall|j: int| 0 <= j < list.len() ==> ((#[trigger] list[j]) as int) < entries.len(),
        forall|j: int|
            #![trigger entries[list[j] as int]]
            0 <= j < list.len() ==> entries[list[j] as int] == Entry::<T>::Vacant(
                if j + 1 < list.len() {
                    list[j + 1]
                } else {
                    entries.len() as usize
                },
            ),
    ensures
        follow_free_links(
            entries,
            if i < list.len() { list[i] as int } else { entries.len() as int },
            fuel,
        ) == ints(list.subrange(i, list.len() as int)),
        free_links_terminate(
            entries,
            if i < list.len() { list[i] as int } else { entries.len() as int },
            fuel,
        ),
    decreases list.len() - i,
{
    if i < list.len() {
        lemma_follow_chain(entries, list, i + 1, (fuel - 1) as nat);
        assert(ints(list.subrange(i, list.len() as int)) =~= seq![list[i] as int] + ints(
            list.subrange(i + 1, list.len() as int),
        ));
    } else {
        assert(ints(list.subrange(i, list.len() as int)) =~= Seq::<int>::empty());
    }
}

// The gold free links, followed from `current` while they terminate, form a chain in Claude's
// sense.
proof fn lemma_follow_is_chain<T>(entries: Seq<Entry<T>>, current: int, fuel: nat)
    requires
        free_links_terminate(entries, current, fuel),
        entries.len() <= usize::MAX,
    ensures
        ({
            let f = follow_free_links(entries, current, fuel);
            &&& current == if f.len() == 0 { entries.len() as int } else { f[0] }
            &&& forall|j: int| 0 <= j < f.len() ==> 0 <= #[trigger] f[j] < entries.len()
            &&& forall|j: int|
                #![trigger f[j]]
                0 <= j < f.len() ==> entries[f[j]] == Entry::<T>::Vacant(
                    (if j + 1 < f.len() {
                        f[j + 1]
                    } else {
                        entries.len() as int
                    }) as usize,
                )
        }),
    decreases fuel,
{
    if current != entries.len() {
        if let Entry::Vacant(n) = entries[current] {
            lemma_follow_is_chain(entries, n as int, (fuel - 1) as nat);
            let f2 = follow_free_links(entries, n as int, (fuel - 1) as nat);
            let f = follow_free_links(entries, current, fuel);
            assert(f == seq![current] + f2);
            assert forall|j: int| #![trigger f[j]] 0 <= j < f.len() implies entries[f[j]]
                == Entry::<T>::Vacant(
                (if j + 1 < f.len() {
                    f[j + 1]
                } else {
                    entries.len() as int
                }) as usize,
            ) by {
                if j > 0 {
                    assert(f[j] == f2[j - 1]);
                }
            }
        }
    }
}

// ============================================================== the two invariants agree

// Claude's invariant gives the gold one; the slots, free lists and counts of the two models agree.
proof fn lemma_wf_gold<T>(s: Slab<T>)
    requires
        s.wf(),
    ensures
        slab_rep_ok(&s),
        s.gv().slots == s@,
        s.gv().free == ints(s.vacant_list()),
        s.gv().occupied_count() == num_occupied(s@),
{
    broadcast use axiom_vec_len_le_capacity;

    s.lemma_vacant_list();
    s.lemma_len_bound();
    let entries = s.entries@;
    let list = s.vacant_list();
    let free = ints(list);
    assert(s.gv().slots =~= s@);
    lemma_occupied_count(s.gv());
    assert(free.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < free.len() && 0 <= j < free.len() && i != j implies free[i]
            != free[j] by {
            assert(list[i] != list[j]);
        }
    }
    assert forall|i: int| 0 <= i < free.len() implies 0 <= #[trigger] free[i] < entries.len() by {
        assert(list[i] as int == free[i]);
    }
    lemma_unique_keys_len(free, entries.len() as int);
    lemma_follow_chain(entries, list, 0, entries.len() as nat);
    assert(list.subrange(0, list.len() as int) =~= list);
    let m = s.gv();
    assert(m.free == free);
    assert forall|j: int| 0 <= j < m.free.len() implies (0 <= #[trigger] m.free[j] < m.slots.len()
        && m.slots[m.free[j]].is_none()) by {
        assert(m.free[j] == list[j] as int);
    }
    assert forall|i: int| 0 <= i < m.slots.len() implies (m.slots[i].is_none() <==> m.free.contains(i)) by {
        if m.slots[i].is_none() {
            assert(s@[i] is None);
            assert(list.contains(i as usize));
            let j = choose|j: int| 0 <= j < list.len() && list[j] == i as usize;
            assert(m.free[j] == i);
        }
        if m.free.contains(i) {
            let j = choose|j: int| 0 <= j < m.free.len() && m.free[j] == i;
            assert(list[j] as int == i);
        }
    }
}

// Gold keys as Claude's keys (`usize`).
spec fn usizes(s: Seq<int>) -> Seq<usize> {
    s.map_values(|x: int| x as usize)
}

// Keys in range survive the round trip through `usize`, and stay distinct.
proof fn lemma_usizes<T>(f: Seq<int>, n: int)
    requires
        n <= usize::MAX,
        forall|j: int| 0 <= j < f.len() ==> 0 <= #[trigger] f[j] < n,
    ensures
        ints(usizes(f)) == f,
        forall|j: int| 0 <= j < f.len() ==> (#[trigger] usizes(f)[j]) as int == f[j],
        f.no_duplicates() ==> usizes(f).no_duplicates(),
{
    assert(ints(usizes(f)) =~= f);
    if f.no_duplicates() {
        assert forall|i: int, j: int|
            0 <= i < usizes(f).len() && 0 <= j < usizes(f).len() && i != j implies usizes(f)[i]
            != usizes(f)[j] by {
            assert(f[i] != f[j]);
        }
    }
}

// The gold free list from `next`, as Claude's keys, is a vacant chain in Claude's sense.
proof fn lemma_gold_chain<T>(entries: Seq<Entry<T>>, next: usize)
    requires
        free_links_terminate(entries, next as int, entries.len() as nat),
        entries.len() <= usize::MAX,
    ensures
        is_vacant_chain(entries, next, usizes(follow_free_links(entries, next as int, entries.len() as nat))),
{
    lemma_follow_is_chain(entries, next as int, entries.len() as nat);
    let f = follow_free_links(entries, next as int, entries.len() as nat);
    let list = usizes(f);
    lemma_usizes::<T>(f, entries.len() as int);
    assert forall|j: int|
        #![trigger entries[list[j] as int]]
        0 <= j < list.len() implies entries[list[j] as int] == Entry::<T>::Vacant(
        if j + 1 < list.len() {
            list[j + 1]
        } else {
            entries.len() as usize
        },
    ) by {
        assert(list[j] as int == f[j]);
        if j + 1 < list.len() {
            assert(list[j + 1] as int == f[j + 1]);
        }
    }
}

// Under the gold invariant, the gold free list holds every vacant entry.
proof fn lemma_gold_complete<T>(s: Slab<T>)
    requires
        slab_rep_ok(&s),
    ensures
        forall|k: int|
            0 <= k < s.entries@.len() && (#[trigger] s.entries@[k]) is Vacant ==> usizes(
                s.gv().free,
            ).contains(k as usize),
{
    let m = s.gv();
    assert forall|k: int|
        0 <= k < s.entries@.len() && (#[trigger] s.entries@[k]) is Vacant implies usizes(
        m.free,
    ).contains(k as usize) by {
        assert(m.slots[k].is_none());
        assert(m.free.contains(k));
        let j = choose|j: int| 0 <= j < m.free.len() && m.free[j] == k;
        assert(usizes(m.free)[j] == k as usize);
    }
}

// The gold invariant gives Claude's; the slots, free lists and counts of the two models agree.
proof fn lemma_gold_wf<T>(s: Slab<T>)
    requires
        slab_rep_ok(&s),
    ensures
        s.wf(),
        s.gv().slots == s@,
        s.gv().free == ints(s.vacant_list()),
        s.gv().occupied_count() == num_occupied(s@),
{
    s.lemma_len_bound();
    let m = s.gv();
    assert(m.slots =~= s@);
    lemma_occupied_count(m);
    lemma_gold_chain(s.entries@, s.next);
    lemma_usizes::<T>(m.free, s.entries@.len() as int);
    lemma_gold_complete(s);
    s.lemma_wf_intro(usizes(m.free));
}

// Both directions, for every slab: triggered by a slab's `wf()` or gold invariant, so that they
// also apply to the prophesied final value of a slab borrowed by a returned `&mut`.
proof fn lemma_bridge_all<T>()
    ensures
        forall|s: Slab<T>|
            #![trigger s.wf()]
            s.wf() ==> {
                &&& slab_rep_ok(&s)
                &&& s.gv().slots == s@
                &&& s.gv().free == ints(s.vacant_list())
                &&& s.gv().occupied_count() == num_occupied(s@)
            },
        forall|s: Slab<T>|
            #![trigger s.gold_inv()]
            s.gold_inv() ==> {
                &&& s.wf()
                &&& s.gv().slots == s@
                &&& s.gv().free == ints(s.vacant_list())
                &&& s.gv().occupied_count() == num_occupied(s@)
            },
{
    assert forall|s: Slab<T>| #![trigger s.wf()] s.wf() implies {
        &&& slab_rep_ok(&s)
        &&& s.gv().slots == s@
        &&& s.gv().free == ints(s.vacant_list())
        &&& s.gv().occupied_count() == num_occupied(s@)
    } by {
        lemma_wf_gold(s);
    }
    assert forall|s: Slab<T>| #![trigger s.gold_inv()] s.gold_inv() implies {
        &&& s.wf()
        &&& s.gv().slots == s@
        &&& s.gv().free == ints(s.vacant_list())
        &&& s.gv().occupied_count() == num_occupied(s@)
    } by {
        lemma_gold_wf(s);
    }
}

// ======================================================================== key lists

// Distinct `usize` lists give distinct gold lists.
proof fn lemma_ints_injective(a: Seq<usize>, b: Seq<usize>)
    requires
        ints(a) == ints(b),
    ensures
        a == b,
{
    assert(ints(a).len() == a.len() && ints(b).len() == b.len());
    assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
        assert(ints(a)[i] == a[i] as int && ints(b)[i] == b[i] as int);
    }
    assert(a =~= b);
}

// The same, for every pair of lists `ints` is applied to.
proof fn lemma_ints_injective_all()
    ensures
        forall|a: Seq<usize>, b: Seq<usize>| #![trigger ints(a), ints(b)] ints(a) == ints(b) ==> a == b,
{
    assert forall|a: Seq<usize>, b: Seq<usize>| #![trigger ints(a), ints(b)] ints(a) == ints(b) implies a
        == b by {
        lemma_ints_injective(a, b);
    }
}

// `ints` distributes over concatenation.
proof fn lemma_ints_concat(a: Seq<usize>, b: Seq<usize>)
    ensures
        ints(a + b) == ints(a) + ints(b),
{
    assert(ints(a + b) =~= ints(a) + ints(b));
}

// ======================================================================== insert, remove

// The gold insertion, read back in Claude's terms.
proof fn lemma_gold_insert<T>(pre: Slab<T>, post: Slab<T>, key: usize, val: T)
    requires
        pre.wf(),
        post.wf(),
        key as int == pre.gv().vacant_key(),
        post.gv().slots == pre.gv().inserted(val, post.gv().capacity).slots,
        post.gv().free == pre.gv().inserted(val, post.gv().capacity).free,
    ensures
        Slab::insert_post(pre, post, key, val),
{
    lemma_wf_gold(pre);
    lemma_wf_gold(post);
    pre.lemma_vacant_list();
    let vl = pre.vacant_list();
    if vl.len() > 0 {
        assert(ints(vl.drop_first()) =~= ints(vl).drop_first());
        lemma_ints_injective(post.vacant_list(), vl.drop_first());
    } else {
        assert(vl =~= Seq::<usize>::empty());
        lemma_ints_injective(post.vacant_list(), vl);
    }
}

// The gold removal of an occupied key, read back in Claude's terms.
proof fn lemma_gold_removed<T>(pre: Slab<T>, post: Slab<T>, key: usize)
    requires
        pre.wf(),
        post.wf(),
        pre.gv().present(key as int),
        post.gv().slots == pre.gv().removed(key as int).slots,
        post.gv().free == pre.gv().removed(key as int).free,
    ensures
        pre.spec_contains(key),
        post@ == pre@.update(key as int, None),
        post.vacant_list() == seq![key] + pre.vacant_list(),
{
    lemma_wf_gold(pre);
    lemma_wf_gold(post);
    lemma_ints_concat(seq![key], pre.vacant_list());
    assert(ints(seq![key]) =~= seq![key as int]);
    lemma_ints_injective(post.vacant_list(), seq![key] + pre.vacant_list());
}

// Equal gold slots and free lists: the same slab in Claude's terms.
proof fn lemma_gold_unchanged<T>(pre: Slab<T>, post: Slab<T>)
    requires
        pre.wf(),
        post.wf(),
        post.gv().slots == pre.gv().slots,
        post.gv().free == pre.gv().free,
    ensures
        Slab::unchanged(pre, post),
{
    lemma_wf_gold(pre);
    lemma_wf_gold(post);
    lemma_ints_injective(post.vacant_list(), pre.vacant_list());
}

// =========================================================================== retain

// A slot vacant before stays vacant, so the number of values cannot grow.
proof fn lemma_num_occupied_le<T>(pre: Seq<Option<T>>, post: Seq<Option<T>>)
    requires
        post.len() == pre.len(),
        forall|k: int| 0 <= k < pre.len() && (#[trigger] pre[k]) is None ==> post[k] is None,
    ensures
        num_occupied(post) <= num_occupied(pre),
    decreases pre.len(),
{
    if pre.len() > 0 {
        assert(pre[pre.len() - 1] is None ==> post[pre.len() - 1] is None);
        assert forall|k: int| 0 <= k < pre.drop_last().len() && (#[trigger] pre.drop_last()[k]) is None
            implies post.drop_last()[k] is None by {
            assert(pre[k] is None);
        }
        lemma_num_occupied_le(pre.drop_last(), post.drop_last());
    }
}

// The keys below `n` that `p` selects, in decreasing order, are Claude's `removed_keys_desc`.
proof fn lemma_removed_keys<T>(pre: Seq<Option<T>>, post: Seq<Option<T>>, n: int, p: spec_fn(int) -> bool)
    requires
        0 <= n <= pre.len(),
        pre.len() <= usize::MAX,
        forall|i: int| 0 <= i < n ==> #[trigger] p(i) == (pre[i] is Some && post[i] is None),
    ensures
        ints(removed_keys_desc(pre, post, n)) == Seq::new(n as nat, |i: int| i).filter(p).reverse(),
    decreases n,
{
    reveal(Seq::filter);
    let s = Seq::new(n as nat, |i: int| i);
    if n > 0 {
        lemma_removed_keys(pre, post, n - 1, p);
        let s0 = Seq::new((n - 1) as nat, |i: int| i);
        assert(s.drop_last() =~= s0);
        let f0 = s0.filter(p);
        let r0 = removed_keys_desc(pre, post, n - 1);
        if p(n - 1) {
            assert(s.filter(p) == f0.push(n - 1));
            assert(f0.push(n - 1).reverse() =~= seq![n - 1] + f0.reverse());
            assert(ints(seq![(n - 1) as usize] + r0) =~= seq![n - 1] + ints(r0));
        } else {
            assert(s.filter(p) == f0);
        }
    } else {
        assert(ints(removed_keys_desc(pre, post, n)) =~= Seq::<int>::empty());
    }
}

// Claude's retain postcondition gives the gold one, with the events read off the final slab.
proof fn lemma_retain_gold<T>(pre: Slab<T>, post: Slab<T>)
    requires
        pre.wf(),
        post.wf(),
        post@.len() == pre@.len(),
        forall|k: int| 0 <= k < pre@.len() && (#[trigger] pre@[k]) is None ==> post@[k] is None,
        post.vacant_list() == removed_keys_desc(pre@, post@, pre@.len() as int) + pre.vacant_list(),
    ensures
        post.gv().occupied_count() <= pre.gv().occupied_count(),
        exists|events: Seq<Option<RetainEvent<T>>>|
            pre.gv().retain_events_valid(events) && post.gv().slots == pre.gv().retained(events).slots
                && post.gv().free == pre.gv().retained(events).free,
{
    lemma_wf_gold(pre);
    lemma_wf_gold(post);
    pre.lemma_vacant_list();
    let (a, b) = (pre@, post@);
    lemma_num_occupied_le(a, b);
    let events = Seq::new(
        a.len(),
        |k: int|
            if a[k] is Some {
                Some(
                    RetainEvent {
                        after_callback: if b[k] is Some {
                            b[k]->Some_0
                        } else {
                            a[k]->Some_0
                        },
                        keep: b[k] is Some,
                    },
                )
            } else {
                None
            },
    );
    let m = pre.gv();
    let r = m.retained(events);
    assert(m.retain_events_valid(events));
    assert(r.slots =~= b);
    let rk = removed_keys_desc(a, b, a.len() as int);
    lemma_removed_keys(a, b, a.len() as int, |i: int| m.slots[i].is_some() && !events[i].unwrap().keep);
    lemma_ints_concat(rk, pre.vacant_list());
    assert(post.gv().free == r.free);
}

// The gold retain postcondition gives Claude's vacant list.
proof fn lemma_gold_retain<T>(pre: Slab<T>, post: Slab<T>)
    requires
        pre.wf(),
        post.wf(),
        exists|events: Seq<Option<RetainEvent<T>>>|
            pre.gv().retain_events_valid(events) && post.gv().slots == pre.gv().retained(events).slots
                && post.gv().free == pre.gv().retained(events).free,
    ensures
        post.vacant_list() == removed_keys_desc(pre@, post@, pre@.len() as int) + pre.vacant_list(),
{
    lemma_wf_gold(pre);
    lemma_wf_gold(post);
    pre.lemma_vacant_list();
    let events = choose|events: Seq<Option<RetainEvent<T>>>|
        pre.gv().retain_events_valid(events) && post.gv().slots == pre.gv().retained(events).slots
            && post.gv().free == pre.gv().retained(events).free;
    let (a, b) = (pre@, post@);
    let m = pre.gv();
    let r = m.retained(events);
    assert forall|i: int| 0 <= i < a.len() implies b[i] == r.slots[i] by {}
    let rk = removed_keys_desc(a, b, a.len() as int);
    lemma_removed_keys(a, b, a.len() as int, |i: int| m.slots[i].is_some() && !events[i].unwrap().keep);
    lemma_ints_concat(rk, pre.vacant_list());
    lemma_ints_injective(post.vacant_list(), rk + pre.vacant_list());
}

// ================================================================================ notes

// @note gold_implies_claude__Slab__new
// The gold `new` promises `s@ == SlabModel::empty()` but not `s@.valid()`, which `with_capacity`
// states. The view does not fix the `len` field, so the result is not known to satisfy
// `slab_rep_ok`. With `s@.valid()` added to the gold contract, this obligation is proved.

// @note gold_implies_claude__Slab__contains
// Claude's `contains` has no precondition (it is safe on any slab); the gold contract requires
// `self@.valid()`. Claude's contract is the more general one.

// @note gold_implies_claude__Slab__get
// As for `contains`: no precondition in Claude's contract, `self@.valid()` in the gold one.

// @note gold_implies_claude__Slab__clear
// As for `contains`: no precondition in Claude's contract, `old(self)@.valid()` in the gold one.

// @note gold_implies_claude__Slab__vacant_entry
// The gold contract gives only the entry's key. It does not say that the entry borrows this slab
// in its current state, or that the slab ends in the entry's final state, so the gold
// precondition of `VacantEntry::insert` cannot be established from it. Claude's contract says
// both (`entry.slab() == *old(self)`, `entry.final_slab() == *final(self)`).

// @note gold_implies_claude__Slab__get_mut
// The gold contract does not promise `final(self)@.valid()`: the view equality fixes the slots
// and the free list but not the `len` field. With that clause added, this obligation is proved.

// @note gold_implies_claude__Slab__get2_mut
// As for `get_mut`: the gold contract does not promise `final(self)@.valid()`. With that clause
// added, this obligation is proved.

// @note gold_implies_claude__Slab__retain
// The gold events are existential and not tied to the closure (the gold comment says so).
// Claude's `retain_step` says that each value was passed to `f`, and that `f`'s result and the
// value it leaves decide the slot (`f.ensures`). The vacant-list clause is proved.

// @note claude_implies_gold__Slab__retain
// Claude's `retain` requires `f.requires((key, value))` for every key and value: Verus can only
// call a closure whose precondition holds. A closure without a `requires` clause meets it
// trivially, so leaving it out of the gold spec is harmless. Apart from this, only the capacity
// clauses fail.

// @note claude_implies_gold__Slab__retain__nocap
// Only the closure precondition fails (see the full obligation). The postconditions are proved,
// with the events read off the final slab.

// @note gold_implies_claude__VacantEntry__insert
// The gold contract only gives `*r == val`; its own comment notes that the insertion into the
// borrowed slab is still to be specified. Claude's contract states it (`insert_post`).

// ================================================================================ hints

// @hint * before
proof {
    lemma_bridge_all::<T>();
}

// @hint claude_implies_gold__Slab__retain after
proof {
    lemma_retain_gold(pre, *slf);
}

// @hint gold_implies_claude__Slab__insert after
proof {
    lemma_gold_insert(pre, *slf, ret, val);
}

// @hint gold_implies_claude__Slab__remove after
proof {
    lemma_gold_removed(pre, *slf, key);
}

// @hint gold_implies_claude__Slab__try_remove after
proof {
    if pre.gv().present(key as int) {
        lemma_gold_removed(pre, *slf, key);
    } else {
        lemma_gold_unchanged(pre, *slf);
    }
}

// @hint gold_implies_claude__Slab__retain after
proof {
    lemma_gold_retain(pre, *slf);
}

// @hint gold_implies_claude__Slab__get_mut before
proof {
    lemma_ints_injective_all();
}

// @hint gold_implies_claude__Slab__get2_mut before
proof {
    lemma_ints_injective_all();
}
