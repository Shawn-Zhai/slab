# Review: Claude's verified spec against the human-written spec (2026-11-04)

**Inputs.** "Claude's spec" is the specifications and proofs in [`../verus/slab/src/`](../verus/slab/src/).
"The human spec" is Shawn's [`human_written_spec.rs`](human_written_spec.rs). The human spec was the reference,
and both were read as possibly wrong. This folder is a copy of `verus/` with the amendments
applied. Its `human_written_spec.rs` is byte-identical to the original. [`amendments.diff`](amendments.diff)
shows every hand edit against `verus/`.

## Outcome

**Claude's spec contains no false statement**, since Verus proves every contract against the code.
**Three of its contracts were weaker than the human spec.** All three are amended and verified:

| # | Function | Problem in Claude's spec | Human spec | Amendment |
|---|---|---|---|---|
| A1 | `Iter::size_hint` | No postcondition. vstd's iterator spec does not cover `size_hint`, so a client learned nothing from the call | `r == (n, Some(n))` for the `n` items left | `ensures r.0 == self.remaining().len(), r.1 == Some(r.0)` |
| A2 | `retain` | Required `f` to be callable on *every* `(key, &mut value)`. The upstream test `retain` fails to verify against it, because its closure asserts `key == *x` | no requirement on `f` | `f` must be callable only on the arguments `retain` passes: each occupied key, with a reference to the value stored there. Verus needs some such clause to call `f`, and this is the weakest one |
| A3 | `retain` | That the number of values does not grow followed from the contract only through an induction, which each client would have to write | `final.occupied_count() <= old.occupied_count()` | `ensures num_occupied(final(self)@) <= num_occupied(old(self)@)`, proved with the new lemma `lemma_num_occupied_vacated` |

**The human spec has mistakes too** (H1–H6 below; the file is unchanged). The two that matter
most are these. `vacant_entry` and `VacantEntry::insert` cannot be used together. And `retain`'s
contract is met by an implementation that ignores `f`. The fixes suggested for H1 and H2 were
checked mechanically.

**Not amended, because they cannot be written yet.** These are the capacity clauses, and contracts
for the 30 functions Claude left trusted. Each one needs a std method that this Verus (0.2026.10.18)
cannot call under `--no-cheating`. [`vstd_probe.rs`](vstd_probe.rs) shows which methods.

**No executable code changed.** Every amendment is ghost code. `detect_changes.py` finds the
same changes as before (22 changed items, 9 added, 10 trust markers), and all still match their
existing approvals.

## How the specs were compared

1. Both specs were read against the code (upstream `../src/lib.rs` and the annotated
   `slab/src/`) and the docs.
2. `compare_specs.py` generates refinement obligations both ways and has Verus check them. It
   was extended (see [Tooling fixes](#tooling-and-documentation-fixes)). The gold `Iter`
   placeholder can now be read in terms of the crate, which brings `iter` and five `Iter`
   methods into the comparison. Before, they were skipped. 26 of the 56 public functions are now
   compared mechanically; the other 30 are trusted in the verified crate.
3. Small probe files showed which std methods vstd lets verified code call.
4. For each amendment, a verified client uses it. The same clients were also run against the
   original crate, where they must fail.

## Verdicts by function

"Equal except capacity" means the human spec adds capacity clauses, which no `--no-cheating`
contract can state (see [Not amended](#not-amended-and-why)). "Proved" refers to the
`compare_specs.py` obligations in [`spec_comparison.md`](spec_comparison.md).

| Function | Verdict | Notes |
|---|---|---|
| `new`, `Default::default` | Claude stronger on the invariant; equal except capacity | The human spec does not promise `valid()` (H2) |
| `with_capacity` | Equal except capacity | |
| `len`, `is_empty`, `vacant_key`, `VacantEntry::key` | Equivalent | proved both ways |
| `contains`, `get` | Equivalent postconditions; Claude more general | Claude has no precondition; the human spec requires `valid()` (H4) |
| `Index::index` | Equivalent; Claude more general | Claude requires only an occupied key (vstd's `index_req`) |
| `insert`, `try_remove`, `remove` | Equal except capacity | proved both ways without capacity |
| `clear` | Equal except capacity; Claude more general | Claude has no precondition |
| `get_mut`, `get2_mut`, `IndexMut::index_mut` | Equal except capacity; Claude also promises `wf()` afterwards | Both specs require `key1, key2 <= len` for `get2_mut`, since upstream panics past it (finding F1 in VERIFICATION.md) |
| `vacant_entry`, `VacantEntry::insert` | Claude stronger | The human pair cannot be used together (H1) |
| `retain` | **Amended (A2, A3).** Otherwise Claude much stronger | Claude ties each slot to `f.ensures`; the human contract allows any outcome (H3) |
| `iter` | Equivalent | proved both ways, newly compared |
| `Iter::next`, `next_back`, `len` | Equivalent | Claude ⇒ human proved, newly compared |
| `Iter::size_hint` | **Amended (A1)** | unproved for the original crate, proved now |
| `Iter::clone` | Claude stronger (`r == *self`) | |
| `capacity`, `reserve`, `reserve_exact` | Human only; blocked | `Vec::capacity`, `Vec::reserve_exact` unsupported. The human contracts match the code |
| `shrink_to_fit` | Human only; blocked | `Vec::shrink_to_fit` unsupported. The verified private `remove_vacant_tail` has the human `shrunk` behavior for slots and free list |
| `compact` | Human only; blocked | Drop guard, `mem::forget`, `Vec::shrink_to_fit`. The human trace model was checked by hand against the code and matches it; its events are not tied to `rekey` (H3) |
| `drain` and `Drain`'s 4 methods | Human only; blocked | `vec::Drain` unsupported |
| `get_unchecked`, `get_unchecked_mut` | Human only; blocked | `<[T]>::get_unchecked` unsupported. The human precondition (occupied, not only in bounds) is right for a normal return: a vacant key reaches `unreachable!()` |
| `get2_unchecked_mut`, `get_disjoint_mut`, `key_of` | Human only; blocked | raw pointers, `MaybeUninit`, pointer-to-integer casts. `disjoint_error` matches the code's error order |
| `iter_mut`, `IterMut`'s 4 methods, `IntoIterator for &mut Slab` | Human only; blocked | yielding `&mut T` needs prophecy machinery |
| `IntoIterator for Slab` / `&Slab`, `IntoIter`'s 4 methods | Human only; blocked | trait methods cannot require `wf()`; `IntoIter` needs `no_unwind` for `vec::IntoIter::next` |
| `Clone::clone`, `Clone::clone_from` | Human only; blocked | `Vec::clone_from` unsupported, and a trait impl is verified all or nothing |
| `FromIterator::from_iter` | Human only; blocked | arbitrary `IntoIterator`, `size_hint`. The verified `Builder` it drives gives the human slots and also fixes the free list |

## The amendments

### A1. `Iter::size_hint` gets a postcondition

[`slab/src/lib.rs:1340`](slab/src/lib.rs#L1340). Before ([`../verus/slab/src/lib.rs:1328`](../verus/slab/src/lib.rs#L1328)):

```rust
fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
}
```

After:

```rust
fn size_hint(&self) -> (r: (usize, Option<usize>))
    ensures
        r.0 == self.remaining().len(),
        r.1 == Some(r.0),
{
    proof {
        use_type_invariant(self);
    }
    (self.len, Some(self.len))
}
```

`next`, `next_back` and `len` inherit contracts from vstd's iterator laws. `size_hint` does not:
vstd has no spec for it ([`vstd_probe.rs`](vstd_probe.rs)). So the crate must state it. The
equality is stated on integers, so it also tells clients that the count fits in a `usize`.

Evidence:
- `compare_specs.py`, run with the same tool and proofs: unproved for the original crate, proved now.
- Client `example_iter_size_hint` ([`verified_examples.rs:332`](slab/src/verified_examples.rs#L332)):
  `size_hint` is `(len, Some(len))` and drops by one after `next`. Both of its assertions fail on
  the original crate.
- Mutant M23, where `size_hint` counts vacant slots too, is rejected by the new postcondition.

### A2. `retain` requires only what it uses

[`slab/src/lib.rs:1056`](slab/src/lib.rs#L1056). Before:

```rust
requires
    old(self).wf(),
    forall|key: usize, value: &mut T| f.requires((key, value)),
```

After:

```rust
requires
    old(self).wf(),
    // `f` is only called with an occupied key and a reference to the value stored there.
    forall|key: usize, value: &mut T|
        #![trigger f.requires((key, value))]
        old(self).spec_contains(key) && *value == old(self)@[key as int]->Some_0
            ==> f.requires((key, value)),
```

`retain` visits each key once, in increasing order, before anything else touches that slot. So
`f` only ever sees `(k, v)` with `v` the stored value. The old clause also demanded `f` for keys
and values that never occur. The loop invariant changed the same way, and the proof needed nothing
else. The change is backward compatible, since every caller of the old contract meets the new one.

Evidence: upstream's own test `retain` (`tests/slab.rs:222`) passes a closure that asserts
`key == *x`. Client `example_retain_upstream_test`
([`verified_examples.rs:143`](slab/src/verified_examples.rs#L143)) replays it, without the
`capacity` checks. It models the assertion as `requires key == *old(x)` and keeps it as
`runtime_assert`. Against the original crate the call to `retain` is rejected with "precondition
not satisfied"; now it verifies, along with every remaining assertion of the test.

The human spec has no closure precondition at all. Verus cannot call a closure without one, so
`compare_specs.py` still reports this clause as the single Claude ⇒ human failure. It is the
minimal remaining gap.

### A3. `retain` states that the number of values does not grow

New postcondition `num_occupied(final(self)@) <= num_occupied(old(self)@)`, proved by the new
lemma `lemma_num_occupied_vacated` ([`slab/src/spec.rs:742`](slab/src/spec.rs#L742)), which is
public, so clients can use it too. Before, it followed from "vacant slots stay vacant" only by
induction. `spec_proofs.rs` needed its own induction lemma for this one gold clause, and every
verified client would have needed one as well. That lemma is now deleted from `spec_proofs.rs`, and
the gold clause is proved from the contract directly. Client `example_retain_len`
([`verified_examples.rs:200`](slab/src/verified_examples.rs#L200)) shows `len()` does not grow for
any slab and any closure. Against the original crate, its assertion fails even under the old
precondition.

### Tooling and documentation fixes

- **`compare_specs.py`**:
  - Default gold path. It still pointed to `humen_written_spec.rs`, so the script failed without
    `--gold` after the file was renamed.
  - New `// @interpret <name>` convention. It replaces a gold `uninterp` placeholder with a
    definition from `spec_proofs.rs`. It is used once: the gold `Iter` model is read as Claude's
    `remaining()` with `int` keys and dereferenced values. The report prints the definition,
    because it is a modeling choice. Self-check: corrupting three gold iterator clauses (wrong pair
    from `next`, `size_hint` off by one, `iter` pairs reversed) turns each one unproved.
  - A failed multi-line precondition is now shown whole, not only its last line.
- **`spec_proofs.rs`**: the interpretation, `int_pairs`, four lemmas linking Claude's
  `occupied_pairs` to the gold `pairs()`, and two hints. The `retain` induction lemma is removed,
  as described under A3, and the `retain` notes are updated.
- **`negative_controls.py`**: M23. **`verified_examples.rs`**: the three clients above.
- **`slab/README.md`**: counts and file name. It also said vstd does not specify
  `<[T]>::get_mut`; this vstd does, as VERIFICATION.md already said.
- **`VERIFICATION.md`**: counts, contracts, comparison and controls updated.
  **`upstream.diff`** regenerated with the recipe that reproduces the original byte for byte.
  **`changes_report.md`** regenerated; only four trust-marker line numbers moved.

## Findings in the human spec (file unchanged)

**H1. `vacant_entry` and `VacantEntry::insert` cannot be used together** (lines 754, 1036).
`vacant_entry` promises only `e.key == vacant_key()`. `VacantEntry::insert` requires
`self.slab@.valid()` and `self.key == self.slab@.vacant_key()`, but nothing links `e.slab` to the
slab it was created from. So no caller can meet that precondition. `VacantEntry::insert` also
leaves the insertion unspecified, which its comment acknowledges. Suggested fix:

```rust
// vacant_entry, ensures:
*e.slab == *old(self),
*final(e.slab) == *final(self),
// VacantEntry::insert, ensures:
(*final(self.slab))@.valid(),
(*final(self.slab))@ == (*old(self.slab))@.inserted(*final(r), (*final(self.slab))@.capacity),
```

Checked: with these clauses in a scratch copy, human ⇒ Claude is proved for both functions. That
run also needs one hint, a version of `lemma_gold_insert` quantified over all slabs, because the
final slab is prophetic.

**H2. Some postconditions omit `valid()`.** `with_capacity`, `insert`, the removals, `clear` and
`retain` promise it, but these do not:
- `new` (651) and `Default::default` (1054);
- `get_mut` (796), `get2_mut` (813) and `IndexMut::index_mut` (1015);
- `get_unchecked_mut` (843) and `get2_unchecked_mut` (852);
- `drain` (978), and `get_disjoint_mut` when it returns an error.

Read `valid()` as the representation invariant `slab_rep_ok`, which is how `compare_specs.py` reads
it. Then no slab can be used after `new()`, since `insert` requires `valid()`. Read `valid()`
literally, as `SlabModel::valid()`. Then these postconditions do imply it, but it no longer
constrains the `len` and `next` fields, so `len()` and `insert` cannot be implemented against it.
Either way, the clause belongs in those postconditions. Checked: adding `s@.valid()` to `new` and
`final(self)@.valid()` to `get_mut` and `get2_mut` makes human ⇒ Claude proved for all three.

**H3. `retain` and `compact` allow outcomes the code never produces** (959, 936). The callback
events are existential and not tied to the closure, which the comments acknowledge. In practice,
`retain`'s contract is met by an implementation that ignores `f` and removes every value: choose
`keep == false` everywhere. It is also met by one that keeps every key but replaces the values: any
`after_callback`. For `compact`, the trace fixes which value moves where, but not whether a move is
accepted, nor the moved value. `retain` also has no precondition on `f`. Verus cannot call a closure
without one, so this contract cannot be implemented as written. A2 gives the weakest clause that
works. Claude's `retain_step` ties each slot to `f.ensures`.

**H4. Some preconditions are stronger than needed.** `contains`, `get`, `clear` and
`Index::index` require `valid()`, but the code is safe and correct on any slab. This is less
general, not wrong.

**H5. Some trait methods have `requires` clauses that Verus cannot state.** `Clone::clone` and
`Clone::clone_from` (1062, 1073) and `IntoIter::next` (1133) have them. A std trait method's impl
cannot add a precondition. `Index` and `IndexMut` have vstd's `index_req` hook instead, which
Claude's spec uses. The `IntoIter::next` clause, `remaining.len() >= 0`, is always true anyway.

**H6. Editorial.** `get_disjoint_mut`'s comment (874) points to `slab_spec_ghost.rs`, which does not
exist. `disjoint_error` is not recursive but has `decreases N` (619). There are typos ("4,", "remainingc").

**Confirmed right in the human spec:**
- `get2_mut` allows keys up to `len`, the same limit as finding F1.
- `get_unchecked*` requires an occupied key.
- `reserve`'s capacity arithmetic matches the code, with no underflow in `additional - vacant`.
- The `compact` trace model matches the code: a rejected move pushes the mutated value back, the
  free list is rebuilt in ascending order, and full compaction leaves it empty.
- `disjoint_error` checks duplicates first, then the first bad key.

## Not amended, and why

- **Capacity.** The human spec reads capacity through `uninterp` plus a `broadcast axiom`.
  `--no-cheating` rejects both, and vstd does not specify `Vec::capacity`. So no verified contract
  can mention capacity. The 10 "capacity only" results stay.
- **The 30 trusted functions.** Under `--no-cheating`, verified code cannot call an unspecified std
  method, and trusted code cannot carry a contract. [`vstd_probe.rs`](vstd_probe.rs) shows that each
  blocker in the table above is still unsupported: `Vec::capacity`, `reserve_exact`,
  `shrink_to_fit`, `drain`, `clone_from`, `<[T]>::get_unchecked`, `mem::replace` and
  `Iterator::size_hint`. Positive controls (`Vec::reserve`, `<[T]>::get_mut`, `Vec::clone`) pass.
- **Where Claude's spec is stronger, it was kept.** That covers `vacant_entry`/`VacantEntry`, the
  `wf()` results of `new`/`get_mut`/`get2_mut`, the missing preconditions of
  `contains`/`get`/`clear`, `retain_step`, and `Iter::clone`.
- **Possible follow-up, not done.** vstd now specifies `<[T]>::get_mut`, so the `vec_get_mut` and
  `slice_get_mut` stand-ins could revert to upstream's calls. That changes executable code and
  would need new approvals.

## Checks

Every entry in the "after" column was run for this review. In the "before" column, entries marked
"(doc)" are taken from VERIFICATION.md and were not re-run.

| Check | `verus/` (before) | `verus_fixed/` (after) |
|---|---|---|
| Verus `--no-cheating`, `std` / `no_std` | 94 verified, 0 errors / 94 (doc) | **98 / 98 verified, 0 errors** |
| SMT seeds 0–19, 42, 1234 | 0 errors (doc) | 0 errors in all 22 runs |
| Negative controls | 22/22 rejected (doc) | 23/23 rejected |
| `cargo build`: default, `--no-default-features`, `--features serde`, both | pass (doc) | pass, 0 warnings |
| `cargo test --features serde` | 47 + 38 doc + 2 serde (doc) | 47 + 38 doc + 2 serde, all pass |
| `check_trusted.py` | 39 items, 0 unexpected (doc) | 39 items, 0 unexpected |
| `detect_changes.py` | 22 changed, 9 added, 10 trust markers, all approved (doc) | same findings, 0 unreviewed, 0 stale approvals |
| `test_detect_changes.py` | 9/9 (doc) | 9/9 |
| `compare_specs.py`, original tool | 20 compared: 9 proved, 10 capacity only, 1 unproved | — |
| `compare_specs.py`, extended tool, same proofs | 26 compared: 14 proved, 10 capacity only, 2 unproved (`retain`; `size_hint`, unexplained) | 26 compared: **15 proved**, 10 capacity only, 1 unproved (`retain`, the closure precondition), 0 unexplained |
| The 3 new clients | fail: both `retain` calls are rejected, both `size_hint` assertions fail, and the count assertion fails even in a variant that meets the old precondition | all verify |

## Reproduce

From `verus_fixed/`, with `verus` on `PATH` (as `slab/README.md` describes):

    (cd slab && verus --crate-type=lib --no-cheating --cfg 'feature="std"' src/lib.rs)  # 98 verified
    python3 compare_specs.py                                    # writes spec_comparison.md
    python3 compare_specs.py --crate ../verus/slab --report /tmp/before.md   # size_hint unproved
    python3 negative_controls.py                                # 23/23 rejected
    verus --no-cheating vstd_probe.rs                           # the 8 unsupported calls
