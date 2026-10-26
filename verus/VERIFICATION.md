# Verifying `slab` with Verus (2026-10-16)

Crate: `slab` 0.4.12, this fork's `master` @ 7d1d8ab. Verus 0.2026.10.18.7d82994 (first verified with 0.2026.05.03.8b81855; see
[Porting to Verus 0.2026.10.18](#porting-to-verus-20261018)), using the bare `verus` binary and its
bundled vstd. The normal build uses rustc 1.95.0. Every run uses `--no-cheating`.
Annotated crate: [`slab/`](slab/). Diff against upstream: [`upstream.diff`](upstream.diff).
Specifications and proofs were written by Claude (Opus 5.5) in Claude Code on 2026-10-16, from
the crate's documentation, its tests and the code. No human-written spec existed.

## Headline

| | |
|---|---|
| Verus `--no-cheating`, default features (`std`) | **74 verified, 0 errors**, 3.5 s wall clock (3.6 s SMT, 5 threads) |
| Verus `--no-cheating`, no features (`no_std`) | 74 verified, 0 errors |
| `assume`, `admit`, `external_body`, `assume_specification`, axioms, `uninterp` in the crate | **none** (`--no-cheating` rejects them) |
| Verified | 21 upstream functions of `Slab`/`VacantEntry`, the logic of `shrink_to_fit`, and the 3 functions of `Builder` (209 non-comment lines of upstream code), plus 3 std stand-ins, 30 lemmas and 7 example clients |
| Trusted, not verified | everything outside `verus!` blocks: 42 upstream functions (327 lines), plus the serde module, listed in [Trusted base](#trusted-base) |
| Normal `cargo build` of the annotated crate | passes with default features, `--no-default-features`, `--features serde` and both; 0 warnings |
| Upstream tests on the annotated crate | 47/47 integration, 38/38 doc, 2/2 serde (the same counts as upstream) |
| Negative controls | 17/17 injected bugs rejected, including the pre-#102 `FromIterator` bug (issue #100) |
| Proof stability | same result with SMT seeds 0 to 19, 42 and 1234 |
| Upstream finding | `get2_mut` panics when a key is past the last slot, where the docs promise `None` ([F1](#findings-in-the-crate)) |

## The specification

The abstract state of a slab has two parts:

- `slab@: Seq<Option<T>>` holds the slots, indexed by key: `Some(v)` for an occupied key, `None` for a vacant one.
- `slab.vacant_list(): Seq<usize>` holds the vacant keys in the order in which `insert` will reuse them.

The invariant `slab.wf()` says two things. First, `len` counts the occupied slots. Second, `next` heads
a linked list threaded through the `Vacant(next)` entries. The list ends at the end marker
`entries.len()` and contains every vacant entry exactly once.

`vacant_list()` is defined with `choose`, and `lemma_vacant_chain_unique` proves that this list is
unique. So `wf()` depends only on the concrete fields, with no ghost state. Trusted code that
keeps the fields consistent therefore keeps `wf()`.

Every verified public method that takes `&mut self` requires `wf()` and ensures it, except `clear`,
which needs no precondition. Definitions and lemmas are in
[`slab/src/spec.rs`](slab/src/spec.rs).

### Contracts by public item

| Public item | Status | Contract |
|---|---|---|
| `new`, `with_capacity`, `Default::default` | verified | `wf()`, no slots, empty vacant list |
| `clear` | verified, no precondition | same as `new` |
| `len`, `is_empty` | verified | `num_occupied(slab@)`, `== 0` |
| `get` | verified, no precondition | `Some(&v)` exactly when `key` holds `v` |
| `contains` | verified, no precondition | `spec_contains(key)` |
| `get_mut` | verified | on `Some(v)`, the final slab is the old one with `key` set to `*final(v)`. On `None`, the key is not occupied and nothing changes |
| `get2_mut` | verified, **added precondition** (F1) | requires `key1 != key2` and both keys `<= slab@.len()`. On `Some((v1, v2))`, both keys are occupied and the final slab has both updated. On `None`, nothing changes |
| `insert` | verified | `insert_post`: the key is the head of the vacant list. If that list is empty, the key is the number of slots and the slab grows by one slot (it grows only when no slot is vacant). The vacant list loses its head |
| `vacant_key` | verified | `next_key()`: the key that `insert` will return |
| `vacant_entry` | verified | `entry.spec_key() == next_key()`. `entry.final_slab()` is the slab's final value |
| `VacantEntry::key`, `VacantEntry::insert` | verified | `insert_post(slab, final_slab, key, *final(value))`: the slab ends up holding whatever the caller leaves behind the returned `&mut T` |
| `try_remove` | verified | on `Some(v)`, `remove_post`: `key` held `v`, its slot becomes `None`, and `key` becomes the head of the vacant list. On `None`, the key is not occupied and nothing changes |
| `remove` | verified, precondition `spec_contains(key)` | `remove_post` |
| `retain` | verified | requires `f` to be callable on every `(key, &mut T)`. Slot count is unchanged and vacant slots stay vacant. For every occupied key, `retain_step`: `f` was called on that key and value, and the slot afterwards is `Some(value as f left it)` if `f` returned `true`, `None` otherwise. Vacant list: removed keys in decreasing order, then the old list |
| `Index::index` (`slab[key]`) | verified, precondition `spec_contains(key)` (vstd `index_req`) | `*value == slab@[key]` |
| `shrink_to_fit` | trusted 2-line shell over verified `remove_vacant_tail` | — |
| `FromIterator::from_iter` | trusted shell over the verified `Builder` | — |
| `capacity`, `reserve`, `reserve_exact`, `compact`, `iter`, `iter_mut`, `drain`, `get_disjoint_mut`, `get_unchecked`, `get_unchecked_mut`, `get2_unchecked_mut`, `key_of`, `IndexMut`, `Clone`, the three `IntoIterator` impls, the iterator types, `Debug`, `Display`, `Error`, serde | trusted | see [Trusted base](#trusted-base) |
| `GetDisjointMutError` | the type is verified; its derives are not given specs | — |

### Private items, also verified

- `insert_at`: ensures `insert_post`.
- `recreate_vacant_list`: requires only `len == num_occupied(slab@)`, which is the "self.len must be correct" in its doc comment. Ensures `wf()` and an unchanged `slab@`, with the vacant list in increasing key order.
- `remove_vacant_tail`, the logic of `shrink_to_fit`: ensures `slab@ == trim_vacant_tail(old@)`. The vacant list is unchanged when nothing was trimmed (the case checked by upstream test `shrink_to_fit_doesnt_recreate_list_when_nothing_can_be_done`). Otherwise it is in increasing key order.
- `Builder::with_capacity`, `pair`, `build` (in `builder.rs`): `pair(key, value)` stores `value` at `key`, padding with vacant slots. `build` returns a `wf()` slab with the same slots. Its vacant list is in increasing key order if some pair filled a hole (the list was recreated) and in decreasing order otherwise.

### Intent decisions the contracts commit to

The docs leave these unstated. The contracts fix them to what the code does.

1. **Key reuse is last-in, first-out.** `try_remove` pushes the key onto the vacant list and `insert` pops from it. The slab grows only when no slot is vacant.
2. **`retain` visits keys in increasing order**, so removed keys are reused in decreasing order. The closure may change the values it keeps.
3. **After `FromIterator`, reuse order depends on the input.** Vacant keys come in increasing order if a later pair filled an earlier hole, and in decreasing order otherwise. The upstream `from_iterator_*` tests depend on exactly this.
4. **Panics become preconditions.** `remove` and `slab[key]` require an occupied key. `get2_mut` requires distinct keys that are both at most the number of slots. This is standard Verus practice: verified callers must prove that the call does not panic. Unverified callers still get the upstream panics.

## Trusted base

Under `--no-cheating` the crate cannot contain `external_body`, `assume_specification`, `uninterp`
or axioms. The only way to mark code as trusted is to leave it unverified.

All trusted code sits outside the `verus!` blocks and is compiled exactly as upstream wrote it,
except the `shrink_to_fit` shell. Each item is marked
`#[cfg_attr(verus_keep_ghost, verifier::external)]` with a `// TRUSTED (not verified): reason`
comment (`grep -n TRUSTED slab/src/lib.rs`). The rule is simple: code inside `verus!` is verified,
and code outside it is trusted. The trusted code is the reason column in this table and nothing more.

| id | Items | Upstream lines | Why it cannot be verified |
|---|---|---|---|
| T1 | `iter`, `iter_mut`, `drain`, the 3 `IntoIterator` impls, `IntoIter`/`Iter`/`IterMut`/`Drain` with their `Iterator`, `DoubleEndedIterator`, `ExactSizeIterator` and `FusedIterator` impls, `Clone for Iter` | 143 | built on `Enumerate`, `slice::IterMut`, `vec::Drain` and `next_back`, which vstd does not specify. The `verus!` macro rewrites every `for` loop, even in external items, so these must stay outside it |
| T2 | `get_disjoint_mut`, `get_unchecked`, `get_unchecked_mut`, `get2_unchecked_mut`, `key_of` | 62 | raw pointers, `MaybeUninit`, unchecked indexing, pointer-to-integer casts, `size_of` |
| T3 | `compact` | 40 | a `Drop` guard that repairs the slab when the closure unwinds, `mem::forget` and `Vec::shrink_to_fit`. Its guard calls the verified `recreate_vacant_list` |
| T4 | `Debug` (5 impls), `Display for GetDisjointMutError`, `std::error::Error` | 36 | formatting is not supported |
| T5 | `capacity`, `reserve`, `reserve_exact` | 17 | `Vec::capacity` and `Vec::reserve_exact` are unspecified |
| T6 | `Clone for Slab` (`clone`, `clone_from`) | 12 | `Vec::clone_from` is unspecified, and Verus verifies a trait impl all-or-nothing |
| T7 | `FromIterator::from_iter` | 11 | iterates an arbitrary `IntoIterator` and calls `size_hint`. It drives the verified `Builder` |
| T8 | `IndexMut::index_mut` | 6 | it must panic on a vacant key, but vstd's `IndexMut` specification admits no precondition and `panic!` is unsupported |
| T9 | `shrink_to_fit` (the call to `Vec::shrink_to_fit`) | 1 | unspecified. The other 9 lines moved into the verified `remove_vacant_tail` |
| T10 | `serde` module | 62 (file) | serde is not supported. Not compiled under Verus. It uses the verified `Builder` |

**Obligations on the trusted code.** These hold by inspection, not by proof:

- Trusted code that mutates a slab (`compact`, `drain`, `clone_from`, `reserve*`, `shrink_to_fit`, `index_mut`, `get_unchecked_mut`, `get2_unchecked_mut`, `get_disjoint_mut`, `IterMut`) must keep `wf()`. All of them except `compact` and `drain` change only values or capacity.
- Trusted callers must meet the preconditions of the verified functions they call:
  - `shrink_to_fit` calls `remove_vacant_tail`, which requires `wf()`.
  - `compact`'s guard calls `recreate_vacant_list`, which requires `len == num_occupied`. `compact`'s normal path instead sets `next = len`, which is valid because every slot is occupied at that point.
  - `from_iter` and serde's `visit_map` call `Builder::with_capacity`, then `pair` repeatedly, then `build`. Each call's precondition is the previous call's postcondition.
- The iterators' `len` counters and the `capacity() - len` arithmetic in `reserve*` are correct because of the verified invariant `len == num_occupied(slab@)`.

**Trusted outside the crate:**

- vstd's specifications of the std items used: `Vec` (`new`, `with_capacity`, `len`, `push`, `pop`, `clear`, `as_mut_slice`, indexing, `IndexMut`, index assignment, and `Deref` to `get` and `last`), slices (`len`, `get`, `first_mut`, `split_at_mut`), `Option::expect` and `mem::swap`.
- vstd's `pervasive::unreached` and `pervasive::runtime_assert`, and vstd's `FnMut` call axioms.
- Verus, Z3 and rustc.

## Findings in the crate

**F1. `get2_mut` panics instead of returning `None` when a key is past the last slot.**
The docs say: "If any one of the given keys is not associated with a value, then `None` is
returned." But the code calls `split_at_mut(max(key1, key2))`, which panics with `mid > len` when
the larger key exceeds the number of slots. Reproduced on the upstream code:

```rust
let mut slab = Slab::new();
slab.insert(1);
slab.insert(2);
slab.get2_mut(0, 5); // panics: "mid > len" (src/lib.rs:801); get2_mut(0, 2) returns None
```

Verus reported it as a failed precondition of `split_at_mut`. The verified contract states the
condition (`key1, key2 <= slab@.len()`) and keeps upstream behavior. A fix would be to return
`None` when the larger key is `>= self.entries.len()` before splitting. A one-line doc change
would also work.

**F2. `insert_at` increments `len` before `push`, so an unwinding `push` would leave `len` one too
high.** This is theoretical: `push` unwinds only on capacity overflow, past `isize::MAX` bytes.
The annotated crate moves the increment after the branch (see Changes), which removes the
problem.

**F3. Comment on the `next` field.** It says `next` is "set to the slab's capacity when the slab is
full". The invariant shows it is set to the number of slots (`entries.len()`), which can be lower
than the capacity.

## Changes to the crate (audit of `upstream.diff`)

- `lib.rs`: 57 lines removed, 609 added. Most additions are contracts, proof blocks, `verus!`
  block boundaries and `TRUSTED` comments.
- `builder.rs`: 7 removed, 274 added.
- New files: `spec.rs` (921 lines), `std_ext.rs` (57), `verified_examples.rs` (160).
- `serde.rs` and `tests/` are unchanged.

### Executable code

Every change is behavior-preserving on all reachable paths, and the upstream test suite passes
unchanged.

| Change | Where | Reason |
|---|---|---|
| `unreachable!()` → `vstd::pervasive::unreached()` (5×) | `insert_at`, `try_remove`, `VacantEntry::insert`, `Builder::build` (2×) | `panic!`-family macros are unsupported. `unreached` requires `false`, so each one is proved unreachable, and it still panics if reached |
| `assert!(key1 != key2)` → `runtime_assert(key1 != key2)` | `get2_mut` | same reason. The panic message becomes `assertion failed: b` |
| `match … _ => panic!("invalid key")` → `self.get(key).expect("invalid key")` | `Index::index` | same message and the same caller location (`expect` is `#[track_caller]`) |
| `get_mut` on `Vec` and slices → `vec_get_mut` / `slice_get_mut` (7×) | `get_mut`, `get2_mut`, `try_remove`, `VacantEntry::insert` | `<[T]>::get_mut` is unspecified. The verified stand-ins in `std_ext.rs` use `IndexMut`, `split_at_mut` and `first_mut` |
| `core::mem::replace` → `mem_replace` | `try_remove` | unspecified. The stand-in is built on `mem::swap`. It may affect the copy elision that #160 aimed for, which I have not measured |
| `val.into()` → `Some(val)` | `try_remove` | `From<T> for Option<T>` is unspecified. Identical code |
| `self.entries.split_at_mut(k)` → `self.entries.as_mut_slice().split_at_mut(k)` | `get2_mut` | the implicit `Vec`-to-slice `DerefMut` coercion is unsupported |
| reference patterns (`&Entry::X(..)`, `&mut Entry::X(ref mut v)`) → match ergonomics | `insert_at`, `get_mut`, `get2_mut`, `contains`, `VacantEntry::insert` | reference patterns are unsupported. Same bindings |
| `while let Some(&Entry::Vacant(_)) = self.entries.last()` → `while matches!(self.entries.last(), Some(Entry::Vacant(_)))` | `shrink_to_fit` (now `remove_vacant_tail`) | `while let` is unsupported |
| `for (i, entry) in self.entries.iter_mut().enumerate().rev()` → index `while` loop with the same order and the same early `break` | `recreate_vacant_list` | `for` works only over vstd-specified iterators |
| `shrink_to_fit` split: everything before `self.entries.shrink_to_fit()` moved, unchanged, into the new verified `remove_vacant_tail` | `shrink_to_fit` | `Vec::shrink_to_fit` is unspecified |
| `self.len += 1` moved after the `if`/`else` | `insert_at` | the branch does not read `len`. After `push`, Verus knows the new length fits in a `usize`, so it can prove that the increment cannot overflow. Without the move, `insert` would need a `len < usize::MAX` precondition (mutant M4). Also fixes F2 |
| `let x = Struct { .. }; proof { .. } x` instead of a bare struct literal | `new`, `with_capacity`, `Builder::with_capacity` | names the value for the proof. Erases to the same code; `new` stays `const` |
| `for i in 0..n` → `for i in iter: 0..n` | `retain` | Verus syntax that names the iterator for the invariant. Erased |

### Build-only changes

- `Cargo.toml` gains a `vstd` dependency, which provides the `verus!` macro (it erases ghost code in
  normal builds), and `vstd/std` follows slab's `std` feature.
- `rust-version` goes from 1.51 to 1.95, and `rust-toolchain.toml` pins 1.95.0.
- The ghost-only `IndexSpecImpl` impl is `#[cfg(verus_keep_ghost)]`.

### Ghost-only additions

- `requires`/`ensures` on 28 functions.
- Invariants on 4 loops.
- 42 `proof` blocks.
- 30 spec functions and 30 lemmas, in `spec.rs` and `builder.rs`.
- `verified_examples.rs`.

## Negative controls (all rejected)

Each mutant is one edit to a scratch copy, checked with the same command
(`--no-cheating --cfg 'feature="std"'`). To rerun them all:
`python3 negative_controls.py` from `verus/`, with `verus` on `PATH` or `VERUS=/path/to/verus`.

| # | Injected bug | Verus error |
|---|---|---|
| M1 | `try_remove` does not push the freed key (drops `self.next = key`) | precondition of `lemma_wf_intro`: the new list is not headed by `next` |
| M2 | `try_remove` links the freed entry to itself | postcondition of `try_remove` |
| M3 | `insert_at` forgets `len += 1` | precondition of `lemma_wf_intro`: `len` no longer counts the occupied slots |
| M4 | `insert_at` increments `len` first, as upstream does | possible arithmetic overflow at `self.len += 1` |
| M5 | `insert_at` (reuse case) sets `next = key + 1` instead of following the link | precondition of `lemma_wf_intro`: `next` is not the head of the remaining list |
| M6 | `recreate_vacant_list` links each vacant entry to itself | assertion in the loop body |
| M7 | `recreate_vacant_list` stops one vacant entry early | assertion before the `break` |
| M8 | `shrink_to_fit`'s tail removal skips repairing the vacant list | postcondition of `remove_vacant_tail` |
| M9 | `shrink_to_fit`'s tail removal pops occupied entries | loop invariant |
| M10 | `retain` removes the entries the closure keeps | precondition of `remove`: it is now called on vacant keys |
| M11 | `get2_mut` fetches the wrong second entry in one branch | postcondition of `get2_mut` |
| M12 | `contains` reports vacant keys | postcondition of `contains` |
| M13 | `vacant_key` returns `len` | postcondition of `vacant_key` |
| M14 | `Builder::build` without the #102 fix: the first hole keeps its bogus link | postcondition of `build` |
| M15 | `Builder::pair` does not mark the list broken when it fills a hole | assertion in `pair` |
| M16 | `Builder::pair` inserts one hole too many | loop invariant |
| M17 | the `mem_replace` stand-in returns the new value | postcondition of `mem_replace` |

M14 is the historical bug behind issue #100, fixed in 5bc6f62 (#102). Verus rejects the pre-fix
logic.

## Verified example clients (spec sanity checks)

[`verified_examples.rs`](slab/src/verified_examples.rs) proves documented behavior using only the
contracts. A vacuous or too-weak spec would make these proofs fail.

- **Crate docs.** `insert` returns 0, then 1. `slab[key]` and `get` return the stored values, and `get(123)` returns `None`.
- **`vacant_key` docs.** Keys come back 0, then 1, then 0 again after `remove(0)`.
- **`VacantEntry` docs.** After `entry.insert((key, 7))`, `slab@[key] == Some((key, 7))`. This goes through the prophetic `final_slab`.
- **`get_mut` docs.** Writing through the returned reference changes `slab[key]`.
- **`try_remove` test.** Returns `Some(1)`, then `None`. `contains` is false afterwards.
- **`retain` docs.** Given a closure with `ensures keep == (key == k1 || *old(val) == 1)`, the proof shows that `k1` and `k2` stay, `k3` goes, `len() == 2`, and the next `insert` returns `k3`.
- **Upstream test `from_iterator_issue_100`, first case, through the `Builder`.** The next three `insert`s return 0, 2 and 3.

## Porting to Verus 0.2026.10.18

Verus 0.2026.10.18.7d82994 (rustc 1.99.1) needed two proof-only changes. No executable code changed.

- **`for` loop iterator.** vstd now wraps a `for` loop's iterator in `VerusForLoopWrapper`, so the
  `retain` invariant `iter.end == pre@.len()` becomes `iter.snapshot.end == pre@.len()`.
- **Unstable `Builder` proofs.** `Builder::build` exceeded the rlimit, even at 3x. Profiling showed
  that about two thirds of the quantifier instantiations came from the ordering fact in
  `lemma_vacant_keys_from` (`forall|i, j| i < j ==> keys[i] < keys[j]`), which is quadratic in the
  number of holes.
  - The proof for `build`'s last case (the #102 fix) moved into a new lemma,
    `lemma_close_hole_chain`, in `builder.rs`. Its proof is unchanged, except that
    `lemma_vacant_keys_from` is now called inside each `assert ... by` that needs it rather than
    once for the whole proof.
  - `Builder::pair` failed on some seeds for the same reason, so its two calls to
    `lemma_vacant_keys_from` were scoped the same way.
  - Moving the proof into the lemma without scoping the calls still left 5 of 14 seeds failing,
    in the new lemma or in `pair`. With the calls scoped, all 22 seeds checked pass.
- **Negative controls.** All 17 are still rejected. M7 is now rejected by an rlimit in the
  `recreate_vacant_list` loop rather than by the assertion before the `break`.

## Verus notes from this pass

- **What `--no-cheating` allows.** It rejects `uninterp spec fn` (lowered to `external_body`) as
  well as `assume`, `admit`, `external_body`, `assume_specification` and axioms. It accepts
  `#[verifier::external]` and opaque `external_type_specification` types. So under
  `--no-cheating` a trusted item cannot be given a spec: verified code cannot call it at all.
  That is why `Vec::capacity` makes all of `capacity`/`reserve`/`reserve_exact` trusted.
- **No panics in verified code.** `panic!`, `unreachable!` and `assert!` are unsupported, and their
  library seams (`panic_fmt`) would need `assume_specification`. vstd's `unreached()`,
  `runtime_assert()` and `Option::expect` are the replacements that `--no-cheating` accepts.
- **`verus!` rewrites `for` loops even in `#[verifier::external]` items.** Trusted code with `for`
  loops over unspecified iterators therefore has to live outside `verus!`. I put all trusted code
  outside, which also makes the boundary easy to audit.
- **Trait impls are all-or-nothing.** One method of a trait impl cannot be external, which is why
  `clone` goes along with `clone_from`. vstd's `IndexMut` declares no method, so `index_mut`
  cannot carry a precondition.
- **Matching loop.** A chain quantifier triggered on `list[i]` whose body mentions `list[i + 1]`
  made three functions hit the rlimit. Triggering it on `entries[list[i]]` instead cut the whole
  run from timeouts to 1.9 s.
- **New mutable references.**
  - Postconditions must say `final(x)`.
  - Spec functions that read a stored `&mut` need `#[verifier::prophetic]`. That is how
    `VacantEntry` exposes the slab's final value.
  - Facts about the final values of returned references (in `get_mut`, `get2_mut` and
    `VacantEntry::insert`) are best proved as `forall` lemmas triggered on `s.wf()` or on the
    postcondition predicate.
- **`FnMut` closures.** vstd models an `FnMut` call as leaving the closure value unchanged. A loop
  still forgets `f == f(at entry)` unless the invariant says so; without it, `retain`'s
  postcondition failed.
- **`choose` is a function of the whole value.** It depends on `self`, not on the fields its body
  reads. Proving the vacant list unique made it independent of capacity and other hidden state.
- **Trigger shape in client-facing postconditions.** A trigger containing `k as usize` does not
  match a client's literal key. `retain`'s postcondition triggers on `final(self)@[k]` instead.
- **Other limitations hit.**
  - `when_used_as_spec` needs the spec function in the same impl block.
  - `while let`, reference patterns and the `Vec`-to-slice `DerefMut` coercion are unsupported.
  - `<[T]>::get_mut`, `mem::replace`, `From<T> for Option<T>`, `Vec::{capacity, reserve_exact, shrink_to_fit, clone_from, drain, iter_mut}` and `Iterator::size_hint` are unspecified.
  - Derived `Clone` impls get no spec (warning only).
- **`cargo verus` is still unusable with this release.** It panics compiling the crates.io vstd
  (`unexpected verus diagnostic item … shr_ref_struct_wrap`). The bare binary works.

## Reproduce

See [`slab/README.md`](slab/README.md):
`verus --crate-type=lib --no-cheating --cfg 'feature="std"' src/lib.rs` from `verus/slab/`, and
`cargo test --features serde` for the upstream tests.
