# Verifying `slab` with Verus (2026-10-16)

Crate: `slab` 0.4.12, this fork's `master` @ 7d1d8ab. Verus 0.2026.10.18.7d82994 (first verified with 0.2026.05.03.8b81855; see
[Porting to Verus 0.2026.10.18](#porting-to-verus-20261018)), using the bare `verus` binary and its
bundled vstd. The normal build uses rustc 1.95.0. Every run uses `--no-cheating`.
Annotated crate: [`slab/`](slab/). Diff against upstream: [`upstream.diff`](upstream.diff).
Specifications and proofs were written by Claude (Opus 5.5) in Claude Code on 2026-10-16, from
the crate's documentation, its tests and the code. No human-written spec existed.
Specifications for `iter`, `Iter` and `IndexMut` were added on 2026-10-26 (see
[Newly verified with Verus 0.2026.10.18](#newly-verified-with-verus-20261018)).

## Headline

| | |
|---|---|
| Verus `--no-cheating`, default features (`std`) | **94 verified, 0 errors**, 4.1 s wall clock (5.1 s SMT, 5 threads) |
| Verus `--no-cheating`, no features (`no_std`) | 94 verified, 0 errors |
| `assume`, `admit`, `external_body`, `assume_specification`, axioms, `uninterp` in the crate | **none** (`--no-cheating` rejects them) |
| Verified | 28 upstream functions of `Slab`/`VacantEntry`/`Iter`, the logic of `shrink_to_fit`, and the 3 functions of `Builder` (253 non-comment lines of upstream code), plus 3 std stand-ins, 33 lemmas and 11 example clients |
| Trusted, not verified | everything in [`trusted.rs`](slab/src/trusted.rs): 35 upstream functions (283 lines), plus the serde module, listed in [Trusted base](#trusted-base) |
| Normal `cargo build` of the annotated crate | passes with default features, `--no-default-features`, `--features serde` and both; 0 warnings |
| Upstream tests on the annotated crate | 47/47 integration, 38/38 doc, 2/2 serde (the same counts as upstream) |
| Negative controls | 22/22 injected bugs rejected, including the pre-#102 `FromIterator` bug (issue #100) |
| Proof stability | same result with SMT seeds 0 to 19, 42 and 1234 |
| Change detection | `detect_changes.py` finds 22 changed and 9 added items of executable code, plus 10 lines that mark code trusted or ghost-only ([Change detection](#change-detection)) |
| Gold spec comparison | `compare_specs.py` compares Shawn's human-written spec with the verified one for the 20 functions both cover. The verified spec implies the gold one for 9, for 10 more except for capacity, and not for `retain` (the closure's precondition). Every remaining failure is a real difference between the specs and is explained in the report ([Comparison with the gold spec](#comparison-with-the-gold-spec)) |
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
| `IndexMut::index_mut` (`slab[key] = v`) | verified, precondition `spec_contains(key)` (vstd `index_req`) | `*value == slab@[key]`, and the final slab is the old one with `key` set to `*final(value)`. Keeps `wf()` and the vacant list |
| `iter` | verified | the iterator's `remaining()` is `ref_pairs(occupied_pairs(slab@, 0))`: a `(key, &value)` pair for each occupied slot, in increasing key order |
| `Iter`: `next`, `next_back`, `len`, `size_hint`, `clone` | verified | vstd's iterator laws: `next` and `next_back` return the first and the last remaining pair and remove it, then `None`. `len()` is the number of pairs left. `clone` returns an equal iterator. A type invariant says that `len` counts the pairs left |
| `shrink_to_fit` | trusted 2-line shell over verified `remove_vacant_tail` | — |
| `FromIterator::from_iter` | trusted shell over the verified `Builder` | — |
| `capacity`, `reserve`, `reserve_exact`, `compact`, `iter_mut`, `drain`, `get_disjoint_mut`, `get_unchecked`, `get_unchecked_mut`, `get2_unchecked_mut`, `key_of`, `Clone for Slab`, the three `IntoIterator` impls, `IntoIter`, `IterMut`, `Drain`, `Debug`, `Display`, `Error`, serde | trusted | see [Trusted base](#trusted-base) |
| `GetDisjointMutError` | the type is verified; its derives are not given specs | — |

### Private items, also verified

- `insert_at`: ensures `insert_post`.
- `recreate_vacant_list`: requires only `len == num_occupied(slab@)`, which is the "self.len must be correct" in its doc comment. Ensures `wf()` and an unchanged `slab@`, with the vacant list in increasing key order.
- `remove_vacant_tail`, the logic of `shrink_to_fit`: ensures `slab@ == trim_vacant_tail(old@)`. The vacant list is unchanged when nothing was trimmed (the case checked by upstream test `shrink_to_fit_doesnt_recreate_list_when_nothing_can_be_done`). Otherwise it is in increasing key order.
- `iter_next`, `iter_next_back`: the bodies of `Iter::next` and `Iter::next_back`, on the iterator's fields (see [Executable code](#executable-code)).
- `Builder::with_capacity`, `pair`, `build` (in `builder.rs`): `pair(key, value)` stores `value` at `key`, padding with vacant slots. `build` returns a `wf()` slab with the same slots. Its vacant list is in increasing key order if some pair filled a hole (the list was recreated) and in decreasing order otherwise.

### Intent decisions the contracts commit to

The docs leave these unstated. The contracts fix them to what the code does.

1. **Key reuse is last-in, first-out.** `try_remove` pushes the key onto the vacant list and `insert` pops from it. The slab grows only when no slot is vacant.
2. **`retain` visits keys in increasing order**, so removed keys are reused in decreasing order. The closure may change the values it keeps.
3. **After `FromIterator`, reuse order depends on the input.** Vacant keys come in increasing order if a later pair filled an earlier hole, and in decreasing order otherwise. The upstream `from_iterator_*` tests depend on exactly this.
4. **Panics become preconditions.** `remove`, `slab[key]` and `slab[key] = v` require an occupied key. `get2_mut` requires distinct keys that are both at most the number of slots. This is standard Verus practice: verified callers must prove that the call does not panic. Unverified callers still get the upstream panics.
5. **Iteration is in key order.** `iter` yields the occupied keys in increasing order from the front and in decreasing order from the back, and skips vacant slots.

## Trusted base

Under `--no-cheating` the crate cannot contain `external_body`, `assume_specification`, `uninterp`
or axioms. The only way to mark code as trusted is to leave it unverified.

All trusted code is in [`slab/src/trusted.rs`](slab/src/trusted.rs), apart from serde (T9), which
keeps its own file. `lib.rs` declares the module with `#[cfg_attr(verus_keep_ghost,
verifier::external)]`, so Verus skips the whole file, and normal builds compile it like any other
module. The file opens with this table, and each item carries a `// T<n>: reason` comment. Its items
are upstream's code moved there unchanged, doc comments included, except the `shrink_to_fit` shell;
`python3 check_trusted.py` (from `verus/`) checks each item against upstream `src/lib.rs`. The rule is
simple: `lib.rs`, `builder.rs` and `std_ext.rs` are verified, and `trusted.rs` is not.

| id | Items | Upstream lines | Why it cannot be verified |
|---|---|---|---|
| T1 | `iter_mut`, `drain`, the 3 `IntoIterator` impls, `IntoIter`/`IterMut`/`Drain` with their `Iterator`, `DoubleEndedIterator`, `ExactSizeIterator` and `FusedIterator` impls | 105 | built on `Enumerate`, `slice::IterMut`, `vec::Drain` and `next_back`, which vstd does not specify (`IntoIter` is blocked for another reason, see [Newly verified](#newly-verified-with-verus-20261018)). The `IntoIterator` impls are trait methods, which cannot require `wf()`; the one for `&Slab` is a call to the verified `iter`. The `verus!` macro rewrites every `for` loop, even in external items, so these must stay outside it |
| T2 | `get_disjoint_mut`, `get_unchecked`, `get_unchecked_mut`, `get2_unchecked_mut`, `key_of` | 62 | raw pointers, `MaybeUninit`, unchecked indexing, pointer-to-integer casts, `size_of` |
| T3 | `compact` | 40 | a `Drop` guard that repairs the slab when the closure unwinds, `mem::forget` and `Vec::shrink_to_fit`. Its guard calls the verified `recreate_vacant_list` |
| T4 | `Debug` (5 impls), `Display for GetDisjointMutError`, `std::error::Error` | 36 | formatting is not supported |
| T5 | `capacity`, `reserve`, `reserve_exact` | 17 | `Vec::capacity` and `Vec::reserve_exact` are unspecified |
| T6 | `Clone for Slab` (`clone`, `clone_from`) | 12 | `Vec::clone_from` is unspecified, and Verus verifies a trait impl all-or-nothing |
| T7 | `FromIterator::from_iter` | 11 | iterates an arbitrary `IntoIterator` and calls `size_hint`. It drives the verified `Builder` |
| T8 | `shrink_to_fit` (the call to `Vec::shrink_to_fit`) | 1 | unspecified. The other 9 lines moved into the verified `remove_vacant_tail` |
| T9 | `serde` module | 62 (file) | serde is not supported. Not compiled under Verus. It uses the verified `Builder` |

**Obligations on the trusted code.** These hold by inspection, not by proof:

- Trusted code that mutates a slab (`compact`, `drain`, `clone_from`, `reserve*`, `shrink_to_fit`, `get_unchecked_mut`, `get2_unchecked_mut`, `get_disjoint_mut`, `IterMut`) must keep `wf()`. All of them except `compact` and `drain` change only values or capacity.
- Trusted callers must meet the preconditions of the verified functions they call:
  - `shrink_to_fit` calls `remove_vacant_tail`, which requires `wf()`.
  - `IntoIterator for &Slab` and the alternate `Debug` format of `Slab` call `iter`, which requires `wf()`.
  - `compact`'s guard calls `recreate_vacant_list`, which requires `len == num_occupied`. `compact`'s normal path instead sets `next = len`, which is valid because every slot is occupied at that point.
  - `from_iter` and serde's `visit_map` call `Builder::with_capacity`, then `pair` repeatedly, then `build`. Each call's precondition is the previous call's postcondition.
- The `len` counters of `IntoIter`, `IterMut` and `Drain`, and the `capacity() - len` arithmetic in `reserve*`, are correct because of the verified invariant `len == num_occupied(slab@)`. (`Iter`'s counter is verified by its type invariant.)

**Trusted outside the crate:**

- vstd's specifications of the std items used: `Vec` (`new`, `with_capacity`, `len`, `push`, `pop`, `clear`, `as_slice`, `as_mut_slice`, indexing, `IndexMut`, index assignment, and `Deref` to `get` and `last`), slices (`len`, `get`, indexing, `first_mut`, `split_first`, `split_at`, `split_at_mut`), `Option::expect` and `mem::swap`.
- vstd's iterator specification: the `Iterator`, `DoubleEndedIterator` and `ExactSizeIterator` laws that `Iter` is verified against, and `VerusForLoopWrapper`, which verified `for` loops use.
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

- `lib.rs`: 850 lines removed, 672 added. Most of the removed lines are the trusted items, which
  moved unchanged to `trusted.rs`. Most additions are contracts, proof blocks and `verus!` block
  boundaries.
- `builder.rs`: 7 removed, 308 added.
- New files: `spec.rs` (1057 lines), `std_ext.rs` (57), `trusted.rs` (894), `verified_examples.rs` (270).
- `serde.rs` and `tests/` are unchanged.

### Executable code

This table was written by the agent that made the changes. [Change detection](#change-detection)
finds the changes mechanically, so a reviewer does not have to rely on it. Every change is
behavior-preserving on all reachable paths, and the upstream test suite passes unchanged.

| Change | Where | Reason |
|---|---|---|
| `unreachable!()` → `vstd::pervasive::unreached()` (5×) | `insert_at`, `try_remove`, `VacantEntry::insert`, `Builder::build` (2×) | `panic!`-family macros are unsupported. `unreached` requires `false`, so each one is proved unreachable, and it still panics if reached |
| `assert!(key1 != key2)` → `runtime_assert(key1 != key2)` | `get2_mut` | same reason. Equal keys still panic (in the vstd linked at run time, `runtime_assert` is `assert!(b)`), but the message becomes `assertion failed: b` and is reported inside vstd |
| `match … _ => panic!("invalid key")` → `.expect("invalid key")` on the looked-up value | `Index::index`, `IndexMut::index_mut` | same message and the same caller location (`expect` is `#[track_caller]`) |
| `get_mut` on `Vec` and slices → `vec_get_mut` / `slice_get_mut` (8×) | `get_mut`, `get2_mut`, `try_remove`, `VacantEntry::insert`, `index_mut` | `<[T]>::get_mut` is unspecified. The verified stand-ins in `std_ext.rs` use `IndexMut`, `split_at_mut` and `first_mut` |
| `core::mem::replace` → `mem_replace` | `try_remove` | unspecified. The stand-in is built on `mem::swap`. Measured in release builds: the same machine code as upstream for `u64` values. For 512-byte values, #160's copy elision still holds when the result is unused, but each removal re-tests the old tag (about 3 instructions), and a used result goes through a partial stack copy (138 instructions against 45) |
| `val.into()` → `Some(val)` | `try_remove` | `From<T> for Option<T>` is unspecified. Identical code |
| `self.entries.split_at_mut(k)` → `self.entries.as_mut_slice().split_at_mut(k)` | `get2_mut` | the implicit `Vec`-to-slice `DerefMut` coercion is unsupported |
| reference patterns (`&Entry::X(..)`, `&mut Entry::X(ref mut v)`) → match ergonomics | `insert_at`, `get_mut`, `get2_mut`, `contains`, `VacantEntry::insert`, `index_mut` | reference patterns are unsupported. Same bindings |
| `while let Some(&Entry::Vacant(_)) = self.entries.last()` → `while matches!(self.entries.last(), Some(Entry::Vacant(_)))` | `shrink_to_fit` (now `remove_vacant_tail`) | `while let` is unsupported |
| `for (i, entry) in self.entries.iter_mut().enumerate().rev()` → index `while` loop with the same order and the same early `break` | `recreate_vacant_list` | `for` works only over vstd-specified iterators |
| `shrink_to_fit` split: everything before `self.entries.shrink_to_fit()` moved, unchanged, into the new verified `remove_vacant_tail` | `shrink_to_fit` | `Vec::shrink_to_fit` is unspecified |
| `self.len += 1` moved after the `if`/`else` | `insert_at` | the branch does not read `len`. After `push`, Verus knows the new length fits in a `usize`, so it can prove that the increment cannot overflow. Without the move, `insert` would need a `len < usize::MAX` precondition (mutant M4). Also fixes F2 |
| `let x = Struct { .. }; proof { .. } x` instead of a bare struct literal | `new`, `with_capacity`, `Builder::with_capacity` | names the value for the proof. Erases to the same code; `new` stays `const` |
| `for i in 0..n` → `for i in iter: 0..n` | `retain` | Verus syntax that names the iterator for the invariant. Erased |
| `Iter`'s field `entries: Enumerate<slice::Iter<Entry<T>>>` → `entries: &[Entry<T>]`, the entries not yet visited, and `front: usize`, the key of the first of them | `Iter`, `iter`, `Clone for Iter` | vstd specifies neither `Enumerate` nor `slice::Iter::next_back`. `next` takes an entry with `split_first` and `next_back` with `split_at`, which vstd specifies. The items and their order are the same, and `Debug` prints only `len`, so its output is unchanged. In a release-mode benchmark over 2 million slots, forward iteration took the same time, while `rev()` and a `for` loop took about 3–4% longer |
| `Iter::next` and `Iter::next_back` bodies moved into `iter_next` and `iter_next_back`, which take the three fields by `&mut` | `Iter` | Verus checks a type invariant after every field assignment, so the fields are updated in one call and checked once after it, as in vstd's verified `IterMut` example. The loops are written with `loop`/`match` instead of `for` and `while let` |
| `debug_assert_eq!(self.len, 0)` removed | `Iter::next`, `Iter::next_back` | panic macros are unsupported. The condition is proved at that point instead |

### Build-only changes

- `Cargo.toml` gains a `vstd` dependency, which provides the `verus!` macro (it erases ghost code in
  normal builds), and `vstd/std` follows slab's `std` feature.
- `rust-version` goes from 1.51 to 1.95, and `rust-toolchain.toml` pins 1.95.0.
- The ghost-only `IndexSpecImpl` impl, `Iter`'s iterator-spec impls and the `IteratorSpec` import are `#[cfg(verus_keep_ghost)]`.
- The trusted items live in the private module `trusted`. `IntoIter`, `IterMut` and `Drain` are defined
  there and re-exported from the crate root, so the public paths (`slab::IntoIter` and so on) are
  unchanged.

### Ghost-only additions

- `requires`/`ensures` on 33 functions.
- Invariants on 6 loops.
- 54 `proof` blocks.
- 33 spec functions and 33 lemmas, in `spec.rs` and `builder.rs`.
- A type invariant on `Iter`, and its `IteratorSpecImpl`, `DoubleEndedIteratorSpecImpl` and `ExactSizeIteratorSpecImpl` impls.
- `verified_examples.rs`.

## Change detection

AI-written verification may change the code it verifies, and the agent's own audit (the table
above) is not a check. [`detect_changes.py`](detect_changes.py) finds every change to executable
code mechanically and fails until a human has approved each one.

**How it works.**

1. It compiles both crates to macro-expanded Rust (`rustc -Zunpretty=expanded`, the same
   toolchain for both). In a normal build the `verus!` macro erases specifications, proofs and
   ghost code, so the annotated expansion is the code that runs.
2. It splits each expansion into items (functions, methods, impl headers, structs, ...) and matches
   them by name rather than by file. Code that moved, such as the items in `trusted.rs`, is listed
   as moved but not flagged.
3. It compares the items token by token. It ignores formatting, comments, trailing commas and the
   empty `{}` and `else {}` that erased proof blocks leave. Documentation is compared on its own.
4. It also flags:
   - imports, as one finding;
   - `Cargo.toml`, `rust-toolchain.toml` and `tests/`;
   - every source line, not in upstream, that makes code trusted rather than verified
     (`verifier::external`, `external_body`, `assume_specification`, `unsafe`, ...);
   - every `verus_keep_ghost` cfg, which is where the program Verus checks and the program that
     runs can differ.
5. Each finding has a fingerprint. It passes only if
   [`approved_changes.json`](approved_changes.json) has the same key and fingerprint with a
   non-empty `reviewer`. The script never fills in `reviewer`. Any later edit to an approved item
   changes its fingerprint and needs a new review.

The output is [`changes_report.md`](changes_report.md): each finding with its diff and heuristic
hints (such as "`unreachable!()` -> vstd `unreached()`"), plus the agent's explanation from the
approvals file, labeled as a claim to check.

**Current result.** 22 changed items, 9 added items (`iter_next`, `iter_next_back`,
`remove_vacant_tail`, the three `std_ext` stand-ins, a ghost-only `View` impl), 10 trust-boundary
lines and 2 import findings, one per configuration. All of them are the changes in the table above.

**Review (2026-10-26).** All 41 findings are approved with reviewer Shawn, based on Claude's review
of each diff and these checks:
- **Equivalence:** every changed and added function was read against its upstream version. Each
  computes the same result whenever it does not panic. The observable differences are the ones in
  the table above: panic messages and locations, the removed debug assertion, the `insert_at`
  reorder (it only matters if `push` unwinds) and performance.
- **Run-time vstd:** normal builds link the crates.io vstd (`0.0.0-2026-05-06`), not the
  Verus-bundled one. In it, `unreached()` panics with `"unreached_external"`, and `runtime_assert(b)`
  is `assert!(b)`.
- **Imports:** replacing each `vstd::prelude::*` glob with explicit imports of the names a normal
  build needs leaves the MIR identical in both configurations. A one-token control edit does
  change the MIR, so the comparison is sensitive.
- **`try_remove` codegen:** measured in release assembly (see the `mem_replace` row above).
- **Ghost-only items:** the `verus_keep_ghost` items contain only spec and proof functions, plus
  the example clients, which nothing calls.

**Self-test.** `python3 test_detect_changes.py` edits a scratch copy and checks the outcome. All 9
cases pass:
- **Benign edits pass:** no edit, an added proof block, a new comment and reformatting.
- **Real edits are flagged:** a changed condition in verified code, a changed call in trusted
  code, an added function, code hidden from Verus with `cfg(not(verus_keep_ghost))`, a verified
  function made `external_body`, and changed documentation.

**Limitations.**
- **Equivalence is not decided.** A rewrite such as reference patterns to match ergonomics is
  flagged even though the compiled code is the same. Comparing compiled code (MIR or LLVM IR) for
  the flagged items could clear some automatically; for `get_unchecked` that comparison only
  matched after normalizing register order and panic-location constants.
- **Names are not resolved.** An unchanged function body could call something different if an
  import changed, which is why imports are a finding. A new glob import such as
  `vstd::prelude::*` can shadow names from the std prelude. For slab, the MIR comparison in the
  review above shows that it does not.
- **Only the given configurations are compared.** By default these are `--features serde` and
  `--no-default-features`.
- **The `verus!` macro is trusted** to erase only ghost code, as Verus itself trusts it.

## Comparison with the gold spec

[`humen_written_spec.rs`](humen_written_spec.rs) is a human-written gold spec of the public
functions. [`compare_specs.py`](compare_specs.py) compares it with the verified spec, the script builds the equivalence obligations, Verus checks them,
and proofs come from a separate file.

**Directions.**
- **Claude ⇒ gold.** A wrapper with the gold contract calls the verified function. Verus then
  checks that the gold precondition implies Claude's, and that the gold precondition plus
  Claude's postcondition imply the gold postcondition. This is contract refinement, and it handles
  `&mut` returns, `final(..)`, closures and trait methods through the real call.
- **Gold ⇒ Claude.** A wrapper with Claude's contract calls a stand-in that has the gold contract.
  Inherent functions only.

**Conventions applied to the gold spec**, all listed in the report:
- the gold `View` becomes a `GoldView` trait, since the crate has its own `View` for `Slab`;
- `x@.valid()` on a slab is read as the gold invariant `slab_rep_ok`;
- the gold `broadcast axiom` (`len <= capacity`) is in force;
- gold definitions about types the crate leaves trusted are dropped.

A model equality `x@ == y` is checked field by field. This has the same meaning, but Verus then
applies extensional equality to each field, so a failing clause is a real difference rather than
an automation gap. An obligation with capacity clauses or model equalities is also checked
without capacity. If only that variant holds, the report says "capacity only": Claude's spec says
nothing about capacity.

**Proofs** go in [`spec_proofs.rs`](spec_proofs.rs). That file holds lemmas, plus `proof { }`
hints marked `// @hint <obligation> before|after`, where `*` means every obligation. The
obligations are regenerated from the two spec files on every run, so proofs cannot change what
is checked. `assume`, `admit`, `external_body` and axioms are rejected in that file. If any lemma
fails to verify, the run is refused (exit 2), so no result can rest on a failing lemma.

**Notes.** A `// @note <obligation>` comment in `spec_proofs.rs` explains why an obligation stays
unproved. The report shows the note next to the failure and counts failures that are neither
capacity only nor explained by a note. Notes are not checked; they are there for the human
review.

**The proofs** (Claude, 2026-10-26; about 500 non-comment lines, made up of 22 lemmas and helper spec
functions and 9 hints):
- `lemma_wf_gold` and `lemma_gold_wf` prove that Claude's invariant `wf()` and the gold
  `slab_rep_ok` are equivalent. They also show that the two models agree: the gold slots are
  Claude's view, the gold free list (`follow_free_links`) is `vacant_list()`, and the occupied
  counts are equal. `lemma_bridge_all` states both directions for every slab, so they also apply
  to the final value of a slab behind a returned `&mut`. A `*` hint brings them into every
  obligation.
- Per-function lemmas translate insertion, removal and `retain` between the models. For `retain`
  in the Claude ⇒ gold direction, the gold callback events are read off the final slab. The
  ascending removed keys (`filter`, then `reverse`) are shown to equal Claude's descending
  `removed_keys_desc`.

**Current result** ([`spec_comparison.md`](spec_comparison.md)):
- **Comparable:** 20 functions. The other 36 are trusted in the verified crate, or use gold
  placeholders such as the `Iter` view.
- **Claude ⇒ gold:** 9 proved (`len`, `is_empty`, `contains`, `get`, `vacant_key`,
  `vacant_entry`, `Index::index`, `VacantEntry::key`, `VacantEntry::insert`).
  10 capacity only (`new`, `with_capacity`, `insert`, `try_remove`, `remove`, `clear`, `get_mut`,
  `get2_mut`, `IndexMut::index_mut`, `Default::default`).
  1 unproved: `retain`. Claude requires the closure's precondition for every argument
  (`f.requires((key, value))`), which Verus needs in order to call the closure. A closure with
  no `requires` clause meets it trivially. Every postcondition is proved.
- **Gold ⇒ Claude** (17 inherent functions): 8 proved (`with_capacity`, `len`, `is_empty`,
  `vacant_key`, `insert`, `try_remove`, `remove`, `VacantEntry::key`). The other 9 are real
  differences:
  - *Claude's contract is more general:* `contains`, `get` and `clear` have no precondition,
    while the gold contracts require `valid()`.
  - *The gold contract leaves something out:*
    - `new`, `get_mut` and `get2_mut` do not promise that the result is `valid()`, although
      `with_capacity` and the removals do. The view does not fix the `len` field. With the clause
      added (checked on a scratch copy of the gold spec), all three obligations are proved.
    - `vacant_entry` does not tie the entry to the slab it borrows.
    - `VacantEntry::insert` does not describe the insertion; its comment says so.
    - In `retain`, the events are not tied to the closure; its comment says so. The vacant-list
      clause of Claude's contract is proved; only `retain_step`, the link to `f.ensures`, is not.

**Self-check.** Negating `contains`' gold postcondition, and corrupting `get`'s and
`VacantEntry::key`'s, turns all three from proved to unproved. Each failure names the clause.
Eight further mutations of proved gold clauses were all caught. These included a wrong `insert`
key, a `removed` that keeps the free list, a `retained` without the `reverse`, and dropped return
values. Five were reported as unproved obligations. In the other three, the mutated gold
definition broke a linking lemma, so the run was refused. None was reported as proved.

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
| M18 | `Iter::next` does not decrement `len` | postcondition of `iter_next` |
| M19 | `Iter::next` does not advance the key | loop invariant of `iter_next` |
| M20 | `Iter::next_back` yields the key one past the entry | postcondition of `iter_next_back` |
| M21 | `iter` starts counting keys at 1 | postcondition of `iter` |
| M22 | `index_mut` always returns the value at key 0 | postcondition of `index_mut` |

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
- **`iter` docs.** `next` returns `(0, &0)`, `(1, &1)`, `(2, &2)`, then `None`.
- **Upstream test `iter_rev`, with `next_back`.** After `remove(0)`, `len()` is 3, `next_back` returns `(3, &3)`, `(2, &2)` and `(1, &1)`, then `None`, and `len()` is 0.
- **A `for` loop over `slab.iter()`.** For any `wf()` slab, each `(key, value)` the loop sees has `slab@[key] == Some(*value)`, and the loop body runs `slab.len()` times.
- **`slab[key] = 2`.** Afterwards `slab[key] == 2`, and the slab is still `wf()`: the next `insert` returns 1.

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
- **Negative controls.** All 17 were still rejected. M7 was then rejected by an rlimit in the
  `recreate_vacant_list` loop rather than by the assertion before the `break`; after the changes
  in the next section, it is rejected by that assertion again.

## Newly verified with Verus 0.2026.10.18

The new vstd specifies more of std. On 2026-10-26 this made three trusted items verifiable:

- **`IndexMut`.** vstd's `index_mut` now has the same precondition as `index`
  (`index_req`), so `slab[key] = v` can require an occupied key instead of panicking.
- **`iter` and `Iter` (previously in T1).** vstd now has an iterator specification: an iterator provides
  a prophetic `remaining()` sequence, and `next` and `next_back` must remove and return its first
  and last item. `Iter`'s `remaining()` is the `(key, &value)` pairs of the occupied slots it has
  not yet yielded, and a type invariant says that `len` counts them. Verified clients can use
  `slab.iter()` in `for` loops.
- **`Clone for Iter`**, which copies the fields.

Still trusted, and why:

- **`IntoIter`.** I verified it too, then reverted it. Its fields must be updated through one
  helper call (the type invariant is checked after every field assignment), and Verus requires
  such a helper to be `no_unwind`. vstd does not mark `Iterator::next` as `no_unwind`, so the
  helper cannot call `vec::IntoIter::next`. Adding `no_unwind` to those specs in vstd would
  unblock it. The workaround, swapping the whole iterator out on every `next`, would cost speed.
- **`IterMut`.** Its items are `&mut T`, so `remaining()` must predict references that do not
  exist yet. vstd's own verified `slice::IterMut` example needs custom prophecy machinery
  (`ProphecyGhostConstrainedSeq`) for this.
- **The `IntoIterator` impls for `Slab` and `&Slab`.** A trait method cannot have a precondition,
  and the iterators' invariants need `wf()`.
- **`get_unchecked`, `get_unchecked_mut`, `capacity`, `reserve`, `reserve_exact`,
  `shrink_to_fit`, `clone_from` and `drain`.** vstd still does not specify
  `<[T]>::get_unchecked`, `Vec::capacity`, `Vec::reserve_exact`, `Vec::shrink_to_fit`,
  `Vec::clone_from` or `vec::Drain`.

vstd now also specifies `<[T]>::get_mut`, so the `vec_get_mut` and `slice_get_mut` stand-ins could
be replaced by upstream's calls. That is not done here.

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
  loops over unspecified iterators therefore has to live outside `verus!`. All of it is in
  `trusted.rs`, which Verus skips through one `#[verifier::external]` on the module declaration.
- **Trait impls are all-or-nothing.** One method of a trait impl cannot be external, which is why
  `clone` goes along with `clone_from`. (In 0.2026.05.03, vstd's `IndexMut` declared no method, so
  `index_mut` could not carry a precondition. The new vstd gives it `index_req`.)
- **Trait methods cannot have preconditions.** So a trait impl cannot require `wf()`, and the
  `IntoIterator` impls stay trusted. A type invariant would be the alternative, but putting one on
  `Slab` would mean restructuring every method that updates its fields.
- **Type invariants.** Verus checks a `#[verifier::type_invariant]` after every assignment to a
  field. Updates that break it temporarily go through one call that borrows all the fields, and
  that call must be `no_unwind`. This is what blocks `IntoIter` (see above).
- **Iterator-spec traits.** Inside an `impl IteratorSpecImpl` block, `x.remaining()` is ambiguous
  between `IteratorSpec` and `IteratorSpecImpl`, so the crate imports only `IteratorSpec` and
  names the `*SpecImpl` traits by path. Method calls on `final(x)` need an explicit dereference:
  `(*final(x)).remaining()`.
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
  - `mem::replace`, `From<T> for Option<T>`, `Vec::{capacity, reserve_exact, shrink_to_fit, clone_from, drain}`, `<[T]>::get_unchecked`, `Enumerate`, the `next_back` of `slice::Iter` and `slice::IterMut`, and `Iterator::size_hint` are unspecified. (`<[T]>::get_mut` and `iter_mut` were unspecified in 0.2026.05.03 and are specified now.)
  - Derived `Clone` impls get no spec (warning only).
- **`cargo verus` is still unusable with this release.** It panics compiling the crates.io vstd
  (`unexpected verus diagnostic item … shr_ref_struct_wrap`). The bare binary works.

## Reproduce

See [`slab/README.md`](slab/README.md):
`verus --crate-type=lib --no-cheating --cfg 'feature="std"' src/lib.rs` from `verus/slab/`, and
`cargo test --features serde` for the upstream tests. From `verus/`: `python3 negative_controls.py`,
`python3 check_trusted.py`, `python3 detect_changes.py`, `python3 test_detect_changes.py` and
`python3 compare_specs.py`.
