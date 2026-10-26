# `slab` annotated for Verus

`src/` is slab `master` (7d1d8ab, v0.4.12) with Verus specifications and proofs added in place.
Results, contracts, the trusted base and the audited list of code changes are in
[`../VERIFICATION.md`](../VERIFICATION.md); the full diff against upstream is
[`../upstream.diff`](../upstream.diff).

- `src/lib.rs`, `src/builder.rs`: upstream code, verified (inside `verus! { ... }` blocks).
- `src/trusted.rs`: upstream code that is trusted, not verified. Verus skips the module
  (`#[verifier::external]` on its declaration); each item has a `// T<n>: reason` comment.
- `src/spec.rs`: the specification (abstract state, invariant, lemmas). Ghost code only; nothing in it is trusted.
- `src/std_ext.rs`: verified stand-ins for `<[T]>::get_mut` and `mem::replace`, which vstd does not specify.
- `src/verified_examples.rs`: verified clients that prove documented examples from the contracts.
- `src/serde.rs`, `tests/`: unchanged from upstream.

Scripts in `../`:
- `negative_controls.py`: injected bugs that Verus must reject.
- `check_trusted.py`: `src/trusted.rs` is verbatim upstream.
- `detect_changes.py`: every change to executable code, against human approvals in
  `approved_changes.json`; writes `changes_report.md`.
- `test_detect_changes.py`: injected edits that `detect_changes.py` must flag or ignore.

## Reproduce

Verus 0.2026.10.18.7d82994 (bare `verus` binary with its bundled vstd; with 0.2026.05.03, `cargo verus`
panicked while compiling the crates.io vstd, and this has not been rechecked). Run from this directory:

    verus --crate-type=lib --no-cheating --cfg 'feature="std"' src/lib.rs   # 94 verified, 0 errors
    verus --crate-type=lib --no-cheating src/lib.rs                          # no_std: 94 verified, 0 errors

Normal build and the upstream tests (ghost code erased; toolchain pinned to 1.95.0 by `rust-toolchain.toml`):

    cargo build && cargo build --no-default-features && cargo build --features serde
    cargo test --features serde        # 47 integration + 38 doc + 2 serde tests
