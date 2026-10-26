# `slab` annotated for Verus

`src/` is slab `master` (7d1d8ab, v0.4.12) with Verus specifications and proofs added in place.
Results, contracts, the trusted base and the audited list of code changes are in
[`../VERIFICATION.md`](../VERIFICATION.md); the full diff against upstream is
[`../upstream.diff`](../upstream.diff).

- `src/lib.rs`, `src/builder.rs`: upstream code. Everything inside a `verus! { ... }` block is
  verified. Everything outside one is trusted (not verified), marked
  `#[cfg_attr(verus_keep_ghost, verifier::external)]` with a `// TRUSTED (not verified): reason` comment.
- `src/spec.rs`: the specification (abstract state, invariant, lemmas). Ghost code only; nothing in it is trusted.
- `src/std_ext.rs`: verified stand-ins for `<[T]>::get_mut` and `mem::replace`, which vstd does not specify.
- `src/verified_examples.rs`: verified clients that prove documented examples from the contracts.
- `src/serde.rs`, `tests/`: unchanged from upstream.

## Reproduce

Verus 0.2026.10.18.7d82994 (bare `verus` binary with its bundled vstd; with 0.2026.05.03, `cargo verus`
panicked while compiling the crates.io vstd, and this has not been rechecked). Run from this directory:

    verus --crate-type=lib --no-cheating --cfg 'feature="std"' src/lib.rs   # 74 verified, 0 errors
    verus --crate-type=lib --no-cheating src/lib.rs                          # no_std: 74 verified, 0 errors

Normal build and the upstream tests (ghost code erased; toolchain pinned to 1.95.0 by `rust-toolchain.toml`):

    cargo build && cargo build --no-default-features && cargo build --features serde
    cargo test --features serde        # 47 integration + 38 doc + 2 serde tests
