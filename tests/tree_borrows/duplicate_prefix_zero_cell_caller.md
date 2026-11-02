# Finite zero-cell caller Miri diagnostic

`duplicate_prefix_zero_cell_caller.rs` is one unsafe diagnostic using the
unchanged `examples/duplicate_prefix/duplicate_prefix.rs` with len2/count1.
It is not an automatically passing test or a Rust validity proof.
See [STATUS.md](../../STATUS.md#one-finite-pinned-miri-rust-caller-qa) for the
source-event correspondence, current results and dependency hashes.

With the existing pinned QA environment, run from the repository root:

```bash
qa_tools=/workspace/lean-miri
LD_LIBRARY_PATH="$qa_tools/.rustup/toolchains/miri-exporter-8144389c895d/lib" \
  "$qa_tools/upstream/miri-source/target/debug/miri" \
  --sysroot="$qa_tools/scratch/miri-sysroot" --edition=2021 \
  --crate-name=duplicate_prefix_zero_cell_caller -Copt-level=0 -Cdebug-assertions=yes \
  -Zmiri-tree-borrows -Zmiri-tree-borrows-no-precise-interior-mut \
  -Zmiri-permissive-provenance -Zmiri-disable-data-race-detector -Zmiri-seed=0 \
  tests/tree_borrows/duplicate_prefix_zero_cell_caller.rs
```

The observed debug-Miri exit101/panic is at pinned `tree.rs:241`,
`LocationState::record_new_access`. Neither captured run emitted an earlier UB
diagnostic; a crash does not establish absence of UB. ICE, timeout or unsupported
execution is not successful safety validation and does not classify this source
as valid or invalid Rust. Guest debug assertions do not toggle host assertions.

Miri pin: `7fa591d7d4dd9af8154becbc8332f8096f8323b1`; rustc pin:
`8144389c895da997dbdecaa635e41d6a50be6ffd`. This reuses existing freshly hashed
artifacts, not a fresh/hermetic sysroot build. Rust validity, ordinary caller
admission and identity of compiler-generated tags/state to the Lean packet remain
unproved. The Lean certificate uses its stated static interpretation; the three
metadata conditions and ValidInput are unchanged. No other case or flag setting
was tested for this diagnostic.
