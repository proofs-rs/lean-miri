# duplicate_prefix

A client example in the existing Lake project. The Rust source is exported
with the repository's pinned rustc/Miri toolchain and reflected into Lean
constants with `Miri.Frontend.ImportMIR`. The included library explicitly
changes wildcard postorder handling; these proofs target that implementation.

Run from the repository root:

```bash
bash tools/check-duplicate-prefix.sh
```

This checks the retained source/input hashes, compiles the MIR import and
component theorems in the Lean kernel, and rejects transitive axioms other
than `propext`, `Quot.sound` and `Classical.choice`. No new toolchain downloads
or MIR export are required once the normal Lean setup is available.
Each run uses a fresh client output directory under ignored `scratch/` because
the external JSON read by `import_mir` is not an ordinary Lean import dependency.
To check a selected component and its complete import closure, pass its module
name, for example `bash tools/check-duplicate-prefix.sh GeneralBorrowRange`.
Multiple module names select the union of their closures. Selected-root runs
also audit every imported example theorem; they do not certify unselected drafts.

The example proves complete function calls inside the pinned Lean interpreter
for the declared current valid-call-input domain and older explicit caller
contracts, including every UInt64 count, normal physical return and finite-prefix
UB freedom. GenericFunctionPoolSafety accepts
a call-time PoolInput directly; generated-history theorems separately establish
such premises for selected client families. Arbitrary pre-call history formation
is an additional guarantee, not a prerequisite for call-time function safety.
The exposed-concrete bounded-window family also has a complete all-count
call-time theorem, GeneralBorrowPositiveConcreteWindowAllCountSafety.invoke,
with its permission/leaf/tag-order/allocator limits kept explicit.

`S03EmptyContract.complete` proves empty-slice safety for every UInt64 count
and every argument/return provenance admitted by the explicit
`S05ConsistentCallSpecification.ConsistentContract`. Initialization, actual MIR
execution, return, absence of interpreter errors and finite-prefix NoUB are
proved internally. The contract includes fixed model/resource/external metadata
conditions and the approved initial extras/cache consistency refinement; it is
not a characterization of every valid Rust caller. Original contracts remain
available unchanged. Check this theorem independently with
`bash tools/check-duplicate-prefix.sh S03EmptyContract`.

On this revision, `S05ZeroCellActualCallRepaired` provides completion regressions
using a generated tree.
The strong Result definition remains unchanged.
`CurrentCallOrdinarySafety.invoke input count` proves it for ALL declared current
ordinary inputs, including empty slices, and every UInt64 count. The theorem
internally selects all source/return representations, LIVE/CURRENT backing and
SAME/different IDs. SAME-ID conversion happens once; different-ID conversion is
connected in sequence. Original initialization, execution, release/store/return,
NoErrors, finite-prefix NoUB and progress use the shared continuations.

OrdinaryInput explicitly states physical/ABI/copy identity, per-byte ownership,
pointer/address/cache/root consistency, configuration, finite resources, external
metadata and typed choice-input readiness. No operation-success, NoUB, producer
factory or intermediate checkpoint is an additional public premise. Removing
these explicit conditions, arbitrary caller-history formation, Rust computation
equivalence and extra Bool-value guarantees are outside this completed goal.
Check the final theorem with
`bash tools/check-duplicate-prefix.sh CurrentCallOrdinarySafety`.
`CurrentCallOrdinaryWitness.nonempty` constructs one concrete positive input,
conditional only on the existing fixed span and two JSON-comparator contracts.
Its CURRENT source and return share a three-byte allocation: source [0,2), Bool
[2,3), initial bytes [11,22,0]. `CurrentCallOrdinaryWitness.positive_result`
applies the original theorem at length 2/count 1, whose nonzero accepted-copy
guard is proved separately. This is a synthetic registry: all 15 fixed
relocation targets map to the same runtime ID. It proves declared-domain
nonemptiness, not initial LIVE ownership or formation from a Rust history.
Check it with
`bash tools/check-duplicate-prefix.sh CurrentCallOrdinaryWitnessSafety`.
See [STATUS.md](../../STATUS.md#completed-duplicate_prefix-ordinary-input-goal)
for current validation and the separation between old and new results.

| File | Claim or role |
| --- | --- |
| `duplicate_prefix.rs` | The original function using `std::ptr::copy_nonoverlapping` |
| `input.json` | Retained rooted MIR, compiler metadata and producer evidence |
| `Program.lean` | Safe constant import and facts about the fixed document |
| `Bounds.lean` | Unsigned guard, checked arithmetic, actual allocation-bounds checks and adjacency |
| `Alignment.lean` | Actual `checkPtrAlign` accepts `Align.ONE` for any pointer |
| `PointerAccess.lean` | Actual dereference check from resolution, live metadata and derived bounds |
| `Borrows.lean` | FnEntry policy and actual accesses on an explicit two-node location tree |
| `CallSafety.lean` | Call-scoped safety predicates over production `ExecutionMachine.step` |
| `DuplicatePrefixCallResult.lean` | Common real-call/return, NoErrors and NoUB conclusion; existing Pool adapter |
| `DuplicatePrefixBorrowContract.lean` | Static runtime facts and window-local normal Write kernel; full caller coverage remains open |
| `DuplicatePrefixCallSpecification.lean` | Older provisional contract and all-count goal; separate from the adopted ordinary-input declaration |
| `DuplicatePrefixArgumentCallResult.lean` | Common actual-call result for pointer and integer/no-provenance slice encodings; preserves the older pointer result |
| `CurrentCallOrdinaryInput.lean` | Explicit current-input ownership, physical representation, configuration, metadata and resource conditions |
| `CurrentCallOrdinarySafety.lean` | All declared ordinary inputs and all UInt64 counts imply the unchanged original strong Result |
| `CurrentCallOrdinaryWitness.lean` | Concrete positive CURRENT/CURRENT input and conditional nonemptiness of the declared domain |
| `CurrentCallOrdinaryWitnessSafety.lean` | Original strong Result for that input at length 2/count 1, with the accepted-copy guard |
| `CurrentCallOrdinaryJointSafety.lean` | Original strong Result for every count in the adopted positive source/LIVE return branch with both allocations LIVE; per-byte spatial source ownership |
| `S05ZeroCellActualCallRepaired.lean` | Revised generated-state access/copy completion regressions |
| `Check.lean` | Imports and transitive axiom audit |

`guarded_copy_checks` quantifies over arbitrary 64-bit lengths/counts and
allocation-relative slice starts. Its assumptions are containment of the
slice in an allocation, signed-representable slice length, and the unsigned
branch guard. It derives successful source and destination `checkedBounds`
calls and the checked source endpoint. It does not assume these conclusions.
`u8_checkPtrAlign_all_pointers` uses the actual alignment checker, with arbitrary
pointer provenance, resolver, lookup, enforcement policy and machine hook.
Neither theorem asserts that the enclosing interpreter invocation has been
constructed or proved safe.

The call-scoped infrastructure stops extending a trace once stack depth drops
below the entry depth. It does not classify unwinding as normal return, prove
that the original frame is retained at that depth, construct a valid call, or
supply a client invariant. A whole-program `RunLoop.UBFreedomFrom` claim would
also include the caller's later code and is not the function-local goal.

To regenerate MIR after changing the source:

```bash
bash examples/duplicate_prefix/export.sh
sha256sum examples/duplicate_prefix/duplicate_prefix.rs \
  examples/duplicate_prefix/input.json \
  examples/duplicate_prefix/prior_cell_context/prior_cell_context.rs \
  examples/duplicate_prefix/prior_cell_context/input.json > examples/duplicate_prefix/SHA256SUMS
bash tools/check-duplicate-prefix.sh
```

Inspect the regenerated artifact and producer metadata before updating hashes.
The retained target is `x86_64-unknown-linux-gnu`; rustc is
`8144389c895da997dbdecaa635e41d6a50be6ffd`, Miri is
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`, and Lean is pinned by the repository's
`lean-toolchain`. This example is checked together with its enclosing
repository revision, rather than fetching another library copy.
`LIBRARY-SHA256SUMS` binds the exact library sources and build configuration;
the DAG checker verifies both its content hash and every listed file.
The wildcard postorder guard skips an exact-Foreign node only for Cell,
Disabled when unprotected or unaccessed, or unprotected ReservedIM, and only
when the postchildren skip predicate permits it. Local kernel proofs establish
same-state normal return and preserve excluded protected errors.
Compiler/export correctness and fidelity to Rust remain trust boundaries.

The auxiliary `prior_cell_context/` source obtains caller type metadata from
`UnsafeCell<()>` and `&mut [u8]`. Regenerate it with
`bash examples/duplicate_prefix/prior_cell_context/export.sh` after the ordinary
pinned exporter/sysroot setup. Its JSON is separate from the fixed function MIR;
`S05PriorCellProgram` imports that document; `S05PriorCellPrepared` reflects
preparation products with an independent document-identity check. The metadata
and layout modules prove actual compiler-query facts about those constants. All four Rust
and JSON inputs are bound in `SHA256SUMS`; the checker verifies them before and
after fresh example elaboration. Regeneration changes producer path metadata and
requires inspecting the export before updating its hash.

These auxiliary type facts do not execute `prior_context` as a caller prefix.
That function's entry retags have protectors; the finite caller construction uses
explicit Default retags. Type IDs are local to the auxiliary document and cannot
replace fixed function metadata or establish that every caller is admissible.

## Continuous integration

[The proof workflow](../../.github/workflows/duplicate-prefix-proof.yml) runs the full
`Check` closure on `main` pushes and by manual dispatch. It checks fixed-input hashes and transitive axioms. Only the
Lean toolchain and library build artifacts are cached; example proofs are
checked again on every run. Diagnostic logs are retained as workflow artifacts.
