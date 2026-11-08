# Empty-function UB freedom

`ActualNoUBFinal.target` proves `TotalCallGoal.Target s`: actual initialization
and every finite execution prefix of `pub fn empty_function() {}` report no undefined
behavior while this call remains in scope. `ActualNoUBFinal.noUB` is the
per-caller theorem; neither entry point takes remaining family or stage proofs.

The target admits exactly the following premises:

```lean
(Nonempty (Metadata s)) → Profile s →
  ∀ p, RuntimeProfile s p ∧ Nonempty (InputDraft.CurrentInputDraft s p) →
    CallLevelNoUB.NoUB s p
```

Allocator/generator coherence for projected backing is required only when
its raw runtime and enabled-source counters are active. Zero/wrapped counters
and exhaustion flags remain admitted; when allocation is attempted, its
actual checked error is observed. Reserving the final MAX ID itself is also admitted.
`AllocatorActive` is a guard on coherence fields, not a caller premise, and
the allocator implementation is unchanged.

There is no numeric resource reserve, supported-choice/`ChoiceFits` condition,
successful-return premise, or remaining family/stage proof in this target.
Both actual initialization errors and actual in-call errors are observed with
their failed states. Checked non-UB stops, including resource exhaustion, are
allowed. This is a UB-freedom result; it does not promise normal return for
all resource supplies. The normal-return/NoErrors and eleven-clause
preservation theorems are conditional intermediate results.

`CurrentInputDraft` describes the admitted raw machine states: caller/local
bindings and representations, pointer/source metadata, live allocation and
Tree Borrows coherence, address/ID tables, and the runtime dictionaries used
by the actual call. Other caller state is arbitrary within those premises.
The agreed pure compiler metadata properties are assumed as `Metadata`, not
introduced as Lean axioms. A theorem mapping every Rust-valid caller state to
this explicit domain has not been proved. Compiler/exporter correctness and
correspondence between the interpreter and Rust remain trusted boundaries.

`Profile` and `RuntimeProfile` retain the exact switches in
`Specification.lean`: fixed scheduling, absent race clocks/weak backend,
shallow validation, and the specified debug, retag, and control configuration.
The observer ends after returning to the caller; arbitrary scheduler
interleavings and later caller execution are outside this theorem.

Miri source additions expose proof-only APIs; the interpreter implementation
is unchanged by this example. The fixed Rust/MIR hashes are recorded in
`SHA256SUMS`. The proof-only reflected MIR block is `noncomputable` to avoid
a Lean native-code-generation boxing panic; no native executable validation
of that block is claimed.

`input.json` is a fresh root-schema-4 export from the pinned rustc/Miri
exporter, using the same root and compiler flags as the preceding input.
Types, definitions, spans, constants and ABI metadata use the current numeric
identity tables. The production importer resolves those references before the
example reflects its ordinary Lean constants; no historical JSON conversion or
compatibility reader participates in this proof. This transport migration does
not change the Rust function, caller/profile premises, or final UB-freedom claim.

To regenerate it after building the pinned exporter and MIR sysroot, run from
the repository root with `EXPORTER_BIN` and `MIRI_SYSROOT` pointing to those
artifacts:

```sh
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=0 LEAN_MIRI_RUN_PREPARED_MIRI=0 \
  "$EXPORTER_BIN" --output scratch/empty-function-schema4.json \
  --root empty_function -- examples/empty_function/empty_function.rs \
  --crate-type=lib --crate-name=empty_function --edition=2024 \
  -Zmir-opt-level=0 --cfg=miri -Zalways-encode-mir \
  -Zextra-const-ub-checks -Zmir-preserve-ub \
  -Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums \
  -Zmir-enable-passes=-ReferencePropagation,-GVN \
  -Zdeduplicate-diagnostics=no --sysroot "$MIRI_SYSROOT"
```

Review the generated input, replace the committed snapshot, update its
`SHA256SUMS` entry, and rerun the proof checks below. The Rust source hash must
remain unchanged for this example.

Run `bash tools/check-empty-function.sh` to compile the committed root and its source
closure, check the final target type, and audit imported EmptyFunction/Miri declarations
(including private/generated declarations) for transitive axioms. Only
`propext`, `Quot.sound`, and `Classical.choice` are permitted.
See [STATUS.md](../../STATUS.md#empty-function-caller-domain-transport).

## Continuous integration

[The proof workflow](../../.github/workflows/empty-function-proof.yml) runs the full
`Check` closure on `main` pushes and by manual dispatch. It checks fixed-input hashes and transitive axioms. Only the
Lean toolchain and library build artifacts are cached; example proofs are
checked again on every run. Diagnostic logs are retained as workflow artifacts.
