# Shared input tables

Runtime import keeps the producer's shared JSON references until the reader
extracts typed data. It does not first construct a fully expanded JSON tree.
`decodeRuntimeJson` and `decodeRuntimeJsonProfiled` use `Reader.Catalog` and
`JsonTraversalCache.fromCatalog`. Production has no expanding resolver or
alternate traversal branch. The old `SharedPayloads.resolveGraph`, expanded
comparison decoder and structural traversal builder live exclusively under
`MiriTests/Input`; only tests import them.

The reader checks references and their contextual roles, then stores types,
layouts, ABI evidence, MIR syntax and compiler-query results in typed tables.
Shared syntax IDs index checked `Array (Option ...)` slots. A missing, wrong-role
or out-of-range slot fails; it does not synthesize an instruction or successful
query. Query-specific failures remain typed deferred results where appropriate.
The interpreter reads place, operand, rvalue, statement, block and terminator IDs
directly through these tables. Compiler adapters consume typed semantic fields,
including constant normalization, complete instances, vtable predicates, startup,
panic strategy, foreign symbols, allocation-world identity and source spans.
A generic JSON cursor is confined to the import/validation boundary.
Producer diagnostic paths are interpreted against the original transport order;
dense typed tables use explicit IDs. These two coordinate systems are kept
separate. Symbolic const parameters remain symbolic when the producer reports
an incomplete uninstantiated generic template; concrete evaluated constants
still require supported evidence.

`RuntimeProgram` owns one input and provides its lowered-program and runtime
views. Updating the lowered tables preserves that input. Preparation therefore
needs neither an expanded-JSON equality check nor a JSON reflexivity certificate
to bind those views. Physical allocation data, source/runtime allocation IDs,
complete query keys, salts and conflicting evidence still have checked typed
validation. Constant reuse checks the complete instance and original constant,
then the normalized constant and span; a colliding numeric ID alone is not a
successful compiler query.

Frames carry execution tables obtained from their checked loaded body.
Canonical compiler instruction/span queries read the prepared compiler's tables,
so manually replacing a frame's table cannot impersonate compiler evidence.
The body identity, body ID, body metadata and full-instance guards still apply.
The evaluator's instruction lookup continues to reject missing execution slots.

Ordinary source-MIR records retain source information and extracted syntax
obligations, rather than a second executable syntax tree. `Miri.MIR.Contents`
reconstructs a flat semantic observation for proofs only. The independent flat
lowering and expanded-JSON adapters live in the test oracle. Neither is the
interpreter's execution representation. Full diagnostic `decodeJson` can still
retain its diagnostic projection; use runtime import for execution.

The public import/preparation API changes with this representation. Compatibility
with handcrafted records, old inline-only ABI fixtures and exact legacy malformed
JSON diagnostic wording is not provided. Tests emit the current ID format and
check accepted values, rejected evidence, failure isolation and rollback at the
reader boundary. This does not relax guest UB, provenance, initialization,
allocation identity, permissions or concurrency checks.

## Validation and limits

The final-source default build and its repeat passed (775 jobs); the aggregate
axiom audit checked 75,803 declarations using only the three allowed axioms.
The VM runtime registry passed all 50 checks. `tools/check-quick.sh` passed all
97 Python tests plus the semantic-source, coverage, ledger and fixture-integrity
checks. `+NativeRunner:olean` passed without constructing a native executable.
All 303 empty-function proof roots passed against 675 frozen source/library
modules; the example's axiom audit covered 73,747 declarations.

A fresh 25MB symbolic-repeat export completed the full VM guest with exit 0,
including its assertion that repeating 7 three times initializes element 2 and
returns 10 after adding the length. The pinned independent Miri execution also
completed with exit 0. The final-source isolated Lean run took 96.217 seconds
(CPU 96.196 seconds, peak RSS 3.03GB); it has no matching large baseline timing.


The input suite passed in one full run: 64 Lean invocations and 8 fresh genuine
exports, using the unchanged pinned exporter binary (exporter rebuilding was
excluded because of local storage limits). The independent old flat lowering
comparison passed for 97 bodies and 231 blocks.


Final VM comparison (2026-11-07, baseline `7c4cb57`, three measured alternating
pairs after one warmup pair, CPU 2, one Lean thread, fresh unchanged pinned
exporter per run; exporter included, build excluded):

| no_std/custom-start workload | baseline wall median | ID-table wall median | baseline/head peak RSS median |
| --- | ---: | ---: | ---: |
| empty main | 6.656s | 5.982s | 1.272 / 1.327GB |
| HRTB upcast and assertion | 8.398s | 7.449s | 1.276 / 1.335GB |

Observed wall differences are −10.1% and −11.3%; these small shared-host samples
are not a general speedup claim. Both workloads completed with exit 0 in all
rounds. Source and all frozen artifact hashes matched before/after; there was
no observed throttling and CPU steal counters were recorded. Baseline/head
both rejected dangling and guaranteed-align4 negative controls. Native binaries
were not compared, and the 25MB guest has no matched large baseline timing.

`tests/input/UnexpandedTransport.lean` compares normal import with the explicit
expanded oracle for readiness, obligations and typed MIR, and verifies that normal
import retains the unexpanded transport. The ID and compiler-table tests cover
checked slots, source-role errors, normalization conflicts, independent query
failures and failed-reader rollback. `CanonicalFrameTables.lean` checks that
forged frame tables cannot change canonical compiler instructions or spans.
`AllocWorldTypedValidation.lean` checks typed world validation even after deleting
diagnostic JSON, plus invalid frontiers, pools, identities and salt coverage.

The empty-function example is a separate kernel-checked, conditional result;
its exact scope is documented in [its README](../examples/empty_function/README.md).
Finite oracle comparisons and selected guest executions do not establish generic
reader equivalence, exporter correctness, Rust correspondence or UB freedom for
all programs and permitted choices. Current missing validation remains listed
in [STATUS](../STATUS.md).
